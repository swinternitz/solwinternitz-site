/* ===========================================================================
   TETRABBLE — Tetris × Scrabble
   Authentic NES feel: frame-stepped gravity table, DAS (16/6), NES line scoring,
   level-based recolor, ARE + line-clear delay. Plus our Scrabble word-clears,
   arcade initials entry, gamepad/keyboard/touch, switchable chiptunes, fit-to-TV.
   =========================================================================== */
(function () {
'use strict';

// ---- Board geometry --------------------------------------------------------
const COLS = 10, ROWS = 20, CELL = 44;
const BW = COLS * CELL, BH = ROWS * CELL;

const board = document.getElementById('board');
board.width = BW; board.height = BH;
const ctx = board.getContext('2d');
const pCanvas = document.getElementById('previewCanvas'), pCtx = pCanvas.getContext('2d');
const hCanvas = document.getElementById('holdCanvas'), hCtx = hCanvas.getContext('2d');
const WORDS = window.TETRABBLE_WORDS || new Set();

// ---- Tetromino shapes ------------------------------------------------------
const PIECES = {
  I:[[[0,1],[1,1],[2,1],[3,1]],[[2,0],[2,1],[2,2],[2,3]],[[0,2],[1,2],[2,2],[3,2]],[[1,0],[1,1],[1,2],[1,3]]],
  O:[[[1,0],[2,0],[1,1],[2,1]],[[1,0],[2,0],[1,1],[2,1]],[[1,0],[2,0],[1,1],[2,1]],[[1,0],[2,0],[1,1],[2,1]]],
  T:[[[1,0],[0,1],[1,1],[2,1]],[[1,0],[1,1],[2,1],[1,2]],[[0,1],[1,1],[2,1],[1,2]],[[1,0],[0,1],[1,1],[1,2]]],
  S:[[[1,0],[2,0],[0,1],[1,1]],[[1,0],[1,1],[2,1],[2,2]],[[1,1],[2,1],[0,2],[1,2]],[[0,0],[0,1],[1,1],[1,2]]],
  Z:[[[0,0],[1,0],[1,1],[2,1]],[[2,0],[1,1],[2,1],[1,2]],[[0,1],[1,1],[1,2],[2,2]],[[1,0],[0,1],[1,1],[0,2]]],
  J:[[[0,0],[0,1],[1,1],[2,1]],[[1,0],[2,0],[1,1],[1,2]],[[0,1],[1,1],[2,1],[2,2]],[[1,0],[1,1],[0,2],[1,2]]],
  L:[[[2,0],[0,1],[1,1],[2,1]],[[1,0],[1,1],[1,2],[2,2]],[[0,1],[1,1],[2,1],[0,2]],[[0,0],[1,0],[1,1],[1,2]]],
};
const KEYS = Object.keys(PIECES);
// base hue per piece; level rotates the whole palette (authentic NES recolor feel)
const BASE_HUE = { I:188, O:52, T:286, S:145, Z:0, J:222, L:32 };
function pieceHSL(k, lvl){ return [((BASE_HUE[k]||0) + (lvl-1)*24) % 360, 85, 58]; }
const EMPTY_HSL = [230, 35, 7];
function hslStr(a, dl){ return 'hsl('+a[0]+','+a[1]+'%,'+Math.max(0,Math.min(100,a[2]+(dl||0)))+'%)'; }

// ---- Letters ---------------------------------------------------------------
const SCRABBLE={A:9,B:2,C:2,D:4,E:12,F:2,G:3,H:2,I:9,J:1,K:1,L:4,M:2,N:6,O:8,P:2,Q:1,R:6,S:4,T:6,U:4,V:2,W:2,X:1,Y:2,Z:1};
const VALUE={A:1,B:3,C:3,D:2,E:1,F:4,G:2,H:4,I:1,J:8,K:5,L:1,M:3,N:1,O:1,P:3,Q:10,R:1,S:1,T:1,U:1,V:4,W:4,X:8,Y:4,Z:10};
function bag(w){ const b=[]; for(const k in w) for(let i=0;i<w[k];i++) b.push(k); return b; }
const BAGS={
  easy:bag(Object.assign({},SCRABBLE,{A:13,E:16,I:13,O:12,U:7,Q:0,Z:0,X:0,J:0,K:1,V:1,W:1})),
  medium:bag(SCRABBLE),
  hard:bag(Object.assign({},SCRABBLE,{A:6,E:8,I:6,O:5,U:3,Q:2,Z:2,X:2,J:2,K:3,V:3,W:3,Y:4})),
};
// levelEvery = how many clears (full rows + words) advance one level
const MODES={ easy:{minWord:3,startLevel:1,levelEvery:16}, medium:{minWord:3,startLevel:1,levelEvery:11}, hard:{minWord:4,startLevel:5,levelEvery:8} };

// ---- Authentic NES timing --------------------------------------------------
const FPS = 60.0988;                       // NES NTSC frame rate
const FRAME = 1/FPS;
// frames-per-row gravity table by level (level 1 -> index 0)
const GRAV=[48,43,38,33,28,23,18,13,8,6,5,5,5,4,4,4,3,3,3,2,2,2,2,2,2,2,2,2,2,1];
function framesPerRow(lvl){ const i=Math.max(0,Math.min(lvl-1,GRAV.length-1)); return GRAV[i]; }
const DAS_DELAY=16, DAS_REPEAT=6, SOFT_FPR=2, ARE_FRAMES=10, CLEAR_FRAMES=40;
const LINE_SCORE=[0,40,100,300,1200];      // NES: x (level)

// ---- State -----------------------------------------------------------------
let grid, cur, nextQueue=[], holdKey=null, holdUsed=false, nextLetters=[];
let mode='medium', score=0, level=1, lines=0, wordsCleared=0;
let best=+(localStorage.getItem('tetrabble_best')||0);
let gameState='idle';                      // idle | playing | dead
let gravCounter=0, dasDir=0, dasTimer=0, areTimer=0, clearTimer=0, chain=0;
let pendingClear=null;
let leftHeld=false, rightHeld=false, downHeld=false;
const wordTally=new Map(); const wordPts=new Map(); let wordOrder=[];

function randLetter(){ const b=BAGS[mode]; return b[(Math.random()*b.length)|0]; }
function genLetters(){ return [randLetter(),randLetter(),randLetter(),randLetter()]; }
let typeBag=[];
function nextType(){
  if(!typeBag.length){ typeBag=KEYS.slice(); for(let i=typeBag.length-1;i>0;i--){ const j=(Math.random()*(i+1))|0; [typeBag[i],typeBag[j]]=[typeBag[j],typeBag[i]]; } }
  return typeBag.pop();
}
function canAct(){ return gameState==='playing' && cur && clearTimer===0 && areTimer===0; }

// ---- Piece mechanics -------------------------------------------------------
function spawnPiece(){
  const k=nextQueue.shift(); nextQueue.push(nextType());
  const letters=nextLetters; nextLetters=genLetters();
  const p={k,rot:0,x:3,y:-1,letters};
  holdUsed=false; gravCounter=0;
  if(collides(p,p.x,p.y,p.rot)){ endGame(); return; }
  cur=p;
}
function cellsOf(p,x,y,rot){ return PIECES[p.k][rot].map(([dx,dy])=>[x+dx,y+dy]); }
function collides(p,x,y,rot){
  for(const [cx,cy] of cellsOf(p,x,y,rot)){
    if(cx<0||cx>=COLS||cy>=ROWS) return true;
    if(cy>=0 && grid[cy][cx]) return true;
  } return false;
}
function tryMove(dir){ if(cur && !collides(cur,cur.x+dir,cur.y,cur.rot)){ cur.x+=dir; sfx('move'); } }
function rotate(dir){
  if(!canAct()) return; const nr=(cur.rot+(dir>0?1:3))%4;
  for(const kx of [0,-1,1,-2,2]) if(!collides(cur,cur.x+kx,cur.y,nr)){ cur.x+=kx; cur.rot=nr; sfx('rotate'); return; }
}
function stepDown(soft){
  if(!collides(cur,cur.x,cur.y+1,cur.rot)){ cur.y++; if(soft){ score++; updateHUD(); } }
  else lockPiece();
}
function hardDrop(){ if(!canAct()) return; let d=0; while(!collides(cur,cur.x,cur.y+1,cur.rot)){ cur.y++; d++; } score+=d*2; sfx('drop'); lockPiece(); }
function doHold(){
  if(!canAct()||holdUsed) return; holdUsed=true;
  if(holdKey===null){ holdKey=cur.k; spawnPiece(); }
  else { const s=holdKey; holdKey=cur.k; cur={k:s,rot:0,x:3,y:-1,letters:genLetters()}; gravCounter=0; }
  drawHold();
}
function lockPiece(){
  cellsOf(cur,cur.x,cur.y,cur.rot).forEach(([cx,cy],i)=>{ if(cy>=0) grid[cy][cx]={k:cur.k,letter:cur.letters[i]}; });
  cur=null; chain=0; beginResolve();
}

// ---- Clearing (rows + words) ----------------------------------------------
function findWordCells(){
  const minLen=MODES[mode].minWord, toClear=new Set(), found=[];
  function scan(coords){
    const letters=coords.map(([x,y])=>grid[y][x]?grid[y][x].letter:null), n=coords.length;
    for(let i=0;i<n;i++){ if(letters[i]===null) continue;
      for(let len=n-i;len>=minLen;len--){ if(i+len>n) continue;
        let ok=true,w=''; for(let kk=i;kk<i+len;kk++){ if(letters[kk]===null){ok=false;break;} w+=letters[kk]; }
        if(ok && WORDS.has(w)){ const wc=coords.slice(i,i+len); found.push({word:w,coords:wc}); for(const c of wc) toClear.add(c[0]+','+c[1]); i+=len-1; break; }
      }
    }
  }
  for(let y=0;y<ROWS;y++){ const c=[]; for(let x=0;x<COLS;x++) c.push([x,y]); scan(c); }
  for(let x=0;x<COLS;x++){ const c=[]; for(let y=0;y<ROWS;y++) c.push([x,y]); scan(c); }
  return {found,toClear};
}
function findFullRows(){ const r=[]; for(let y=0;y<ROWS;y++) if(grid[y].every(c=>c)) r.push(y); return r; }
function beginResolve(){
  const full=findFullRows(); const {found,toClear}=findWordCells();
  if(!full.length && !found.length){ areTimer=ARE_FRAMES; return; }
  chain++;
  scoreStep(full, found);
  pendingClear={ full:new Set(full), cells:toClear };
  clearTimer=CLEAR_FRAMES;
}
function finishClear(){
  // remove full rows + word cells, then compact columns
  for(const y of pendingClear.full) for(let x=0;x<COLS;x++) grid[y][x]=null;
  for(const key of pendingClear.cells){ const [x,y]=key.split(',').map(Number); grid[y][x]=null; }
  for(let x=0;x<COLS;x++){ const st=[]; for(let y=ROWS-1;y>=0;y--) if(grid[y][x]) st.push(grid[y][x]); for(let y=ROWS-1,i=0;y>=0;y--) grid[y][x]=(i<st.length)?st[i++]:null; }
  pendingClear=null;
  const full=findFullRows(); const {found}=findWordCells();
  if(full.length||found.length){ beginResolve(); }   // chain reaction
  else { chain=0; areTimer=ARE_FRAMES; }
}
function scoreStep(full, found){
  const simul = full.length>0 && found.length>0;
  const mult = (simul?2.5:1) * (chain>1?(1+0.5*(chain-1)):1);
  for(const w of found){
    let v=0; for(const ch of w.word) v+=(VALUE[ch]||1);
    wordsCleared++;
    const pts=Math.round(v*w.word.length*10*level*mult);   // this word's actual points
    recordWord(w.word, pts); queueWordPop(w, pts);
  }
  lines+=full.length;
  let gained = Math.round(LINE_SCORE[Math.min(full.length,4)]*level*mult);
  for(const w of found){ let v=0; for(const ch of w.word) v+=(VALUE[ch]||1); gained+=Math.round(v*w.word.length*10*level*mult); }
  score+=gained;
  // level advances on total clears (rows + words), so word-heavy play still ramps up
  const clears = lines + wordsCleared;
  const nl=MODES[mode].startLevel+Math.floor(clears/MODES[mode].levelEvery);
  if(nl>level){ level=nl; sfx('level'); }
  if(score>best){ best=score; localStorage.setItem('tetrabble_best',best); }
  if(full.length) sfx(full.length>=4?'tetris':'line');
  updateHUD();
}
function recordWord(w, pts){ wordTally.set(w,(wordTally.get(w)||0)+1); wordPts.set(w,(wordPts.get(w)||0)+(pts||0)); wordOrder=wordOrder.filter(x=>x!==w); wordOrder.unshift(w); renderWordList(); }
function renderWordList(){
  const el=document.getElementById('wordList'); if(!el) return; el.innerHTML='';
  for(const w of wordOrder){ const d=document.createElement('div'); d.className='wrow';
    const cnt=wordTally.get(w), p=wordPts.get(w)||0;
    d.innerHTML='<span class="w">'+w+'</span><span class="pts">'+p.toLocaleString()+'</span>'+(cnt>1?'<span class="c">×'+cnt+'</span>':'');
    el.appendChild(d); }
  const cnt=document.getElementById('wordCount'); if(cnt) cnt.textContent=wordsCleared+' words · '+wordTally.size+' unique';
}

// ---- Frame loop (fixed timestep) ------------------------------------------
let acc=0, lastT=0;
function tickFrame(){
  if(gameState!=='playing') return;
  if(clearTimer>0){ clearTimer--; if(clearTimer===0) finishClear(); return; }
  if(areTimer>0){ areTimer--; if(areTimer===0) spawnPiece(); return; }
  if(!cur) return;
  // DAS movement
  const dir=(leftHeld?-1:0)+(rightHeld?1:0);
  if(dir!==0){
    if(dir!==dasDir){ dasDir=dir; dasTimer=DAS_DELAY; tryMove(dir); }
    else { dasTimer--; if(dasTimer<=0){ tryMove(dir); dasTimer=DAS_REPEAT; } }
  } else dasDir=0;
  // gravity
  let fpr=framesPerRow(level); if(downHeld) fpr=Math.min(fpr,SOFT_FPR);
  if(++gravCounter>=fpr){ gravCounter=0; stepDown(downHeld); }
}
function loop(t){
  if(gameState!=='playing'){ return; }
  const dt=(t-lastT)/1000; lastT=t; acc+=dt;
  let steps=0;
  while(acc>=FRAME && steps<8){ tickFrame(); acc-=FRAME; steps++; }
  updateMusicDanger();
  drawPreview(); render();
  requestAnimationFrame(loop);
}

// ---- Rendering -------------------------------------------------------------
function roundRect(c,x,y,w,h,r){ c.beginPath(); c.moveTo(x+r,y); c.arcTo(x+w,y,x+w,y+h,r); c.arcTo(x+w,y+h,x,y+h,r); c.arcTo(x,y+h,x,y,r); c.arcTo(x,y,x+w,y,r); c.closePath(); }
function drawBlock(c,px,py,size,a,letter){
  const x=px+1,y=py+1,s=size-2;
  const g=c.createLinearGradient(x,y,x,y+s);
  g.addColorStop(0,hslStr(a,18)); g.addColorStop(.5,hslStr(a,0)); g.addColorStop(1,hslStr(a,-16));
  roundRect(c,x,y,s,s,5); c.fillStyle=g; c.fill();
  c.strokeStyle=hslStr(a,26); c.lineWidth=2; c.beginPath(); c.moveTo(x+2,y+s-3); c.lineTo(x+2,y+3); c.lineTo(x+s-3,y+3); c.stroke();
  c.strokeStyle=hslStr(a,-26); c.beginPath(); c.moveTo(x+s-2,y+3); c.lineTo(x+s-2,y+s-2); c.lineTo(x+3,y+s-2); c.stroke();
  if(letter){
    const cx=x+s/2, cy=y+s/2;
    c.font='900 '+Math.floor(s*0.6)+"px 'Trebuchet MS',Arial,sans-serif"; c.textAlign='center'; c.textBaseline='middle';
    c.lineJoin='round'; c.miterLimit=2;
    c.lineWidth=Math.max(3.5, s*0.12); c.strokeStyle='rgba(0,0,0,0.92)'; c.strokeText(letter,cx,cy);   // thick dark halo
    c.fillStyle='#ffffff'; c.fillText(letter,cx,cy);                                                     // crisp white face
    const v=VALUE[letter];
    if(v){ c.font='bold '+Math.floor(s*0.24)+'px Arial,sans-serif'; c.textAlign='right'; c.textBaseline='bottom';
      c.lineWidth=Math.max(2,s*0.06); c.strokeStyle='rgba(0,0,0,0.9)'; c.strokeText(v,x+s-3,y+s-1);
      c.fillStyle='rgba(255,255,255,0.92)'; c.fillText(v,x+s-3,y+s-1); }
  }
}
function render(){
  ctx.clearRect(0,0,BW,BH); ctx.fillStyle=hslStr(EMPTY_HSL); ctx.fillRect(0,0,BW,BH);
  ctx.strokeStyle='rgba(255,255,255,0.04)'; ctx.lineWidth=1;
  for(let x=0;x<=COLS;x++){ ctx.beginPath(); ctx.moveTo(x*CELL,0); ctx.lineTo(x*CELL,BH); ctx.stroke(); }
  for(let y=0;y<=ROWS;y++){ ctx.beginPath(); ctx.moveTo(0,y*CELL); ctx.lineTo(BW,y*CELL); ctx.stroke(); }
  const blink = pendingClear ? (0.5 + 0.5*Math.sin(clearTimer*0.5)) : 0;  // smooth pulse
  for(let y=0;y<ROWS;y++) for(let x=0;x<COLS;x++){ const cell=grid[y][x]; if(!cell) continue;
    drawBlock(ctx,x*CELL,y*CELL,CELL,pieceHSL(cell.k,level),cell.letter);   // always keep letters visible
    if(pendingClear){
      const isRow=pendingClear.full.has(y), isWord=pendingClear.cells.has(x+','+y);
      if(isRow||isWord){
        ctx.save();
        ctx.globalAlpha=0.25+0.45*blink;
        roundRect(ctx,x*CELL+1,y*CELL+1,CELL-2,CELL-2,5); ctx.fillStyle='#ffffff'; ctx.fill();
        ctx.globalAlpha=0.9; ctx.lineWidth=3; ctx.strokeStyle=isWord?'#ffd24a':'#ffffff';
        roundRect(ctx,x*CELL+2,y*CELL+2,CELL-4,CELL-4,4); ctx.stroke();
        ctx.restore();
      }
    }
  }
  if(cur && gameState==='playing' && clearTimer===0 && areTimer===0){
    let gy=cur.y; while(!collides(cur,cur.x,gy+1,cur.rot)) gy++;
    ctx.globalAlpha=0.2; for(const [cx,cy] of cellsOf(cur,cur.x,gy,cur.rot)) if(cy>=0) drawBlock(ctx,cx*CELL,cy*CELL,CELL,pieceHSL(cur.k,level),''); ctx.globalAlpha=1;
    cellsOf(cur,cur.x,cur.y,cur.rot).forEach(([cx,cy],i)=>{ if(cy>=0) drawBlock(ctx,cx*CELL,cy*CELL,CELL,pieceHSL(cur.k,level),cur.letters[i]); });
  }
}
function drawMini(c,canvas,k,letters,cs){
  c.clearRect(0,0,canvas.width,canvas.height); c.fillStyle=hslStr(EMPTY_HSL); c.fillRect(0,0,canvas.width,canvas.height);
  if(!k) return; const cells=PIECES[k][0], xs=cells.map(p=>p[0]), ys=cells.map(p=>p[1]);
  const w=Math.max(...xs)-Math.min(...xs)+1, h=Math.max(...ys)-Math.min(...ys)+1;
  const ox=(canvas.width-w*cs)/2-Math.min(...xs)*cs, oy=(canvas.height-h*cs)/2-Math.min(...ys)*cs;
  cells.forEach(([dx,dy],i)=>drawBlock(c,ox+dx*cs,oy+dy*cs,cs,pieceHSL(k,level),letters?letters[i]:''));
}
function drawPreview(){ drawMini(pCtx,pCanvas,nextQueue[0],nextLetters,36);
  const mn=document.getElementById('mNext'); if(mn){ drawMini(mn.getContext('2d'),mn,nextQueue[0],null,10); } }
function drawHold(){ drawMini(hCtx,hCanvas,holdKey,null,18); }
function queueWordPop(w, pts){
  const wrap=document.getElementById('boardWrap'); const mid=w.coords[Math.floor(w.coords.length/2)];
  const el=document.createElement('div'); el.className='wordPop'; el.innerHTML=w.word+'<span style="font-size:0.6em;color:#ffe27a;"> +'+pts+'</span>';
  el.style.left=(mid[0]*CELL+CELL/2)+'px'; el.style.top=(mid[1]*CELL+CELL/2)+'px';
  wrap.appendChild(el); sfx('word'); setTimeout(()=>el.remove(),1400);
}
function updateHUD(){
  document.getElementById('scoreV').textContent=score;
  document.getElementById('levelV').textContent=level;
  document.getElementById('linesV').textContent=lines;
  document.getElementById('wordsV').textContent=wordsCleared;
  document.getElementById('bestV').textContent=best;
  const set=(id,v)=>{ const e=document.getElementById(id); if(e) e.textContent=v; };
  set('mScore',score); set('mLevel',level); set('mLines',lines); set('mWords',wordsCleared);
}

// ---- Start / end -----------------------------------------------------------
function startGame(){
  grid=Array.from({length:ROWS},()=>Array(COLS).fill(null));
  typeBag=[]; nextQueue=[nextType(),nextType(),nextType()]; nextLetters=genLetters();
  holdKey=null; holdUsed=false; score=0; lines=0; wordsCleared=0; level=MODES[mode].startLevel;
  gravCounter=0; dasDir=0; areTimer=0; clearTimer=0; chain=0; pendingClear=null;
  leftHeld=rightHeld=downHeld=false;
  wordTally.clear(); wordPts.clear(); wordOrder=[]; renderWordList();
  spawnPiece(); drawHold(); updateHUD();
  document.getElementById('title').style.display='none';
  document.getElementById('overlay').style.display='none';
  document.body.classList.add('ingame');
  gameState='playing'; acc=0; lastT=performance.now(); startMusic(); requestAnimationFrame(loop);
  fitToScreen();
}
function endGame(){
  gameState='dead'; cur=null; stopMusic();
  const ov=document.getElementById('overlay');
  document.getElementById('ovTitle').textContent='GAME OVER';
  document.getElementById('ovMsg').textContent=(score>=best?'NEW BEST! ':'')+'Score '+score+' · '+wordsCleared+' words';
  if(isHighScore(score)){ startInitials(); } else { document.getElementById('nameEntry').style.display='none'; renderOvTable(null); setBtn('PLAY AGAIN','again'); }
  ov.style.display='flex';
}
function togglePause(){
  if(gameState==='dead') return;
  if(gameState==='playing'){ gameState='paused'; const ov=document.getElementById('overlay');
    document.getElementById('ovTitle').textContent='PAUSED'; document.getElementById('ovMsg').textContent=''; document.getElementById('nameEntry').style.display='none'; document.getElementById('ovTable').innerHTML=''; setBtn('RESUME','resume'); ov.style.display='flex'; pauseMusic();
  } else if(gameState==='paused'){ gameState='playing'; document.getElementById('overlay').style.display='none'; lastT=performance.now(); acc=0; resumeMusic(); requestAnimationFrame(loop); }
}
function setBtn(text,action){ const b=document.getElementById('resumeBtn'); b.textContent=text; b.dataset.action=action; }

// ---- High scores + arcade initials ----------------------------------------
function getScores(){ try{ return JSON.parse(localStorage.getItem('tetrabble_scores')||'[]'); }catch(e){ return []; } }
function isHighScore(s){ const l=getScores(); return s>0 && (l.length<10 || s>l[l.length-1].score); }
function saveScore(name,s){ const l=getScores(); l.push({name:(name||'AAA').toUpperCase().slice(0,3),score:s,mode,words:wordsCleared,date:Date.now()}); l.sort((a,b)=>b.score-a.score); l.splice(10); localStorage.setItem('tetrabble_scores',JSON.stringify(l)); return l; }
function renderHiScores(list,container,hi){ list=list||getScores(); container=container||document.getElementById('hsRows'); container.innerHTML='';
  if(!list.length){ container.innerHTML='<div style="color:#556;text-align:center;padding:14px;">No scores yet — be the first!</div>'; return; }
  list.forEach((e,i)=>{ const d=document.createElement('div'); d.className='hs'+(i===hi?' me':''); d.innerHTML='<span class="rank">'+(i+1)+'.</span><span class="nm">'+e.name+'</span><span class="sc">'+e.score+'</span>'; container.appendChild(d); }); }
function renderOvTable(hi){ renderHiScores(getScores(),document.getElementById('ovTable'),hi); }

let enteringInitials=false, initL=['A','A','A'], initSlot=0, initLockUntil=0;
function initLocked(){ return performance.now()<initLockUntil; }
function startInitials(){ enteringInitials=true; initL=['A','A','A']; initSlot=0; initLockUntil=performance.now()+450; document.getElementById('nameEntry').style.display='flex'; document.getElementById('ovTable').innerHTML=''; setBtn('SAVE','save'); renderInitials(); }
function renderInitials(){ const sl=document.querySelectorAll('#initials .slot'); sl.forEach((s,i)=>{ s.textContent=initL[i]; s.classList.toggle('active',i===initSlot); }); }
function initChange(d){ let c=initL[initSlot].charCodeAt(0)-65; c=(c+d+26)%26; initL[initSlot]=String.fromCharCode(65+c); renderInitials(); }
function initMoveSlot(d){ initSlot=(initSlot+d+3)%3; renderInitials(); }
function commitInitials(){ const name=initL.join(''); const list=saveScore(name,score); const idx=list.findIndex(e=>e.name===name&&e.score===score); enteringInitials=false; document.getElementById('nameEntry').style.display='none'; document.getElementById('ovTitle').textContent='HIGH SCORE!'; renderOvTable(idx); setBtn('PLAY AGAIN','again'); renderHiScores(); }
function initConfirm(){ if(initSlot<2){ initSlot++; renderInitials(); } else commitInitials(); }

// ---- Keyboard --------------------------------------------------------------
window.addEventListener('keydown',(e)=>{
  if(enteringInitials){
    if(initLocked()){ e.preventDefault(); return; }
    switch(e.key){
      case 'ArrowUp': initChange(1); break;
      case 'ArrowDown': initChange(-1); break;
      case 'ArrowLeft': initMoveSlot(-1); break;
      case 'ArrowRight': initMoveSlot(1); break;
      case 'Enter': case ' ': initConfirm(); break;
      case 'Backspace': initMoveSlot(-1); break;
      default: if(/^[a-zA-Z]$/.test(e.key)){ initL[initSlot]=e.key.toUpperCase(); renderInitials(); if(initSlot<2){initSlot++;renderInitials();} }
    }
    e.preventDefault(); return;
  }
  let h=true;
  switch(e.key){
    case 'ArrowLeft': case 'a': case 'A': leftHeld=true; break;
    case 'ArrowRight': case 'd': case 'D': rightHeld=true; break;
    case 'ArrowUp': case 'x': case 'X': rotate(1); break;
    case 'z': case 'Z': rotate(-1); break;
    case 'ArrowDown': case 's': case 'S': downHeld=true; break;
    case ' ': hardDrop(); break;
    case 'c': case 'C': doHold(); break;
    case 'Escape': case 'p': case 'P': togglePause(); break;
    case 'q': case 'Q': if(e.shiftKey) quitKiosk(); else h=false; break;
    case 'Enter': if(gameState==='dead'){ document.getElementById('resumeBtn').click(); } else if(gameState==='idle'){ document.getElementById('playBtn').click(); } else h=false; break;
    default: h=false;
  }
  if(h) e.preventDefault();
});
window.addEventListener('keyup',(e)=>{
  switch(e.key){ case 'ArrowLeft': case 'a': case 'A': leftHeld=false; break; case 'ArrowRight': case 'd': case 'D': rightHeld=false; break; case 'ArrowDown': case 's': case 'S': downHeld=false; break; }
});

// ---- Gamepad ---------------------------------------------------------------
let padPrev={}, _padId=null, _padDownKey='';
function pressed(pad,i){ return pad.buttons[i]&&pad.buttons[i].pressed; }
function snap(pad){ const s={}; pad.buttons.forEach((b,i)=>s[i]=b.pressed); return s; }
function dpad(pad){
  const ax0=pad.axes[0]||0, ax1=pad.axes[1]||0, hat=pad.axes.length>9?pad.axes[9]:2;
  const hU=hat>-1.3&&hat<-0.7,hR=hat>-0.6&&hat<-0.1,hD=hat>0.1&&hat<0.6,hL=hat>0.6&&hat<1.1;
  return { L:pressed(pad,14)||ax0<-0.5||hL, R:pressed(pad,15)||ax0>0.5||hR, U:pressed(pad,12)||ax1<-0.5||hU, D:pressed(pad,13)||ax1>0.5||hD };
}
function padTelemetry(pad,down){ try{
  if(_padId!==pad.id){ _padId=pad.id; fetch('/__pad?info='+encodeURIComponent('id='+pad.id+'|map='+pad.mapping+'|btns='+pad.buttons.length+'|axes='+pad.axes.length)).catch(()=>{}); }
  const key=down.join(','); if(key!==_padDownKey){ _padDownKey=key; fetch('/__pad?'+encodeURIComponent('btn=['+key+'] ax=['+pad.axes.map(a=>a.toFixed(2)).join(',')+']')).catch(()=>{}); }
}catch(e){} }
let edge={};
function padEdge(pad,i){ const p=!!padPrev[i], n=pressed(pad,i); return n&&!p; }
function pollGamepad(){
  const pads=navigator.getGamepads?navigator.getGamepads():[]; let pad=null;
  for(const p of pads) if(p){ pad=p; break; }
  const st=document.getElementById('padStatus');
  // No gamepad: do NOT clear held flags here — keyboard/touch own them. (Clearing
  // every frame was wiping touch/keyboard left/right/down on no-controller devices.)
  if(!pad){ if(st){ st.textContent='⚇ no controller'; st.classList.remove('on'); } padPrev={}; return; }
  const down=[]; pad.buttons.forEach((b,i)=>{ if(b.pressed) down.push(i); });
  if(st){ st.classList.add('on'); const axA=pad.axes.some(a=>Math.abs(a)>0.4);
    st.textContent='🎮 '+((down.length||axA)?'btn['+down.join(',')+'] ax['+pad.axes.map(a=>a.toFixed(1)).join(',')+']':((pad.mapping||'?')+' · '+pad.id.slice(0,20))); }
  padTelemetry(pad,down);
  const d=dpad(pad);

  // quit on any screen
  if(pressed(pad,8)&&pressed(pad,9)){ quitKiosk(); padPrev=snap(pad); return; }

  // initials entry
  if(enteringInitials){
    if(initLocked()){ padPrev=snap(pad); padPrev._U=d.U; padPrev._D=d.D; padPrev._L=d.L; padPrev._R=d.R; return; }
    const upE=(d.U&&!padPrev._U), dnE=(d.D&&!padPrev._D), lE=(d.L&&!padPrev._L), rE=(d.R&&!padPrev._R);
    if(upE) initChange(1); if(dnE) initChange(-1); if(lE) initMoveSlot(-1); if(rE) initMoveSlot(1);
    if(padEdge(pad,0)||padEdge(pad,9)) initConfirm();
    if(padEdge(pad,1)) initMoveSlot(-1);
    padPrev=snap(pad); padPrev._U=d.U; padPrev._D=d.D; padPrev._L=d.L; padPrev._R=d.R; return;
  }

  // menus
  if(gameState!=='playing'){
    if(padEdge(pad,0)||padEdge(pad,9)){
      if(gameState==='dead'){ document.getElementById('resumeBtn').click(); }
      else if(gameState==='paused'){ togglePause(); }
      else if(document.getElementById('title').style.display!=='none'){ ensureAudio(); document.getElementById('playBtn').click(); }
    }
    padPrev=snap(pad); return;
  }

  // in-game
  leftHeld=d.L; rightHeld=d.R; downHeld=d.D;
  if(d.U&&!padPrev._U) hardDrop();
  if(padEdge(pad,0)) rotate(1);
  if(padEdge(pad,1)) rotate(-1);
  if(padEdge(pad,3)) hardDrop();
  if(padEdge(pad,4)||padEdge(pad,5)) doHold();
  if(padEdge(pad,9)) togglePause();
  padPrev=snap(pad); padPrev._U=d.U;
}
function inputLoop(){ try{ pollGamepad(); }catch(e){} requestAnimationFrame(inputLoop); }
requestAnimationFrame(inputLoop);

// quit kiosk -> tell launcher to close Chromium
let quitting=false;
function quitKiosk(){ if(quitting) return; quitting=true; fetch('/__quit').catch(()=>{}).finally(()=>{ try{ window.close(); }catch(e){} }); }

// ---- Touch controls --------------------------------------------------------
(function setupTouch(){
  const isTouch = ('ontouchstart' in window) || navigator.maxTouchPoints>0;
  if(isTouch) document.body.classList.add('touch');
  function hold(el, on, off){ if(!el) return;
    const dn=(e)=>{ e.preventDefault(); on(); }; const up=(e)=>{ e.preventDefault(); off&&off(); };
    el.addEventListener('touchstart',dn,{passive:false}); el.addEventListener('touchend',up,{passive:false});
    el.addEventListener('touchcancel',up,{passive:false});
    el.addEventListener('mousedown',dn); el.addEventListener('mouseup',up); el.addEventListener('mouseleave',up);
  }
  hold(document.getElementById('tLeft'), ()=>leftHeld=true, ()=>leftHeld=false);
  hold(document.getElementById('tRight'),()=>rightHeld=true,()=>rightHeld=false);
  hold(document.getElementById('tDown'), ()=>downHeld=true, ()=>downHeld=false);
  hold(document.getElementById('tRotate'),()=>rotate(1));
  hold(document.getElementById('tDrop'), ()=>hardDrop());
  hold(document.getElementById('tHold'), ()=>doHold());
  // tap initials slots to cycle (touch high-score entry)
  document.querySelectorAll('#initials .slot').forEach((s,i)=>{ s.addEventListener('click',()=>{ if(!enteringInitials) return; initSlot=i; initChange(1); }); });

  // mobile HUD music toggle (mirrors the desktop button)
  const mm=document.getElementById('mMusic');
  if(mm) mm.addEventListener('click',()=>{ musicOn=!musicOn; mm.textContent='♪ '+(musicOn?'ON':'OFF'); const mb=document.getElementById('musicBtn'); if(mb) mb.textContent='Music: '+(musicOn?'ON':'OFF'); if(musicOn){ if(gameState==='playing') resumeMusic(); } else pauseMusic(); });

  // ---- Gesture controls on the board (tap=rotate, swipe=move, drag/flick down=drop) ----
  function softStep(){ if(canAct()){ if(!collides(cur,cur.x,cur.y+1,cur.rot)){ cur.y++; score++; updateHUD(); } else lockPiece(); } }
  let gs=null;
  function cellPx(){ const r=document.getElementById('boardWrap').getBoundingClientRect(); return Math.max(14, r.width/COLS); }
  board.addEventListener('touchstart',(e)=>{ const t=e.touches[0]; gs={x:t.clientX,y:t.clientY,t:performance.now(),moved:false}; e.preventDefault(); },{passive:false});
  board.addEventListener('touchmove',(e)=>{
    if(!gs) return; const t=e.touches[0]; const step=cellPx();
    let dx=t.clientX-gs.x, dy=t.clientY-gs.y;
    while(dx>=step){ move(1); gs.x+=step; gs.moved=true; dx-=step; }
    while(dx<=-step){ move(-1); gs.x-=step; gs.moved=true; dx+=step; }
    if(dy>=step){ const n=Math.floor(dy/step); for(let i=0;i<n;i++) softStep(); gs.y+=n*step; gs.moved=true; }
    e.preventDefault();
  },{passive:false});
  board.addEventListener('touchend',(e)=>{
    if(!gs) return; const dt=performance.now()-gs.t;
    const ch=e.changedTouches[0]; const totalDy=ch?ch.clientY-gs.y:0;
    if(!gs.moved && dt<260){ rotate(1); }                         // quick tap = rotate
    else if(totalDy>cellPx()*2 && dt<220){ hardDrop(); }          // fast downward flick = hard drop
    gs=null; e.preventDefault();
  },{passive:false});
  board.addEventListener('touchcancel',()=>{ gs=null; });
})();

// ===========================================================================
//  MUSIC — switchable chiptunes, lookahead scheduler, danger-tempo, celesta
// ===========================================================================
const N={REST:0,A2:110,B2:123.47,C3:130.81,D3:146.83,DS3:155.56,E3:164.81,F3:174.61,FS3:185,G3:196,GS3:207.65,
  A3:220,AS3:233.08,B3:246.94,C4:261.63,CS4:277.18,D4:293.66,DS4:311.13,E4:329.63,F4:349.23,FS4:369.99,G4:392,GS4:415.30,
  A4:440,AS4:466.16,B4:493.88,C5:523.25,CS5:554.37,D5:587.33,DS5:622.25,E5:659.25,F5:698.46,FS5:739.99,G5:783.99,GS5:830.61,A5:880,B5:987.77};
const TRACKS={
  sugarplum:{ name:'Sugar Plum Fairy', bpm:132, celesta:true, melody:[
    ['E5',.5],['DS5',.5],['E5',.5],['DS5',.5],['E5',.5],['B4',.5],['D5',.5],['C5',.5],
    ['A4',1],['REST',.25],['C4',.25],['E4',.5],['A4',.5],['B4',1],['REST',.25],['E4',.25],
    ['GS4',.5],['B4',.5],['C5',1],['REST',.5],
    ['E5',.5],['DS5',.5],['E5',.5],['DS5',.5],['E5',.5],['B4',.5],['D5',.5],['C5',.5],
    ['A4',1],['REST',.25],['C4',.25],['E4',.5],['A4',.5],['B4',1],['REST',.25],['E4',.25],
    ['C5',.5],['B4',.5],['A4',1.5],['REST',.5],
  ], bass:[
    ['A2',1],['E3',1],['A2',1],['E3',1],['A2',1],['E3',1],['GS3',1],['E3',1],
    ['A2',1],['E3',1],['F3',1],['C3',1],['E3',1],['E3',1],
    ['A2',1],['E3',1],['A2',1],['E3',1],['A2',1],['E3',1],['GS3',1],['E3',1],
    ['A2',1],['E3',1],['A2',1],['E3',1],
  ]},
  korobeiniki:{ name:'Korobeiniki', bpm:150, celesta:false, melody:[
    ['E5',2],['B4',1],['C5',1],['D5',2],['C5',1],['B4',1],['A4',2],['A4',1],['C5',1],['E5',2],['D5',1],['C5',1],
    ['B4',3],['C5',1],['D5',2],['E5',2],['C5',2],['A4',2],['A4',2],['REST',2],
    ['REST',1],['D5',2],['F5',1],['A5',2],['G5',1],['F5',1],['E5',3],['C5',1],['E5',2],['D5',1],['C5',1],
    ['B4',2],['B4',1],['C5',1],['D5',2],['E5',2],['C5',2],['A4',2],['A4',2],['REST',2],
  ], bass:[
    ['E3',2],['E4',2],['A2',2],['A3',2],['GS3',2],['E3',2],['A2',2],['A2',2],
    ['D3',2],['D4',2],['C3',2],['C4',2],['B2',2],['E3',2],['E3',2],['E3',2],
  ]},
};
let curTrack='sugarplum', actx=null, musicGain=null, musicOn=true; const MUSIC_VOL=0.55;
let schedTimer=null, melIdx=0, melTime=0, bassIdx=0, bassTime=0;
// real NES Music 1 (Sugar Plum Fairy) mp3 + danger (sped-up) variant
let normalAudio=null, dangerAudio=null, dangerMode=false;
function initMusicAudio(){ if(normalAudio) return; normalAudio=new Audio('music1.mp3'); normalAudio.loop=true; normalAudio.preload='auto'; normalAudio.volume=0; dangerAudio=new Audio('music1_danger.mp3'); dangerAudio.loop=true; dangerAudio.preload='auto'; dangerAudio.volume=0; }
function applyMusicVolume(){ if(!normalAudio) return; normalAudio.volume=(musicOn&&!dangerMode)?MUSIC_VOL:0; dangerAudio.volume=(musicOn&&dangerMode)?MUSIC_VOL:0; }
function updateMusicDanger(){ if(!normalAudio||!musicOn||gameState!=='playing') return; const d=dangerFactor()>1.05; if(d!==dangerMode){ dangerMode=d; applyMusicVolume(); } }
function pauseMusic(){ if(normalAudio){ normalAudio.pause(); dangerAudio.pause(); } }
function resumeMusic(){ if(normalAudio&&musicOn){ normalAudio.play().catch(()=>{}); dangerAudio.play().catch(()=>{}); applyMusicVolume(); } }
function ensureAudio(){ if(!actx){ actx=new (window.AudioContext||window.webkitAudioContext)(); musicGain=actx.createGain(); musicGain.gain.value=musicOn?MUSIC_VOL:0; musicGain.connect(actx.destination); } return actx.state==='suspended'?actx.resume():Promise.resolve(); }
function dangerFactor(){ if(!grid) return 1; let top=ROWS; for(let y=0;y<ROWS;y++){ if(grid[y].some(c=>c)){ top=y; break; } } const fill=(ROWS-top)/ROWS; return fill<0.6?1:1+(fill-0.6)/0.4*0.6; }
function playNote(freq,start,dur,type,gain,bell){
  if(!freq) return;
  const o=actx.createOscillator(),g=actx.createGain(); o.type=type; o.frequency.value=freq;
  const a=0.006,r=0.05; g.gain.setValueAtTime(0,start); g.gain.linearRampToValueAtTime(gain,start+a); g.gain.setValueAtTime(gain,start+Math.max(a,dur-r)); g.gain.linearRampToValueAtTime(0,start+dur);
  o.connect(g); g.connect(musicGain); o.start(start); o.stop(start+dur+0.02);
  if(bell){ const o2=actx.createOscillator(),g2=actx.createGain(); o2.type='sine'; o2.frequency.value=freq*2; const bd=Math.min(dur,0.5); g2.gain.setValueAtTime(0,start); g2.gain.linearRampToValueAtTime(gain*0.35,start+0.004); g2.gain.exponentialRampToValueAtTime(0.0008,start+bd); o2.connect(g2); g2.connect(musicGain); o2.start(start); o2.stop(start+bd+0.02); }
}
function scheduler(){
  const tk=TRACKS[curTrack]; const beat=60/tk.bpm/dangerFactor(); const ahead=0.12, now=actx.currentTime;
  if(melTime<now) melTime=now+0.02; if(bassTime<now) bassTime=now+0.02;
  while(melTime<now+ahead){ const [n,b]=tk.melody[melIdx]; playNote(N[n],Math.max(melTime,now),b*beat*0.9,tk.celesta?'triangle':'square',0.85,tk.celesta); melTime+=b*beat; melIdx=(melIdx+1)%tk.melody.length; }
  while(bassTime<now+ahead){ const [n,b]=tk.bass[bassIdx]; playNote(N[n],Math.max(bassTime,now),b*beat*0.9,'triangle',0.55,false); bassTime+=b*beat; bassIdx=(bassIdx+1)%tk.bass.length; }
  schedTimer=setTimeout(scheduler,25);
}
function startMusic(){ if(!musicOn) return; initMusicAudio(); dangerMode=false; try{ normalAudio.currentTime=0; dangerAudio.currentTime=0; }catch(e){} normalAudio.play().catch(()=>{}); dangerAudio.play().catch(()=>{}); applyMusicVolume(); }
function stopMusic(){ if(normalAudio){ normalAudio.pause(); dangerAudio.pause(); try{ normalAudio.currentTime=0; }catch(e){} } }
function setTrack(k){ /* music fixed to NES Music 1 mp3 */ }
function sfx(kind){ if(!actx||!musicOn) return; const o=actx.createOscillator(),g=actx.createGain(); const map={move:220,rotate:330,drop:110,line:520,tetris:660,word:680,level:440}; o.type='square'; o.frequency.value=map[kind]||200; const t=actx.currentTime; g.gain.setValueAtTime(0,t); g.gain.linearRampToValueAtTime(0.05,t+0.005); g.gain.exponentialRampToValueAtTime(0.001,t+((kind==='word'||kind==='tetris'||kind==='level')?0.25:0.08)); o.connect(g); g.connect(actx.destination); o.start(t); o.stop(t+0.3);
  if(kind==='word'||kind==='tetris'||kind==='level'){ const seq=kind==='level'?[523,659,784,1047]:[523,653,783]; seq.forEach((f,i)=>{ const d=i*0.06; const o2=actx.createOscillator(),g2=actx.createGain(); o2.type='square'; o2.frequency.value=f; g2.gain.setValueAtTime(0.05,t+d); g2.gain.exponentialRampToValueAtTime(0.001,t+d+0.1); o2.connect(g2); g2.connect(actx.destination); o2.start(t+d); o2.stop(t+d+0.12); }); } }

// ---- Track UI / buttons ----------------------------------------------------
// music is fixed to the real NES Music 1 mp3; hide the old track-selector UI
(function(){ const tb=document.getElementById('trackBtn'); if(tb) tb.style.display='none'; const ts=document.getElementById('trackSel'); if(ts) ts.style.display='none'; })();
document.getElementById('musicBtn').addEventListener('click',()=>{ musicOn=!musicOn; document.getElementById('musicBtn').textContent='Music: '+(musicOn?'ON':'OFF'); if(musicOn){ if(gameState==='playing') resumeMusic(); } else pauseMusic(); });
document.getElementById('testBtn').addEventListener('click',()=>{ ensureAudio().then(()=>{ const b=document.getElementById('testBtn'); const o=actx.createOscillator(),g=actx.createGain(); o.type='square'; o.frequency.value=440; const t=actx.currentTime; g.gain.setValueAtTime(0,t); g.gain.linearRampToValueAtTime(0.4,t+0.02); g.gain.setValueAtTime(0.4,t+0.45); g.gain.linearRampToValueAtTime(0,t+0.5); o.connect(g); g.connect(actx.destination); o.start(t); o.stop(t+0.55); b.textContent='🔊 '+actx.state+' @'+actx.sampleRate; setTimeout(()=>b.textContent='🔊 Test Sound',2500); }); });
document.querySelectorAll('.mode').forEach(el=>el.addEventListener('click',()=>{ document.querySelectorAll('.mode').forEach(m=>m.classList.remove('sel')); el.classList.add('sel'); mode=el.dataset.mode; }));
document.getElementById('playBtn').addEventListener('click',()=>{ ensureAudio(); startGame(); });
document.getElementById('resumeBtn').addEventListener('click',()=>{
  const act=document.getElementById('resumeBtn').dataset.action;
  if(act==='save'){ commitInitials(); }
  else if(act==='resume'){ togglePause(); }
  else { document.getElementById('title').style.display='flex'; document.getElementById('overlay').style.display='none'; document.body.classList.remove('ingame'); gameState='idle'; renderHiScores(); fitToScreen(); }
});

// ---- Fit to screen ---------------------------------------------------------
function fitToScreen(){
  const g=document.getElementById('game'); if(!g) return;
  g.style.transform='none';
  const gw=g.offsetWidth, gh=g.offsetHeight; if(!gw||!gh) return;
  const touch=document.body.classList.contains('touch');
  const tb=document.getElementById('touchBar');
  const sidePad = touch ? 10 : 0;                             // breathing room at edges
  const reserveTop = touch ? 60 : 0;                          // mobile HUD bar
  const reserveBottom = (touch && tb) ? tb.offsetHeight + 12 : 0;  // touch buttons (incl. safe area)
  const availW = window.innerWidth - sidePad*2;
  const availH = window.innerHeight - reserveTop - reserveBottom;
  const s = Math.min(availW/gw, availH/gh) * 0.98;
  // #game is anchored top-left in #stage; position it deterministically with
  // an explicit translate (origin top-left) so it always fits and centers.
  g.style.transformOrigin = 'top left';
  const tx = Math.max(sidePad, (window.innerWidth - gw*s) / 2);
  const ty = reserveTop + Math.max(0, (availH - gh*s) / 2);
  g.style.transform = 'translate('+tx.toFixed(1)+'px,'+ty.toFixed(1)+'px) scale('+s.toFixed(4)+')';
}
window.addEventListener('resize',fitToScreen); window.addEventListener('load',()=>{ fitToScreen(); setTimeout(fitToScreen,300); });
setTimeout(fitToScreen,100); setTimeout(fitToScreen,800);

// ---- Audio unlock on first interaction -------------------------------------
function unlockAudio(){ ensureAudio().then(()=>{ if(gameState==='playing'&&musicOn) startMusic(); }); window.removeEventListener('pointerdown',unlockAudio); window.removeEventListener('keydown',unlockAudio); window.removeEventListener('touchstart',unlockAudio); }
window.addEventListener('pointerdown',unlockAudio); window.addEventListener('keydown',unlockAudio); window.addEventListener('touchstart',unlockAudio);

// ---- Boot ------------------------------------------------------------------
initMusicAudio(); renderHiScores(); updateHUD(); render();
})();
