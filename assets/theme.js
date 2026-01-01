// assets/theme.js
// Simple dark/light switch with persistence.
// Default is dark unless user has chosen otherwise.

(() => {
  const KEY = "sw-theme";
  const root = document.documentElement;

  const getSaved = () => {
    try { return localStorage.getItem(KEY); } catch { return null; }
  };

  const save = (val) => {
    try { localStorage.setItem(KEY, val); } catch {}
  };

  const setTheme = (theme) => {
    root.dataset.theme = theme;
    const btn = document.getElementById("theme-toggle");
    if (btn) {
      btn.textContent = theme === "dark" ? "Light mode" : "Dark mode";
      btn.setAttribute("aria-label", `Switch theme (currently ${theme})`);
    }
  };

  const initial = getSaved() || "dark";
  setTheme(initial);

  window.__toggleTheme = () => {
    const cur = root.dataset.theme || "dark";
    const next = cur === "dark" ? "light" : "dark";
    save(next);
    setTheme(next);
  };
})();
