// Extend the host site's MathJax configuration before its shared loader runs.
(() => {
  const config = window.MathJax;
  config.loader = config.loader || {};
  config.loader.load = [...(config.loader.load || []), '[tex]/html'];
  config.tex.packages['[+]'] = [...(config.tex.packages['[+]'] || []), 'html'];
  for (const [name, value] of Object.entries(window.PAPER.math.macros)) {
    const body = value.replace(/\\htmlClass/g, '\\class');
    const count = Math.max(0, ...Array.from(body.matchAll(/#([1-9])/g), m => Number(m[1])));
    config.tex.macros[name.replace(/^\\/, '')] = count ? [body, count] : body;
  }
  config.startup = {...config.startup, typeset: false};
  window.PAPER_MATH = {
    async renderIn(container) {
      const spans = [...container.querySelectorAll('.math:not([data-math-rendered])')];
      for (const span of spans) span.dataset.mathRendered = 'pending';
      await window.MathJax.startup.promise;
      // Direct tex2svg conversion does not install MathJax's document styles.
      // Install them so the assistive MathML stays accessible but visually hidden.
      if (!document.getElementById('MJX-SVG-styles')) window.MathJax.startup.document.updateDocument();
      for (const span of spans) {
        if (!span.isConnected) continue;
        const tex = span.textContent.replace(/^\\[([]/, '').replace(/\\[)\]]$/, '')
          .replace(/\\Theta\b/g, '\\class{notation-ref notation--theta}{\\Theta}');
        const rendered = await window.MathJax.tex2svgPromise(tex, {display: span.classList.contains('display')});
        span.replaceChildren(rendered);
        for (const element of span.querySelectorAll('.notation-ref')) {
          const match = element.getAttribute('class').match(/notation--([a-z0-9-]+)/);
          if (match) element.setAttribute('data-notation', match[1]);
        }
        span.dataset.mathRendered = 'true';
      }
    }
  };
})();
