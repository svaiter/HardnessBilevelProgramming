// Shared by the build-time validator and the browser. A classic script keeps
// the exported site usable from file:// as well as any hosting subdirectory.
(() => {
  'use strict';

  function formula(text) {
    return text.replace(/^\\[([]/, '').replace(/\\[)\]]$/, '');
  }

  function renderToString(text, displayMode, macros, engine) {
    const source = formula(text).replace(/\\Theta\b/g, '\\htmlClass{notation-ref notation--theta}{\\Theta}');
    return engine.renderToString(source, {
      displayMode,
      throwOnError: true,
      strict: 'ignore',
      macros: {...macros},
      output: 'htmlAndMathml',
      trust: context => context.command === '\\htmlClass'
    }).replace(/class="([^"]*notation--([a-z0-9-]+)[^"]*)"/g, 'class="$1" data-notation="$2"');
  }

  function renderIn(container, macros, engine) {
    for (const span of container.querySelectorAll('.math:not([data-math-rendered])')) {
      // Read textContent so escaped <, > and & return to their original TeX.
      span.innerHTML = renderToString(span.textContent, span.classList.contains('display'), macros, engine);
      span.dataset.mathRendered = 'true';
    }
  }

  globalThis.PAPER_MATH = {renderToString, renderIn};
})();
