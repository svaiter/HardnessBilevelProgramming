(() => {
  'use strict';

  const paper = window.PAPER ?? {};
  const meta = paper.meta ?? {};
  const nodes = Array.isArray(paper.nodes) ? paper.nodes : [];
  const notation = Array.isArray(paper.notation) ? paper.notation : [];
  const corrections = Array.isArray(paper.corrections) ? paper.corrections : [];
  const nodeById = new Map(nodes.map(node => [String(node.id), node]));
  const mainIds = new Set(meta.mainTheorems ?? ['thm11', 'thm212', 'thm215', 'thm221', 'thm32']);
  const $ = id => document.getElementById(id);
  const mobile = matchMedia('(max-width: 700px)');
  const dark = matchMedia('(prefers-color-scheme: dark)');
  const icon = name => '<svg class="icon" aria-hidden="true"><use href="#i-' + name + '"/></svg>';
  const list = value => value == null ? [] : Array.isArray(value) ? value : [value];
  const plain = value => typeof value === 'string' || typeof value === 'number' ? String(value) : value?.text ?? '';
  const escape = value => String(value ?? '').replace(/[&<>"']/g, letter => ({
    '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'
  })[letter]);
  const rich = value => value?.html || escape(plain(value));
  const inlineRich = value => rich(value).trim().replace(/^<p>([\s\S]*)<\/p>$/, '$1');
  const url = value => {
    const raw = String(value ?? '').trim();
    if (!raw || /^[\/]{2}/.test(raw)) return '';
    const match = raw.match(/^([a-z][a-z0-9+.-]*):/i);
    return match && !/^https?$/i.test(match[1]) ? '' : raw;
  };
  const truncate = (value, size) => value.length > size ? value.slice(0, size - 1).trimEnd() + '…' : value;
  const titleOf = node => plain(node?.title) || resultLabel(node) || 'Untitled result';
  const resultLabel = node => {
    const number = plain(node?.number);
    const kind = plain(node?.kind).replace(/[-_]/g, ' ');
    if (!kind) return number;
    const label = kind.charAt(0).toUpperCase() + kind.slice(1);
    return number.toLowerCase().startsWith(label.toLowerCase()) ? number : [label, number].filter(Boolean).join(' ');
  };
  const sectionId = value => String(value?.id ?? value ?? '');
  const nodeSection = node => sectionId(node?.section);
  const isExternal = node => Boolean(node?.external || ['external', 'companion'].includes(node?.kind));
  const isMain = node => Boolean(node?.main || node?.mainTheorem || mainIds.has(node?.id));
  const uses = node => list(node?.uses).map(use => typeof use === 'string' ? {id: use} : use)
    .filter(use => use?.id && nodeById.has(String(use.id)));

  const sections = [];
  const sectionById = new Map();
  function addSection(raw, parent = '') {
    const id = sectionId(raw);
    if (!id || sectionById.has(id)) return;
    const section = typeof raw === 'string' ? {id, title: raw, parent} : {...raw, id, parent: sectionId(raw.parent || parent)};
    sections.push(section);
    sectionById.set(id, section);
    for (const subsection of list(section.subsections ?? section.children)) addSection(subsection, id);
  }
  for (const section of list(paper.sections)) addSection(section);
  for (const node of nodes) {
    if (nodeSection(node) && !sectionById.has(nodeSection(node))) addSection(node.section);
  }
  const sectionTitle = id => plain(sectionById.get(id)?.title) || id || 'Results';
  function ancestors(id) {
    const ids = [];
    while (id && !ids.includes(id)) {
      ids.push(id);
      id = sectionById.get(id)?.parent;
    }
    return ids;
  }
  const topSection = id => ancestors(id).at(-1) ?? '';
  const within = (node, id) => !id || ancestors(nodeSection(node)).includes(id);
  const bySection = id => nodes.filter(node => within(node, id));
  const dependents = new Map(nodes.map(node => [node.id, []]));
  for (const node of nodes) {
    for (const use of uses(node)) dependents.get(use.id)?.push({node, use});
  }
  const hasCorrections = node => Boolean(list(node?.corrections).length || corrections.some(correction =>
    list(correction.nodes ?? correction.node).some(id => String(id?.id ?? id) === node?.id)));
  const first = nodes.find(isMain) ?? nodes[0];
  const state = {
    selected: first?.id, mode: 'whole', section: '', page: 'map', outline: false,
    reading: false, expanded: false, external: true, trail: first ? [first.id] : [], trailIndex: 0,
    size: 16, split: 54, graph: null
  };

  function loadSetting(key, fallback) {
    try { return localStorage.getItem(key === 'theme' ? 'theme' : 'visual-paper:' + key) ?? fallback; }
    catch { return fallback; }
  }
  function saveSetting(key, value) {
    try { localStorage.setItem(key === 'theme' ? 'theme' : 'visual-paper:' + key, value); }
    catch { /* The controls still work when storage is disabled. */ }
  }
  function press(id, value) { $(id).setAttribute('aria-pressed', String(Boolean(value))); }
  function externalLink(href, label, classes = 'source-link') {
    const target = url(href);
    return target ? '<a class="' + classes + '" href="' + escape(target) + '">' + escape(label) + icon('external') + '</a>' : '';
  }
  function resultHash(id, detail = 'summary') {
    return '#/' + encodeURIComponent(id) + '/' + encodeURIComponent(detail);
  }
  function claimSource(value) {
    const citations = list(value?.cites).filter(citation => url(citation?.url));
    const citation = citations.find(item => item.url.includes('arxiv.org')) ?? citations[0];
    if (!citation) return '';
    const label = 'Cited source' + (citation.line ? ' at line ' + citation.line : '');
    return '<a class="claim-source" href="' + escape(url(citation.url)) + '" aria-label="' + escape(label) +
      '" title="' + escape(label) + '">' + icon('external') + '</a>';
  }
  function claimList(values) {
    return list(values).map(value => {
      const html = rich(value).trim();
      if (!html) return '';
      const source = claimSource(value);
      const content = html.endsWith('</p>') ? html.slice(0, -4) + source + '</p>' : html + source;
      return '<div class="claim">' + content + '</div>';
    }).join('');
  }
  function sourceHtml(html, value) {
    if (html) return html;
    return plain(value).split(/\n\s*\n/).filter(Boolean).map(paragraph => '<p>' + escape(paragraph).replace(/\n/g, ' ') + '</p>').join('');
  }
  function outlineItem(node, current = false) {
    const label = resultLabel(node);
    return '<li><button class="outline-result" type="button" data-result="' + escape(node.id) + '"' +
      (current ? ' aria-current="true"' : '') + '><strong>' + inlineRich(node.title || titleOf(node)) + '</strong>' +
      (label ? '<span>' + escape(label) + '</span>' : '') + '</button></li>';
  }

  function setupPaper() {
    const title = plain(meta.title);
    if (title) {
      $('paper-title').textContent = title;
      document.title = title + ' | Visual Paper';
    }
    const authors = Array.isArray(meta.authors) ? meta.authors.map(author => plain(author) || author.name).join(' · ') : plain(meta.authors);
    const authorDisplay = authors || 'J. Bolte · Q.-T. Lê · E. Pauwels · S. Vaiter';
    $('paper-authors').textContent = authorDisplay;
    const year = plain(meta.year) || '2025';
    const yearLabel = document.createElement('span');
    yearLabel.className = 'author-year';
    yearLabel.textContent = year;
    $('paper-authors').append(yearLabel);
    $('footer-copyright')?.append(document.createTextNode(' ' + year));
    if ($('footer-version')) $('footer-version').textContent = 'Visual companion';
    const arxiv = plain(meta.arxiv ?? meta.arxiv_id);
    if (arxiv) $('paper-link').href = url(arxiv.startsWith('https://') ? arxiv : 'https://arxiv.org/abs/' + arxiv);
    else if ('arxiv' in meta || 'arxiv_id' in meta) $('paper-link').hidden = true;
    const repo = url(meta.repository ?? meta.lean?.repository ?? meta.github);
    if (repo) $('repo-link').href = repo;
    $('map-stats').textContent = nodes.length + (nodes.length === 1 ? ' result' : ' results') + ' · ' +
      sections.filter(section => !section.parent).length + ' sections';
    $('external-control').hidden = !nodes.some(isExternal);
    for (const section of sections) {
      const option = document.createElement('option');
      option.value = section.id;
      option.textContent = (section.parent ? '↳ ' : '') + sectionTitle(section.id);
      $('section-select').append(option);
    }
    $('view-focus').disabled = !first;
    renderOverview(authorDisplay, year, arxiv);
    renderCorrections();
    decorateNotation($('overview-view'));
    decorateNotation($('corrections-view'));
  }

  function graphModel() {
    const current = nodeById.get(state.selected);
    const visible = nodes.filter(node => state.external || !isExternal(node));
    const entries = new Map();
    const representation = new Map();
    const addResult = (node, context = false) => {
      if (!node || !visible.includes(node)) return;
      const label = resultLabel(node);
      const title = truncate(titleOf(node), 42);
      const status = node.lean?.status;
      entries.set(node.id, {id: node.id, label: label && title !== label ? label + '\n' + title : title,
        classes: ['result', isMain(node) && 'main', isExternal(node) && 'external', hasCorrections(node) && 'corrected',
          context && 'context', status === 'formalized' && 'formalized', status === 'reduction-only' && 'reduction-only'].filter(Boolean).join(' ')});
      representation.set(node.id, node.id);
    };
    const addSection = id => {
      if (!id || !sectionById.has(id)) return;
      const section = sectionById.get(id);
      const number = plain(section.number);
      const displayTitle = truncate(sectionTitle(id), 44);
      const key = 'section:' + id;
      const count = visible.filter(node => within(node, id)).length;
      if (!count) return;
      const label = (number ? 'Section ' + number : count + (count === 1 ? ' result' : ' results')) + '\n' + displayTitle;
      entries.set(key, {id: key, section: id, label, classes: 'section'});
      return key;
    };

    if (state.mode === 'focus' && current) {
      addResult(current);
      const neighbors = [
        ...uses(current).map(use => use.id),
        ...(dependents.get(current.id) ?? []).map(({node}) => node.id)
      ];
      for (const neighbor of new Set(neighbors)) addResult(nodeById.get(neighbor));
    } else if (state.section) {
      const inside = visible.filter(node => within(node, state.section));
      const insideIds = new Set(inside.map(node => node.id));
      for (const node of inside) {
        const sub = ancestors(nodeSection(node)).find(id => sectionById.get(id)?.parent === state.section);
        if (!sub || isMain(node)) addResult(node);
        else representation.set(node.id, addSection(sub));
      }
      for (const node of visible) {
        for (const use of uses(node)) {
          if (insideIds.has(node.id) && !insideIds.has(use.id)) addResult(nodeById.get(use.id), true);
          if (insideIds.has(use.id) && !insideIds.has(node.id)) addResult(node, true);
        }
      }
    } else {
      for (const node of visible) {
        if (isMain(node) || !nodeSection(node)) addResult(node);
        else representation.set(node.id, addSection(topSection(nodeSection(node))));
      }
      for (const node of visible.filter(isExternal)) {
        if (nodes.some(candidate => !isExternal(candidate) && uses(candidate).some(use => use.id === node.id))) addResult(node, true);
      }
    }

    const seen = new Set();
    const edges = [];
    for (const node of visible) {
      for (const use of uses(node)) {
        const source = representation.get(use.id);
        const target = representation.get(node.id);
        const id = JSON.stringify([source, target]);
        if (!source || !target || source === target || seen.has(id)) continue;
        seen.add(id);
        const aggregate = source.startsWith('section:') || target.startsWith('section:');
        const active = current?.id === source || current?.id === target;
        edges.push({data: {id: 'edge:' + id, source, target}, classes: [active && 'active', aggregate && 'aggregate'].filter(Boolean).join(' ')});
      }
    }
    return {
      entries,
      elements: [...entries.values()].map(({classes, ...data}) => ({
        data, classes: classes + (data.id === current?.id ? ' current' : '')
      })).concat(edges)
    };
  }

  function graphStyle() {
    const css = getComputedStyle(document.querySelector('.visual-paper') || document.documentElement);
    const color = name => css.getPropertyValue('--' + name).trim();
    const marker = (paint, markup) => 'data:image/svg+xml,' + encodeURIComponent(
      '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 14 14" fill="' + paint + '">' + markup + '</svg>'
    );
    const checked = marker(color('badge-green'), '<path d="M5.4 10.7 2.3 7.6l1.3-1.3 1.8 1.8 4.9-4.9 1.3 1.3z"/>');
    const partial = marker(color('amber'), '<circle cx="7" cy="7" r="4.4" fill="none" stroke="' + color('amber') + '"/><path d="M7 2.6a4.4 4.4 0 1 1 0 8.8z"/>');
    return [
      {selector: 'node', style: {
        shape: 'roundrectangle', width: 178, height: 78, label: 'data(label)', color: color('ink'),
        'background-color': color('surface'), 'border-color': color('line-strong'), 'border-width': 1,
        'text-valign': 'center', 'text-halign': 'center', 'text-wrap': 'wrap', 'text-max-width': 152,
        'text-overflow-wrap': 'whitespace', 'font-family': 'Arial, sans-serif', 'font-size': 12,
        'line-height': 1.08, 'overlay-opacity': 0
      }},
      {selector: 'node.section', style: {'background-color': color('wash'), 'border-color': color('line-strong'), 'border-style': 'dashed', 'font-weight': 600}},
      {selector: 'node.main', style: {'background-color': color('teal-wash'), 'border-color': color('teal-line'), 'color': color('teal-dark'), 'font-weight': 600}},
      {selector: 'node.context', style: {'background-color': color('outside'), 'border-style': 'dashed'}},
      {selector: 'node.corrected', style: {'border-width': 2, 'border-color': color('amber-line')}},
      {selector: 'node.current', style: {'background-color': color('teal'), 'border-color': color('teal'), color: color('white'), 'border-width': 2, 'font-weight': 700}},
      {selector: 'node.current.corrected', style: {'border-color': color('amber-line')}},
      {selector: 'node.hovered', style: {'border-width': 2, 'border-color': color('edge-active')}},
      {selector: 'node.formalized, node.reduction-only', style: {
        'background-width': 13, 'background-height': 13, 'background-position-x': '96%', 'background-position-y': '8%',
        'background-image-containment': 'over'
      }},
      {selector: 'node.formalized', style: {'background-image': checked}},
      {selector: 'node.formalized.current', style: {'background-image': marker(color('white'), '<path d="M5.4 10.7 2.3 7.6l1.3-1.3 1.8 1.8 4.9-4.9 1.3 1.3z"/>')}},
      {selector: 'node.reduction-only', style: {'background-image': partial}},
      {selector: 'edge', style: {
        'curve-style': 'bezier', width: 1.2, 'line-color': color('edge'), 'target-arrow-color': color('edge'),
        'target-arrow-shape': 'triangle', 'arrow-scale': 0.85, 'overlay-opacity': 0
      }},
      {selector: 'edge.aggregate', style: {'line-style': 'dashed', 'line-dash-pattern': [4, 3]}},
      {selector: 'edge.active', style: {width: 1.75, 'line-color': color('edge-active'), 'target-arrow-color': color('edge-active')}}
    ];
  }

  function initGraph() {
    if (state.graph || !window.cytoscape) return state.graph;
    if (window.cytoscapeDagre && !window.cytoscape('layout', 'dagre')) window.cytoscape.use(window.cytoscapeDagre);
    const cy = window.cytoscape({
      container: $('graph'), elements: [], style: graphStyle(), layout: {name: 'preset'},
      minZoom: 0.18, maxZoom: 3, wheelSensitivity: 0.16,
      autoungrabify: true, autounselectify: true, boxSelectionEnabled: false
    });
    cy.on('tap', 'node', event => {
      const section = event.target.data('section');
      if (section) showSection(section);
      else chooseResult(event.target.id(), {keepExpanded: true});
    });
    cy.on('mouseover', 'node', event => {
      $('graph').style.cursor = 'pointer';
      event.target.addClass('hovered');
    });
    cy.on('mouseout', 'node', event => {
      $('graph').style.cursor = '';
      event.target.removeClass('hovered');
    });
    state.graph = cy;
    return cy;
  }

  function fitGraph() {
    const cy = state.graph;
    if (!cy || !cy.nodes().length || mobile.matches || state.reading || state.outline || state.page !== 'map') return;
    cy.resize();
    cy.fit(cy.elements(), 28);
    if (cy.zoom() > 1.18) {
      cy.zoom(1.18);
      cy.center();
    }
  }

  function updateGraph() {
    const {entries, elements} = graphModel();
    const scope = state.mode === 'focus' ? 'Local dependencies' : state.section ? sectionTitle(state.section) : 'Sections and main theorems';
    $('graph-scope').textContent = scope;
    $('graph-empty').hidden = Boolean(entries.size);
    press('view-whole', state.mode !== 'focus');
    press('view-focus', state.mode === 'focus');
    renderOutline(entries);
    if (mobile.matches || state.reading || state.page !== 'map' || state.outline) return;
    const cy = initGraph();
    if (!cy) {
      setOutline(true);
      return;
    }
    cy.batch(() => {
      cy.elements().remove();
      cy.add(elements);
    });
    if (!entries.size) return;
    const dagre = Boolean(window.cytoscape('layout', 'dagre'));
    const graph = $('graph');
    const compact = graph.clientWidth < 480;
    const vertical = state.mode !== 'focus' && graph.clientWidth < 1.95 * graph.clientHeight;
    cy.layout(dagre ? {
      name: 'dagre', rankDir: vertical ? 'TB' : 'LR', rankSep: vertical ? 28 : compact ? 35 : 47, nodeSep: 19, edgeSep: 12,
      fit: false, animate: false, ranker: 'tight-tree'
    } : {name: 'breadthfirst', directed: true, fit: false, animate: false, spacingFactor: 1.2}).run();
    fitGraph();
  }

  function renderOutline(entries) {
    const outline = $('proof-outline');
    const wasOpen = new Set([...outline.querySelectorAll('details[open]')].map(detail => detail.dataset.section));
    if (state.mode === 'focus') {
      const results = [...entries.keys()].map(id => nodeById.get(id)).filter(Boolean);
      outline.innerHTML = '<ul class="outline-list">' + results.map(node => outlineItem(node, node.id === state.selected)).join('') + '</ul>';
      decorateNotation(outline);
      return;
    }
    const display = nodes.filter(node => within(node, state.section) && (state.external || !isExternal(node)));
    const main = display.filter(isMain);
    let html = main.length ? '<ul class="outline-list">' + main.map(node => outlineItem(node, node.id === state.selected)).join('') + '</ul>' : '';
    const grouped = new Map();
    for (const node of display.filter(node => !isMain(node))) {
      const id = state.section ? nodeSection(node) : topSection(nodeSection(node));
      if (!grouped.has(id)) grouped.set(id, []);
      grouped.get(id).push(node);
    }
    for (const [id, results] of grouped) {
      const open = state.section || wasOpen.has(id) || results.some(node => node.id === state.selected);
      html += '<details class="outline-group" data-section="' + escape(id) + '"' + (open ? ' open' : '') +
        '><summary>' + escape(sectionTitle(id)) + '</summary><ul class="outline-list">' +
        results.map(node => outlineItem(node, node.id === state.selected)).join('') + '</ul></details>';
    }
    outline.innerHTML = html || '<p>No results in this view.</p>';
    decorateNotation(outline);
  }

  function showSection(id) {
    state.section = id;
    state.mode = id ? 'cluster' : 'whole';
    $('section-select').value = id;
    updateGraph();
  }

  const leanBadges = {
    formalized: ['Lean formalized', 'check'],
    'reduction-only': ['Lean · reduction only', 'info'],
    'source-changed': ['Lean source updated · review needed', 'info'],
    unresolved: ['Lean declaration not resolved', 'info'],
    'not-formalized': ['No Lean formalization', 'info']
  };

  function leanBadge(lean) {
    if (!leanBadges[lean?.status]) return '';
    const [label, symbol] = leanBadges[lean.status];
    const classes = 'badge ' + lean.status;
    const href = url(lean.url);
    const description = escape([plain(lean.declaration) || plain(lean.file) || label, lean.reason].filter(Boolean).join(' — '));
    return href
      ? '<a class="' + classes + '" href="' + escape(href) + '" title="' + description + '">' + icon(symbol) + escape(label) + '</a>'
      : '<span class="' + classes + '" title="' + description + '">' + icon(symbol) + escape(label) + '</span>';
  }

  function correctionsFor(node) {
    return corrections.filter(correction => list(correction.nodes ?? correction.node).some(id => String(id?.id ?? id) === node.id));
  }

  function correctionBody(correction) {
    const parts = [
      ['In the paper', correction.original ?? correction.printed],
      ['Correction', correction.corrected ?? correction.revision]
    ].filter(([, value]) => value);
    const body = claimList(correction.claims ?? correction.summary ?? correction);
    return (parts.length
      ? '<div class="correction-parts">' + parts.map(([label, value]) => '<div><h4>' + label + '</h4>' + claimList(value) + '</div>').join('') + '</div>'
      : '') + body;
  }

  function resultCorrections(node) {
    const local = list(node.corrections);
    const related = correctionsFor(node);
    if (!local.length && !related.length) return '';
    const text = (related.length ? related : local).map(correction => {
      const title = inlineRich(correction.title);
      return '<div class="result-correction-entry">' + (title ? '<h4>' + title + '</h4>' : '') + correctionBody(correction) + '</div>';
    }).join('');
    const href = '#/corrections' + (related.length === 1 && related[0].id ? '/' + encodeURIComponent(related[0].id) : '');
    return '<aside class="result-correction" id="result-correction" tabindex="-1"><h3 class="reading-label">Correction</h3>' +
      text + '<a class="source-link" href="' + escape(href) + '">See the corrections</a></aside>';
  }

  function relations(label, pairs) {
    if (!pairs.length) return '';
    return '<section class="relation-group"><h3 class="reading-label">' + label + '</h3><ul class="relation-list">' +
      pairs.map(({node, use}) => '<li><a href="' + resultHash(node.id) + '"><span class="relation-id">' +
        escape(resultLabel(node)) + '</span>' + inlineRich(node.title || titleOf(node)) + '</a>' + claimList(use?.why) + '</li>').join('') +
      '</ul></section>';
  }

  function linkedFigures(node) {
    const matches = list(paper.figures).filter(figure => list(figure.nodes ?? figure.node ?? figure.nodeId)
      .some(id => String(id?.id ?? id) === node.id));
    const refs = list(node.figure ?? node.figures).map(figure => typeof figure === 'string'
      ? list(paper.figures).find(entry => entry.id === figure) ?? {id: figure} : figure);
    return [...new Map([...refs, ...matches].filter(Boolean).map(figure => [figure.id, figure])).values()];
  }

  function figureMarkup(figure) {
    const src = url(figure.src);
    const caption = claimList(figure.caption);
    const title = inlineRich(figure.title);
    const formula = claimList(figure.formula);
    const iframe = figure.interactive || /\.html(?:[?#]|$)/i.test(src);
    return '<figure class="result-figure" data-figure="' + escape(figure.id) + '">' +
      (title ? '<h3 class="figure-title">' + title + '</h3>' : '') +
      (formula ? '<div class="figure-formula">' + formula + '</div>' : '') +
      '<div class="figure-host">' + (figure.html || (src ? iframe
        ? '<iframe src="' + escape(src) + '" title="' + escape(plain(figure.title) || 'Interactive figure') + '" loading="lazy"></iframe>'
        : '<img src="' + escape(src) + '" alt="' + escape(plain(figure.alt) || plain(figure.title)) + '" loading="lazy">'
        : '')) + '</div>' + (caption ? '<figcaption>' + caption + '</figcaption>' : '') + '</figure>';
  }

  function rawSource(value, label) {
    const text = plain(value);
    return text ? '<details class="source-details raw-source"><summary>' + label + '</summary><pre>' + escape(text) + '</pre></details>' : '';
  }

  function renderResult({detail = 'summary', focus = false} = {}) {
    const node = nodeById.get(state.selected);
    $('reader-section').textContent = node ? sectionTitle(nodeSection(node)) : 'Reading panel';
    $('result-back').disabled = state.trailIndex < 1;
    $('result-forward').disabled = state.trailIndex >= state.trail.length - 1;
    const result = $('result');
    if (!node) {
      result.innerHTML = '<div class="result-inner"><h2 id="result-heading" class="result-heading" tabindex="-1">Select a result</h2>' +
        '<p>Choose a result in the map or search by title.</p></div>';
      return;
    }

    const summary = claimList(node.summary);
    const idea = claimList(node.idea);
    const repositoryIdea = claimList(node.repositoryIdea);
    const statement = sourceHtml(node.statementHtml, node.statementText);
    const proof = sourceHtml(node.proofHtml, node.proofText);
    const steps = list(node.steps);
    const figures = linkedFigures(node);
    const badge = leanBadge(node.lean);
    const corrected = hasCorrections(node);
    const source = typeof node.source === 'string' ? {url: node.source} : node.source;
    const leanDetail = node.lean?.declaration || node.lean?.file;
    const sourceFormat = node.sourceKind === 'blueprint' ? 'Markdown' : 'TeX';
    const renderedSteps = steps.map((step, i) => {
      const text = sourceHtml(step.html, step.text);
      return '<li><details id="proof-step-' + (i + 1) + '"><summary>' + (inlineRich(step.title) || 'Step ' + (i + 1)) + '</summary>' +
        (text ? '<div class="source-math">' + text + claimSource(step.title) + '</div>' : '') + '</details></li>';
    }).join('');
    const sourceLink = externalLink(source?.url, source?.label || 'Paper source');
    const leanLink = externalLink(node.lean?.url, 'Lean source');
    const dependencies = uses(node).map(use => ({node: nodeById.get(String(use.id)), use}));
    const followers = dependents.get(node.id) ?? [];

    result.innerHTML = '<div class="result-inner">' +
      '<div class="result-meta"><span class="result-type">' + escape(resultLabel(node)) + '</span></div>' +
      '<h2 class="result-heading" id="result-heading" tabindex="-1">' + inlineRich(node.title || titleOf(node)) + '</h2>' +
      (badge || corrected ? '<div class="result-badges">' + badge + (corrected
        ? '<a class="badge correction-badge" href="#result-correction">' + icon('info') + 'Correction</a>' : '') + '</div>' : '') +
      (summary ? '<div class="result-summary">' + summary + '</div>' : '') +
      (statement ? '<section class="statement-box" id="result-statement" tabindex="-1"><h3 class="reading-label">' +
        (corrected ? 'Statement as printed' : 'Statement') + '</h3><div class="source-math">' + statement + '</div></section>' : '') +
      resultCorrections(node) + figures.map(figureMarkup).join('') +
      (idea ? '<section class="reading-section" id="result-idea" tabindex="-1"><h3 class="reading-label">Proof idea</h3>' + idea + '</section>' : '') +
      (steps.length || proof ? '<section class="reading-section" id="result-proof" tabindex="-1"><h3 class="reading-label">Proof</h3>' +
        (steps.length ? '<ol class="proof-steps">' + renderedSteps + '</ol>' : '') +
        (proof ? '<details class="source-details"><summary>Full proof from the paper</summary><div class="source-math">' + proof + '</div></details>' : '') +
        rawSource(node.proofText, 'Raw proof source (' + sourceFormat + ')') + '</section>' : '') +
      (repositoryIdea ? '<section class="reading-section"><h3 class="reading-label">Formalization route</h3>' + repositoryIdea + '</section>' : '') +
      relations('Uses', dependencies) + relations('Used by', followers) +
      (sourceLink || leanLink || leanDetail ? '<footer class="result-footer" id="result-source" tabindex="-1">' + sourceLink + leanLink +
        (leanDetail ? '<code class="result-lean-code">' + escape(plain(leanDetail)) + '</code>' : '') + '</footer>' : '') +
      rawSource(node.statementText, 'Raw statement source (' + sourceFormat + ')') +
      '</div>';

    for (const figure of figures) {
      const host = [...result.querySelectorAll('[data-figure]')].find(element => element.dataset.figure === String(figure.id))?.querySelector('.figure-host');
      const render = window.PAPER_FIGURES?.[figure.id];
      if (host && typeof render === 'function') render(host, figure, node);
    }
    decorateNotation(result);
    result.scrollTop = 0;
    const match = detail.match(/^(?:step-)(\d+)$/);
    const target = match ? $('proof-step-' + match[1]) : ({
      statement: $('result-statement'), idea: $('result-idea'), proof: $('result-proof'), source: $('result-source')
    })[detail] ?? $('result-heading');
    if (match && target) target.open = true;
    if (target !== $('result-heading') && target) target.scrollIntoView({block: 'start', behavior: 'instant'});
    if (focus) {
      const focusTarget = target?.matches('details') ? target.querySelector('summary') : target;
      focusTarget?.focus({preventScroll: true});
    }
  }

  function renderOverview(authorDisplay, year, arxiv) {
    const main = nodes.filter(isMain);
    const citation = plain(meta.citation) || authorDisplay + '. ' + $('paper-title').textContent + '. ' + year + '.';
    $('overview-view').innerHTML = '<h2 id="overview-title" class="alternate-heading" tabindex="-1">About this companion</h2>' +
      '<p class="alternate-intro">Start with a main theorem, then follow its links into the supporting results. Each arrow points from a result to a result that uses it.</p>' +
      '<div class="overview-layout"><section><h3>Main theorems</h3><ul class="outline-list">' +
      (main.length ? main : nodes.slice(0, 5)).map(node => outlineItem(node)).join('') + '</ul></section>' +
      '<section class="overview-notes"><h3>Reading the map</h3><p>Open a section to see its results, or choose Focus to see the dependencies around the current result. Use the reading panel to open each proof step and the full proof from the paper.</p>' +
      '<p>Lean badges link to ' + (meta.leanSnapshot ? 'bundled source pages for ' : 'declarations at repository commit ') + escape((meta.commit || '').slice(0, 8)) + (meta.leanSnapshot?.dirty ? ' plus local changes' : '') + '. A reduction-only badge covers the encoded reduction, not the complexity-class theorem. Refreshing source links does not run Lean or establish correspondence with a modified statement.</p>' +
      (meta.leanSnapshot?.changedFiles || meta.leanSnapshot?.issues ? '<p>Lean sources have changed since the reviewed snapshot. Updated or unresolved declarations are marked for review; paper statements and proof excerpts retain their original source version.</p>' : '') +
      '<p>Statements and proofs are extracted from hashed source spans. ' + escape(meta.audit?.reviewed || 0) + ' editorial claims have current independent-model reviews. Both reviewers use the GPT family; the cross-provider audit and author approvals required for public release remain outstanding.</p>' +
      '<h3>How to cite</h3><p class="overview-citation">' + escape(citation) + '</p>' +
      (arxiv ? externalLink($('paper-link').getAttribute('href'), 'arXiv record') : '') + '</section></div>';
  }

  function renderCorrections() {
    const entries = corrections.length ? corrections : nodes.filter(hasCorrections).map(node => ({
      id: node.id, title: node.title, claims: node.corrections, nodes: [node.id]
    }));
    const cards = entries.map(correction => {
      const refs = list(correction.nodes ?? correction.node).map(id => nodeById.get(String(id?.id ?? id))).filter(Boolean);
      return '<article class="correction-card" id="correction-' + escape(correction.id) + '" tabindex="-1">' +
        '<div class="reading-label">Paper correction</div><h3>' + (inlineRich(correction.title) || 'Correction') + '</h3>' +
        correctionBody(correction) + (refs.length ? '<div class="correction-links">' +
          refs.map(node => '<a href="' + resultHash(node.id) + '">' + escape(resultLabel(node) || titleOf(node)) + '</a>').join('') + '</div>' : '') + '</article>';
    }).join('');
    $('corrections-view').innerHTML = '<h2 id="corrections-title" class="alternate-heading" tabindex="-1">Corrections</h2>' +
      (cards ? '<p class="alternate-intro">These notes accompany the paper excerpts and link to the affected results.</p><div class="correction-list">' +
        cards + '</div>' : '<p class="alternate-intro">No corrections are listed.</p>');
  }

  function rememberResult(id) {
    if (state.trail[state.trailIndex] === id) return;
    state.trail.splice(state.trailIndex + 1, state.trail.length, id);
    state.trailIndex = state.trail.length - 1;
  }

  function setMobilePane(pane) {
    $('panes').dataset.mobile = pane;
    press('mobile-map', pane === 'map');
    press('mobile-reading', pane === 'reading');
  }

  function pageView(page) {
    state.page = page;
    $('map-workspace').hidden = page !== 'map';
    $('overview-view').hidden = page !== 'overview';
    $('corrections-view').hidden = page !== 'corrections';
    for (const name of ['map', 'overview', 'corrections']) {
      if (page === name) $('nav-' + name).setAttribute('aria-current', 'page');
      else $('nav-' + name).removeAttribute('aria-current');
    }
  }

  function route(hash, options = {}) {
    if (hash && !hash.startsWith('#/')) return;
    let [id, detail] = ['', ''];
    try { [id, detail] = hash.slice(2).split('/').map(decodeURIComponent); }
    catch { /* A malformed link opens the map. */ }
    if (id === 'overview' || id === 'corrections') {
      pageView(id);
      const target = id === 'corrections' && detail ? $('correction-' + detail) : $(id + '-title');
      if (detail) target?.scrollIntoView({block: 'nearest'});
      if (options.focus) target?.focus({preventScroll: true});
      return;
    }
    pageView('map');
    if (nodeById.has(id)) {
      if (!options.fromTrail) rememberResult(id);
      state.selected = id;
      if (!options.keepExpanded) setExpanded(false, false);
      setMobilePane('reading');
    }
    renderResult({detail: detail || 'summary', focus: Boolean(options.focus)});
    updateGraph();
  }

  function navigate(hash, options = {}) {
    if (location.hash !== hash) history.pushState(null, '', hash);
    route(hash, options);
  }

  function chooseResult(id, options = {}) {
    if (!nodeById.has(id)) return;
    navigate(resultHash(id), {focus: true, ...options});
  }

  function traverseResults(direction) {
    const next = state.trailIndex + direction;
    if (next < 0 || next >= state.trail.length) return;
    state.trailIndex = next;
    chooseResult(state.trail[next], {fromTrail: true});
  }

  const searchable = nodes.map(node => {
    const section = sectionTitle(nodeSection(node));
    const number = plain(node.number);
    const heading = [titleOf(node), resultLabel(node), node.id, number].join(' ');
    const context = [section, ...list(node.summary).map(plain), ...list(node.idea).map(plain), plain(node.lean?.declaration)].join(' ');
    return {node, heading: normalize(heading), context: normalize(context)};
  });
  function normalize(value) {
    return String(value).toLowerCase().normalize('NFD').replace(/[\u0300-\u036f]/g, '');
  }
  function renderSearch() {
    const words = normalize($('search-input').value.trim()).split(/\s+/).filter(Boolean);
    const matches = searchable.map(entry => ({
      node: entry.node,
      rank: words.reduce((score, word) => score + (entry.heading.includes(word) ? 3 : entry.context.includes(word) ? 1 : -100), 0)
    })).filter(entry => entry.rank >= 0).sort((a, b) => b.rank - a.rank);
    $('search-count').textContent = matches.length ? matches.length + (matches.length === 1 ? ' result' : ' results') : 'No results found.';
    $('search-results').innerHTML = matches.map(({node}) => outlineItem(node)).join('');
    decorateNotation($('search-results'));
  }
  function openSearch() {
    const dialog = $('search-dialog');
    if (dialog.open) return;
    $('notation-dialog').close();
    $('search-input').value = '';
    renderSearch();
    dialog.showModal();
    $('search-input').focus();
  }
  function renderNotation(selected) {
    $('notation-content').innerHTML = notation.map(entry => {
      const active = String(entry.id) === selected;
      return '<section class="notation-entry' + (active ? ' is-highlighted' : '') + '" id="notation-' + escape(entry.id) + '" tabindex="-1">' +
        '<h3>' + (inlineRich({html: entry.html, text: plain(entry.symbol)}) || escape(entry.id)) + '</h3>' + claimList(entry.definition) + '</section>';
    }).join('') || '<p>No notation is listed.</p>';
    decorateNotation($('notation-content'));
  }
  function openNotation(id = '') {
    const dialog = $('notation-dialog');
    if ($('search-dialog').open) $('search-dialog').close();
    renderNotation(id);
    if (!dialog.open) dialog.showModal();
    const entry = $('notation-' + id);
    if (entry) {
      entry.scrollIntoView({block: 'nearest'});
      entry.focus({preventScroll: true});
    }
  }
  function notationId(element) {
    const token = element.dataset.notation ?? element.dataset.symbol ?? element.getAttribute('href')?.replace(/^#(?:\/notation\/|notation-)?/, '');
    return notation.find(entry => entry.id === token || plain(entry.symbol) === token)?.id;
  }
  function decorateNotation(container) {
    const decorate = () => {
      for (const element of container.querySelectorAll('[data-notation], [data-symbol], .notation-ref')) {
        if (!notationId(element) || element.matches('button, a[href]')) continue;
        element.tabIndex = 0;
        element.setAttribute('role', 'button');
      }
    };
    const pending = window.PAPER_MATH.renderIn(container, paper.math.macros, window.katex);
    if (pending && typeof pending.then === 'function') pending.then(decorate);
    else decorate();
  }

  function setSplit(value) {
    state.split = Math.max(28, Math.min(70, value));
    $('panes').style.setProperty('--split', state.split + 'fr');
    $('panes').style.setProperty('--reader-split', (100 - state.split) + 'fr');
    $('splitter').setAttribute('aria-valuenow', String(Math.round(state.split)));
  }

  function setFont(value) {
    state.size = Math.max(13, Math.min(22, value));
    $('reader').style.setProperty('--reading-size', state.size + 'px');
    $('font-smaller').disabled = state.size === 13;
    $('font-larger').disabled = state.size === 22;
    saveSetting('font-size', state.size);
  }

  function setTheme(theme) {
    const embedded = document.querySelector('.visual-paper');
    if (!embedded) document.documentElement.dataset.theme = theme;
    if (embedded) embedded.dataset.theme = theme;
    const label = theme === 'dark' ? 'Switch to light theme' : 'Switch to dark theme';
    const toggle = $('toggle-theme');
    if (toggle) { toggle.setAttribute('aria-label', label); toggle.title = label; toggle.innerHTML = icon(theme === 'dark' ? 'sun' : 'moon'); }
    if (state.graph) state.graph.style().fromJson(graphStyle()).update();
  }

  function setExpanded(expanded, refresh = true) {
    state.expanded = expanded;
    $('panes').classList.toggle('is-expanded', expanded);
    press('toggle-expand', expanded);
    const label = expanded ? 'Return to split view' : 'Expand graph';
    $('toggle-expand').setAttribute('aria-label', label);
    $('toggle-expand').title = label;
    $('toggle-expand').innerHTML = icon(expanded ? 'contract' : 'expand');
    if (refresh) requestAnimationFrame(fitGraph);
  }

  function setReading(reading) {
    if (state.page !== 'map') navigate('#/map');
    if (reading) setExpanded(false, false);
    state.reading = reading;
    $('panes').classList.toggle('is-reading', reading);
    press('toggle-reading', reading);
    $('toggle-reading').querySelector('span').textContent = reading ? 'Show graph' : 'Reading mode';
    if (mobile.matches) setMobilePane(reading ? 'reading' : 'map');
    if (!reading) updateGraph();
    if (reading && document.activeElement?.closest('.map-pane')) $('reader').focus({preventScroll: true});
    saveSetting('reading', reading);
  }

  function setOutline(open) {
    state.outline = open;
    $('panes').classList.toggle('is-outline', open);
    $('toggle-outline').setAttribute('aria-expanded', String(open));
    $('toggle-outline').textContent = open ? 'Diagram' : 'Outline';
    if (!open) updateGraph();
  }

  function zoomBy(factor) {
    const cy = state.graph;
    if (!cy) return;
    cy.zoom({level: cy.zoom() * factor, renderedPosition: {x: cy.width() / 2, y: cy.height() / 2}});
  }

  function bindControls() {
    $('open-search').addEventListener('click', openSearch);
    $('open-notation').addEventListener('click', () => openNotation());
    $('search-input').addEventListener('input', renderSearch);
    $('search-dialog').addEventListener('keydown', event => {
      const buttons = [...$('search-results').querySelectorAll('button')];
      const current = buttons.indexOf(document.activeElement);
      if (event.key === 'Enter' && document.activeElement === $('search-input') && buttons.length) {
        event.preventDefault();
        buttons[0].click();
      }
      if (event.key === 'ArrowDown' || event.key === 'ArrowUp') {
        event.preventDefault();
        const next = current + (event.key === 'ArrowDown' ? 1 : -1);
        if (next < 0) $('search-input').focus();
        else buttons[next]?.focus();
      }
    });
    for (const dialog of document.querySelectorAll('dialog')) {
      dialog.querySelector('[data-close-dialog]').addEventListener('click', () => dialog.close());
      dialog.addEventListener('click', event => {
        if (event.target !== dialog) return;
        const bounds = dialog.getBoundingClientRect();
        if (event.clientX < bounds.left || event.clientX > bounds.right || event.clientY < bounds.top || event.clientY > bounds.bottom) dialog.close();
      });
    }
    $('section-select').addEventListener('change', event => {
      showSection(event.target.value);
      if (mobile.matches) setMobilePane('map');
    });
    $('view-whole').addEventListener('click', () => showSection(''));
    $('view-focus').addEventListener('click', () => {
      state.mode = 'focus';
      $('section-select').value = '';
      updateGraph();
    });
    $('toggle-outline').addEventListener('click', () => setOutline(!state.outline));
    $('toggle-reading').addEventListener('click', () => setReading(!state.reading));
    $('toggle-expand').addEventListener('click', () => setExpanded(!state.expanded));
    $('show-external').addEventListener('change', event => {
      state.external = event.target.checked;
      updateGraph();
    });
    $('zoom-in').addEventListener('click', () => zoomBy(1.25));
    $('zoom-out').addEventListener('click', () => zoomBy(0.8));
    $('zoom-fit').addEventListener('click', fitGraph);
    $('result-back').addEventListener('click', () => traverseResults(-1));
    $('result-forward').addEventListener('click', () => traverseResults(1));
    $('font-smaller').addEventListener('click', () => setFont(state.size - 1));
    $('font-larger').addEventListener('click', () => setFont(state.size + 1));
    $('mobile-map').addEventListener('click', () => setMobilePane('map'));
    $('mobile-reading').addEventListener('click', () => setMobilePane('reading'));
    $('toggle-theme')?.addEventListener('click', () => {
      const theme = document.documentElement.dataset.theme === 'dark' ? 'light' : 'dark';
      setTheme(theme);
      saveSetting('theme', theme);
    });
    dark.addEventListener('change', () => {
      if (!loadSetting('theme', '')) setTheme(dark.matches ? 'dark' : 'light');
    });
    mobile.addEventListener('change', updateGraph);
    document.addEventListener('click', event => {
      const element = event.target.closest('[data-result], [data-notation], [data-symbol], .notation-ref, a[href^="#"]');
      if (!element || event.altKey || event.ctrlKey || event.metaKey || event.shiftKey) return;
      if (element.dataset.result) {
        if ($('search-dialog').open) $('search-dialog').close();
        chooseResult(element.dataset.result);
        return;
      }
      const id = notationId(element);
      const href = element.getAttribute('href');
      if (id) {
        event.preventDefault();
        openNotation(id);
      } else if (href?.startsWith('#/')) {
        event.preventDefault();
        navigate(href, {focus: true});
      } else if (href === '#result-heading' || href === '#result-correction') {
        event.preventDefault();
        if (state.page !== 'map') navigate('#/map');
        setExpanded(false);
        setMobilePane('reading');
        const target = $(href.slice(1));
        target?.scrollIntoView({block: 'nearest'});
        target?.focus({preventScroll: true});
      }
    });
    document.addEventListener('keydown', event => {
      if (event.altKey || event.ctrlKey || event.metaKey) return;
      const key = event.key.toLowerCase();
      if (key === 'escape') {
        const dialog = document.querySelector('dialog[open]');
        if (dialog) { event.preventDefault(); dialog.close(); return; }
      }
      if (key === 'escape' && state.expanded && !$('notation-dialog').open && !$('search-dialog').open) setExpanded(false);
      if (event.target.closest('input, textarea, select, [contenteditable], dialog')) return;
      const notationLink = event.target.closest('[data-notation], [data-symbol], .notation-ref');
      if (notationLink && !notationLink.matches('button, a[href]') && ['enter', ' '].includes(key)) {
        const id = notationId(notationLink);
        if (id) {
          event.preventDefault();
          openNotation(id);
        }
      }
      if (key === '/') {
        event.preventDefault();
        openSearch();
      }
      if (key === 'g') setReading(!state.reading);
    });
    window.addEventListener('hashchange', () => route(location.hash));
  }

  function bindSplitter() {
    const splitter = $('splitter');
    function move(event) {
      const bounds = $('panes').getBoundingClientRect();
      setSplit((event.clientX - bounds.left) / bounds.width * 100);
    }
    function end(event) {
      if (splitter.hasPointerCapture(event.pointerId)) splitter.releasePointerCapture(event.pointerId);
      splitter.removeEventListener('pointermove', move);
      document.body.classList.remove('dragging');
      saveSetting('split', state.split);
      requestAnimationFrame(fitGraph);
    }
    splitter.addEventListener('pointerdown', event => {
      if (event.button !== 0) return;
      splitter.setPointerCapture(event.pointerId);
      splitter.addEventListener('pointermove', move);
      document.body.classList.add('dragging');
    });
    splitter.addEventListener('pointerup', end);
    splitter.addEventListener('pointercancel', end);
    splitter.addEventListener('keydown', event => {
      const changes = {ArrowLeft: state.split - 3, ArrowRight: state.split + 3, Home: 28, End: 70};
      if (!(event.key in changes)) return;
      event.preventDefault();
      setSplit(changes[event.key]);
      saveSetting('split', state.split);
      requestAnimationFrame(fitGraph);
    });
  }

  function watchGraphSize() {
    let frame;
    let size = [0, 0];
    const resize = () => {
      const width = $('graph').clientWidth;
      const height = $('graph').clientHeight;
      if (width < 2 || height < 2 || (Math.abs(width - size[0]) < 2 && Math.abs(height - size[1]) < 2)) return;
      size = [width, height];
      cancelAnimationFrame(frame);
      frame = requestAnimationFrame(fitGraph);
    };
    if ('ResizeObserver' in window) new ResizeObserver(resize).observe($('graph'));
    else window.addEventListener('resize', resize);
  }

  setupPaper();
  setTheme(loadSetting('theme', dark.matches ? 'dark' : 'light'));
  if (document.querySelector('.visual-paper')) new MutationObserver(() => {
    const theme = document.documentElement.dataset.theme || (dark.matches ? 'dark' : 'light');
    const embedded = document.querySelector('.visual-paper');
    embedded.dataset.theme = theme;
    if (state.graph) state.graph.style().fromJson(graphStyle()).update();
  }).observe(document.documentElement, {attributes: true, attributeFilter: ['data-theme']});
  setFont(Number(loadSetting('font-size', 16)) || 16);
  setSplit(Number(loadSetting('split', 54)) || 54);
  bindControls();
  bindSplitter();
  watchGraphSize();
  route(location.hash.startsWith('#/') ? location.hash : '');
})();
