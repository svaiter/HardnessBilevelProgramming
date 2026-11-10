# Bilevel hardness — visual paper

An author-review companion to Bolte, Lê, Pauwels and Vaiter,
*Geometric and computational hardness of bilevel programming*.

The application has 18 result nodes, 35 directed dependencies, 38 source proof
steps, 29 correction notes, a notation glossary and two interactive examples.
Its 233 editorial claims have hash-bound independent-model review verdicts.
Paper quotations are extracted at build time from pinned arXiv v2 TeX; the
repository's corrected arguments are displayed separately. No paper or Lean file
outside this directory was edited.

[Open the private review site](https://bilevel-hardness-visual-paper.starrymandrill2.chatgpt.site).

## Host it on your website

Upload the contents of **`website/`**, or extract
**`bilevel-hardness-website.zip`**. All assets and Lean source pages are bundled;
the folder works at any URL sub-path without a backend or ChatGPT account.

After editing Lean sources, from this directory run:

```sh
npm run update
```

This refreshes the local Lean snapshot and declaration links, then regenerates the
upload directory and ZIP. It includes uncommitted edits. Use
`npm run update -- --ref HEAD` for a committed snapshot. For layout-only changes,
use `npm run export`. See **[HOSTING.md](HOSTING.md)** for upload instructions,
renamed declarations, and the editable mapping file.

## Use

Open `dist/index.html` directly in a browser (no server is needed), or:

```sh
cd visual-paper
npm run build
npm test
npm run preview
```

The build uses Node.js and Pandoc. KaTeX, Cytoscape, Dagre, their browser assets
and licences are vendored, so it requires no package download. To reproduce
browser tests, install Playwright or use the bundled Codex runtime, then run
`npm run test:browser`. Optional `--chromium <executable>` and
`--webkit <executable>` arguments select installed browsers.

## Integrity and review

- `SOURCE.lock` pins the TeX, compiled numbering and the Lean repository at
  `d1032f4c70da9b037605c2f444ce2450900e5a76`.
- Anchors use Unicode codepoint offsets, start inclusive and end exclusive,
  and SHA-256 of the UTF-8 source slice.
- `scripts/check.mjs` checks anchors, citations, complete proof partitions,
  graph acyclicity, linked declaration names and current audit verdicts.
- `scripts/build.mjs` extracts quotes, resolves references from `main.aux`,
  validates every formula with KaTeX and fails on any error. The exported data
  keeps compact TeX; bundled KaTeX renders it in the browser when a view opens,
  using the same macro table and renderer, with MathML and notation links.
- `audit/ledger.json` retains the initial findings and the independent revision
  verdicts. Editing claim text or evidence invalidates its supported verdict.
- The initial review supported 227 of 230 claims; a separate reviewer supported
  three revised claims and three additional dependency explanations.
- `npm run release` is deliberately blocked without hash-bound author approval,
  accepted audit policy and approved figures. No approval is fabricated.

The mathematical writer used GPT-6.1 Sol. Independent reviewers used separate
GPT-6 Astra sessions, each calibrated with a source-first trial. This is not a
cross-provider audit. Figures and public release await author review. Lean badges
link to existing pinned declarations; this companion did not rerun the Lean build.

## Validation

Fifteen integrity and source-update tests pass. Chromium and WebKit checked the
exported website, every result and bundled Lean declaration link, all 1,266 math
expressions (including MathML and repeated rendering), proof expanders, figure
controls and pop-outs, search, notation, focus views, corrections,
dark theme and a 390px mobile viewport. Relative URL resolution was tested under
a project sub-path through Playwright request routing, and direct `file://`
opening was tested in both engines. The shell could not bind a local HTTP server,
so this was not a live-server test.

Browser rendering reduces `data.js` from 3,728,883 to 517,014 bytes (86.1%).
The bundled KaTeX engine and shared renderer add 277,918 bytes. All 361 generated
HTML snippets match the previous rendering after removing the new math wrappers.

Detailed results are in `reports/build.json`, `reports/browser-checks.json`,
`reports/math-parity.json`, `reports/math-size.json`, `reports/content-report.md`,
and `audit/reviewer2-figures.md`.

## Deployment

The registered Site is owner-private. Its source checkout contains only the built
site and hosting manifest, not manuscript source, audit packets or local reports.
The original public GitHub repository was not pushed or changed remotely.
Reuse `.openai/hosting.json` when updating this Site; do not create a second one.

## Updating sources

Lean updates use `npm run update`; they are recorded independently in
`LEAN.lock.json` and `source/lean/`. Edit `content/lean-map.json` to change a
paper-node/declaration association. Line changes and unambiguous file moves are
resolved automatically. Changed code and dependencies receive review-needed
badges; missing declarations receive unresolved badges. This never runs Lean or
silently updates mathematical summaries.

For a revised paper or corrected exposition, replace the relevant pinned evidence
deliberately, recompile numbering and re-anchor changed content. Regenerate audit
packets with `node scripts/audit-packet.mjs`; review all changed claim/evidence
hashes before rebuilding. Keep `SOURCE.lock` for that historical evidence separate
from the current Lean snapshot. Never mark old verdicts current by editing their
hashes.

Paper text retains its existing rights. Dependency licences are bundled in the
build's `THIRD_PARTY_LICENSES.txt`.
