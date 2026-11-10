# Visual paper — plan of record

Source: arXiv:2407.12372v2, retrieved 2026-11-09; Lean repository commit
`d1032f4c70da9b037605c2f444ce2450900e5a76`.

Build a private author-review preview covering the main smooth, polynomial,
convex-lower-level and complexity results. Exact paper statements and proofs are
extracted from hashed spans; corrections appear separately, attributed to the
repository's blueprint and its current Lean implementation. No manuscript edits.

Navigation: a proof map, local focus views, searchable reading panel, corrections
index, notation glossary and pinned Lean links. Browser history tracks result
navigation; graph zoom changes do not add history entries.

Independent content review: writer GPT-6.1 Sol; auditor GPT-6 Astra, with a separate
source-first stage and calibration packet. This is independent model review within
the GPT family, not a cross-provider audit. Public release is blocked until the
author has approved the preview and the required audit policy is satisfied.

The existing Lean repository is public. New companion source remains local and is
not pushed into that repository. Only a built site may be deployed for private
review. Public deployment, licensing the paper text, and an arXiv watcher are not
authorized. The original repository's files are unchanged.

## Review gates

- [ ] Author review of this plan, visual direction, structure and sample content.
- [ ] Author review of figures (each remains labelled pending review).
- [ ] Cross-provider mathematical audit, or explicit author approval of the
      independent-model audit used for this private preview.
- [ ] Author approval to publish publicly and choice of destination.

## Validation

Hash verification for source files and every anchor; exact proof-step partitions;
citation coverage; dependency acyclicity; KaTeX render checks; hash-bound audit
ledger; Chromium and WebKit interaction, rendering and sub-path tests.

## Deviations / constraints

- Work takes place in disjoint local directories, not agent worktrees, because the
  environment permits editing the checkout but restricts Git metadata writes.
- The original source is already public; its privacy is not changed. Companion
  source is kept local for review.
- Author gates are consolidated into one concrete preview review; none is treated
  as approval for public release.
- No approved cross-provider auditor is exposed. The independent-model audit does
  not satisfy that stronger control and is never described as doing so.

## Change log

- 2026-11-09: pinned repository head and arXiv v2; began private preview.
- 2026-11-09: completed 18 nodes, 35 dependencies, 38 proof steps, 29 correction
  entries and two interactive illustrations. All 233 claims now have current
  independent-model verdicts; three initial imprecisions were revised and reviewed
  by a separate auditor. Both calibrated auditors rejected every planted error.
- 2026-11-09: seven integrity tests and both browser suites passed. Local socket
  binding was unavailable; sub-path checks used intercepted browser requests.
- 2026-11-09: registered an owner-private review Site. Only generated assets and
  the hosting manifest were synchronized to its separate source repository.
- 2026-11-09: at the author's request, prepared a standalone `website/` directory
  and ZIP for their own web host. Added `npm run update`, a separate current Lean
  snapshot, name-based declaration lookup, bundled source pages and an editable
  mapping. Historical paper evidence and its verdicts remain pinned. Local exports
  retain preview status; no deployment or access change was performed this turn.
- 2026-11-09: fifteen integrity/source-update tests passed; Chromium and WebKit
  checked the exported directory under a sub-path, including every Lean source
  link, mobile layout and existing interactive controls.
- 2026-11-10: at the author's request, moved mathematics to browser-side KaTeX.
  The build still validates all formulas using the same renderer and macro table;
  compact TeX is shipped with bundled offline assets. Audited text, source anchors
  and the Lean refresh workflow are unchanged. Rebuilt the upload directory and
  ZIP; no deployment. `data.js` decreased from 3,728,883 to 517,014 bytes, with
  277,918 bytes of additional renderer scripts. Both browsers checked all 1,266
  expressions, MathML, notation, proof expanders, relative hosting and file access.
  All 361 HTML snippets match the earlier output after removing math wrappers.
  Fifteen integrity/source-update tests passed.
