# Content and source review

The draft covers 18 map nodes from the bilevel framework through the geometric representations and strict-threshold hardness. The frozen content has 233 unique cited claims, 38 exact proof cuts, 35 dependency edges, 29 correction entries, and two figure proposals.

## Source and correspondence

- The upstream source is arXiv 2407.12372v2. The downloaded archive has SHA-256 `96bdc12e6f7069ddc90e9456b1531046c734ef18eb9303818052a288f64e674d`. Its `main.tex` and `main.bbl` supply the paper excerpts and references.
- Two successful pdfLaTeX passes generated the derived `main.aux` and a 33-page scratch PDF. Every result number in the map matches its compiled label. The archive and extracted source files retain their original bytes.
- The Lean badges point to declarations at `d1032f4c70da9b037605c2f444ce2450900e5a76`. Theorem 3.2 has a reduction-only badge, with correctness and degree bounds linked separately from the paper's complexity claim. Proposition 2.5's badge points to the proved instance of the corrected growth bound.
- The original paper statements and proof excerpts remain separate from the corrections in `blueprint.md` §5. The repository proof ideas for the compactness result, the two box representations, the basic indicator construction and the bounded convex result are stored separately from the original proof ideas.

## Dependency review

The source reference ledger records all active reference tokens in the selected statement and proof spans. It ignores TeX comments and the disabled block in Lemma 3.3. It contains 31 references within a node, 22 represented by a graph edge, 10 to items outside the current map scope, four navigational or erroneous references; all former edge-review items are resolved.

- Theorem 2.15 uses the optimistic value definition explicitly. The proof opening's two references to Theorem 2.21 should read Theorem 2.15, as recorded in correction E-4.
- Theorem 2.20 refers twice to Theorem 2.15. The bounded-box classification supplies the upper inclusion, and the normalization argument motivates the construction. The repository derives the upper inclusion directly from Proposition 2.6 and Corollary 2.9 and uses a polynomial bound on the pieces for the construction.
- The pessimistic summary references the pessimistic value definition twice. The map currently connects the summary to the optimistic results transferred by negation.
- Theorem 2.21 cites Tarski–Seidenberg in the convex-hull argument. The graph records it as a source reference.
- Whitney's theorem, Berge's theorem, the definitions of basic semialgebraic sets and piecewise polynomials, the disjoint decomposition in Appendix C, and the expressivity table are recorded as references outside the 18-node scope.

## Figures awaiting review

- Proposition 2.5 illustrates the reciprocal singularity in E-1 by approaching a positive diagonal point from one side while staying outside the comparison radius.
- Proposition 2.6 illustrates E-8 by moving along the positive branch of the lower minimizer hyperbola and approaching an upper infimum that is never attained.

## Revisions after independent review

- The second proof idea for Proposition 2.6 now cites the whole infimum criterion, including the universal lower bound and the approximation condition.
- The dependency from Proposition 2.4 to Theorem 2.15 distinguishes the graph closure in the paper from the closed epigraph in the repository proof, with a separate source span for each.
- Theorem 3.2's proof step now identifies the subset sum interval reduction as the input to the hardness deduction and cites the lemma that gives the reduction.
- The proof cut in Theorem 2.18 now follows the closing delimiter of the independent-block display. All 38 proof cuts fall outside explicit math environments.
