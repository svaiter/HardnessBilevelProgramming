# Audit brief (Opus auditors) — read fully before starting

You are auditing ONE research report written by another agent for a Lean 4 + Mathlib formalization blueprint of
arXiv:2407.12372 ("Geometric and computational hardness of bilevel programming", Bolte–Lê–Pauwels–Vaiter).
Read first: <SCRATCH>/brief/common.md (project conventions, resources, baseline Lean encoding) and then the
report assigned to you. <SCRATCH> = /tmp/claude-0/-home-user-HardnessBilevelProgramming/418e0315-f899-5121-bf9e-35c4125b9a45/scratchpad
Paper text: <SCRATCH>/paper/paper_html.txt. Mathlib source: <SCRATCH>/mathlib/mathlib4/Mathlib (grep it; no Lean toolchain).

Your stance: adversarial, independent. The researcher may be wrong in confident language. Do not accept a claim
because it is plausible; re-derive it. In particular:
1. MATH: re-prove every lemma in the report's proof DAG yourself at the level of detail given. For each, record a verdict:
   CONFIRMED (you re-derived it), FIXED (wrong/incomplete; give the corrected statement/proof), or UNRESOLVED (say exactly
   what is missing). Pay special attention to: argmin computations (nonemptiness, exact description, free coordinates),
   attainment vs infimum, EReal edge cases (empty argmin ⇒ +∞, unbounded below ⇒ −∞), boundary cases of boxes
   (closed intervals, coordinate at endpoints), degenerate index sets (empty families, single piece), sign conditions,
   and whether the theorem proved is the theorem STATED in the paper (or a clearly flagged variant).
2. PAPER ERRORS: check each "error in the paper" the report claims. Confirm or refute each with a precise reference to the
   paper text. Also look for paper errors the report MISSED in its scope.
3. MATHLIB: for every Mathlib declaration cited, grep the local source and confirm the name exists, the file:line is right,
   and the statement actually provides what the report uses it for (read the declaration's hypotheses/universes/typeclasses).
   Record MISSING or MISUSED citations. Also check the "NOT IN MATHLIB" claims by grepping for plausible alternative names
   (Mathlib naming conventions: `IsCompact.`, `ConvexOn.`, `MvPolynomial.`, `LowerSemicontinuous.`, `Finset.`, ...).
4. ROUTE: assess whether the chosen proof route is really the cheapest correct one. If you see a materially simpler route,
   describe it with enough detail to be checked. If the report proposes a simplification of the paper's construction, verify the
   simplified construction with the same rigor as the original — a wrong "simplification" is the most dangerous outcome.
5. LEAN ENCODING: flag type-level problems (e.g. `Fin n ⊕ Fin m` vs `Fin (n+m)`, EReal coercions, `⨅` over empty sets,
   decidability, `MvPolynomial.eval` of products over `Finset`, `ConvexOn` needing a convex domain, `ContDiff ℝ ⊤` vs `∞`
   in current Mathlib (check `Mathlib/Analysis/Calculus/ContDiff/Defs.lean` for the `WithTop ℕ∞` convention)).

Output: write <SCRATCH>/audit/<report-name>-AUDIT.md with sections:
A. Summary verdict (2–5 sentences: is the report reliable? what must change?)
B. Lemma-by-lemma verdict table (lemma id, verdict, note)
C. Corrections (numbered; each with the wrong claim quoted briefly, the fix, and a proof/argument)
D. Mathlib citation check table (declaration, exists?, file:line verified?, statement adequate?, note)
E. Missed issues (math or Lean) the report did not raise
F. Route assessment and final recommended route for the blueprint (short, concrete)
G. Items to escalate to the orchestrator (cross-report consistency questions, definitional choices affecting other parts)
Do NOT write files into the repository /home/user/HardnessBilevelProgramming. End with a short summary in your final message.
