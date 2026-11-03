# Planning notes behind `blueprint.md`

Provenance for the blueprint (not part of the formalization itself).

- `research/R1`–`R6`: six independent research reports, one per result group of arXiv:2407.12372
  (R1 framework / Thm 1.1 / Berge; R2 semialgebraic infrastructure; R3 Thm 2.12; R4 Thms 2.15 and 2.21;
  R5 Lemma 2.19, Thms 2.18 and 2.20; R6 Section 3 hardness).
- `audit/`: an adversarial audit of each report (every lemma re-derived, every Mathlib citation grepped against
  Mathlib master commit 1df8067a, Lean v4.36.0-rc2). **Where a report and its audit disagree, the audit wins.**
- `consolidation.md`: the decisions (D1–D44 plus ten global ones) that resolve cross-report conflicts; these
  override the reports and are what the blueprint implements.
- `briefs/`: the instructions the research, audit and blueprint-writing agents were given.

Paths of the form `/tmp/.../scratchpad/...` inside these files refer to the planning session's working
directory (paper text, Mathlib checkout) and are not reproduced here. Nothing in these notes was compiled with Lean.
