# Blueprint-writer brief (Sonnet) — read fully before starting

Goal: write `blueprint.md` at the ROOT of the repository /home/user/HardnessBilevelProgramming (currently empty, branch
claude/elegant-maxwell-o2ppx8). It is the master plan for a Lean 4 + Mathlib formalization of arXiv:2407.12372
("Geometric and computational hardness of bilevel programming", Bolte–Lê–Pauwels–Vaiter, v2, Jan 2025).
Audience: mathematicians and Lean developers who will implement it, file by file, lemma by lemma. It must be
self-contained (a reader should not need the research reports) and faithful to the AUDITED conclusions.

Inputs (read ALL of them, in this order):
1. <SCRATCH>/brief/common.md  (conventions, baseline encoding)
2. The paper text <SCRATCH>/paper/paper_html.txt (to quote statements exactly)
3. The six research reports in <SCRATCH>/research/*.md
4. The six audit reports in <SCRATCH>/audit/*-AUDIT.md — WHERE A REPORT AND ITS AUDIT DISAGREE, THE AUDIT WINS unless the
   orchestrator's consolidation note (<SCRATCH>/brief/consolidation.md) says otherwise. Read the consolidation note too.
<SCRATCH> = /tmp/claude-0/-home-user-HardnessBilevelProgramming/418e0315-f899-5121-bf9e-35c4125b9a45/scratchpad

Required structure of blueprint.md (use these top-level sections; Markdown with LaTeX math in $...$):
0. Header: title, paper reference (arXiv id, authors, version), purpose, status legend, how to read.
1. Executive summary: what will be formalized fully, what is formalized relative to explicitly stated assumptions
   (Tarski–Seidenberg, finiteness theorem, growth bound, complexity-theoretic facts), what is out of scope — with a one-screen
   dependency diagram (ASCII or Mermaid) of theorems → lemmas → Mathlib/assumptions.
2. Conventions and Lean encoding: types for points, polynomials, boxes, bilevel data, argmin set, optimistic/pessimistic value
   functions in EReal, semialgebraic sets/functions (the chosen definition), the quarantined assumptions (exact Lean-style
   statements, one file), notational table paper ↔ Lean.
3. Module/file plan: proposed directory layout (e.g. `HardnessBilevel/Framework/*.lean`, `.../Semialgebraic/*.lean`,
   `.../Smooth/*.lean`, `.../Unbounded/*.lean`, `.../Bounded/*.lean`, `.../Convex/*.lean`, `.../Hardness/*.lean`), each file
   with its purpose, its lemmas (by id), imports, and an effort estimate; plus a build order.
4. One section per result group, in dependency order: framework lemmas; semialgebraic infrastructure; Theorem 1.1;
   Corollary 2.9/Berge; Theorem 2.12; Theorem 2.15; Theorems 2.18–2.20; Theorem 2.21; Section 3 (Lemma 3.3 / Theorem 3.2).
   For EVERY lemma/theorem: a stable id (e.g. `fw.argmin_prod`, `sa.closure`, `t212.gadget_strict`), the precise mathematical
   statement, a Lean-style signature (pseudo-Lean is fine but types must be right), the proof at implementer granularity
   (every case split and inequality; reference the lemma ids it uses), the Mathlib declarations used (name + file path, exactly
   as verified in the audits), status tag (`[prove]`, `[assume: TS]`, `[assume: finiteness]`, `[assume: growth]`,
   `[not formalized: complexity]`, `[optional]`), and effort (S/M/L/XL).
5. Paper errata: numbered list of every confirmed error/gap/typo in the paper, with the fix adopted in the blueprint.
6. Risks, open questions, and alternatives rejected (short).
7. Roadmap: phases/milestones (what to formalize first to de-risk), and a checklist.

Rules:
- Never cite a Mathlib name that the audits did not confirm; if you need one that was not checked, grep the local Mathlib
  source (<SCRATCH>/mathlib/mathlib4/Mathlib) yourself and give file:line, or mark it "(to verify)".
- Do not invent new mathematics. If something is unresolved in the audits, say so under Open questions rather than papering over it.
- Write the file with the Write tool (or a heredoc); it will be long (expect 1500–3000 lines). Keep it well organized with a table
  of contents at the top. Use consistent lemma ids; every lemma referenced must be defined somewhere in the file.
- Do not create any other file in the repository. Do not commit. When done, reply with a short summary and the list of
  assumptions/stubs the blueprint declares.
