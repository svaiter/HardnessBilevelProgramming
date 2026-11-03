# Standing brief for Lean WRITER agents (Opus) — read fully before touching any file

Project: /home/user/HardnessBilevelProgramming (Lake project `HardnessBilevel`, Lean v4.36.0-rc2, Mathlib pinned at
commit 1df8067a; the Mathlib SOURCE is at .lake/packages/mathlib/Mathlib — grep it for names; the ONLINE docs are NOT
guaranteed to match this commit). Shell: put `export PATH="$HOME/.elan/bin:$PATH"` at the start of every Bash command.

Read first: /home/user/HardnessBilevelProgramming/PLAN.md (ground rules §1, build discipline §1.7) and the sections of
/home/user/HardnessBilevelProgramming/blueprint.md named in your assignment. The blueprint is the specification:
statements, names, proof routes and Mathlib names were checked against this Mathlib commit, but the Lean text there is
pseudo-Lean — expect to adapt tactic details, implicit arguments and the odd lemma name.

## Non-negotiable rules
1. No `sorry`, `axiom`, `native_decide`, `unsafe`, `opaque` tricks. Every file you deliver must type-check with
   `lake env lean <file>` (single-file check) and build with `lake build HardnessBilevel.<Module>` (your modules only).
   NEVER run a bare `lake build` (other agents are building concurrently). Never edit lakefile.toml / lean-toolchain /
   HardnessBilevel.lean (root) / files outside your assignment. Never `lake update` or `lake exe cache get`.
2. Statements must be the blueprint's (same hypotheses, same conclusion, same types). You may STRENGTHEN (drop an unused
   hypothesis, prove a more general version) but never weaken, never add a hypothesis, never change a definition's meaning
   to make a proof easier. If something in the blueprint is wrong or un-provable as written, prove the correct variant
   and document the deviation in the file header AND in your final report.
3. Definitions: `namespace Bilevel`; names as in the blueprint (`argminSet`, `valueFun`, `pvalueFun`, `IsPolyFun`, …);
   universe-0 `Type` for index types in existentials; `autoImplicit` is off (declare every variable).
4. `#print axioms` of every public theorem must be ⊆ {propext, Classical.choice, Quot.sound}. Add a commented-out or
   trailing `#print axioms` check during development; remove noisy commands from the delivered file (no `#eval`, `#check`
   output left behind; `#print axioms` lines are allowed at the end of a file if you want, but prefer removing them).
5. Forbidden (deprecated/wrong in this Mathlib): `stdSimplex`, `isCompact_stdSimplex`, `isClosed_stdSimplex`,
   `stdSimplex_subset_Icc`, `Set.mem_setOf_eq` (use `Set.mem_ofPred_eq`/simp), `IsMinOn.on_subset`, `ContDiff ℝ ⊤`
   (= analytic; C^∞ is `ContDiff ℝ ∞` with `open scoped ContDiff`), casting ℕ/ℤ/ℚ directly into `EReal` (go through ℝ).
6. Keep proofs robust: prefer `simp only [...]`/`rw` with named lemmas over bare `simp` where the goal shape matters;
   use `nlinarith`/`positivity`/`linarith`/`fun_prop` freely; no `decide` on non-trivial props.
7. Work incrementally: write a small piece, check it with `lake env lean`, continue. Expect each `lake env lean` of a file
   importing Mathlib to take ~10–60 s (loading .oleans). Do NOT loop on huge files; split lemmas.
8. When you finish: write a report to <SCRATCH>/reports/<unit>-WRITER.md with: files delivered; the list of blueprint ids
   implemented (with the Lean names); deviations from the blueprint (statement or route) with reasons; Mathlib names that
   differed from the blueprint; anything NOT done and why; the exact `lake build` command(s) you ran last and their result.
   <SCRATCH> = /tmp/claude-0/-home-user-HardnessBilevelProgramming/418e0315-f899-5121-bf9e-35c4125b9a45/scratchpad
   Final chat message: a 10-line summary. Do not commit (the orchestrator commits).

## Practical notes
* `lake env lean HardnessBilevel/Foo/Bar.lean` checks a file against the already-built imports. If your file imports
  another project module (from an EARLIER wave, or your own earlier file), that module must already be built:
  `lake build HardnessBilevel.Foo.Earlier` first.
* Searching Mathlib: `grep -rn "theorem name" .lake/packages/mathlib/Mathlib`; for `to_dual`/`to_additive`-generated
  names grep the source twin (`iSup`/`mul` versions). `#check @name` inside a scratch file is the final arbiter.
* EReal API lives in Mathlib/Data/EReal/{Basic,Operations}.lean and Mathlib/Topology/Instances/EReal/*.lean;
  semicontinuity in Mathlib/Topology/Semicontinuity/{Defs,Basic}.lean; MvPolynomial eval in
  Mathlib/Algebra/MvPolynomial/{Basic,Eval,Rename,Monad}.lean; order-compactness in Mathlib/Topology/Order/Compact.lean.
* A scratch file for experiments: put it under <SCRATCH>/lean/ (NOT in the repo) and check it with
  `cd /home/user/HardnessBilevelProgramming && lake env lean <SCRATCH>/lean/scratch.lean`.
