# W2-e WRITER report (Section 3: Lemma 3.3, reduction, Theorem 3.2 instance type)

## Files delivered
* /home/user/HardnessBilevelProgramming/HardnessBilevel/Hardness/SSI.lean
* /home/user/HardnessBilevelProgramming/HardnessBilevel/Hardness/Construction.lean
* /home/user/HardnessBilevelProgramming/HardnessBilevel/Hardness/Analysis.lean
* /home/user/HardnessBilevelProgramming/HardnessBilevel/Hardness/Reduction.lean
(root HardnessBilevel.lean NOT edited; orchestrator must add the four imports.)

## Blueprint ids -> Lean names (namespace `Bilevel`)
* §4.I.1 definitions: `SSI`, `SSI.subsetSum`, `SSI.Yes` (verbatim); `SSI.Ffun/Gfun/Hfun/Lfun/Qfun/Pfun`,
  `SSI.cube n`, `SSI.box I` (= `Set.pi univ (fun _ => Icc 0 1)` on `Fin (k+1) → ℝ`), polynomials
  `SSI.Fp/Gp/Hp/Lp/Qp/Pp : MvPolynomial (Fin r ⊕ Fin (k+1)) ℤ`, evaluation identities `SSI.aeval_*`,
  `SSI.Pfun_eq_aeval`, `SSI.Qfun_eq_aeval`, glue `SSI.aeval_eq_eval_map`, `SSI.isPolyFun_Pfun/Qfun`.
* s3.L0: `SSI.isMinOn_cons_iff`, `SSI.argminSet_cons` (+ `box_eq`, `mem_box_iff`).
* s3.L1: `SSI.IsBinary`, `Lfun_nonneg`, `Lfun_zero`, `Lfun_eq_zero_iff`, `isMinOn_Lfun_iff`, `Zset`, `mem_Zset_iff`, `Zset_eq`.
* s3.L2: `Hfun_nonneg`, `Hfun_eq_zero_iff`, `continuous_Hfun`, `Tset`, `Tset_nonempty`, `mval`, `Hfun_eq_mval`,
  `mval_le`, `mval_nonneg`, `mval_eq_zero_iff`.
* s3.L3: `argminSet_Qfun`, `mem_argminSet_Qfun_iff`, `cons_mem_argminSet_Qfun`, `argminSet_Qfun_nonempty`.
* s3.L4: `isBinary_iff_exists_fin_two`, `Ffun_fin_two`, `exists_nat_of_isBinary`, `exists_isBinary_Ffun_eq`.
* s3.L5: `tInd`, `tInd_mem_cube`, `isBinary_tInd`, `Gfun_tInd`, `Gfun_of_isBinary`.
* s3.L6: `valueFun_eq` (+ `valueFun_of_isBinary`, `valueFun_of_not_isBinary`, `Pfun_of_mem_argminSet`).
* s3.L7: `optVal_lt_zero_of_yes`. s3.L8: `valueFun_nonneg_of_not_yes`, `valueFun_zero_of_not_yes`.
* s3.lemma33: `SSI.lemma33`, `SSI.lemma33_no`.
* `BilevelInstance` (fields as specified), `.box`, `.Pfun`, `.Qfun` (aeval), `.optVal`, `.Yes`
  (`I.optVal < ((I.c : ℝ) : EReal)`), `.isPolyFun_Pfun/Qfun`; `reduce`; `reduce_box`, `reduce_optVal`.
* s3.degree: `SSI.totalDegree_Pp`, `SSI.totalDegree_Qp` (≤ 5 only; helpers `totalDegree_Fp/Gp ≤ 1`, `Hp ≤ 4`, `Lp ≤ 5`).
* s3.reduce_correct: `reduce_correct`. s3.integer_coeff: by construction (`Pp Qp : MvPolynomial _ ℤ`; documented in
  Reduction header).

## Deviations (naming/packaging only; no change of meaning)
* All instance-dependent objects are in `Bilevel.SSI` (avoids clashes like a global `Bilevel.box`). So the blueprint's
  `lemma33 (I) : optVal (Pfun I) (Qfun I) (box I.k) < 0 ↔ I.Yes` is `Bilevel.SSI.lemma33 : optVal I.Pfun I.Qfun I.box < 0 ↔ I.Yes`;
  `I.box` is the same set as the blueprint's `box I.k` (`[0,1]^(k+1)`).
* `Zset x`, `Tset x` defined as `argminSet Lfun (Icc 0 1) x` / `argminSet Hfun (cube k) x` (equal, via `mem_argminSet_iff`,
  to the blueprint's IsMinOn sets). `mval x := sInf (H x '' cube k)`, proved to be the attained minimum (`Hfun_eq_mval`).
* `IsBinary` has a noncomputable `DecidablePred` instance (from `Real.decidableEq`) so the `if` in `Zset_eq`, `valueFun_eq`
  elaborates with no `open Classical`.
* `s3.coeff_bound` (optional) NOT done.

## Mathlib name differences
* `if_pos`/`if_neg` are deprecated in this Mathlib (use `ite_eq_left`/`ite_eq_right`).
* Used own helper `sum_sq_eq_zero_iff'` (via `Finset.sum_eq_zero_iff_of_nonneg`) instead of `Finset.sum_sq_eq_zero_iff`.
  Everything else as in the blueprint (`finFunctionFinEquiv_apply`, `Finset.sum_ite_mem`, `Finset.sum_filter`, `iInf_lt_iff`,
  `IsCompact.exists_isMinOn`, `isCompact_univ_pi`, `aeval_def`, `eval₂_eq_eval_map`, `totalDegree_*`).

## Build
`lake build HardnessBilevel.Hardness.Reduction` -> "Build completed successfully (18255 jobs)" (only the generic
"designed for use with the module system" warning). No sorry/axiom/native_decide. `#print axioms` on all 97 declarations
⊆ {propext, Classical.choice, Quot.sound}.
