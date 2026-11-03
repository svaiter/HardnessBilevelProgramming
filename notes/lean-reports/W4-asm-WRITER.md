# W4-asm + W5-a WRITER report

## Files delivered
- /home/user/HardnessBilevelProgramming/HardnessBilevel/Bounded/Thm215.lean
- /home/user/HardnessBilevelProgramming/HardnessBilevel/Convex/Thm220.lean
- /home/user/HardnessBilevelProgramming/HardnessBilevel/Convex/Thm221.lean
- /home/user/HardnessBilevelProgramming/HardnessBilevel/Pessimistic.lean
(root HardnessBilevel.lean NOT edited: the orchestrator must add the four imports.)

## Blueprint ids -> Lean names, with assumption binders (A1 = HasSemialgebraicProjections, A2 = HasFinitenessTheorem, A3 = HasGrowthBound)
| id | Lean | binders |
|---|---|---|
| t215.supset | `thm215_supset` | A1, A2, A3 |
| t215.supset (class form) | `thm215_mem_P_bounded` | A1, A2, A3 |
| t215.eq | `thm215_eq` | A1, A2, A3 |
| helpers | `mem_boundedBox_of_sum_sq_le`, `bdd_sum_sq_of_bdd_compact`, `eq_coeFun_toReal_of_mem_CB`, `exists_real_of_mem_SA_LSC_CB` | none |
| t220.supset | `thm220_supset` | A2 only |
| t220.main | `thm220_main` | A1, A2 |
| t221.hull_sa | `thm221_hull_sa` (+ helper `Msp_eq_eval`, no binders) | A1 |
| t221.compact_sa_incl | `thm221_compact_sa_incl`, `thm221_compact_sa_incl_pess` | A1 |
| t221.supset | `thm221_supset` | A1, A2, A3 |
| t221.eq | `thm221_eq` | A1, A2, A3 |
| pess.target_neg (PP) | `neg_mem_PP`, `neg_mem_PP_iff`, `coeFun_neg`, `neg_mem_SA_LSC_CB` | none |
| pess.t11 | `pess_thm11` | none |
| pess.berge | `pess_cor29` | none |
| pess.t212 | `pess_thm212` | A1 |
| pess.t218 | `pess_thm218` | A1 |
| pess.t215 | `pess_thm215` | A1, A2, A3 |
| pess.t220 | `pess_thm220` | A1, A2 |
| pess.t221 | `pess_thm221` | A1, A2, A3 |
(`pess.class_neg` and the rest of `pess.target_neg` are the existing `mem_Pp_*_iff`, `mem_Cp_*_iff`, `neg_mem_*_iff` of
Framework/Classes.lean, cited in the Pessimistic.lean docstring, not restated.)

## Proof routes
As the blueprint/assignment: thm215_supset = A3 (`HasGrowthBound.growth'`, with the ball hypothesis from `hcb` via the
containment `{∑ x_i² ≤ r} ⊆ [-(|r|+1), |r|+1]^n`), `wq := C (|B|+1) + (1 + ∑ X i^2)^M`, epigraph closed
(`isClosed_epigraph_sum`) and semialgebraic (`isSemialgebraic_epigraph`, A1), A2 presentation, `thm215_of_presentation`.
thm220_supset: per piece A2 on `{f ≤ p_i}` (`t220_D_sa`, `t220_D_closed`), `choose`, `t220_mem_C_bounded_of_presentations`.
thm221: `isPolyFun_iff_exists_polyFun`, `S := pP.support ∪ pQ.support` (generic ι, `le_rfl` works for the support hypothesis),
`t221_linearize_value`/`_pvalue`, `t221_cc_data_*`, `isCompact_convexHull_Msp`, `thm221_hull_sa`. Pessimistic: negation throughout.

## Deviations
- `thm215_supset` takes `IsSemialgebraicMap f` (definitionally `IsSemialgebraic (graphSet f)`, the blueprint's form), as the
  assignment specifies. No other deviations; no extra hypotheses.

## Mathlib names differing from blueprint: none relevant (`EReal.coe_toReal`, `EReal.coe_neg`, `Finset.single_le_sum`, `map_prod`).

## Not done: nothing.

## Checks
- `lake build HardnessBilevel.Bounded.Thm215 HardnessBilevel.Convex.Thm220 HardnessBilevel.Convex.Thm221 HardnessBilevel.Pessimistic`
  -> Build completed successfully; then `lake build HardnessBilevel.Pessimistic` after a docstring edit -> success.
- `#print axioms` of all 26 declarations (scratch file .../scratchpad/lean/ax_w4asm.lean): all [propext, Classical.choice, Quot.sound].
- grep: no `sorry`, no `axiom`, no `instance` declaration in the four files.
