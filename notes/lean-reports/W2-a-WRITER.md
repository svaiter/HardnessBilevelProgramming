# W2-a WRITER report (Theorem 1.1)

## Files delivered
- /home/user/HardnessBilevelProgramming/HardnessBilevel/Smooth/Whitney.lean (imports Mathlib)
- /home/user/HardnessBilevelProgramming/HardnessBilevel/Smooth/Thm11.lean (imports Smooth.Whitney, Framework.Basic, Framework.Value, Framework.Semicont)

## Blueprint ids -> Lean names (namespace Bilevel)
- t11.whitney -> `exists_contDiff_zeroSet_eq`
- t11.isClosed_realEpigraph -> already provided as `isClosed_realEpigraph` (Framework/Semicont.lean, W1-d); reused, not duplicated
- t11.T0 (construction) -> `thm11P` (P x y = y 0), `thm11Q h g` (Q x y = h (x, y 0)^2 + (g x * y 1)^2 + (1 - y 1 * y 2)^2)
- t11.smooth -> `contDiff_thm11P`, `contDiff_thm11Q` (both by `fun_prop`)
- t11.nonneg -> `thm11Q_nonneg`
- t11.case_finite -> `argminSet_thm11Q_of_ne_top` (argmin = Z), `valueFun_thm11_of_ne_top`
- t11.case_top -> `argminSet_thm11Q_of_eq_top`, `valueFun_thm11_of_eq_top`
- t11.main -> `exists_smooth_of_lowerSemicontinuous` (statement exactly as in the blueprint)
- t11.main_paper -> `exists_smooth_of_lowerSemicontinuous_proper`
- t11.main_pess -> `exists_smooth_of_upperSemicontinuous`

## Deviations
None in statements. The case lemmas take the Whitney properties as hypotheses
`hh : ∀ p, h p = 0 ↔ f p.1 ≤ ↑p.2`, `hg : ∀ x, g x = 0 ↔ f x ≠ ⊤` (abstracting over h, g); the main theorem
instantiates them from `exists_contDiff_zeroSet_eq`. `Function.support_eq_iff` was not needed (used
`congrArg (p ∈ ·)` on the support equation + simp + tauto). `(n := (⊤ : ℕ∞))` coerces to `∞` definitionally, as expected.

## Mathlib names
All as in the blueprint; none differed (`IsOpen.exists_contDiff_support_eq`, `add_eq_zero_iff_of_nonneg`,
`sq_eq_zero_iff`, `EReal.le_coe_toReal`, `EReal.eq_bot_iff_forall_lt`, `iInf₂_le`, `le_iInf₂`, `mul_one_div_cancel`,
`le_div_iff₀`, `EReal.neg_eq_top_iff`, `ContDiff.neg`). Project lemmas used: `argminSet_eq_zeroSet`,
`argminSet_eq_empty_iff`, `valueFun_eq_top_iff`, `pvalueFun_eq_neg_valueFun_neg`,
`upperSemicontinuous_iff_lowerSemicontinuous_neg`, `isClosed_realEpigraph`.

## Not done
Nothing. (Optional remark (b), Smith–Volterra–Cantor example, is not a target.)

## Last build
`lake build HardnessBilevel.Smooth.Thm11` -> "Build completed successfully" (only the generic "consider adding
`module`" warning that every Mathlib-importing file gets). No sorry/axiom/native_decide; #print axioms lines removed
from the delivered files.
