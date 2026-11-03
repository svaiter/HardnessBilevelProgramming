# W1-a WRITER report (framework core)

## Files delivered
- HardnessBilevel/Framework/Basic.lean (imports Mathlib)
- HardnessBilevel/Framework/Value.lean (imports Basic)
- HardnessBilevel/Framework/Separable.lean (imports Basic)
Full API with signatures: reports/W1-a-API.md (47 declarations).

## Blueprint ids -> Lean names (all in namespace Bilevel)
- defs §4.A.1: argminSet, valueFun (⨅ y ∈ argminSet Q S x, ((P x y : ℝ) : EReal)), pvalueFun (⨆), optVal (⨅ x, valueFun) — verbatim.
- F1 mem_argminSet_iff; F2 argminSet_subset; mem_argminSet_univ (@[simp]); F3 argminSet_eq_empty_iff;
  F4 argminSet_eq_zeroSet; F4′ mem_argminSet_of_nonneg_zero; F6 argminSet_mul_pos, argminSet_add_left;
  F8 argminSet_isClosed, argminSet_isCompact (only [TopologicalSpace Y]; no T2 needed); helper argminSet_eq_inter.
- fw.argmin_empty_of_pos_inf (§4.E.1 A2): argminSet_empty_of_pos_inf (general S) + corollary argminSet_univ_empty_of_pos_inf.
- V1 valueFun_eq_top_iff / pvalueFun_eq_bot_iff; V2 valueFun_eq_of_isMinOn / pvalueFun_eq_of_isMaxOn;
  F0 valueFun_eq_of_isLeast / pvalueFun_eq_of_isGreatest; V5 valueFun_eq_of_const / pvalueFun_eq_of_const;
  V5′ valueFun_unique (conjunction of both values).
- A5 fw.value_eq_bot_of_unbounded: valueFun_eq_bot_of_unbounded (general S), twin pvalueFun_eq_top_of_unbounded
  (hyp `∀ r, ∃ y ∈ Θ, r ≤ P x y`).
- helpers: valueFun_le_coe_of_mem, coe_le_pvalueFun_of_mem, coe_le_valueFun_of_forall, pvalueFun_le_coe_of_forall.
- fw.value_shift_attained (§4.G.1): value_shift_attained.
- V3 valueFun_eq_coe_iff, twin pvalueFun_eq_coe_iff (`(∀ y ∈ Θ, P x y ≤ r) ∧ ∀ ε > 0, ∃ y ∈ Θ, r - ε < P x y`).
- V4 valueFun_eq_bot_iff, twin pvalueFun_eq_top_iff (`∀ r, ∃ y ∈ Θ, r < P x y`) — named without a prime (no clash).
- V8 pvalueFun_eq_neg_valueFun_neg (pointwise, as in the brief) and symmetric valueFun_eq_neg_pvalueFun_neg.
- V9 (optional) valueFun_real_iff.
- F5 argminSet_prod_add; F7 argminSet_comp_equiv, valueFun_comp_equiv, pvalueFun_comp_equiv (function equalities, e : Y' ≃ Y).
- fw.argmin_pi_sum: argminSet_pi_sum (argminSet form, objective `∑ i, g x i (y i)` may depend on x) and
  pi_sum_min_eq (literal blueprint set equation, derived from it with X := Unit).
- convenience argminSet_sum_elim (y : α ⊕ β → Z, via Equiv.sumArrowEquivProdArrow + F5 + F7).

## Deviations
- None in statements. Additions only (helpers, the univ corollary, the literal pi form, argminSet_sum_elim).
- F8 needs no T2Space (closedness/compactness of the intersection only uses continuity of Q x and closedness of sublevel sets).
- Not implemented: V6/V7 (optional, blueprint says no consumer); fw.pvalue_class_neg (later wave, needs classes).

## Mathlib names differing from blueprint
- `biInf_lt_iff` does not exist at this commit; V3/V4 proved by hand (le_iInf₂/iInf₂_le + by_contra).
- `push_neg` is deprecated here; used `push Not`.
- V8 proved by hand with EReal.le_neg / EReal.neg_le / EReal.neg_le_neg_iff / EReal.coe_neg (no negOrderIso needed).
- valueFun_comp_equiv: `simp only [valueFun]` then `rw [argminSet_comp_equiv, ← Equiv.image_symm_eq_preimage]`, `Equiv.biInf_comp` (exists).

## Checks
- No sorry/axiom/native_decide; #print axioms of all 47 declarations = [propext, Classical.choice, Quot.sound].
- Last command: `lake build HardnessBilevel.Framework.Basic HardnessBilevel.Framework.Value HardnessBilevel.Framework.Separable`
  -> "Build completed successfully (18245 jobs)." Only warning: Mathlib's generic "consider adding `module`" notice for `import Mathlib`.
- Nothing committed.
