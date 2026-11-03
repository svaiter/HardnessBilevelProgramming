# W3-d WRITER report

## Files delivered
* HardnessBilevel/Semialgebraic/Value.lean (imports Framework.Classes, Semialgebraic.Projection, Semialgebraic.Ext)
* HardnessBilevel/Semialgebraic/Hull.lean (imports Semialgebraic.Projection)

## Blueprint ids implemented
* sa.value_semialgebraic (Prop 2.6, any semialgebraic Y): `valueFun_isExtSemialgebraic` (exact blueprint signature),
  `pvalueFun_isExtSemialgebraic`. Helpers: `IsPolyFun.exists_eval_pick`, `IsSemialgebraic.pick` (pullback along
  `w ↦ Sum.elim (w ∘ a) (w ∘ b)`), `argminGraph`, `sumElim_mem_argminGraph_iff`, `isSemialgebraic_argminGraph`.
  Route exactly as §4.B.6 (Θ via cylinder + polynomial inequality + `forall_sumElim`; ⊤ via `forall_sumElim` of Θᶜ;
  ⊥ via `exists_sumElim` then `forall_real`; graph via `forall_sumElim` (part A) and `exists_sumElim` + `forall_pos` (part B)).
  No attainment used.
* sa.class_sub_SA: `P_unbound_subset_SA`, `P_bounded_subset_SA`, `P_box_subset_SA`, `C_unbound_subset_SA`
  (= t218.Cunbound_sub_SA), `C_bounded_subset_SA`, `C_cc_subset_SA`, and `Pp_unbound/Pp_bounded/Pp_box/Cp_unbound/
  Cp_bounded/Cp_cc_subset_SA`.
* t212.eq_SA: `thm212_eq_SA : P_unbound n = SA n`, `thm212_eq_SA_pess : Pp_unbound n = SA n`.
* t218.main: `thm218_main : PPe n ⊆ C_unbound n ∧ C_unbound n ⊆ SA n`, `thm218_main_pess` (Cp_unbound).
* ⊆ halves: `thm215_subset`, `thm220_subset`, `thm221_subset` (⊆ SA ∩ LSC ∩ CB), and `_pess` twins (⊆ SA ∩ USC ∩ CB).
* sa.hull_semialgebraic: `isSemialgebraic_convexHull_image [HasSemialgebraicProjections] [Fintype m] [Fintype K]
  (hY : IsSemialgebraic Y) (F : K → MvPolynomial m ℝ) : IsSemialgebraic (convexHull ℝ ((fun y k => eval y (F k)) '' Y))`.
  Helpers: `hullSlice`, `hullSlice_subset_convexHull`, `convexHull_subset_iUnion_hullSlice`,
  `convexHull_eq_iUnion_hullSlice` (hull = ⋃ N : Fin (card K + 2), hullSlice Y F N), `isSemialgebraic_hullSlice`.

## Deviations
* Strengthening: hull lemma over arbitrary finite index types `m`, `K` (blueprint: `Fin m`, `Fin K`).
* Route variant (explicitly allowed by the assignment): finite union over N ≤ card K + 1 instead of padding to exactly
  card K + 1 points. Existential block type `Fin N ⊕ (Fin N × m)` as in the blueprint.
* Graph clause written as `∀ ε, 0 < ε → ∃ y, ...` (via `forall_pos`), equivalent to the blueprint's `ε ≤ 0 ∨ ...`.
* Not done: a `Msp`-specialised version of the hull lemma (Msp lives in Convex/Linearize, which Hull.lean is not
  allowed/needed to import); the consumer applies the general F form (Msp S y d = eval y of a monomial).

## Mathlib names
All as in the blueprint: `eq_pos_convex_span_of_mem_convexHull`, `AffineIndependent.card_le_finrank_succ`,
`Module.finrank_fintype_fun_eq_card`, plus `Submodule.finrank_le`, `Convex.sum_mem`, `Equiv.sum_comp`,
`MvPolynomial.eval_rename`, `Set.eq_empty_iff_forall_notMem`.

## Last build commands
`lake build HardnessBilevel.Semialgebraic.Value` — Build completed successfully.
`lake build HardnessBilevel.Semialgebraic.Hull` — Build completed successfully.
Both files: no warnings under `lake env lean`; #print axioms of all 35 theorems = [propext, Classical.choice, Quot.sound].
