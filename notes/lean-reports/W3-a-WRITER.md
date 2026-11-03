# W3-a WRITER report

## Files delivered
* /home/user/HardnessBilevelProgramming/HardnessBilevel/Semialgebraic/Poly.lean (imports Semialgebraic.Basic, Framework.Poly, Framework.Box)
* /home/user/HardnessBilevelProgramming/HardnessBilevel/Semialgebraic/Ext.lean (imports Semialgebraic.Poly)
* API: reports/W3-a-API.md

## Blueprint ids -> Lean names (namespace Bilevel)
* sa.preimage_poly (L4): `IsSemialgebraic.preimage_poly`; pointwise form `IsSemialgebraic.preimage_of_poly` (φ with `∀ x i, φ x i = eval x (F i)`)
* sa.reindex: `IsSemialgebraic.reindex` (any `e : ι → κ`), `IsSemialgebraic.preimage_equiv`, `IsSemialgebraic.image_equiv` (`(· ∘ e.symm) '' S`), `IsSemialgebraic.image_comp_equiv` (`(· ∘ e) '' S`, `e : κ ≃ ι`), `isSemialgebraic_reindex_equiv_iff`
* sa.cylinder: `isSemialgebraic_cylinder_inl`, `isSemialgebraic_cylinder_inr`, `isSemialgebraic_cylinder` (two-sided)
* sa.poly_graph: `isSemialgebraic_poly_graph [Finite κ]`, `isSemialgebraicMap_eval`
* sa.box: `isSemialgebraic_boxSet [Finite ι]`, `isSemialgebraic_boundedBox`, `IsBox.isSemialgebraic`, `IsBoundedBox.isSemialgebraic`, `IsUnboundedBox.isSemialgebraic`; helpers `isSemialgebraic_ereal_le_coord`, `isSemialgebraic_coord_le_ereal`, `isSemialgebraic_const_le_coord`, `isSemialgebraic_coord_le_const`, `isSemialgebraic_coord_eq_const`
* sa.singleton / sa.finite_set: `isSemialgebraic_singleton`, `isSemialgebraic_of_finite` (from `s.Finite`)
* sa.sup_ball: `isSemialgebraic_sup_ball` (open), `isSemialgebraic_sup_closedBall`
* sa.euclid_ball: `isSemialgebraic_euclid_ball` (`∑ x i^2 ≤ ρ`), `isSemialgebraic_euclid_ball_lt`
* sa.poly_bound (L17): `exists_abs_eval_le` (alias `poly_bound`), with `0 ≤ c` variant `exists_abs_eval_le'`; helpers `one_le_one_add_sum_sq`, `abs_le_one_add_sum_sq`
* sa.growth_shape: `growth_shape_iff` (alias `growth_shape`), directions `growth_shape_mul_to_add`, `growth_shape_add_to_mul`
* Def 2.2: `structure IsExtSemialgebraic` with exactly the fields `top`, `bot`, `graph`
* sa.ext_dom: `IsExtSemialgebraic.dom`
* sa.ext_coe: `isExtSemialgebraic_coe_iff`, `IsSemialgebraicMap.isExtSemialgebraic`
* sa.ext_neg: `IsExtSemialgebraic.neg` (polynomial preimage of the graph; no A1), `isExtSemialgebraic_neg_iff`
* `IsExtSemialgebraic.const`
* sa.ext_graph_equiv (optional, done): `extGraph`, `isExtSemialgebraic_iff_extGraph`

## Deviations
* Finite intersections over an index type need finiteness of that index (an element of the generated algebra
  depends on finitely many coordinates): `isSemialgebraic_poly_graph`, `isSemialgebraic_singleton`,
  `isSemialgebraic_of_finite`, boxes, sup-balls take `[Finite _]` (weaker than `[Fintype _]`); the brief's
  `isSemialgebraic_boxSet [Fintype ι]` is thus strengthened. Euclidean ball / growth lemmas use `[Fintype ι]`.
* `Set.Finite.isSemialgebraic` renamed `isSemialgebraic_of_finite`: inside `namespace Bilevel` the name would be
  `Bilevel.Set.Finite.isSemialgebraic`, and dot notation on `hs : s.Finite` does not find it.
* `sa.growth_shape` proved as an `Iff` (both implications also provided separately).

## Mathlib names
All as in the blueprint; used the project lemma `eval_bind₁'` (Framework.Poly) for the bind₁ step;
`MvPolynomial.induction_on` (C / add / mul_X); `pow_unbounded_of_one_lt`, `pow_le_pow_right₀`, `pow_le_pow_left₀`,
`one_le_pow₀`; `EReal.rec`, `EReal.neg_eq_top_iff`, `EReal.neg_eq_bot_iff`, `EReal.coe_neg`, `neg_eq_iff_eq_neg`.

## Not done
Nothing from the assignment is missing.

## Last build
`lake build HardnessBilevel.Semialgebraic.Poly HardnessBilevel.Semialgebraic.Ext` -> Build completed successfully.
`#print axioms` on all 46 public declarations: [propext, Classical.choice, Quot.sound] (or a subset). No sorry.
