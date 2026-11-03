# W4-c WRITER report

## Files delivered
* /home/user/HardnessBilevelProgramming/HardnessBilevel/Convex/Linearize.lean
* /home/user/HardnessBilevelProgramming/HardnessBilevel/Convex/Hull.lean
(Not added to the root HardnessBilevel.lean — orchestrator's job.)

## Blueprint ids implemented (Lean names, namespace Bilevel)
* definitions: `Msp`, `cPoly`, `plin` (+ helper `plinLin` linear map, `plinLin_apply`)
* `t221.splitting` — `t221_splitting`
* `t221.linearize` — `t221_linearize_value` (optimistic), `t221_linearize_pvalue` (pessimistic), `t221_linearize` (both,
  as a conjunction of ∀ x statements); proof claims `t221_claim1` (Msp '' A ⊆ A'), `t221_claim2` (A' ⊆ conv(Msp '' A),
  via positive weights)
* `t221.cc_data` (a) `t221_cc_data_isPolyFun` (for any p, so covers P' and Q'), (b) `t221_cc_data_convexLower`,
  (c) `t221_cc_data_convex`, (f) `t221_cc_data_nonempty`; bundle `t221_cc_data`; (d) is `isCompact_convexHull_Msp`
  in Hull.lean
* `t221.caratheodory_union` — `t221_caratheodory_union`
* `t221.weights_compact` — `weights_isClosed`, `weights_isCompact`
* `t221.hull_compact` — `isCompact_convexHull_of_isCompact`, `continuous_hullComb`, `continuous_Msp`,
  `isCompact_convexHull_Msp`

## Deviations
* The inline weight set `W k` is named `hullWeights k` (a def, definitionally the blueprint's set; a top-level `W` in
  namespace Bilevel seemed too clash-prone). The map `(w,z) ↦ ∑ w i • z i` is named `hullComb k`. No stdSimplex used.
* `cPoly` takes `d : ↥S` (S implicit) as the brief's `cPoly p d x` with `d.1`.
* `t221_cc_data_isPolyFun`/`_convexLower` do not need `[Fintype ι]` (omitted: strengthening).
* No statement weakened, no hypothesis added. Linearization hypothesis is `P.support ∪ Q.support ⊆ S`, Y arbitrary.

## Mathlib names differing from the blueprint
* `continuous_finset_sum`/`continuous_finset_prod` are `continuous_finsetSum`/`continuous_finsetProd` at this commit.
* Everything else as given (`eq_pos_convex_span_of_mem_convexHull`, `ConcaveOn.exists_le_of_mem_convexHull`,
  `ConvexOn.exists_ge_of_mem_convexHull`, `LinearMap.concaveOn/convexOn`, `AffineIndependent.card_le_finrank_succ`,
  `Submodule.finrank_le`, `Module.finrank_fintype_fun_eq_card`, `Fintype.equivFin`, `Equiv.sum_comp`,
  `MvPolynomial.eval_eq'`, `Fintype.prod_sum_type`, `Finset.sum_subset`, `MvPolynomial.notMem_support_iff`,
  `convexHull_nonempty_iff`, `Finset.isCompact_biUnion`, `isCompact_univ_pi`, `IsCompact.of_isClosed_subset`).

## Not done (by assignment)
`t221.hull_sa` (needs A1), `t221.subset/supset/eq`, `compact_sa_incl` (W4-d).

## Last build
`lake build HardnessBilevel.Convex.Linearize HardnessBilevel.Convex.Hull` → Build completed successfully (no warnings
from these files). `#print axioms` of every public theorem: [propext, Classical.choice, Quot.sound].
