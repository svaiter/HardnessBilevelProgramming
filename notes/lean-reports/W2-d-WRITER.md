# W2-d WRITER report

File delivered: /home/user/HardnessBilevelProgramming/HardnessBilevel/Semialgebraic/Basic.lean (399 lines, imports only Mathlib,
`namespace Bilevel`, `open MeasureTheory Function`). Full signatures: reports/W2-d-API.md.

## Blueprint ids -> Lean names
* Defs (§2.4/§4.B.1): `IsSemialgebraic` (exact blueprint body), `IsBasicSA`, `graphSet`, `IsSemialgebraicMap`; extra `mem_graphSet` (simp, Iff.rfl).
* sa.gen: `isSemialgebraic_eval_eq_zero`, `isSemialgebraic_eval_pos`.
* sa.bool: `isSemialgebraic_empty`, `isSemialgebraic_univ`, `IsSemialgebraic.compl/union/inter/sdiff`, `isSemialgebraic_compl_iff`,
  `isSemialgebraic_biUnion`, `isSemialgebraic_biInter` (Finset), `isSemialgebraic_iUnion`, `isSemialgebraic_iInter` ([Finite κ]),
  `isSemialgebraic_setOf_and/or/not/forall/exists`, `IsSemialgebraic.of_eq`.
* sa.sign_sets: `isSemialgebraic_eval_ne_zero`, `_eval_neg` (p<0), `_eval_nonneg` (0≤p), `_eval_nonpos` (p≤0), `_eval_lt` (p<q),
  `_eval_le` (p≤q), `_eval_eq` (p=q), `_eval_ne` (p≠q), `isSemialgebraic_sign_eval_eq p σ` ({sign (eval x p) = σ}).
* sa.sign_normal_form: `isSemialgebraic_iff_sign_normal_form` (iff, exact blueprint statement); directions
  `IsSemialgebraic.exists_sign_normal_form` (generateSetAlgebra_induction, union via Fin.append) and `isSemialgebraic_setOf_sign`.
* sa.cell_basic: `signCell p σ := {x | ∀ i, sign (eval x (p i)) = σ i}`, `cellP` (= ∑ i, if σ i = 0 then p i ^ 2 else 0),
  `cellQ` (= if σ i = 1 then p i else if σ i = -1 then -p i else 1), `signCell_eq_basic`, `isBasicSA_signCell`,
  `disjoint_signCell` (σ ≠ τ), `iUnion_signCell` (= univ), `setOf_sign_eq_iUnion_signCell`, `isSemialgebraic_signCell`.
* sa.finite_union_basic: `isSemialgebraic_iff_finite_union_basic`, `isBasicSA_isSemialgebraic`, `isSemialgebraic_basic P Q`.
* sa.finite_union_basic_uniform: `IsSemialgebraic.exists_uniform_basic` (exact requested shape) and iff `isSemialgebraic_iff_uniform_union_basic`.
  No padding needed: m = number of sign vectors satisfying Φ, k = number of polynomials (all cells share k).
* sa.disjoint_basic (Prop C.1): `isSemialgebraic_iff_disjoint_union_basic` (∃ m S, (∀ i, IsBasicSA (S i)) ∧ Pairwise (Disjoint on S) ∧ s = ⋃ i, S i),
  uniform+disjoint: `IsSemialgebraic.exists_disjoint_uniform_basic`, `isSemialgebraic_iff_disjoint_uniform_union_basic`.

## Deviations
None in statements. Strengthening: finite iUnion/iInter take `[Finite κ]` (weaker than `[Fintype κ]`).
Auxiliary public declarations added: `signCell`, `cellP`, `cellQ`, `mem_graphSet`, `isSemialgebraic_basic`, `isSemialgebraic_compl_iff`.
Not done (by instruction): coordinate-permutation preimage (needs polynomial preimages, Wave 3).

## Mathlib names
All as in the blueprint. `sign_eq_one_iff`/`sign_eq_neg_one_iff`/`sign_eq_zero_iff` are in Mathlib/Basic/Sign/Defs.lean (root namespace);
`Finset.sum_eq_zero_iff_of_nonneg`, `Fin.append_left/right`, `Fintype.equivFin`, `Function.Surjective.iUnion_comp` used.
The `on` notation needs `open Function`.

## Checks
`#print axioms` of all 53 declarations: [propext, Classical.choice, Quot.sound] only. No sorry/native_decide/Set.mem_setOf_eq.
Last command: `lake build HardnessBilevel.Semialgebraic.Basic` -> "Build completed successfully" (only the generic
"consider adding `module`" warning that every Mathlib-importing file gets).
