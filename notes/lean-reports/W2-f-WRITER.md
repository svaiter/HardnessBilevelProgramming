# W2-f WRITER report (convex lower-level toolkit, Lemma 2.19, Thm 2.18 construction)

## Files delivered
* /home/user/HardnessBilevelProgramming/HardnessBilevel/Convex/Toolkit.lean
* /home/user/HardnessBilevelProgramming/HardnessBilevel/Convex/Lemma219.lean
* /home/user/HardnessBilevelProgramming/HardnessBilevel/Convex/Thm218.lean
(API: reports/W2-f-API.md.) No sorry/axiom/native_decide; no warnings; `#print axioms` of all 41 public theorems =
[propext, Classical.choice, Quot.sound].

## Blueprint ids -> Lean names
* §2.3 `ConvexLower` -> `Bilevel.ConvexLower` (defined in Toolkit.lean; exactly `∀ x, ConvexOn ℝ Set.univ (fun y => Q x y)`).
* `fw.argmin_scalar` (i) -> `argmin_scalar_univ` (full set equality) + consequences `mul_eq_of_isMin_univ`
  (`c*t = if c = 0 then 0 else 1`), `isMin_univ_witness`;
  (ii) -> `argmin_scalar_Ici` (full set equality) + `mul_eq_of_isMin_Ici` (`c*u = if 0 < c then 1 else 0`),
  `isMin_Ici_witness`; (iii) -> `isMin_one_Icc_iff` (1 minimises `-c z` on `Icc 0 1` iff `0 ≤ c`), `eq_zero_of_isMin_Icc`.
* `fw.convex_toolkit` -> `convexOn_sq_affine` (route B, nlinarith), `convexOn_finset_sum` (Finset induction),
  `convexOn_linear_coord`, `convexOn_sq_one_sub_mul_coord`, `ConvexLower.add`, `ConvexLower.finset_sum`,
  `convexLower_const`, `ConvexLower.comp_reindex` (restriction to a block), `ConvexLower.convexOn` (restriction to a
  convex `Y` via `ConvexOn.subset`). Box convexity: already in Framework/Box (`IsUnboundedBox.convex`, `IsBox.convex`),
  not restated. Extra: `isUnboundedBox_pi_univ_or_Ici` (pi of intervals each `univ`/`Ici 0`, one `univ`).
* `fw.value_shift_attained` -> already `Bilevel.value_shift_attained` (W1-a); `fw.const_on_argmin` ->
  `valueFun_eq_of_const`/`pvalueFun_eq_of_const` (W1-a). Not restated.
* `t219.main` -> `lemma219` (for the concrete `gadP P Q`, `gadQ P Q`, `gadY J`, `basicSet P Q`: IsPolyFun P', IsPolyFun Q',
  ConvexLower Q', IsUnboundedBox Y, ∀ x nonempty argmin ∧ P' = 1_S x on the argmin, valueFun = pvalueFun = ↑(1_S x));
  `lemma219_exists` (existential form, `ι : Type`). Pieces: `mem_argminSet_gadQ_iff`, `gadMin`, `gadMin_mem`,
  `argminSet_gadQ_nonempty`, `gadP_eq_indicator`, `isPolyFun_gadQ/P`, `convexLower_gadQ`, `isUnboundedBox_gadY`.
* `t218.sum_indicator` -> `sum_indicator` (basic sets as data `PT i j`, `QT i j : Fin (K i j) → _`, hypothesis
  `S i = ⋃ j, basicSet (PT i j) (QT i j)`), `sum_indicator_basic` (hyp. `∀ i, ∃ m T, (∀ j, IsBasicSA (T j)) ∧ S i = ⋃ j, T j`),
  `sum_indicator_semialgebraic` (hyp. `∀ i, IsSemialgebraic (S i)`, via `isSemialgebraic_iff_finite_union_basic`).
  Conclusion as specified: `∃ (ι : Type) (_ : Fintype ι) P Q Y, IsPolyFun P ∧ IsPolyFun Q ∧ ConvexLower Q ∧
  IsUnboundedBox Y ∧ (∀ x, nonempty argmin ∧ ∀ y ∈ argmin, P x y = ∑ i, (S i).indicator 1 x * eval x (p i)) ∧
  valueFun P Q Y = fun x => ↑(…) ∧ pvalueFun P Q Y = fun x => ↑(…)`.
  Construction: `t218Idx J K = Unit ⊕ Σ (b : Σ i, Fin (J i)), (Unit ⊕ Fin (K b.1 b.2))`, block projection `t218Blk`,
  `t218Q`, `t218P`, `t218Y`; helpers `mem_argminSet_comp_inr_iff` (dummy coordinates), `mem_argminSet_sigma_iff`
  (block-separable argmin over a Sigma type, from `argminSet_pi_sum` + `argminSet_comp_equiv` along `Equiv.piCurry`),
  `one_sub_prod_one_sub_indicator` (`1 − ∏ (1 − 1_{T j}) = 1_{⋃ T j}`), `mem_argminSet_t218Q_iff`,
  `argminSet_t218Q_nonempty`, `t218P_eq_on_argmin`, `isPolyFun_t218Q/P`, `convexLower_t218Q`, `isUnboundedBox_t218Y`.

## Deviations
* None in statements. The Lemma 2.19 gadget is the blueprint's simplified one (§4.G.2), with `Q'` written as
  `(1 - y (inl ()) * eval x P)^2 + ∑ j, (1 - eval x (Q j) * y (inr j))^2` exactly as in the assignment.
* The scalar lemmas are stated with `c * t` (not `t * c`); the gadget uses `mul_comm` where needed.
* No flattening of the Sigma index type (ι is existential, so `t218Idx` is used directly; it lives in `Type`).
* `PP ⊆ C_unbound` / `t218.main` not done (Wave 3, as instructed).

## Mathlib names differing from the blueprint
* `Unit.forall` does not exist (handled by hand). `if_pos`/`if_neg` are deprecated in this Mathlib (avoided).
* `ConvexOn.comp_linearMap` with `LinearMap.funLeft` produced an SMul-instance mismatch (`Function.hasSMul` vs Pi smul);
  `ConvexLower.comp_reindex` is proved directly from the definition of `ConvexOn` instead.

## Last build
`lake build HardnessBilevel.Convex.Thm218` -> "Build completed successfully (18257 jobs)." (also built
`HardnessBilevel.Convex.Toolkit` and `HardnessBilevel.Convex.Lemma219`, both successful; `lake env lean` on each of the
three files: no output).
