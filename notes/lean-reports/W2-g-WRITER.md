# W2-g WRITER report

Files delivered: /home/user/HardnessBilevelProgramming/HardnessBilevel/Gadgets/Box.lean (namespace Bilevel, imports HardnessBilevel.Framework.Poly).

## Blueprint ids implemented
* gad.G6: `gadgetGe` (def); (a) `gadgetGe_nonneg`; (b) `gadgetGe_eq_zero_iff`; (c) `exists_gadgetGe_eq_zero_iff`;
  witness `gadgetGe_witness p := p/(p^2+1)` with `gadgetGe_witness_mem` (0 ≤ p) and `gadgetGe_witness_eq_zero`;
  extras `nonneg_of_gadgetGe_eq_zero` (0 ≤ z → G p z = 0 → 0 ≤ p), `gadgetGe_pos_of_neg` (p < 0 → 0 ≤ z → 0 < G p z).
* gad.G7: box `gadgetBox α β` (+ simp lemma `mem_gadgetBox`), `unionGadget` (def); (a) `unionGadget_nonneg`;
  (b) `unionGadget_eq_zero_iff`; (c) (★★) `exists_unionGadget_eq_zero_iff`; (d) `isPolyFun_gadgetGe`,
  `isPolyFun_unionGadget` (general), `isPolyFun_unionGadget_sum` (Thm 2.15 form, lower index `Unit ⊕ (α × β)`).

## Deviations
* Generalised `Fin a × Fin b` to arbitrary `[Fintype α] [Fintype β]` (any universes) and parameter type `U` (strengthening).
* Box is a named noncomputable def `gadgetBox α β`, definitionally the blueprint's `Set.pi Set.univ (fun _ => Icc 0 (1/2))`.
* Polynomiality formulations: `isPolyFun_unionGadget` takes `P : α → β → (Fin n → ℝ) → (ι → ℝ) → ℝ` and box-coordinate
  functions `Zc : α × β → (Fin n → ℝ) → (ι → ℝ) → ℝ`, all IsPolyFun, and concludes IsPolyFun of
  `fun x y => unionGadget (fun i j (u : (Fin n → ℝ) × (ι → ℝ)) => P i j u.1 u.2) (x, y) (fun ij => Zc ij x y)`.
  `isPolyFun_unionGadget_sum` specialises to `U = (Fin n → ℝ) × ℝ`, `t = y (Sum.inl ())`, `z ij = y (Sum.inr ij)`,
  with hypotheses `IsPolyFun (fun x (t : Unit → ℝ) => p i j x (t ()))` (proved via `IsPolyFun.rename`).

## Mathlib names
`if_true` deprecated → `ite_true`. Others as in the blueprint (`sq_eq_zero_iff`, `mul_div_cancel₀`, `div_le_iff₀`,
`Finset.prod_eq_zero_iff`, `Finset.sum_eq_zero_iff_of_nonneg`, `Finset.prod_nonneg`).

## Not done
Nothing.

## Last build
`lake build HardnessBilevel.Gadgets.Box` → "Build completed successfully" (no warnings in Box.lean). `#print axioms` of all
public declarations checked in a scratch file: only propext, Classical.choice, Quot.sound.
