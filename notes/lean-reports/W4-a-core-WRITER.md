# W4-a-core WRITER report

File delivered: /home/user/HardnessBilevelProgramming/HardnessBilevel/Bounded/Thm215Core.lean (namespace Bilevel).
Imports: Framework.Basic, Framework.Box, Framework.Poly, Gadgets.Box. No assumption classes, no sorry/axiom/instance.

## Blueprint ids implemented
* t215.core -> `t215_core` (statement exactly as §4.F.2), attained form `t215_core_isLeast`.
  Generic engine: `t215_core_gen` (IsLeast form) / `t215_core_gen_value` over an arbitrary lower type Θ with a
  t-coordinate `T : Θ → ℝ`; proof: t₀ = f x / w x ∈ [-1,1], zero at θ₀, `argminSet_eq_zeroSet`, `valueFun_eq_of_isLeast`.
* transport to `Unit ⊕ ζ` -> `sumBox`, `t215_core_sum`; box identification `sumBox_gadgetBox :
  sumBox (gadgetBox α β) = boundedBox t215Lo t215Hi`, `t215Lo_le_t215Hi`.
* t215.epi_closed -> `isClosed_epigraph_sum` (via `LowerSemicontinuous.isClosed_epigraph` + preimage under
  the continuous map z ↦ (z ∘ inl, z (inr ()))).
* step 5 rescaling -> `rescaledPoly`, `isPolyFun_rescaledPoly` (via `IsPolyFun.comp`), `exists_rescaledPoly_iff` (Iff.rfl).
* steps 6–7 packaging -> `thm215_of_presentation` (statement as in the assignment; ι = Unit ⊕ (α × β),
  P x y = y (inl ()) * eval x wq, Q = unionGadget of rescaled polys, box boundedBox t215Lo t215Hi).

## Deviations
* `t215_core_sum` proved directly from the generic lemma instead of via `valueFun_comp_equiv` (same statement).
* `thm215_of_presentation`: row/column index types are arbitrary `α β : Type` with `[Fintype]` (strengthening of Fin a, Fin b);
  the weight is given as `wq : MvPolynomial (Fin n) ℝ` with hypotheses on `eval x wq`.
* Not done (by assignment): epi_sa, supset, subset, eq.

## Mathlib names
`LowerSemicontinuous.isClosed_epigraph` (as in blueprint), `le_div_iff₀`, `div_le_iff₀`, `div_mul_cancel₀`. No differences.

## Last build
`lake build HardnessBilevel.Bounded.Thm215Core` -> Build completed successfully. `#print axioms` of all 12 declarations
= [propext, Classical.choice, Quot.sound].
