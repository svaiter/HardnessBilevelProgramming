/-
Copyright: HardnessBilevel project.

# Pessimistic counterparts (paper §2.4; blueprint §4.J)

All pessimistic results are obtained by **one uniform mechanism, negation**. The identity
`pvalueFun P Q S = -valueFun (-P) Q S` (`fw.pvalue_eq_neg_value_neg`) leaves the lower-level data `Q`, `S`
unchanged and keeps `-P` polynomial, so membership in each pessimistic class is membership of `-h` in the
optimistic class (`pess.class_neg`: `mem_Pp_unbound_iff`, `mem_Pp_bounded_iff`, `mem_Cp_bounded_iff`,
`mem_Cp_cc_iff`, … in `HardnessBilevel.Framework.Classes`). The target classes are closed under negation, with
lower and upper semicontinuity exchanged (`pess.target_neg`: `neg_mem_SA_iff`, `neg_mem_CB_iff`,
`neg_mem_LSC_iff_USC`, `neg_mem_USC_iff_LSC`, and `neg_mem_PP` below). Each pessimistic theorem is therefore the
optimistic theorem applied to `-h`.

Ids: `pess.t11` (`pess_thm11`), `pess.berge` (`pess_cor29`), `pess.t212` (`pess_thm212`), `pess.t218`
(`pess_thm218`), `pess.t215` (`pess_thm215`), `pess.t220` (`pess_thm220`), `pess.t221` (`pess_thm221`);
`pess.target_neg` for `PP` (`neg_mem_PP`, `neg_mem_PP_iff`).

Assumptions are inherited from the optimistic statements and taken only as instance-implicit binders; no
instance of any assumption class exists.

Deviations: none.
-/
import HardnessBilevel.Convex.Thm220
import HardnessBilevel.Convex.Thm221
import HardnessBilevel.Smooth.Thm11

open MeasureTheory Function MvPolynomial
open scoped ContDiff

namespace Bilevel

-- No instance of the assumption classes exists (by policy), so they are deliberately local binders.
set_option linter.concreteInstances false

/-- `pess.target_neg` for `PP`: piecewise polynomial functions are closed under negation. -/
theorem neg_mem_PP {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : f ∈ PP n) : (fun x => -f x) ∈ PP n := by
  obtain ⟨N, S, p, hS, hdisj, hcov, hfp⟩ := hf
  refine ⟨N, S, fun i => -p i, hS, hdisj, hcov, fun i x hx => ?_⟩
  rw [hfp i x hx, map_neg]

theorem neg_mem_PP_iff {n : ℕ} {f : (Fin n → ℝ) → ℝ} : (fun x => -f x) ∈ PP n ↔ f ∈ PP n := by
  refine ⟨fun h => ?_, neg_mem_PP⟩
  have := neg_mem_PP h
  simpa only [neg_neg] using this

theorem coeFun_neg {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    coeFun (fun x => -f x) = fun x => -coeFun f x := by
  funext x
  simp only [coeFun, EReal.coe_neg]

/-- `pess.t11` (Theorem 1.1′): an upper semicontinuous `f` with `{f ≠ ⊥}` closed is the pessimistic value
function of a bilevel problem with `C^∞` data and lower set `ℝ³`. -/
theorem pess_thm11 {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : UpperSemicontinuous f) (hdom : IsClosed {x | f x ≠ ⊥}) :
    ∃ P Q : (Fin n → ℝ) → (Fin 3 → ℝ) → ℝ,
      ContDiff ℝ ∞ (Function.uncurry P) ∧ ContDiff ℝ ∞ (Function.uncurry Q) ∧
      pvalueFun P Q Set.univ = f :=
  exists_smooth_of_upperSemicontinuous f hf hdom

/-- `pess.berge` (Cor 2.9′): for continuous data and nonempty compact lower set, the pessimistic value
function is upper semicontinuous, real-valued and bounded on compacts. -/
theorem pess_cor29 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {P Q : X → Y → ℝ} {S : Set Y}
    (hP : Continuous (Function.uncurry P)) (hQ : Continuous (Function.uncurry Q)) (hS : IsCompact S)
    (hne : S.Nonempty) :
    UpperSemicontinuous (pvalueFun P Q S) ∧
      (∀ x, pvalueFun P Q S x ≠ ⊤ ∧ pvalueFun P Q S x ≠ ⊥) ∧
      ∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ x ∈ K,
        (((-M : ℝ)) : EReal) ≤ pvalueFun P Q S x ∧ pvalueFun P Q S x ≤ (M : EReal) :=
  cor29_pess hP hQ hS hne

/-- `pess.t212` (Thm 2.12, pessimistic) `[A1]`: `𝒫^p_unbound = SA`. -/
theorem pess_thm212 [HasSemialgebraicProjections] {n : ℕ} : Pp_unbound n = SA n :=
  thm212_eq_SA_pess

/-- `pess.t218` (Thm 2.18, pessimistic) `[A1]`: `PP ⊆ 𝒞^p_unbound ⊆ SA`. -/
theorem pess_thm218 [HasSemialgebraicProjections] {n : ℕ} :
    PPe n ⊆ Cp_unbound n ∧ Cp_unbound n ⊆ SA n :=
  thm218_main_pess

/-- Negation maps `SA ∩ USC ∩ CB` into `SA ∩ LSC ∩ CB`. -/
theorem neg_mem_SA_LSC_CB {n : ℕ} {h : (Fin n → ℝ) → EReal} (hh : h ∈ SA n ∩ USC n ∩ CB n) :
    (fun x => -h x) ∈ SA n ∩ LSC n ∩ CB n :=
  ⟨⟨neg_mem_SA_iff.2 hh.1.1, neg_mem_LSC_iff_USC.2 hh.1.2⟩, neg_mem_CB_iff.2 hh.2⟩

/-- `pess.t215` (Thm 2.15, pessimistic) `[A1, A2, A3]`: `𝒫^p_bounded = SA ∩ USC ∩ CB`. -/
theorem pess_thm215 [HasSemialgebraicProjections] [HasFinitenessTheorem] [HasGrowthBound] {n : ℕ} :
    Pp_bounded n = SA n ∩ USC n ∩ CB n := by
  refine Set.Subset.antisymm thm215_subset_pess ?_
  intro h hh
  have h1 : (fun x => -h x) ∈ P_bounded n := by
    rw [thm215_eq]; exact neg_mem_SA_LSC_CB hh
  exact mem_Pp_bounded_iff.2 h1

/-- `pess.t220` (Thm 2.20, pessimistic) `[A1, A2]` (A2 for the first inclusion, A1 for the second):
`PP ∩ USC ⊆ 𝒞^p_bounded ⊆ SA ∩ USC ∩ CB`. -/
theorem pess_thm220 [HasSemialgebraicProjections] [HasFinitenessTheorem] {n : ℕ} :
    coeFun '' (PP n ∩ {f | UpperSemicontinuous f}) ⊆ Cp_bounded n ∧
      Cp_bounded n ⊆ SA n ∩ USC n ∩ CB n := by
  refine ⟨?_, thm220_subset_pess⟩
  rintro _ ⟨f, ⟨hPP, husc⟩, rfl⟩
  have h1 := thm220_supset (fun x => -f x) (neg_mem_PP hPP)
    ((lowerSemicontinuous_neg_iff_real f).2 husc)
  rw [coeFun_neg] at h1
  exact mem_Cp_bounded_iff.2 h1

/-- `pess.t221` (Thm 2.21, pessimistic) `[A1, A2, A3]`: `𝒞^p_cc = SA ∩ USC ∩ CB`. -/
theorem pess_thm221 [HasSemialgebraicProjections] [HasFinitenessTheorem] [HasGrowthBound] {n : ℕ} :
    Cp_cc n = SA n ∩ USC n ∩ CB n := by
  refine Set.Subset.antisymm thm221_subset_pess ?_
  intro h hh
  exact mem_Cp_cc_iff.2 (thm221_supset (neg_mem_SA_LSC_CB hh))

end Bilevel
