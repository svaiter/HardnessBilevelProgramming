/-
Copyright: HardnessBilevel project.

# Assumption-free forms of the main theorems

Every theorem of the core library `HardnessBilevel` that takes one of the assumption classes
`HasSemialgebraicProjections` (A1), `HasFinitenessTheorem` (A2), `HasGrowthBound` (A3) as a binder is restated here
with no binder, in the namespace `Bilevel.Unconditional`, under the same name. Each proof is the core theorem
itself: the binders are filled by the proved instances of `HardnessBilevelUnconditional/Instances.lean`.

Covered: Proposition 2.6, Theorems 2.12, 2.15, 2.18, 2.20, 2.21 and their pessimistic counterparts (paper §2.4).
The statements are copied from the core library with the class binders removed and nothing else changed.

`scripts/CheckAxiomsUnconditional.lean` prints the axioms of every theorem of this file; they are exactly
`propext`, `Classical.choice`, `Quot.sound`.
-/
import HardnessBilevel
import HardnessBilevelUnconditional.Instances

namespace Bilevel.Unconditional

/-! ### Proposition 2.6 -/

/-- Proposition 2.6 (corrected), for any semialgebraic lower-level set `Y`: the optimistic value function of a
polynomial bilevel problem is extended-real semialgebraic. -/
theorem valueFun_isExtSemialgebraic
    {n : ℕ} {ι : Type} [Fintype ι] {P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} {Y : Set (ι → ℝ)}
    (hP : IsPolyFun P) (hQ : IsPolyFun Q) (hY : IsSemialgebraic Y) :
    IsExtSemialgebraic (valueFun P Q Y) :=
  _root_.Bilevel.valueFun_isExtSemialgebraic hP hQ hY

/-- Proposition 2.6, pessimistic twin. -/
theorem pvalueFun_isExtSemialgebraic
    {n : ℕ} {ι : Type} [Fintype ι] {P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} {Y : Set (ι → ℝ)}
    (hP : IsPolyFun P) (hQ : IsPolyFun Q) (hY : IsSemialgebraic Y) :
    IsExtSemialgebraic (pvalueFun P Q Y) :=
  _root_.Bilevel.pvalueFun_isExtSemialgebraic hP hQ hY

/-! ### Theorem 2.12 -/

/-- Theorem 2.12: `𝒫_unbound = SA`. -/
theorem thm212_eq_SA {n : ℕ} : P_unbound n = SA n :=
  _root_.Bilevel.thm212_eq_SA

/-- Theorem 2.12, pessimistic: `𝒫^p_unbound = SA`. -/
theorem pess_thm212 {n : ℕ} : Pp_unbound n = SA n :=
  _root_.Bilevel.pess_thm212

/-! ### Theorem 2.15 -/

/-- Theorem 2.15 (`⊇`, construction): every real semialgebraic, lower semicontinuous function bounded on compacts
is the value function of a polynomial bilevel problem over a bounded box. -/
theorem thm215_supset
    {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hsa : IsSemialgebraicMap f)
    (hlsc : LowerSemicontinuous f)
    (hcb : ∀ K : Set (Fin n → ℝ), IsCompact K → ∃ B, ∀ x ∈ K, |f x| ≤ B) :
    ∃ (ι : Type) (_ : Fintype ι) (P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ) (a b : ι → ℝ),
      IsPolyFun P ∧ IsPolyFun Q ∧ (∀ k, a k ≤ b k) ∧
      ∀ x, valueFun P Q (boundedBox a b) x = ((f x : ℝ) : EReal) :=
  _root_.Bilevel.thm215_supset f hsa hlsc hcb

/-- Theorem 2.15: `𝒫_bounded = SA ∩ LSC ∩ CB`. -/
theorem thm215_eq {n : ℕ} : P_bounded n = SA n ∩ LSC n ∩ CB n :=
  _root_.Bilevel.thm215_eq

/-- Theorem 2.15, pessimistic: `𝒫^p_bounded = SA ∩ USC ∩ CB`. -/
theorem pess_thm215 {n : ℕ} : Pp_bounded n = SA n ∩ USC n ∩ CB n :=
  _root_.Bilevel.pess_thm215

/-! ### Theorem 2.18 -/

/-- Theorem 2.18: `PP ⊆ 𝒞_unbound ⊆ SA`. -/
theorem thm218_main {n : ℕ} : PPe n ⊆ C_unbound n ∧ C_unbound n ⊆ SA n :=
  _root_.Bilevel.thm218_main

/-- Theorem 2.18, pessimistic: `PP ⊆ 𝒞^p_unbound ⊆ SA`. -/
theorem pess_thm218 {n : ℕ} : PPe n ⊆ Cp_unbound n ∧ Cp_unbound n ⊆ SA n :=
  _root_.Bilevel.pess_thm218

/-! ### Theorem 2.20 -/

/-- Theorem 2.20 (first inclusion, construction): a lower semicontinuous piecewise polynomial function is the
value function of a polynomial bilevel problem with convex lower level over a bounded box. -/
theorem thm220_supset {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hPP : f ∈ PP n)
    (hlsc : LowerSemicontinuous f) : coeFun f ∈ C_bounded n :=
  _root_.Bilevel.thm220_supset f hPP hlsc

/-- Theorem 2.20: `PP ∩ LSC ⊆ 𝒞_bounded ⊆ SA ∩ LSC ∩ CB`. -/
theorem thm220_main {n : ℕ} :
    coeFun '' (PP n ∩ {f | LowerSemicontinuous f}) ⊆ C_bounded n ∧
      C_bounded n ⊆ SA n ∩ LSC n ∩ CB n :=
  _root_.Bilevel.thm220_main

/-- Theorem 2.20, pessimistic: `PP ∩ USC ⊆ 𝒞^p_bounded ⊆ SA ∩ USC ∩ CB`. -/
theorem pess_thm220 {n : ℕ} :
    coeFun '' (PP n ∩ {f | UpperSemicontinuous f}) ⊆ Cp_bounded n ∧
      Cp_bounded n ⊆ SA n ∩ USC n ∩ CB n :=
  _root_.Bilevel.pess_thm220

/-! ### Theorem 2.21 -/

/-- A polynomial bilevel problem with nonempty compact semialgebraic lower set has its optimistic value function
in `𝒞_cc`. -/
theorem thm221_compact_sa_incl {n : ℕ} {ι : Type} [Fintype ι]
    {P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} (hP : IsPolyFun P) (hQ : IsPolyFun Q) {Y : Set (ι → ℝ)}
    (hYc : IsCompact Y) (hYn : Y.Nonempty) (hYs : IsSemialgebraic Y) :
    valueFun P Q Y ∈ C_cc n :=
  _root_.Bilevel.thm221_compact_sa_incl hP hQ hYc hYn hYs

/-- Pessimistic twin of `thm221_compact_sa_incl`. -/
theorem thm221_compact_sa_incl_pess {n : ℕ} {ι : Type} [Fintype ι]
    {P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} (hP : IsPolyFun P) (hQ : IsPolyFun Q) {Y : Set (ι → ℝ)}
    (hYc : IsCompact Y) (hYn : Y.Nonempty) (hYs : IsSemialgebraic Y) :
    pvalueFun P Q Y ∈ Cp_cc n :=
  _root_.Bilevel.thm221_compact_sa_incl_pess hP hQ hYc hYn hYs

/-- Theorem 2.21: `𝒞_cc = SA ∩ LSC ∩ CB`. -/
theorem thm221_eq {n : ℕ} : C_cc n = SA n ∩ LSC n ∩ CB n :=
  _root_.Bilevel.thm221_eq

/-- Theorem 2.21, pessimistic: `𝒞^p_cc = SA ∩ USC ∩ CB`. -/
theorem pess_thm221 {n : ℕ} : Cp_cc n = SA n ∩ USC n ∩ CB n :=
  _root_.Bilevel.pess_thm221

end Bilevel.Unconditional
