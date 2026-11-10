/-
Blueprint §4.C, id `t11.whitney` (paper Thm A.1, Whitney): every closed subset of a
finite-dimensional real normed space is the zero set of a `C^∞` real function.

Provides: `Bilevel.exists_contDiff_zeroSet_eq`.
-/
import Mathlib

open scoped ContDiff

namespace Bilevel

/-- `t11.whitney`: a closed set `C` in a finite-dimensional real normed space is the exact zero
set of a `C^∞` function. Obtained from `IsOpen.exists_contDiff_support_eq` applied to `Cᶜ`. -/
theorem exists_contDiff_zeroSet_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {C : Set E} (hC : IsClosed C) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ ∀ p, g p = 0 ↔ p ∈ C := by
  obtain ⟨g, hsupp, hg, -⟩ := hC.isOpen_compl.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  refine ⟨g, hg, fun p => ?_⟩
  have h := congrArg (p ∈ ·) hsupp
  simp only [Function.mem_support, Set.mem_compl_iff, eq_iff_iff] at h
  tauto

end Bilevel
