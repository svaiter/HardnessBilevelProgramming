/-
Copyright: HardnessBilevel project.

# Theorem 2.20 (convex lower level, bounded boxes)

Implements blueprint §4.G.4: `t220.supset` (`thm220_supset`, assumption A2 ONLY — A1 is not used) and
`t220.main` (`thm220_main`, A1 for the second inclusion, A2 for the first). `t220.subset` is `thm220_subset`
(A1) in `HardnessBilevel.Semialgebraic.Value`; `t220.normalise`, `t220.D_closed`, `t220.D_sa`, `t220.core` are in
`HardnessBilevel.Convex.Thm220Core`.

Assumptions are taken only as instance-implicit binders; no instance of any assumption class exists.

Deviations: none.
-/
import HardnessBilevel.Convex.Thm220Core
import HardnessBilevel.Semialgebraic.Value

open MeasureTheory Function MvPolynomial

namespace Bilevel

-- No instance of the assumption classes exists (by policy), so they are deliberately local binders.
set_option linter.concreteInstances false

/-- **t220.supset** (Thm 2.20, first inclusion) `[A2]`: a lower semicontinuous piecewise polynomial function is
the value function of a polynomial bilevel problem with convex lower level over a bounded box. -/
theorem thm220_supset [HasFinitenessTheorem] {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hPP : f ∈ PP n)
    (hlsc : LowerSemicontinuous f) : coeFun f ∈ C_bounded n := by
  obtain ⟨N, S, p, hSsa, -, hcov, hfp⟩ := hPP
  -- each `D_i = {f ≤ p_i}` is closed and semialgebraic, so A2 presents it
  have hpres : ∀ i : Fin N, ∃ (I J : ℕ) (R : Fin I → Fin J → MvPolynomial (Fin n) ℝ),
      {x | f x ≤ eval x (p i)} = ⋃ j, ⋂ k, {x | 0 ≤ eval x (R j k)} := fun i =>
    HasFinitenessTheorem.exists_eq_iUnion_iInter_nonneg (t220_D_sa hSsa hcov hfp i)
      (t220_D_closed hlsc (p i))
  choose J K R hR using hpres
  exact t220_mem_C_bounded_of_presentations hcov hfp J (fun i _ => K i) R hR

/-- **t220.main** (Thm 2.20) `[A1, A2]`: `PP ∩ LSC ⊆ 𝒞_bounded ⊆ SA ∩ LSC ∩ CB`. -/
theorem thm220_main [HasSemialgebraicProjections] [HasFinitenessTheorem] {n : ℕ} :
    coeFun '' (PP n ∩ {f | LowerSemicontinuous f}) ⊆ C_bounded n ∧
      C_bounded n ⊆ SA n ∩ LSC n ∩ CB n := by
  refine ⟨?_, thm220_subset⟩
  rintro _ ⟨f, ⟨hPP, hlsc⟩, rfl⟩
  exact thm220_supset f hPP hlsc

end Bilevel
