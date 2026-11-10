/-
Copyright: HardnessBilevel project.

# Scalar gadgets (blueprint §4.E.1)

* `gad.G1` — the strict-inequality gadget `gadgetStrict p z = (1 - p * z ^ 2) ^ 2`
  (`gadgetStrict_nonneg`, `gadgetStrict_eq_zero_of_pos`, `one_le_gadgetStrict_of_nonpos`,
  `pos_of_gadgetStrict_eq_zero`).
* `gad.G5` — the escape / non-attainment gadget `escape a u v = a * u ^ 2 + (1 - u * v) ^ 2`
  (`escape_nonneg`, `escape_one_one`, `escape_pos`, `escape_lt`, `escape_eq_zero`,
  `escape_eq_zero_of`).

No assumption (A1–A3) is used. Deviation (strengthening): `escape_lt` (G5 (4)) drops the unused
hypothesis `0 ≤ a`.
-/
import Mathlib

namespace Bilevel

/-- gad.G1: the scalar strict-inequality gadget `g(p,z) = (1 - p z²)²`. -/
def gadgetStrict (p z : ℝ) : ℝ := (1 - p * z ^ 2) ^ 2

/-- gad.G1 (1). -/
theorem gadgetStrict_nonneg (p z : ℝ) : 0 ≤ gadgetStrict p z := sq_nonneg _

/-- gad.G1 (2): for `p > 0` the witness `z = √(p⁻¹)` gives value `0`. -/
theorem gadgetStrict_eq_zero_of_pos {p : ℝ} (hp : 0 < p) :
    gadgetStrict p (Real.sqrt p⁻¹) = 0 := by
  unfold gadgetStrict
  rw [Real.sq_sqrt (inv_nonneg.2 hp.le), mul_inv_cancel₀ hp.ne']
  norm_num

/-- gad.G1 (3): for `p ≤ 0` the gadget is at least `1`. -/
theorem one_le_gadgetStrict_of_nonpos {p : ℝ} (hp : p ≤ 0) (z : ℝ) : 1 ≤ gadgetStrict p z := by
  unfold gadgetStrict
  have h : p * z ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp (sq_nonneg z)
  nlinarith

/-- gad.G1 (4): a zero of the gadget forces `p > 0`. -/
theorem pos_of_gadgetStrict_eq_zero {p z : ℝ} (h : gadgetStrict p z = 0) : 0 < p := by
  by_contra hp
  have := one_le_gadgetStrict_of_nonpos (not_lt.1 hp) z
  linarith

/-- gad.G5: the escape gadget `N(a,u,v) = a u² + (1 - u v)²`. -/
def escape (a u v : ℝ) : ℝ := a * u ^ 2 + (1 - u * v) ^ 2

/-- gad.G5 (1). -/
theorem escape_nonneg {a : ℝ} (ha : 0 ≤ a) (u v : ℝ) : 0 ≤ escape a u v := by
  unfold escape; positivity

/-- gad.G5 (2). -/
@[simp] theorem escape_one_one (a : ℝ) : escape a 1 1 = a := by
  unfold escape; ring

/-- gad.G5 (3): for `a > 0` the gadget is strictly positive everywhere. -/
theorem escape_pos {a : ℝ} (ha : 0 < a) (u v : ℝ) : 0 < escape a u v := by
  unfold escape
  by_cases hu : u = 0
  · subst hu; norm_num
  · have hu2 : 0 < u ^ 2 := by positivity
    exact add_pos_of_pos_of_nonneg (mul_pos ha hu2) (sq_nonneg _)

/-- gad.G5 (4): the infimum of the gadget is `≤ 0` (for `a ≥ 0` it is `0`); the blueprint's
hypothesis `0 ≤ a` is not needed and has been dropped (strengthening). -/
theorem escape_lt (a : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ u v, escape a u v < ε := by
  obtain ⟨c, hc, hac⟩ := exists_pos_mul_lt hε a
  refine ⟨Real.sqrt c, (Real.sqrt c)⁻¹, ?_⟩
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  unfold escape
  rw [Real.sq_sqrt hc.le, mul_inv_cancel₀ hs.ne']
  simpa using hac

/-- gad.G5 (5): a zero of the gadget (with `a ≥ 0`) forces `a = 0` and `u v = 1`. -/
theorem escape_eq_zero {a u v : ℝ} (ha : 0 ≤ a) (h : escape a u v = 0) : a = 0 ∧ u * v = 1 := by
  unfold escape at h
  have h1 : 0 ≤ a * u ^ 2 := by positivity
  have h2 : 0 ≤ (1 - u * v) ^ 2 := sq_nonneg _
  obtain ⟨hA, hB⟩ := (add_eq_zero_iff_of_nonneg h1 h2).1 h
  have huv : u * v = 1 := by
    have := pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 hB
    linarith
  have hu : u ≠ 0 := by rintro rfl; simp at huv
  refine ⟨?_, huv⟩
  rcases mul_eq_zero.1 hA with h | h
  · exact h
  · exact absurd (pow_eq_zero_iff two_ne_zero |>.1 h) hu

/-- gad.G5 (6): converse of (5). -/
theorem escape_eq_zero_of {a u v : ℝ} (ha : a = 0) (huv : u * v = 1) : escape a u v = 0 := by
  unfold escape; rw [ha, huv]; ring

end Bilevel
