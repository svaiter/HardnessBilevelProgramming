import HardnessBilevel.Framework.Basic
import HardnessBilevel.Framework.Value
import HardnessBilevel.Framework.Separable
import HardnessBilevel.Framework.Poly
import HardnessBilevel.Framework.Box

/-!
# Convex lower-level toolkit (blueprint §4.G.1)

Provides
* `ConvexLower` (blueprint §2.3): `∀ x, ConvexOn ℝ univ (Q x)`;
* `fw.argmin_scalar` (i)–(iii): `argmin_scalar_univ`, `argmin_scalar_Ici` (full set descriptions) and the
  consequences used later (`mul_eq_of_isMin_univ`, `isMin_univ_witness`, `mul_eq_of_isMin_Ici`,
  `isMin_Ici_witness`, `isMin_one_Icc_iff`, `eq_zero_of_isMin_Icc`);
* `fw.convex_toolkit`: `convexOn_sq_affine`, `convexOn_finset_sum`, `convexOn_linear_coord`,
  `convexOn_sq_one_sub_mul_coord`, `ConvexLower.add`, `ConvexLower.finset_sum`, `ConvexLower.comp_reindex`,
  `ConvexLower.convexOn`, box convexity (`IsUnboundedBox.convex`, `IsBox.convex` from `Framework.Box`);
* `isUnboundedBox_pi_univ_or_Ici`: a product of intervals each `univ` or `Ici 0`, one of them `univ`, is an
  unbounded box (mixed box of Thm 2.18).

`fw.value_shift_attained` is `Bilevel.value_shift_attained` (Framework/Basic) and `fw.const_on_argmin` is
`Bilevel.valueFun_eq_of_const` / `Bilevel.pvalueFun_eq_of_const`; they are not restated here.
-/

namespace Bilevel

open Set

/-! ### Convexity of the lower level -/

/-- Convexity of the lower level in `y` (blueprint §2.3, Def 2.16): convex on all of `ℝ^ι` for every `x`. -/
def ConvexLower {n : ℕ} {ι : Type*} (Q : (Fin n → ℝ) → (ι → ℝ) → ℝ) : Prop :=
  ∀ x, ConvexOn ℝ Set.univ (fun y => Q x y)

/-! ### fw.argmin_scalar -/

section Scalar

/-- `fw.argmin_scalar` (i): argmin of `t ↦ (1 - c t)^2` over `ℝ`. -/
theorem argmin_scalar_univ (c : ℝ) :
    {t : ℝ | ∀ t', (1 - c * t) ^ 2 ≤ (1 - c * t') ^ 2} = if c = 0 then Set.univ else {c⁻¹} := by
  split_ifs with hc
  · ext t; simp [hc]
  · ext t
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      have h1 := h c⁻¹
      rw [mul_inv_cancel₀ hc, sub_self] at h1
      have h2 : (1 - c * t) ^ 2 = 0 := le_antisymm (by simpa using h1) (sq_nonneg _)
      have h3 : c * t = 1 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
        linarith
      field_simp
      linarith
    · rintro rfl t'
      rw [mul_inv_cancel₀ hc, sub_self]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg _

/-- `fw.argmin_scalar` (i), consequence: on the argmin, `c * t = 1` if `c ≠ 0` and `c * t = 0` if `c = 0`. -/
theorem mul_eq_of_isMin_univ {c t : ℝ} (h : ∀ t', (1 - c * t) ^ 2 ≤ (1 - c * t') ^ 2) :
    c * t = if c = 0 then 0 else 1 := by
  have hm : t ∈ {t : ℝ | ∀ t', (1 - c * t) ^ 2 ≤ (1 - c * t') ^ 2} := h
  rw [argmin_scalar_univ] at hm
  split_ifs at hm ⊢ with hc
  · simp [hc]
  · rw [Set.mem_singleton_iff.mp hm, mul_inv_cancel₀ hc]

/-- `fw.argmin_scalar` (i), witness. -/
theorem isMin_univ_witness (c : ℝ) :
    ∀ t', (1 - c * (if c = 0 then 0 else c⁻¹)) ^ 2 ≤ (1 - c * t') ^ 2 := by
  have : (if c = 0 then (0 : ℝ) else c⁻¹) ∈ {t : ℝ | ∀ t', (1 - c * t) ^ 2 ≤ (1 - c * t') ^ 2} := by
    rw [argmin_scalar_univ]
    split_ifs <;> simp
  exact this

/-- `fw.argmin_scalar` (ii): argmin of `u ↦ (1 - c u)^2` over `Ici 0`. -/
theorem argmin_scalar_Ici (c : ℝ) :
    {u : ℝ | u ∈ Ici 0 ∧ ∀ u' ∈ Ici (0 : ℝ), (1 - c * u) ^ 2 ≤ (1 - c * u') ^ 2} =
      if 0 < c then {c⁻¹} else if c = 0 then Ici 0 else {0} := by
  split_ifs with hc hc0
  · ext u
    simp only [Set.mem_ofPred_eq, Set.mem_Ici, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hu, h⟩
      have h1 := h c⁻¹ (inv_nonneg.mpr hc.le)
      rw [mul_inv_cancel₀ hc.ne', sub_self] at h1
      have h2 : (1 - c * u) ^ 2 = 0 := le_antisymm (by simpa using h1) (sq_nonneg _)
      have h3 : c * u = 1 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
        linarith
      field_simp
      linarith
    · rintro rfl
      refine ⟨inv_nonneg.mpr hc.le, fun u' _ => ?_⟩
      rw [mul_inv_cancel₀ hc.ne', sub_self]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg _
  · ext u; simp [hc0]
  · have hneg : c < 0 := lt_of_le_of_ne (not_lt.mp hc) hc0
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_Ici, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hu, h⟩
      have h1 := h 0 le_rfl
      simp only [mul_zero, sub_zero, one_pow] at h1
      have hcu : c * u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le hu
      have : c * u = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hc0
      · exact h'
    · rintro rfl
      refine ⟨le_rfl, fun u' hu' => ?_⟩
      have hcu : c * u' ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le hu'
      simp only [mul_zero, sub_zero, one_pow]
      nlinarith

/-- `fw.argmin_scalar` (ii), consequence: on the argmin over `Ici 0`, `c * u = 1` if `0 < c`, else `c * u = 0`. -/
theorem mul_eq_of_isMin_Ici {c u : ℝ} (hu : 0 ≤ u)
    (h : ∀ u', 0 ≤ u' → (1 - c * u) ^ 2 ≤ (1 - c * u') ^ 2) :
    c * u = if 0 < c then 1 else 0 := by
  have hm : u ∈ {u : ℝ | u ∈ Ici 0 ∧ ∀ u' ∈ Ici (0 : ℝ), (1 - c * u) ^ 2 ≤ (1 - c * u') ^ 2} :=
    ⟨hu, fun u' hu' => h u' hu'⟩
  rw [argmin_scalar_Ici] at hm
  split_ifs at hm ⊢ with hc hc0
  · rw [Set.mem_singleton_iff.mp hm, mul_inv_cancel₀ hc.ne']
  · simp [hc0]
  · simp [Set.mem_singleton_iff.mp hm]

/-- `fw.argmin_scalar` (ii), witness. -/
theorem isMin_Ici_witness (c : ℝ) :
    0 ≤ (if 0 < c then c⁻¹ else 0) ∧
      ∀ u', 0 ≤ u' → (1 - c * (if 0 < c then c⁻¹ else 0)) ^ 2 ≤ (1 - c * u') ^ 2 := by
  have : (if 0 < c then c⁻¹ else (0 : ℝ)) ∈
      {u : ℝ | u ∈ Ici 0 ∧ ∀ u' ∈ Ici (0 : ℝ), (1 - c * u) ^ 2 ≤ (1 - c * u') ^ 2} := by
    rw [argmin_scalar_Ici]
    split_ifs with hc hc0
    · simp
    · simp
    · simp
  exact ⟨this.1, fun u' hu' => this.2 u' hu'⟩

/-- `fw.argmin_scalar` (iii): `1` minimises `z ↦ -c z` on `Icc 0 1` iff `0 ≤ c`. -/
theorem isMin_one_Icc_iff (c : ℝ) :
    (∀ z' ∈ Icc (0 : ℝ) 1, -c * 1 ≤ -c * z') ↔ 0 ≤ c := by
  constructor
  · intro h
    have := h 0 ⟨le_rfl, zero_le_one⟩
    linarith
  · rintro hc z' ⟨_, hz1⟩
    nlinarith

/-- `fw.argmin_scalar` (iii): if `c < 0`, the minimiser of `z ↦ -c z` on `Icc 0 1` is `0`. -/
theorem eq_zero_of_isMin_Icc {c z : ℝ} (hc : c < 0) (hz : z ∈ Icc (0 : ℝ) 1)
    (h : ∀ z' ∈ Icc (0 : ℝ) 1, -c * z ≤ -c * z') : z = 0 := by
  have := h 0 ⟨le_rfl, zero_le_one⟩
  have : -c * z ≤ 0 := by simpa using this
  nlinarith [hz.1]

end Scalar

/-! ### fw.convex_toolkit -/

section ConvexToolkit

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `fw.convex_toolkit`: the square of an affine function is convex. -/
theorem convexOn_sq_affine (ℓ : E →ₗ[ℝ] ℝ) (c : ℝ) :
    ConvexOn ℝ Set.univ (fun v => (c - ℓ v) ^ 2) := by
  refine ⟨convex_univ, fun v _ w _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, map_add, map_smul]
  obtain rfl : b = 1 - a := by linarith
  nlinarith [mul_nonneg ha hb, mul_nonneg (mul_nonneg ha hb) (sq_nonneg (ℓ v - ℓ w))]

/-- `fw.convex_toolkit`: a finite sum of convex functions is convex. -/
theorem convexOn_finset_sum {κ : Type*} {t : Set E} (ht : Convex ℝ t) (s : Finset κ)
    {f : κ → E → ℝ} (hf : ∀ k ∈ s, ConvexOn ℝ t (f k)) :
    ConvexOn ℝ t (fun v => ∑ k ∈ s, f k v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using convexOn_const (0 : ℝ) ht
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (hf k (Finset.mem_insert_self _ _)).add
      (ih fun k' hk' => hf k' (Finset.mem_insert_of_mem hk'))

/-- `fw.convex_toolkit`: a linear function of one coordinate is convex. -/
theorem convexOn_linear_coord {ι : Type*} (j : ι) (c : ℝ) :
    ConvexOn ℝ Set.univ (fun y : ι → ℝ => c * y j) :=
  (c • (LinearMap.proj j : (ι → ℝ) →ₗ[ℝ] ℝ)).convexOn convex_univ

/-- `fw.convex_toolkit`: `y ↦ (1 - a * y j)^2` is convex. -/
theorem convexOn_sq_one_sub_mul_coord {ι : Type*} (a : ℝ) (j : ι) :
    ConvexOn ℝ Set.univ (fun y : ι → ℝ => (1 - a * y j) ^ 2) :=
  convexOn_sq_affine (a • (LinearMap.proj j : (ι → ℝ) →ₗ[ℝ] ℝ)) 1

end ConvexToolkit

section ConvexLowerLemmas

variable {n : ℕ} {ι : Type*}

theorem ConvexLower.add {Q R : (Fin n → ℝ) → (ι → ℝ) → ℝ} (hQ : ConvexLower Q) (hR : ConvexLower R) :
    ConvexLower (fun x y => Q x y + R x y) :=
  fun x => (hQ x).add (hR x)

theorem ConvexLower.finset_sum {κ : Type*} (s : Finset κ) {Q : κ → (Fin n → ℝ) → (ι → ℝ) → ℝ}
    (hQ : ∀ k ∈ s, ConvexLower (Q k)) : ConvexLower (fun x y => ∑ k ∈ s, Q k x y) :=
  fun x => convexOn_finset_sum convex_univ s fun k hk => hQ k hk x

theorem convexLower_const (c : (Fin n → ℝ) → ℝ) : ConvexLower (fun x (_ : ι → ℝ) => c x) :=
  fun x => convexOn_const (c x) convex_univ

/-- Reindexing the lower variable (restriction to a block) preserves convexity. -/
theorem ConvexLower.comp_reindex {ι' : Type*} {Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} (hQ : ConvexLower Q)
    (g : ι → ι') : ConvexLower (fun x (y : ι' → ℝ) => Q x (fun k => y (g k))) := fun x => by
  refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
  exact (hQ x).2 (Set.mem_univ (fun k => a (g k))) (Set.mem_univ (fun k => b (g k))) hs ht hst

/-- `ConvexLower` gives convexity on any convex feasible set. -/
theorem ConvexLower.convexOn {Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} (hQ : ConvexLower Q) {Y : Set (ι → ℝ)}
    (hY : Convex ℝ Y) (x : Fin n → ℝ) : ConvexOn ℝ Y (Q x) :=
  (hQ x).subset (Set.subset_univ _) hY

end ConvexLowerLemmas

/-! ### Mixed boxes -/

/-- A product of intervals each equal to `univ` or `Ici 0`, at least one equal to `univ`, is an unbounded box. -/
theorem isUnboundedBox_pi_univ_or_Ici {ι : Type*} (I : ι → Set ℝ)
    (hI : ∀ i, I i = Set.univ ∨ I i = Set.Ici 0) (h : ∃ i, I i = Set.univ) :
    IsUnboundedBox (Set.pi Set.univ I) := by
  classical
  refine ⟨fun i => if I i = Set.univ then ⊥ else ((0 : ℝ) : EReal), fun _ => ⊤, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs
    · exact ⟨bot_ne_top, top_ne_bot, bot_le⟩
    · exact ⟨EReal.coe_ne_top 0, top_ne_bot, le_top⟩
  · obtain ⟨i, hi⟩ := h
    exact ⟨i, Or.inl (by simp [hi])⟩
  · ext y
    simp only [Set.mem_pi, Set.mem_univ, true_implies, mem_boxSet, le_top, and_true]
    refine forall_congr' fun i => ?_
    rcases hI i with hi | hi
    · simp [hi]
    · have hne : ¬ (Set.Ici (0 : ℝ) = Set.univ) := fun h' => by
        have : (-1 : ℝ) ∈ Set.Ici (0 : ℝ) := h' ▸ Set.mem_univ _
        norm_num at this
      simp [hi, hne]

end Bilevel
