import HardnessBilevel.Convex.Toolkit
import HardnessBilevel.Semialgebraic.Basic

/-!
# Theorem 2.20 — assumption-free core (blueprint §4.G.4)

Header to be completed.
-/

namespace Bilevel

open Set MvPolynomial

/-! ### t220.normalise -/

/-- `t220.normalise`: `g := 1/4 + ∑ l, p_l²` dominates every `p_l`. -/
theorem t220_normalise {n : ℕ} {L : Type*} [Fintype L] (p : L → MvPolynomial (Fin n) ℝ) :
    ∀ l x, eval x (p l) - eval x (C (1/4) + ∑ l, (p l) ^ 2) ≤ 0 := by
  intro l x
  have h1 : eval x (p l) ^ 2 ≤ ∑ k, eval x (p k) ^ 2 :=
    Finset.single_le_sum (f := fun k => eval x (p k) ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ l)
  simp only [map_add, eval_C, map_sum, map_pow]
  nlinarith [sq_nonneg (eval x (p l) - 1/2)]

/-- `t220.normalise` (semicontinuity half): subtracting a polynomial preserves lower semicontinuity. -/
theorem lowerSemicontinuous_sub_poly {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : LowerSemicontinuous f)
    (q : MvPolynomial (Fin n) ℝ) : LowerSemicontinuous (fun x => f x - eval x q) := by
  have hc : Continuous fun x : Fin n → ℝ => -eval x q := (MvPolynomial.continuous_eval q).neg
  simpa only [sub_eq_add_neg] using hf.add hc.lowerSemicontinuous

/-! ### The construction -/

section Construction

variable {n : ℕ} {L : Type} [Fintype L] {K : L → Type} [∀ l, Fintype (K l)]

/-- Selector part of the lower objective: `(1 − ∑ s)²`. -/
noncomputable def t220A (L : Type) [Fintype L] (n : ℕ) : (Fin n → ℝ) → (L → ℝ) → ℝ :=
  fun _ s => (1 - ∑ l, s l) ^ 2

/-- Indicator part of the lower objective: `∑_{l,k} −R_lk(x) z_lk`. -/
noncomputable def t220B (R : (l : L) → K l → MvPolynomial (Fin n) ℝ) :
    (Fin n → ℝ) → ((Σ l, K l) → ℝ) → ℝ :=
  fun x z => ∑ lk : (Σ l, K l), -eval x (R lk.1 lk.2) * z lk

/-- Lower objective `Q(x,(s,z)) = (1 − ∑ s)² + ∑ −R z` on `L ⊕ Σ l, K l`. -/
noncomputable def t220Q (R : (l : L) → K l → MvPolynomial (Fin n) ℝ) :
    (Fin n → ℝ) → (L ⊕ (Σ l, K l) → ℝ) → ℝ :=
  fun x y => t220A L n x (y ∘ Sum.inl) + t220B R x (y ∘ Sum.inr)

/-- Upper objective `P(x,(s,z)) = ∑_l p_l(x) s_l ∏_k z_lk`. -/
noncomputable def t220P (p : L → MvPolynomial (Fin n) ℝ) :
    (Fin n → ℝ) → (L ⊕ (Σ l, K l) → ℝ) → ℝ :=
  fun x y => ∑ l, eval x (p l) * y (Sum.inl l) * ∏ k : K l, y (Sum.inr ⟨l, k⟩)

theorem boundedBox_sum_eq {α β : Type*} :
    (boundedBox (0 : α ⊕ β → ℝ) 1) =
      {y | y ∘ Sum.inl ∈ boundedBox (0 : α → ℝ) 1 ∧ y ∘ Sum.inr ∈ boundedBox (0 : β → ℝ) 1} := by
  ext y
  simp only [mem_boundedBox, Set.mem_ofPred_eq, Sum.forall, Function.comp_apply, Pi.zero_apply,
    Pi.one_apply]

theorem mem_argminSet_t220A_iff [Nonempty L] (x : Fin n → ℝ) (s : L → ℝ) :
    s ∈ argminSet (t220A L n) (boundedBox 0 1) x ↔ (∀ l, 0 ≤ s l) ∧ ∑ l, s l = 1 := by
  classical
  obtain ⟨l₀⟩ := ‹Nonempty L›
  constructor
  · rintro ⟨hs, hmin⟩
    rw [mem_boundedBox] at hs
    refine ⟨fun l => (hs l).1, ?_⟩
    have hv : (fun l => if l = l₀ then (1:ℝ) else 0) ∈ boundedBox (0 : L → ℝ) 1 := by
      rw [mem_boundedBox]; intro l; split_ifs <;> simp
    have := hmin _ hv
    simp only [t220A, Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_self] at this
    nlinarith [sq_nonneg (1 - ∑ l, s l)]
  · rintro ⟨h0, h1⟩
    have hle : ∀ l, s l ≤ 1 := fun l => by
      rw [← h1]
      exact Finset.single_le_sum (f := s) (fun k _ => h0 k) (Finset.mem_univ l)
    refine ⟨mem_boundedBox.2 fun l => ⟨h0 l, hle l⟩, fun y' _ => ?_⟩
    show (1 - ∑ l, s l) ^ 2 ≤ (1 - ∑ l, y' l) ^ 2
    rw [h1, sub_self]
    nlinarith [sq_nonneg (1 - ∑ l, y' l)]

theorem mem_argminSet_t220B_iff (R : (l : L) → K l → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ)
    (z : (Σ l, K l) → ℝ) :
    z ∈ argminSet (t220B R) (boundedBox 0 1) x ↔
      ∀ lk : (Σ l, K l), z lk ∈ Icc (0:ℝ) 1 ∧
        ∀ v ∈ Icc (0:ℝ) 1, -eval x (R lk.1 lk.2) * z lk ≤ -eval x (R lk.1 lk.2) * v := by
  have h := argminSet_pi_sum (X := Fin n → ℝ) (fun _ : (Σ l, K l) => Icc (0:ℝ) 1)
    (fun x lk v => -eval x (R lk.1 lk.2) * v) x
  have hb : (boundedBox (0 : (Σ l, K l) → ℝ) 1) = Set.univ.pi fun _ => Icc (0:ℝ) 1 := rfl
  beta_reduce at h
  rw [hb, show t220B R = fun x y => ∑ i : (Σ l, K l), -eval x (R i.1 i.2) * y i from rfl, h,
    Set.mem_univ_pi]
  rfl

end Construction

end Bilevel
