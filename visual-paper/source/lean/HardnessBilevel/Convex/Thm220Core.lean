import HardnessBilevel.Convex.Toolkit
import HardnessBilevel.Semialgebraic.Basic
import HardnessBilevel.Framework.Classes

/-!
# Theorem 2.20 — assumption-free core (blueprint §4.G.4)

Ids implemented (no assumption class A1–A3 is used anywhere in this file):
* `t220.normalise` — `t220_normalise` (`g := C (1/4) + ∑ l, (p l)^2` dominates every `p l`) and
  `lowerSemicontinuous_sub_poly`;
* `t220.core` — `t220_core` (statement exactly as in the blueprint) and `t220_core_valueFun`
  (`valueFun P Q (boundedBox a b) = ↑f`, via `fw.value_eq_of_isLeast`);
* `t220.D_closed` — `t220_D_closed`;
* `t220.D_sa` — `t220_D_eq` (set identity; general form `t220_D_eq_of_poly`) and `t220_D_sa`;
* `t220.supset` steps (c)–(e), assumption-free part — `t220_isLeast_of_presentation` (flattening to
  `L := Σ i, Fin (J i)`), `t220_of_presentations` (conclusion of `t220_core_valueFun`) and the class form
  `t220_mem_C_bounded_of_presentations` (`coeFun f ∈ C_bounded n`);
* `t220.eq13` (optional) — `t220_eq13`, `t220_eq13_nonempty`.

Construction (Steps 1–7): lower variables `y : L ⊕ (Σ l, K l) → ℝ` in the box `[0,1]^ι`
(`s = y ∘ inl`, `z = y ∘ inr`),
`Q(x,y) = (1 − ∑_l s_l)² + ∑_{lk} −R_lk(x) z_lk` (`t220Q`), `P(x,y) = ∑_l p_l(x) s_l ∏_k z_lk` (`t220P`).
The argmin is described by `mem_argminSet_t220Q_iff'` (via `argminSet_sum_elim` and `argminSet_pi_sum`);
`le_t220P_of_mem` is the lower bound (Step 3), `exists_mem_argminSet_t220P_eq` the explicit minimiser (Step 4).
In `t220_core` the data are first normalised (`p'_l := p_l − g`, Step 0) and `g` is added back to `P` with
`value_shift_attained`.

Deviations: `t220_normalise` is stated for `L : Type*` (generalisation). The presentation lemmas do not need the
semialgebraicity or disjointness of the pieces `S i` (hypotheses dropped = strengthening); the closed-basic
presentation of `D_i` is taken with `J : Fin N → ℕ`, `K : (i : Fin N) → Fin (J i) → ℕ` index counts (the output
shape of `HasFinitenessTheorem`, with `K` allowed to depend on `j`).
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

theorem mem_argminSet_t220Q_iff (R : (l : L) → K l → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ)
    (y : L ⊕ (Σ l, K l) → ℝ) :
    y ∈ argminSet (t220Q R) (boundedBox 0 1) x ↔
      y ∘ Sum.inl ∈ argminSet (t220A L n) (boundedBox 0 1) x ∧
        y ∘ Sum.inr ∈ argminSet (t220B R) (boundedBox 0 1) x := by
  rw [boundedBox_sum_eq]
  exact Set.ext_iff.1 (argminSet_sum_elim (t220A L n) (t220B R) _ _ x) y

/-- Explicit description of the argmin `Θ(x)` (for `L` nonempty). -/
theorem mem_argminSet_t220Q_iff' [Nonempty L] (R : (l : L) → K l → MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (y : L ⊕ (Σ l, K l) → ℝ) :
    y ∈ argminSet (t220Q R) (boundedBox 0 1) x ↔
      ((∀ l, 0 ≤ y (Sum.inl l)) ∧ ∑ l, y (Sum.inl l) = 1) ∧
        ∀ lk : (Σ l, K l), y (Sum.inr lk) ∈ Icc (0:ℝ) 1 ∧
          ∀ v ∈ Icc (0:ℝ) 1, -eval x (R lk.1 lk.2) * y (Sum.inr lk) ≤ -eval x (R lk.1 lk.2) * v := by
  rw [mem_argminSet_t220Q_iff, mem_argminSet_t220A_iff, mem_argminSet_t220B_iff]
  rfl

/-- Step 3 (lower bound) for normalised data. -/
theorem le_t220P_of_mem (p : L → MvPolynomial (Fin n) ℝ) (R : (l : L) → K l → MvPolynomial (Fin n) ℝ)
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (hp : ∀ l, eval x (p l) ≤ 0)
    (hf : IsLeast {r | ∃ l, (∀ k, 0 ≤ eval x (R l k)) ∧ r = eval x (p l)} (f x))
    {y : L ⊕ (Σ l, K l) → ℝ} (hy : y ∈ argminSet (t220Q R) (boundedBox 0 1) x) :
    f x ≤ t220P p x y := by
  obtain ⟨l₀, -, hl₀⟩ := hf.1
  have : Nonempty L := ⟨l₀⟩
  rw [mem_argminSet_t220Q_iff'] at hy
  obtain ⟨⟨hs, hsum⟩, hz⟩ := hy
  have hf0 : f x ≤ 0 := hl₀ ▸ hp l₀
  have ha : ∀ l, f x ≤ eval x (p l) * ∏ k : K l, y (Sum.inr ⟨l, k⟩) := by
    intro l
    by_cases hB : ∀ k, 0 ≤ eval x (R l k)
    · have h0 : 0 ≤ ∏ k : K l, y (Sum.inr ⟨l, k⟩) :=
        Finset.prod_nonneg fun k _ => (hz ⟨l, k⟩).1.1
      have h1 : ∏ k : K l, y (Sum.inr ⟨l, k⟩) ≤ 1 :=
        Finset.prod_le_one₀ (fun k _ => (hz ⟨l, k⟩).1.1) (fun k _ => (hz ⟨l, k⟩).1.2)
      have hfl : f x ≤ eval x (p l) := hf.2 ⟨l, hB, rfl⟩
      nlinarith [mul_nonneg_of_nonpos_of_nonpos (hp l) (sub_nonpos.2 h1)]
    · push Not at hB
      obtain ⟨k, hk⟩ := hB
      have hzero : y (Sum.inr ⟨l, k⟩) = 0 :=
        eq_zero_of_isMin_Icc (c := eval x (R l k)) hk (hz ⟨l, k⟩).1 (hz ⟨l, k⟩).2
      rw [Finset.prod_eq_zero (Finset.mem_univ k) hzero, mul_zero]
      exact hf0
  calc f x = ∑ l, y (Sum.inl l) * f x := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ l, y (Sum.inl l) * (eval x (p l) * ∏ k : K l, y (Sum.inr ⟨l, k⟩)) :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (ha l) (hs l)
    _ = t220P p x y := Finset.sum_congr rfl fun l _ => by ring

/-- Step 4 (explicit minimiser): for `x ∈ B_{l₀}`, the vertex selector at `l₀` with `z_lk = 1_{R_lk(x) ≥ 0}`
lies in `Θ(x)` and has upper value `p_{l₀}(x)`. -/
theorem exists_mem_argminSet_t220P_eq (p : L → MvPolynomial (Fin n) ℝ)
    (R : (l : L) → K l → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (l₀ : L)
    (hB : ∀ k, 0 ≤ eval x (R l₀ k)) :
    ∃ y ∈ argminSet (t220Q R) (boundedBox 0 1) x, t220P p x y = eval x (p l₀) := by
  classical
  have : Nonempty L := ⟨l₀⟩
  refine ⟨Sum.elim (fun l => if l = l₀ then 1 else 0)
    (fun lk => if 0 ≤ eval x (R lk.1 lk.2) then 1 else 0), ?_, ?_⟩
  · rw [mem_argminSet_t220Q_iff']
    simp only [Sum.elim_inl, Sum.elim_inr]
    refine ⟨⟨fun l => by split_ifs <;> norm_num, by simp⟩, fun lk => ⟨by split_ifs <;> simp, ?_⟩⟩
    by_cases h : 0 ≤ eval x (R lk.1 lk.2)
    · simp only [h, ↓reduceIte]
      exact (isMin_one_Icc_iff _).2 h
    · simp only [h, ↓reduceIte]
      intro v hv
      push Not at h
      nlinarith [hv.1]
  · unfold t220P
    rw [Finset.sum_eq_single l₀]
    · simp only [Sum.elim_inl, Sum.elim_inr, ↓reduceIte, mul_one]
      rw [Finset.prod_eq_one fun k _ => by simp only [hB k, ↓reduceIte], mul_one]
    · intro l _ hl
      simp [hl]
    · intro h; exact absurd (Finset.mem_univ l₀) h

/-- Steps 3–5 for normalised data (all `p_l ≤ 0` at `x`). -/
theorem isLeast_t220P_of_nonpos (p : L → MvPolynomial (Fin n) ℝ)
    (R : (l : L) → K l → MvPolynomial (Fin n) ℝ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hp : ∀ l, eval x (p l) ≤ 0)
    (hf : IsLeast {r | ∃ l, (∀ k, 0 ≤ eval x (R l k)) ∧ r = eval x (p l)} (f x)) :
    IsLeast ((t220P p x) '' argminSet (t220Q R) (boundedBox 0 1) x) (f x) := by
  obtain ⟨l₀, hB, hl₀⟩ := hf.1
  obtain ⟨y, hy, hPy⟩ := exists_mem_argminSet_t220P_eq p R x l₀ hB
  refine ⟨⟨y, hy, hPy.trans hl₀.symm⟩, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  exact le_t220P_of_mem p R f x hp hf hy'

/-- Step 7: polynomiality of the lower objective. -/
theorem isPolyFun_t220Q (R : (l : L) → K l → MvPolynomial (Fin n) ℝ) : IsPolyFun (t220Q R) := by
  have h : IsPolyFun fun (x : Fin n → ℝ) (y : L ⊕ (Σ l, K l) → ℝ) =>
      (1 - ∑ l, y (Sum.inl l)) ^ 2 + ∑ lk : (Σ l, K l), -eval x (R lk.1 lk.2) * y (Sum.inr lk) :=
    (((isPolyFun_const 1).sub (isPolyFun_finset_sum _ fun l _ => isPolyFun_y (Sum.inl l))).pow 2).add
      (isPolyFun_finset_sum _ fun lk _ =>
        (IsPolyFun.of_upper_only (R lk.1 lk.2)).neg.mul (isPolyFun_y (Sum.inr lk)))
  exact h.of_eq fun _ _ => rfl

/-- Step 7: polynomiality of the upper objective. -/
theorem isPolyFun_t220P (p : L → MvPolynomial (Fin n) ℝ) : IsPolyFun (t220P (K := K) p) :=
  isPolyFun_finset_sum _ fun l _ =>
    ((IsPolyFun.of_upper_only (p l)).mul (isPolyFun_y (Sum.inl l))).mul
      (isPolyFun_finset_prod _ fun k _ =>
        isPolyFun_y (ι := L ⊕ (Σ l, K l)) (Sum.inr (⟨l, k⟩ : Σ l, K l)))

/-- Step 6: convexity of the lower objective on `univ`. -/
theorem convexLower_t220Q (R : (l : L) → K l → MvPolynomial (Fin n) ℝ) : ConvexLower (t220Q R) := by
  intro x
  let ℓ : (L ⊕ (Σ l, K l) → ℝ) →ₗ[ℝ] ℝ :=
    ∑ l, LinearMap.proj (R := ℝ) (φ := fun _ : L ⊕ (Σ l, K l) => ℝ) (Sum.inl l)
  have h1 : ConvexOn ℝ Set.univ fun y : L ⊕ (Σ l, K l) → ℝ => (1 - ∑ l, y (Sum.inl l)) ^ 2 := by
    have h := convexOn_sq_affine ℓ 1
    have he : (fun v => (1 - ℓ v) ^ 2) = fun y : L ⊕ (Σ l, K l) → ℝ => (1 - ∑ l, y (Sum.inl l)) ^ 2 := by
      funext v
      simp only [ℓ, LinearMap.sum_apply, LinearMap.proj_apply]
    rwa [he] at h
  have h2 : ConvexOn ℝ Set.univ fun y : L ⊕ (Σ l, K l) → ℝ =>
      ∑ lk : (Σ l, K l), -eval x (R lk.1 lk.2) * y (Sum.inr lk) :=
    convexOn_finset_sum convex_univ _ fun lk _ => convexOn_linear_coord (Sum.inr lk) _
  exact h1.add h2

end Construction

/-! ### t220.core -/

/-- `t220.core` (Theorem 2.20, core, flat form). -/
theorem t220_core {n : ℕ} {L : Type} [Fintype L] {K : L → Type} [∀ l, Fintype (K l)]
    (p : L → MvPolynomial (Fin n) ℝ) (R : (l : L) → K l → MvPolynomial (Fin n) ℝ)
    (f : (Fin n → ℝ) → ℝ)
    (hf : ∀ x, IsLeast {r | ∃ l, (∀ k, 0 ≤ MvPolynomial.eval x (R l k)) ∧ r = MvPolynomial.eval x (p l)}
      (f x)) :
    ∃ (ι : Type) (_ : Fintype ι) (P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ) (a b : ι → ℝ),
      IsPolyFun P ∧ IsPolyFun Q ∧ ConvexLower Q ∧ (∀ i, a i ≤ b i) ∧
      ∀ x, IsLeast ((P x) '' argminSet Q (boundedBox a b) x) (f x) := by
  -- Step 0: normalisation
  set g : MvPolynomial (Fin n) ℝ := C (1/4) + ∑ l, (p l) ^ 2 with hg
  set p' : L → MvPolynomial (Fin n) ℝ := fun l => p l - g with hp'
  have hp'le : ∀ x l, eval x (p' l) ≤ 0 := fun x l => by
    simpa only [hp', map_sub] using t220_normalise p l x
  have hf' : ∀ x, IsLeast {r | ∃ l, (∀ k, 0 ≤ eval x (R l k)) ∧ r = eval x (p' l)}
      (f x - eval x g) := by
    intro x
    obtain ⟨⟨l, hB, hl⟩, hlow⟩ := hf x
    refine ⟨⟨l, hB, by simp only [hp', map_sub, hl]⟩, ?_⟩
    rintro r ⟨l', hB', rfl⟩
    have := hlow ⟨l', hB', rfl⟩
    simp only [hp', map_sub]
    linarith
  refine ⟨L ⊕ (Σ l, K l), inferInstance, fun x y => t220P p' x y + eval x g, t220Q R, 0, 1,
    (isPolyFun_t220P p').add (IsPolyFun.of_upper_only g), isPolyFun_t220Q R, convexLower_t220Q R,
    fun _ => zero_le_one, fun x => ?_⟩
  have h := value_shift_attained (g := fun x => eval x g)
    (isLeast_t220P_of_nonpos p' R (fun x => f x - eval x g) x (hp'le x) (hf' x))
  rwa [sub_add_cancel] at h

/-- Corollary of `t220.core`: the value function equals `f` (via `fw.value_eq_of_isLeast`). -/
theorem t220_core_valueFun {n : ℕ} {L : Type} [Fintype L] {K : L → Type} [∀ l, Fintype (K l)]
    (p : L → MvPolynomial (Fin n) ℝ) (R : (l : L) → K l → MvPolynomial (Fin n) ℝ)
    (f : (Fin n → ℝ) → ℝ)
    (hf : ∀ x, IsLeast {r | ∃ l, (∀ k, 0 ≤ MvPolynomial.eval x (R l k)) ∧ r = MvPolynomial.eval x (p l)}
      (f x)) :
    ∃ (ι : Type) (_ : Fintype ι) (P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ) (a b : ι → ℝ),
      IsPolyFun P ∧ IsPolyFun Q ∧ ConvexLower Q ∧ (∀ i, a i ≤ b i) ∧
      ∀ x, valueFun P Q (boundedBox a b) x = (f x : EReal) := by
  obtain ⟨ι, hι, P, Q, a, b, hP, hQ, hc, hab, hl⟩ := t220_core p R f hf
  exact ⟨ι, hι, P, Q, a, b, hP, hQ, hc, hab, fun x => valueFun_eq_of_isLeast (hl x)⟩

/-! ### t220.D_closed, t220.D_sa -/

/-- `t220.D_closed`: for lsc `f` and a polynomial `q`, `{f ≤ q}` is closed. -/
theorem t220_D_closed {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : LowerSemicontinuous f)
    (q : MvPolynomial (Fin n) ℝ) : IsClosed {x | f x ≤ eval x q} := by
  have h := (lowerSemicontinuous_sub_poly hf q).isClosed_preimage 0
  convert h using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic, sub_nonpos]

/-- `t220.D_sa` (set identity), for an arbitrary polynomial `q` in place of `p i`. -/
theorem t220_D_eq_of_poly {n N : ℕ} {S : Fin N → Set (Fin n → ℝ)} {p : Fin N → MvPolynomial (Fin n) ℝ}
    {f : (Fin n → ℝ) → ℝ} (hcov : ⋃ i, S i = Set.univ) (hfS : ∀ i, ∀ x ∈ S i, f x = eval x (p i))
    (q : MvPolynomial (Fin n) ℝ) :
    {x | f x ≤ eval x q} = ⋃ k, (S k ∩ {x | eval x (p k) ≤ eval x q}) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · intro hx
    have hxu : x ∈ ⋃ i, S i := hcov ▸ Set.mem_univ x
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hxu
    exact ⟨k, hk, (hfS k x hk) ▸ hx⟩
  · rintro ⟨k, hk, hle⟩
    exact (hfS k x hk) ▸ hle

/-- `t220.D_sa` (set identity): `D_i = ⋃_k (S_k ∩ {p_k ≤ p_i})`. -/
theorem t220_D_eq {n N : ℕ} {S : Fin N → Set (Fin n → ℝ)} {p : Fin N → MvPolynomial (Fin n) ℝ}
    {f : (Fin n → ℝ) → ℝ} (hcov : ⋃ i, S i = Set.univ) (hfS : ∀ i, ∀ x ∈ S i, f x = eval x (p i))
    (i : Fin N) :
    {x | f x ≤ eval x (p i)} = ⋃ k, (S k ∩ {x | eval x (p k) ≤ eval x (p i)}) :=
  t220_D_eq_of_poly hcov hfS (p i)

/-- `t220.D_sa`: `D_i = {f ≤ p_i}` is semialgebraic (Boolean operations only, no projection). -/
theorem t220_D_sa {n N : ℕ} {S : Fin N → Set (Fin n → ℝ)} {p : Fin N → MvPolynomial (Fin n) ℝ}
    {f : (Fin n → ℝ) → ℝ} (hS : ∀ i, IsSemialgebraic (S i)) (hcov : ⋃ i, S i = Set.univ)
    (hfS : ∀ i, ∀ x ∈ S i, f x = eval x (p i)) (i : Fin N) :
    IsSemialgebraic {x | f x ≤ eval x (p i)} := by
  rw [t220_D_eq hcov hfS i]
  exact isSemialgebraic_iUnion fun k => (hS k).inter (isSemialgebraic_eval_le (p k) (p i))

/-! ### Bridge from a piecewise-polynomial presentation (blueprint `t220.supset` (c)–(e)) -/

/-- `t220.supset` step (d): if each `D_i = {f ≤ p_i}` is presented as a finite union of closed basic sets
`⋂_k {R_ijk ≥ 0}`, the flattened family `L = Σ i, Fin (J i)` satisfies the hypothesis of `t220_core`.
(No lsc and no semialgebraicity needed here.) -/
theorem t220_isLeast_of_presentation {n N : ℕ} {S : Fin N → Set (Fin n → ℝ)}
    {p : Fin N → MvPolynomial (Fin n) ℝ} {f : (Fin n → ℝ) → ℝ} (hcov : ⋃ i, S i = Set.univ)
    (hfS : ∀ i, ∀ x ∈ S i, f x = eval x (p i)) (J : Fin N → ℕ) (K : (i : Fin N) → Fin (J i) → ℕ)
    (R : (i : Fin N) → (j : Fin (J i)) → Fin (K i j) → MvPolynomial (Fin n) ℝ)
    (hB : ∀ i, {x | f x ≤ eval x (p i)} = ⋃ j, ⋂ k, {x | 0 ≤ eval x (R i j k)}) :
    ∀ x, IsLeast {r | ∃ l : (Σ i, Fin (J i)), (∀ k : Fin (K l.1 l.2), 0 ≤ eval x (R l.1 l.2 k)) ∧
      r = eval x (p l.1)} (f x) := by
  intro x
  have hxu : x ∈ ⋃ i, S i := hcov ▸ Set.mem_univ x
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.1 hxu
  have hfx : f x = eval x (p i₀) := hfS i₀ x hi₀
  have hD : x ∈ {x | f x ≤ eval x (p i₀)} := le_of_eq hfx
  rw [hB i₀] at hD
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hD
  refine ⟨⟨⟨i₀, j⟩, fun k => Set.mem_iInter.1 hj k, hfx⟩, ?_⟩
  rintro r ⟨⟨i, j'⟩, hk, rfl⟩
  have hx : x ∈ ⋃ j, ⋂ k, {x | 0 ≤ eval x (R i j k)} :=
    Set.mem_iUnion.2 ⟨j', Set.mem_iInter.2 hk⟩
  rw [← hB i] at hx
  exact hx

/-- `t220.supset` steps (d)–(e), packaged: from a piecewise-polynomial presentation of `f` together with a
closed-basic presentation of every `D_i = {f ≤ p_i}`, `f` is the value function of a polynomial bilevel problem
with convex lower level over a bounded box. -/
theorem t220_of_presentations {n N : ℕ} {S : Fin N → Set (Fin n → ℝ)}
    {p : Fin N → MvPolynomial (Fin n) ℝ} {f : (Fin n → ℝ) → ℝ} (hcov : ⋃ i, S i = Set.univ)
    (hfS : ∀ i, ∀ x ∈ S i, f x = eval x (p i)) (J : Fin N → ℕ) (K : (i : Fin N) → Fin (J i) → ℕ)
    (R : (i : Fin N) → (j : Fin (J i)) → Fin (K i j) → MvPolynomial (Fin n) ℝ)
    (hB : ∀ i, {x | f x ≤ eval x (p i)} = ⋃ j, ⋂ k, {x | 0 ≤ eval x (R i j k)}) :
    ∃ (ι : Type) (_ : Fintype ι) (P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ) (a b : ι → ℝ),
      IsPolyFun P ∧ IsPolyFun Q ∧ ConvexLower Q ∧ (∀ i, a i ≤ b i) ∧
      ∀ x, valueFun P Q (boundedBox a b) x = (f x : EReal) :=
  t220_core_valueFun (L := Σ i, Fin (J i)) (K := fun l => Fin (K l.1 l.2)) (fun l => p l.1)
    (fun l k => R l.1 l.2 k) f (t220_isLeast_of_presentation hcov hfS J K R hB)

/-- Class form of `t220_of_presentations`: `f ∈ 𝒞_bounded` (as an `EReal`-valued function). -/
theorem t220_mem_C_bounded_of_presentations {n N : ℕ} {S : Fin N → Set (Fin n → ℝ)}
    {p : Fin N → MvPolynomial (Fin n) ℝ} {f : (Fin n → ℝ) → ℝ} (hcov : ⋃ i, S i = Set.univ)
    (hfS : ∀ i, ∀ x ∈ S i, f x = eval x (p i)) (J : Fin N → ℕ) (K : (i : Fin N) → Fin (J i) → ℕ)
    (R : (i : Fin N) → (j : Fin (J i)) → Fin (K i j) → MvPolynomial (Fin n) ℝ)
    (hB : ∀ i, {x | f x ≤ eval x (p i)} = ⋃ j, ⋂ k, {x | 0 ≤ eval x (R i j k)}) :
    coeFun f ∈ C_bounded n := by
  obtain ⟨ι, hι, P, Q, a, b, hP, hQ, hc, hab, hv⟩ := t220_of_presentations hcov hfS J K R hB
  exact ⟨ι, hι, P, Q, boundedBox a b, hP, hQ, ⟨a, b, hab, rfl⟩, hc, funext fun x => (hv x).symm⟩

/-! ### t220.eq13 (optional) -/

/-- `t220.eq13` (paper eq. (13)): for lsc `f` equal to the continuous `P_i` on `S_i` (a cover), `f(x)` is the
least of the `P_i(x)` over the pieces whose closure contains `x`. -/
theorem t220_eq13 {n N : ℕ} {S : Fin N → Set (Fin n → ℝ)} {P : Fin N → (Fin n → ℝ) → ℝ}
    {f : (Fin n → ℝ) → ℝ} (hf : LowerSemicontinuous f) (hP : ∀ i, Continuous (P i))
    (hcov : ⋃ i, S i = Set.univ) (hfS : ∀ i, ∀ x ∈ S i, f x = P i x) (x : Fin n → ℝ) :
    IsLeast {r | ∃ i, x ∈ closure (S i) ∧ r = P i x} (f x) := by
  have hxu : x ∈ ⋃ i, S i := hcov ▸ Set.mem_univ x
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.1 hxu
  refine ⟨⟨i₀, subset_closure hi₀, hfS i₀ x hi₀⟩, ?_⟩
  rintro r ⟨i, hcl, rfl⟩
  by_contra hlt
  push Not at hlt
  set m := (P i x + f x) / 2 with hm
  have h1 : ∀ᶠ x' in nhds x, m < f x' := hf x m (by rw [hm]; linarith)
  have h2 : ∀ᶠ x' in nhds x, P i x' < m :=
    (hP i).continuousAt.eventually_lt continuousAt_const (by rw [hm]; linarith)
  obtain ⟨x', hx'S, hx'1, hx'2⟩ :=
    ((mem_closure_iff_frequently.1 hcl).and_eventually (h1.and h2)).exists
  have := hfS i x' hx'S
  linarith

/-- Corollary of `t220.eq13`: the closure index set `I(x)` is nonempty. -/
theorem t220_eq13_nonempty {n N : ℕ} {S : Fin N → Set (Fin n → ℝ)} (hcov : ⋃ i, S i = Set.univ)
    (x : Fin n → ℝ) : ∃ i, x ∈ closure (S i) := by
  have hxu : x ∈ ⋃ i, S i := hcov ▸ Set.mem_univ x
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.1 hxu
  exact ⟨i₀, subset_closure hi₀⟩

end Bilevel
