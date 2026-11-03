import Mathlib

/-!
# Polynomial functions on `(Fin n → ℝ) × (ι → ℝ)`

Blueprint §2.1, §4.A.1 (`IsPolyFun`, `polyFun`) and §4.A.4
(`fw.isPolyFun_closure`, `fw.continuous_polyFun`).

A function `F : (Fin n → ℝ) → (ι → ℝ) → ℝ` is *polynomial* (`IsPolyFun F`) if it is the evaluation
of some `p : MvPolynomial (Fin n ⊕ ι) ℝ` at `Sum.elim x y`, using `MvPolynomial.eval` as the only
evaluation encoding.

Provided:
* `IsPolyFun`, `polyFun`, `polyFun_apply`, `isPolyFun_polyFun`, `IsPolyFun.of_eq`.
* `fw.isPolyFun_closure`: `isPolyFun_const`, `isPolyFun_upper` (alias `isPolyFun_x`),
  `isPolyFun_lower` (alias `isPolyFun_y`), `IsPolyFun.add/neg/sub/mul/pow/const_mul/mul_const/
  smul_const`, `isPolyFun_finset_sum`, `isPolyFun_finset_prod`, `IsPolyFun.of_upper_only`,
  `IsPolyFun.of_lower_only`, the general substitution `IsPolyFun.comp` (via `MvPolynomial.bind₁`),
  its special cases `IsPolyFun.comp_upper`, `IsPolyFun.comp_upper_poly`, `IsPolyFun.comp_lower`, and
  relabelling of the lower variables `IsPolyFun.rename` (any map `e : ι → ι'`),
  `IsPolyFun.rename_equiv`.
* `fw.continuous_polyFun`: `IsPolyFun.continuous_uncurry`, `IsPolyFun.continuous_right`,
  `IsPolyFun.continuous_left`, `continuous_polyFun`.

The identities `Sum.elim x y ∘ Sum.inl = x` and `Sum.elim x y ∘ Sum.inr = y` are already the core
simp lemmas `Sum.elim_comp_inl` / `Sum.elim_comp_inr`, so they are not restated.
-/

namespace Bilevel

open MvPolynomial

section Defs

variable {n : ℕ} {ι : Type*}

/-- Polynomial data on `(Fin n → ℝ) × (ι → ℝ)`, the *predicate* form. -/
def IsPolyFun (F : (Fin n → ℝ) → (ι → ℝ) → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n ⊕ ι) ℝ, ∀ x y, F x y = MvPolynomial.eval (Sum.elim x y) p

/-- Witness form: the function defined by a polynomial. -/
noncomputable def polyFun (p : MvPolynomial (Fin n ⊕ ι) ℝ) :
    (Fin n → ℝ) → (ι → ℝ) → ℝ := fun x y => MvPolynomial.eval (Sum.elim x y) p

@[simp]
theorem polyFun_apply (p : MvPolynomial (Fin n ⊕ ι) ℝ) (x : Fin n → ℝ) (y : ι → ℝ) :
    polyFun p x y = MvPolynomial.eval (Sum.elim x y) p := rfl

theorem isPolyFun_polyFun (p : MvPolynomial (Fin n ⊕ ι) ℝ) : IsPolyFun (polyFun p) :=
  ⟨p, fun _ _ => rfl⟩

theorem IsPolyFun.of_eq {F G : (Fin n → ℝ) → (ι → ℝ) → ℝ} (hF : IsPolyFun F)
    (h : ∀ x y, G x y = F x y) : IsPolyFun G := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨p, fun x y => (h x y).trans (hp x y)⟩

theorem isPolyFun_iff_exists_polyFun {F : (Fin n → ℝ) → (ι → ℝ) → ℝ} :
    IsPolyFun F ↔ ∃ p : MvPolynomial (Fin n ⊕ ι) ℝ, F = polyFun p := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, funext fun x => funext fun y => hp x y⟩
  · rintro ⟨p, rfl⟩
    exact isPolyFun_polyFun p

end Defs

/-! ### Closure lemmas (`fw.isPolyFun_closure`) -/

section Closure

variable {n : ℕ} {ι : Type*}

theorem isPolyFun_const (c : ℝ) : IsPolyFun (fun (_ : Fin n → ℝ) (_ : ι → ℝ) => c) :=
  ⟨C c, fun _ _ => by simp⟩

theorem isPolyFun_upper (i : Fin n) : IsPolyFun (fun (x : Fin n → ℝ) (_ : ι → ℝ) => x i) :=
  ⟨X (Sum.inl i), fun _ _ => by simp⟩

theorem isPolyFun_lower (j : ι) : IsPolyFun (fun (_ : Fin n → ℝ) (y : ι → ℝ) => y j) :=
  ⟨X (Sum.inr j), fun _ _ => by simp⟩

/-- Alias of `isPolyFun_upper`. -/
theorem isPolyFun_x (i : Fin n) : IsPolyFun (fun (x : Fin n → ℝ) (_ : ι → ℝ) => x i) :=
  isPolyFun_upper i

/-- Alias of `isPolyFun_lower`. -/
theorem isPolyFun_y (j : ι) : IsPolyFun (fun (_ : Fin n → ℝ) (y : ι → ℝ) => y j) :=
  isPolyFun_lower j

variable {F G : (Fin n → ℝ) → (ι → ℝ) → ℝ}

theorem IsPolyFun.add (hF : IsPolyFun F) (hG : IsPolyFun G) :
    IsPolyFun (fun x y => F x y + G x y) := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hG
  exact ⟨p + q, fun x y => by simp [hp, hq]⟩

theorem IsPolyFun.neg (hF : IsPolyFun F) : IsPolyFun (fun x y => -F x y) := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨-p, fun x y => by simp [hp]⟩

theorem IsPolyFun.sub (hF : IsPolyFun F) (hG : IsPolyFun G) :
    IsPolyFun (fun x y => F x y - G x y) := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hG
  exact ⟨p - q, fun x y => by simp [hp, hq]⟩

theorem IsPolyFun.mul (hF : IsPolyFun F) (hG : IsPolyFun G) :
    IsPolyFun (fun x y => F x y * G x y) := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hG
  exact ⟨p * q, fun x y => by simp [hp, hq]⟩

theorem IsPolyFun.pow (hF : IsPolyFun F) (k : ℕ) : IsPolyFun (fun x y => F x y ^ k) := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨p ^ k, fun x y => by simp [hp]⟩

theorem IsPolyFun.const_mul (hF : IsPolyFun F) (c : ℝ) : IsPolyFun (fun x y => c * F x y) :=
  (isPolyFun_const c).mul hF

theorem IsPolyFun.mul_const (hF : IsPolyFun F) (c : ℝ) : IsPolyFun (fun x y => F x y * c) :=
  hF.mul (isPolyFun_const c)

theorem IsPolyFun.smul_const (hF : IsPolyFun F) (c : ℝ) : IsPolyFun (fun x y => c • F x y) :=
  (hF.const_mul c).of_eq fun _ _ => smul_eq_mul _ _

theorem isPolyFun_finset_sum {κ : Type*} (s : Finset κ)
    {H : κ → (Fin n → ℝ) → (ι → ℝ) → ℝ} (hH : ∀ k ∈ s, IsPolyFun (H k)) :
    IsPolyFun (fun x y => ∑ k ∈ s, H k x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (isPolyFun_const 0).of_eq fun _ _ => by simp
  | insert a s ha ih =>
    have h1 : IsPolyFun (H a) := hH a (Finset.mem_insert_self a s)
    have h2 := ih fun k hk => hH k (Finset.mem_insert_of_mem hk)
    exact (h1.add h2).of_eq fun x y => Finset.sum_insert ha

theorem isPolyFun_finset_prod {κ : Type*} (s : Finset κ)
    {H : κ → (Fin n → ℝ) → (ι → ℝ) → ℝ} (hH : ∀ k ∈ s, IsPolyFun (H k)) :
    IsPolyFun (fun x y => ∏ k ∈ s, H k x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (isPolyFun_const 1).of_eq fun _ _ => by simp
  | insert a s ha ih =>
    have h1 : IsPolyFun (H a) := hH a (Finset.mem_insert_self a s)
    have h2 := ih fun k hk => hH k (Finset.mem_insert_of_mem hk)
    exact (h1.mul h2).of_eq fun x y => Finset.prod_insert ha

/-- A polynomial function of the upper variable alone. -/
theorem IsPolyFun.of_upper_only (q : MvPolynomial (Fin n) ℝ) :
    IsPolyFun (fun (x : Fin n → ℝ) (_ : ι → ℝ) => MvPolynomial.eval x q) :=
  ⟨rename Sum.inl q, fun x y => by rw [eval_rename, Sum.elim_comp_inl]⟩

/-- A polynomial function of the lower variable alone. -/
theorem IsPolyFun.of_lower_only (q : MvPolynomial ι ℝ) :
    IsPolyFun (fun (_ : Fin n → ℝ) (y : ι → ℝ) => MvPolynomial.eval y q) :=
  ⟨rename Sum.inr q, fun x y => by rw [eval_rename, Sum.elim_comp_inr]⟩

/-- Evaluation of `bind₁` (glue lemma: `eval` is `eval₂Hom (RingHom.id _)`). -/
theorem eval_bind₁' {σ τ : Type*} (g : τ → ℝ) (h : σ → MvPolynomial τ ℝ)
    (φ : MvPolynomial σ ℝ) :
    MvPolynomial.eval g (bind₁ h φ) = MvPolynomial.eval (fun i => MvPolynomial.eval g (h i)) φ :=
  eval₂Hom_bind₁ (RingHom.id ℝ) g h φ

/-- General substitution: replace both the upper and the lower variable of a polynomial function
by polynomial functions of new variables `(x', y')`. -/
theorem IsPolyFun.comp {n' : ℕ} {ι' : Type*} (hF : IsPolyFun F)
    {τ : Fin n → (Fin n' → ℝ) → (ι' → ℝ) → ℝ} {σ : ι → (Fin n' → ℝ) → (ι' → ℝ) → ℝ}
    (hτ : ∀ i, IsPolyFun (τ i)) (hσ : ∀ j, IsPolyFun (σ j)) :
    IsPolyFun (fun x' y' => F (fun i => τ i x' y') (fun j => σ j x' y')) := by
  obtain ⟨p, hp⟩ := hF
  choose qτ hqτ using hτ
  choose qσ hqσ using hσ
  refine ⟨bind₁ (Sum.elim qτ qσ) p, fun x' y' => ?_⟩
  show F _ _ = _
  rw [hp, eval_bind₁']
  congr 2
  funext s
  cases s with
  | inl i => simp [hqτ]
  | inr j => simp [hqσ]

/-- Substitution of the upper variable by polynomial functions of a new upper variable `x'`. -/
theorem IsPolyFun.comp_upper {n' : ℕ} (hF : IsPolyFun F) {τ : Fin n → (Fin n' → ℝ) → ℝ}
    (hτ : ∀ i, ∃ q : MvPolynomial (Fin n') ℝ, ∀ x', τ i x' = MvPolynomial.eval x' q) :
    IsPolyFun (fun (x' : Fin n' → ℝ) (y : ι → ℝ) => F (fun i => τ i x') y) := by
  choose q hq using hτ
  refine (hF.comp (τ := fun i x' _ => τ i x') (σ := fun j _ y => y j)
    (fun i => (IsPolyFun.of_upper_only (q i)).of_eq fun x' _ => hq i x')
    (fun j => isPolyFun_lower j)).of_eq fun _ _ => rfl

/-- Substitution of the upper variable by explicit polynomials `q i` in a new upper variable. -/
theorem IsPolyFun.comp_upper_poly {n' : ℕ} (hF : IsPolyFun F) (q : Fin n → MvPolynomial (Fin n') ℝ) :
    IsPolyFun (fun (x' : Fin n' → ℝ) (y : ι → ℝ) => F (fun i => MvPolynomial.eval x' (q i)) y) :=
  hF.comp_upper fun i => ⟨q i, fun _ => rfl⟩

/-- Substitution of the lower variable by polynomial functions of `(x, y')`. -/
theorem IsPolyFun.comp_lower {ι' : Type*} (hF : IsPolyFun F)
    {σ : ι → (Fin n → ℝ) → (ι' → ℝ) → ℝ} (hσ : ∀ j, IsPolyFun (σ j)) :
    IsPolyFun (fun x (y' : ι' → ℝ) => F x (fun j => σ j x y')) :=
  (hF.comp (τ := fun i x _ => x i) (σ := σ) (fun i => isPolyFun_upper i) hσ).of_eq
    fun _ _ => rfl

/-- Relabelling of the lower index type along an arbitrary map `e : ι → ι'`. -/
theorem IsPolyFun.rename {ι' : Type*} (hF : IsPolyFun F) (e : ι → ι') :
    IsPolyFun (fun x (y' : ι' → ℝ) => F x (fun j => y' (e j))) := by
  obtain ⟨p, hp⟩ := hF
  refine ⟨MvPolynomial.rename (Sum.map id e) p, fun x y' => ?_⟩
  show F _ _ = _
  rw [hp, eval_rename]
  congr 2
  funext s
  cases s <;> rfl

/-- Relabelling of the lower index type along an equivalence. -/
theorem IsPolyFun.rename_equiv {ι' : Type*} (hF : IsPolyFun F) (e : ι ≃ ι') :
    IsPolyFun (fun x (y' : ι' → ℝ) => F x (y' ∘ e)) :=
  (hF.rename e).of_eq fun _ _ => rfl

end Closure

/-! ### Continuity (`fw.continuous_polyFun`) -/

section Continuity

variable {n : ℕ} {ι : Type*} {F : (Fin n → ℝ) → (ι → ℝ) → ℝ}

theorem continuous_sumElim_prod :
    Continuous (fun p : (Fin n → ℝ) × (ι → ℝ) => Sum.elim p.1 p.2) := by
  refine continuous_pi fun s => ?_
  cases s with
  | inl i => exact (continuous_apply i).comp continuous_fst
  | inr j => exact (continuous_apply j).comp continuous_snd

theorem IsPolyFun.continuous_uncurry (hF : IsPolyFun F) : Continuous (Function.uncurry F) := by
  obtain ⟨p, hp⟩ := hF
  have h : Function.uncurry F = fun q : (Fin n → ℝ) × (ι → ℝ) =>
      MvPolynomial.eval (Sum.elim q.1 q.2) p := by
    funext q
    exact hp q.1 q.2
  rw [h]
  exact (MvPolynomial.continuous_eval p).comp continuous_sumElim_prod

theorem IsPolyFun.continuous_right (hF : IsPolyFun F) (x : Fin n → ℝ) : Continuous (F x) :=
  hF.continuous_uncurry.comp (Continuous.prodMk_right x)

theorem IsPolyFun.continuous_left (hF : IsPolyFun F) (y : ι → ℝ) :
    Continuous (fun x => F x y) :=
  hF.continuous_uncurry.comp (Continuous.prodMk_left y)

theorem continuous_polyFun (p : MvPolynomial (Fin n ⊕ ι) ℝ) :
    Continuous (Function.uncurry (polyFun p)) :=
  (isPolyFun_polyFun p).continuous_uncurry

end Continuity

end Bilevel
