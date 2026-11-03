# W1-b API: HardnessBilevel/Framework/Poly.lean (namespace Bilevel, imports Mathlib only)

All theorems: #print axioms ⊆ {propext, Classical.choice, Quot.sound}. Core simp lemmas Sum.elim_comp_inl/inr already exist (not restated).

```
@IsPolyFun : {n : ℕ} → {ι : Type u_1} → ((Fin n → ℝ) → (ι → ℝ) → ℝ) → Prop
@polyFun : {n : ℕ} → {ι : Type u_1} → MvPolynomial (Fin n ⊕ ι) ℝ → (Fin n → ℝ) → (ι → ℝ) → ℝ
@polyFun_apply : ∀ {n : ℕ} {ι : Type u_1} (p : MvPolynomial (Fin n ⊕ ι) ℝ) (x : Fin n → ℝ) (y : ι → ℝ),
  polyFun p x y = (MvPolynomial.eval (Sum.elim x y)) p
@isPolyFun_polyFun : ∀ {n : ℕ} {ι : Type u_1} (p : MvPolynomial (Fin n ⊕ ι) ℝ), IsPolyFun (polyFun p)
@IsPolyFun.of_eq : ∀ {n : ℕ} {ι : Type u_1} {F G : (Fin n → ℝ) → (ι → ℝ) → ℝ},
  IsPolyFun F → (∀ (x : Fin n → ℝ) (y : ι → ℝ), G x y = F x y) → IsPolyFun G
@isPolyFun_iff_exists_polyFun : ∀ {n : ℕ} {ι : Type u_1} {F : (Fin n → ℝ) → (ι → ℝ) → ℝ},
  IsPolyFun F ↔ ∃ p, F = polyFun p
@isPolyFun_const : ∀ {n : ℕ} {ι : Type u_1} (c : ℝ), IsPolyFun fun x x_1 => c
@isPolyFun_upper : ∀ {n : ℕ} {ι : Type u_1} (i : Fin n), IsPolyFun fun x x_1 => x i
@isPolyFun_lower : ∀ {n : ℕ} {ι : Type u_1} (j : ι), IsPolyFun fun x y => y j
@isPolyFun_x : ∀ {n : ℕ} {ι : Type u_1} (i : Fin n), IsPolyFun fun x x_1 => x i
@isPolyFun_y : ∀ {n : ℕ} {ι : Type u_1} (j : ι), IsPolyFun fun x y => y j
@IsPolyFun.add : ∀ {n : ℕ} {ι : Type u_1} {F G : (Fin n → ℝ) → (ι → ℝ) → ℝ},
  IsPolyFun F → IsPolyFun G → IsPolyFun fun x y => F x y + G x y
@IsPolyFun.neg : ∀ {n : ℕ} {ι : Type u_1} {F : (Fin n → ℝ) → (ι → ℝ) → ℝ}, IsPolyFun F → IsPolyFun fun x y => -F x y
@IsPolyFun.sub : ∀ {n : ℕ} {ι : Type u_1} {F G : (Fin n → ℝ) → (ι → ℝ) → ℝ},
  IsPolyFun F → IsPolyFun G → IsPolyFun fun x y => F x y - G x y
@IsPolyFun.mul : ∀ {n : ℕ} {ι : Type u_1} {F G : (Fin n → ℝ) → (ι → ℝ) → ℝ},
  IsPolyFun F → IsPolyFun G → IsPolyFun fun x y => F x y * G x y
@IsPolyFun.pow : ∀ {n : ℕ} {ι : Type u_1} {F : (Fin n → ℝ) → (ι → ℝ) → ℝ},
  IsPolyFun F → ∀ (k : ℕ), IsPolyFun fun x y => F x y ^ k
@IsPolyFun.const_mul : ∀ {n : ℕ} {ι : Type u_1} {F : (Fin n → ℝ) → (ι → ℝ) → ℝ},
  IsPolyFun F → ∀ (c : ℝ), IsPolyFun fun x y => c * F x y
@IsPolyFun.mul_const : ∀ {n : ℕ} {ι : Type u_1} {F : (Fin n → ℝ) → (ι → ℝ) → ℝ},
  IsPolyFun F → ∀ (c : ℝ), IsPolyFun fun x y => F x y * c
@IsPolyFun.smul_const : ∀ {n : ℕ} {ι : Type u_1} {F : (Fin n → ℝ) → (ι → ℝ) → ℝ},
  IsPolyFun F → ∀ (c : ℝ), IsPolyFun fun x y => c • F x y
@isPolyFun_finset_sum : ∀ {n : ℕ} {ι : Type u_1} {κ : Type u_2} (s : Finset κ) {H : κ → (Fin n → ℝ) → (ι → ℝ) → ℝ},
  (∀ k ∈ s, IsPolyFun (H k)) → IsPolyFun fun x y => ∑ k ∈ s, H k x y
@isPolyFun_finset_prod : ∀ {n : ℕ} {ι : Type u_1} {κ : Type u_2} (s : Finset κ) {H : κ → (Fin n → ℝ) → (ι → ℝ) → ℝ},
  (∀ k ∈ s, IsPolyFun (H k)) → IsPolyFun fun x y => ∏ k ∈ s, H k x y
@IsPolyFun.of_upper_only : ∀ {n : ℕ} {ι : Type u_1} (q : MvPolynomial (Fin n) ℝ),
  IsPolyFun fun x x_1 => (MvPolynomial.eval x) q
@IsPolyFun.of_lower_only : ∀ {n : ℕ} {ι : Type u_1} (q : MvPolynomial ι ℝ), IsPolyFun fun x y => (MvPolynomial.eval y) q
@eval_bind₁' : ∀ {σ : Type u_1} {τ : Type u_2} (g : τ → ℝ) (h : σ → MvPolynomial τ ℝ) (φ : MvPolynomial σ ℝ),
  (MvPolynomial.eval g) ((MvPolynomial.bind₁ h) φ) = (MvPolynomial.eval fun i => (MvPolynomial.eval g) (h i)) φ
@IsPolyFun.comp : ∀ {n : ℕ} {ι : Type u_1} {F : (Fin n → ℝ) → (ι → ℝ) → ℝ} {n' : ℕ} {ι' : Type u_2},
  IsPolyFun F →
    ∀ {τ : Fin n → (Fin n' → ℝ) → (ι' → ℝ) → ℝ} {σ : ι → (Fin n' → ℝ) → (ι' → ℝ) → ℝ},
      (∀ (i : Fin n), IsPolyFun (τ i)) →
        (∀ (j : ι), IsPolyFun (σ j)) → IsPolyFun fun x' y' => F (fun i => τ i x' y') fun j => σ j x' y'
@IsPolyFun.comp_upper : ∀ {n : ℕ} {ι : Type u_1} {F : (Fin n → ℝ) → (ι → ℝ) → ℝ} {n' : ℕ},
  IsPolyFun F →
    ∀ {τ : Fin n → (Fin n' → ℝ) → ℝ},
      (∀ (i : Fin n), ∃ q, ∀ (x' : Fin n' → ℝ), τ i x' = (MvPolynomial.eval x') q) →
        IsPolyFun fun x' y => F (fun i => τ i x') y
@IsPolyFun.comp_upper_poly : ∀ {n : ℕ} {ι : Type u_1} {F : (Fin n → ℝ) → (ι → ℝ) → ℝ} {n' : ℕ},
  IsPolyFun F →
    ∀ (q : Fin n → MvPolynomial (Fin n') ℝ), IsPolyFun fun x' y => F (fun i => (MvPolynomial.eval x') (q i)) y
@IsPolyFun.comp_lower : ∀ {n : ℕ} {ι : Type u_1} {F : (Fin n → ℝ) → (ι → ℝ) → ℝ} {ι' : Type u_2},
  IsPolyFun F →
    ∀ {σ : ι → (Fin n → ℝ) → (ι' → ℝ) → ℝ}, (∀ (j : ι), IsPolyFun (σ j)) → IsPolyFun fun x y' => F x fun j => σ j x y'
@IsPolyFun.rename : ∀ {n : ℕ} {ι : Type u_1} {F : (Fin n → ℝ) → (ι → ℝ) → ℝ} {ι' : Type u_2},
  IsPolyFun F → ∀ (e : ι → ι'), IsPolyFun fun x y' => F x fun j => y' (e j)
@IsPolyFun.rename_equiv : ∀ {n : ℕ} {ι : Type u_1} {F : (Fin n → ℝ) → (ι → ℝ) → ℝ} {ι' : Type u_2},
  IsPolyFun F → ∀ (e : ι ≃ ι'), IsPolyFun fun x y' => F x (y' ∘ ⇑e)
@continuous_sumElim_prod : ∀ {n : ℕ} {ι : Type u_1}, Continuous fun p => Sum.elim p.1 p.2
@IsPolyFun.continuous_uncurry : ∀ {n : ℕ} {ι : Type u_1} {F : (Fin n → ℝ) → (ι → ℝ) → ℝ},
  IsPolyFun F → Continuous (Function.uncurry F)
@IsPolyFun.continuous_right : ∀ {n : ℕ} {ι : Type u_1} {F : (Fin n → ℝ) → (ι → ℝ) → ℝ},
  IsPolyFun F → ∀ (x : Fin n → ℝ), Continuous (F x)
@IsPolyFun.continuous_left : ∀ {n : ℕ} {ι : Type u_1} {F : (Fin n → ℝ) → (ι → ℝ) → ℝ},
  IsPolyFun F → ∀ (y : ι → ℝ), Continuous fun x => F x y
@continuous_polyFun : ∀ {n : ℕ} {ι : Type u_1} (p : MvPolynomial (Fin n ⊕ ι) ℝ),
  Continuous (Function.uncurry (polyFun p))
```
