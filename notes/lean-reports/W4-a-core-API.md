# W4-a-core API: HardnessBilevel/Bounded/Thm215Core.lean (namespace Bilevel)

Imports: Framework.Basic, Framework.Box, Framework.Poly, Gadgets.Box. No assumption classes. All #print axioms = [propext, Classical.choice, Quot.sound].
Defs: sumBox Z = {y | y (inl ()) ∈ Icc (-1) 1 ∧ y ∘ inr ∈ Z}; t215Lo = Sum.elim (fun _ => -1) (fun _ => 0); t215Hi = Sum.elim (fun _ => 1) (fun _ => 1/2) (noncomputable); rescaledPoly wq q x t = eval (Sum.elim x (fun _ => t * eval x wq)) q (noncomputable).

```
@Bilevel.t215_core_gen : ∀ {X : Type u_1} {Θ : Type u_2} (f w : X → ℝ),
  (∀ (x : X), 0 < w x) →
    (∀ (x : X), |f x| ≤ w x) →
      ∀ (E : X → ℝ → Prop),
        (∀ (x : X), E x (f x)) →
          (∀ (x : X) (τ : ℝ), E x τ → f x ≤ τ) →
            ∀ (S : Set Θ) (T : Θ → ℝ) (R : X → Θ → ℝ),
              (∀ (x : X) (θ : Θ), 0 ≤ R x θ) →
                (∀ (x : X), ∀ θ ∈ S, R x θ = 0 → E x (T θ * w x)) →
                  (∀ (x : X), ∀ t ∈ Set.Icc (-1) 1, E x (t * w x) → ∃ θ ∈ S, T θ = t ∧ R x θ = 0) →
                    ∀ (x : X), IsLeast ((fun θ => T θ * w x) '' Bilevel.argminSet R S x) (f x)
@Bilevel.t215_core_isLeast : ∀ {n : ℕ} {ζ : Type} (f w : (Fin n → ℝ) → ℝ),
  (∀ (x : Fin n → ℝ), 0 < w x) →
    (∀ (x : Fin n → ℝ), |f x| ≤ w x) →
      ∀ (E : (Fin n → ℝ) → ℝ → Prop),
        (∀ (x : Fin n → ℝ), E x (f x)) →
          (∀ (x : Fin n → ℝ) (τ : ℝ), E x τ → f x ≤ τ) →
            ∀ (Z : Set (ζ → ℝ)) (R : (Fin n → ℝ) → ℝ → (ζ → ℝ) → ℝ),
              (∀ (x : Fin n → ℝ) (t : ℝ) (z : ζ → ℝ), 0 ≤ R x t z) →
                (∀ (x : Fin n → ℝ) (t : ℝ), E x (t * w x) ↔ ∃ z ∈ Z, R x t z = 0) →
                  ∀ (x : Fin n → ℝ),
                    IsLeast ((fun y => y.1 * w x) '' Bilevel.argminSet (fun x y => R x y.1 y.2) (Set.Icc (-1) 1 ×ˢ Z) x)
                      (f x)
@Bilevel.sumBox : {ζ : Type} → Set (ζ → ℝ) → Set (Unit ⊕ ζ → ℝ)
@Bilevel.t215Lo : {ζ : Type u_1} → Unit ⊕ ζ → ℝ
@Bilevel.t215Hi : {ζ : Type u_1} → Unit ⊕ ζ → ℝ
@Bilevel.t215Lo_le_t215Hi : ∀ {ζ : Type u_1} (k : Unit ⊕ ζ), Bilevel.t215Lo k ≤ Bilevel.t215Hi k
@Bilevel.sumBox_gadgetBox : ∀ {α β : Type},
  Bilevel.sumBox (Bilevel.gadgetBox α β) = Bilevel.boundedBox Bilevel.t215Lo Bilevel.t215Hi
@Bilevel.isClosed_epigraph_sum : ∀ {n : ℕ} {f : (Fin n → ℝ) → ℝ},
  LowerSemicontinuous f → IsClosed {z | f (z ∘ Sum.inl) ≤ z (Sum.inr ())}
@Bilevel.rescaledPoly : {n : ℕ} → MvPolynomial (Fin n) ℝ → MvPolynomial (Fin n ⊕ Unit) ℝ → (Fin n → ℝ) → ℝ → ℝ
@Bilevel.isPolyFun_rescaledPoly : ∀ {n : ℕ} (wq : MvPolynomial (Fin n) ℝ) (q : MvPolynomial (Fin n ⊕ Unit) ℝ),
  Bilevel.IsPolyFun fun x t => Bilevel.rescaledPoly wq q x (t ())
@Bilevel.exists_rescaledPoly_iff : ∀ {n : ℕ} {α : Type u_1} {β : Type u_2} (wq : MvPolynomial (Fin n) ℝ)
  (p : α → β → MvPolynomial (Fin n ⊕ Unit) ℝ) (x : Fin n → ℝ) (t : ℝ),
  (∃ i, ∀ (j : β), 0 ≤ (MvPolynomial.eval (Sum.elim x fun x_1 => t * (MvPolynomial.eval x) wq)) (p i j)) ↔
    ∃ i, ∀ (j : β), 0 ≤ Bilevel.rescaledPoly wq (p i j) x t

-- plus:
@Bilevel.t215_core_gen_value : same hypotheses as t215_core_gen, conclusion valueFun (fun x θ => T θ * w x) R S x = ↑(f x)
```
@Bilevel.t215_core : ∀ {n : ℕ} {ζ : Type} (f w : (Fin n → ℝ) → ℝ),
  (∀ (x : Fin n → ℝ), 0 < w x) →
    (∀ (x : Fin n → ℝ), |f x| ≤ w x) →
      ∀ (E : (Fin n → ℝ) → ℝ → Prop),
        (∀ (x : Fin n → ℝ), E x (f x)) →
          (∀ (x : Fin n → ℝ) (τ : ℝ), E x τ → f x ≤ τ) →
            ∀ (Z : Set (ζ → ℝ)) (R : (Fin n → ℝ) → ℝ → (ζ → ℝ) → ℝ),
              (∀ (x : Fin n → ℝ) (t : ℝ) (z : ζ → ℝ), 0 ≤ R x t z) →
                (∀ (x : Fin n → ℝ) (t : ℝ), E x (t * w x) ↔ ∃ z ∈ Z, R x t z = 0) →
                  ∀ (x : Fin n → ℝ),
                    Bilevel.valueFun (fun x y => y.1 * w x) (fun x y => R x y.1 y.2) (Set.Icc (-1) 1 ×ˢ Z) x = ↑(f x)
@Bilevel.t215_core_sum : ∀ {n : ℕ} {ζ : Type} (f w : (Fin n → ℝ) → ℝ),
  (∀ (x : Fin n → ℝ), 0 < w x) →
    (∀ (x : Fin n → ℝ), |f x| ≤ w x) →
      ∀ (E : (Fin n → ℝ) → ℝ → Prop),
        (∀ (x : Fin n → ℝ), E x (f x)) →
          (∀ (x : Fin n → ℝ) (τ : ℝ), E x τ → f x ≤ τ) →
            ∀ (Z : Set (ζ → ℝ)) (R : (Fin n → ℝ) → ℝ → (ζ → ℝ) → ℝ),
              (∀ (x : Fin n → ℝ) (t : ℝ) (z : ζ → ℝ), 0 ≤ R x t z) →
                (∀ (x : Fin n → ℝ) (t : ℝ), E x (t * w x) ↔ ∃ z ∈ Z, R x t z = 0) →
                  ∀ (x : Fin n → ℝ),
                    Bilevel.valueFun (fun x y => y (Sum.inl ()) * w x) (fun x y => R x (y (Sum.inl ())) (y ∘ Sum.inr))
                        (Bilevel.sumBox Z) x =
                      ↑(f x)
@Bilevel.thm215_of_presentation : ∀ {n : ℕ} (f : (Fin n → ℝ) → ℝ) (wq : MvPolynomial (Fin n) ℝ),
  (∀ (x : Fin n → ℝ), 0 < (MvPolynomial.eval x) wq) →
    (∀ (x : Fin n → ℝ), |f x| ≤ (MvPolynomial.eval x) wq) →
      ∀ {α β : Type} [Fintype α] [Fintype β] (p : α → β → MvPolynomial (Fin n ⊕ Unit) ℝ),
        (∀ (x : Fin n → ℝ), ∃ i, ∀ (j : β), 0 ≤ (MvPolynomial.eval (Sum.elim x fun x_1 => f x)) (p i j)) →
          (∀ (x : Fin n → ℝ) (τ : ℝ),
              (∃ i, ∀ (j : β), 0 ≤ (MvPolynomial.eval (Sum.elim x fun x => τ)) (p i j)) → f x ≤ τ) →
            ∃ ι x P Q a b,
              Bilevel.IsPolyFun P ∧
                Bilevel.IsPolyFun Q ∧
                  (∀ (k : ι), a k ≤ b k) ∧ ∀ (x : Fin n → ℝ), Bilevel.valueFun P Q (Bilevel.boundedBox a b) x = ↑(f x)
