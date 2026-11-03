# W2-d API: HardnessBilevel/Semialgebraic/Basic.lean (namespace Bilevel; open MeasureTheory Function)

```lean
@IsSemialgebraic : {ι : Type u_1} → Set (ι → ℝ) → Prop
@IsBasicSA : {ι : Type u_1} → Set (ι → ℝ) → Prop
@graphSet : {ι : Type u_1} → ((ι → ℝ) → ℝ) → Set (ι ⊕ Unit → ℝ)
@IsSemialgebraicMap : {ι : Type u_1} → ((ι → ℝ) → ℝ) → Prop
@mem_graphSet : ∀ {ι : Type u_1} {f : (ι → ℝ) → ℝ} {z : ι ⊕ Unit → ℝ}, z ∈ graphSet f ↔ f (z ∘ Sum.inl) = z (Sum.inr ())
@isSemialgebraic_eval_eq_zero : ∀ {ι : Type u_1} (p : MvPolynomial ι ℝ),
  IsSemialgebraic {x | (MvPolynomial.eval x) p = 0}
@isSemialgebraic_eval_pos : ∀ {ι : Type u_1} (p : MvPolynomial ι ℝ), IsSemialgebraic {x | 0 < (MvPolynomial.eval x) p}
@IsSemialgebraic.of_eq : ∀ {ι : Type u_1} {s t : Set (ι → ℝ)}, IsSemialgebraic s → s = t → IsSemialgebraic t
@isSemialgebraic_empty : ∀ {ι : Type u_1}, IsSemialgebraic ∅
@isSemialgebraic_univ : ∀ {ι : Type u_1}, IsSemialgebraic Set.univ
@IsSemialgebraic.compl : ∀ {ι : Type u_1} {s : Set (ι → ℝ)}, IsSemialgebraic s → IsSemialgebraic sᶜ
@IsSemialgebraic.union : ∀ {ι : Type u_1} {s t : Set (ι → ℝ)},
  IsSemialgebraic s → IsSemialgebraic t → IsSemialgebraic (s ∪ t)
@IsSemialgebraic.inter : ∀ {ι : Type u_1} {s t : Set (ι → ℝ)},
  IsSemialgebraic s → IsSemialgebraic t → IsSemialgebraic (s ∩ t)
@IsSemialgebraic.sdiff : ∀ {ι : Type u_1} {s t : Set (ι → ℝ)},
  IsSemialgebraic s → IsSemialgebraic t → IsSemialgebraic (s \ t)
@isSemialgebraic_compl_iff : ∀ {ι : Type u_1} {s : Set (ι → ℝ)}, IsSemialgebraic sᶜ ↔ IsSemialgebraic s
@isSemialgebraic_biUnion : ∀ {ι : Type u_1} {κ : Type u_2} (S : Finset κ) {s : κ → Set (ι → ℝ)},
  (∀ i ∈ S, IsSemialgebraic (s i)) → IsSemialgebraic (⋃ i ∈ S, s i)
@isSemialgebraic_biInter : ∀ {ι : Type u_1} {κ : Type u_2} (S : Finset κ) {s : κ → Set (ι → ℝ)},
  (∀ i ∈ S, IsSemialgebraic (s i)) → IsSemialgebraic (⋂ i ∈ S, s i)
@isSemialgebraic_iUnion : ∀ {ι : Type u_1} {κ : Type u_2} [Finite κ] {s : κ → Set (ι → ℝ)},
  (∀ (i : κ), IsSemialgebraic (s i)) → IsSemialgebraic (⋃ i, s i)
@isSemialgebraic_iInter : ∀ {ι : Type u_1} {κ : Type u_2} [Finite κ] {s : κ → Set (ι → ℝ)},
  (∀ (i : κ), IsSemialgebraic (s i)) → IsSemialgebraic (⋂ i, s i)
@isSemialgebraic_setOf_and : ∀ {ι : Type u_1} {p q : (ι → ℝ) → Prop},
  IsSemialgebraic {x | p x} → IsSemialgebraic {x | q x} → IsSemialgebraic {x | p x ∧ q x}
@isSemialgebraic_setOf_or : ∀ {ι : Type u_1} {p q : (ι → ℝ) → Prop},
  IsSemialgebraic {x | p x} → IsSemialgebraic {x | q x} → IsSemialgebraic {x | p x ∨ q x}
@isSemialgebraic_setOf_not : ∀ {ι : Type u_1} {p : (ι → ℝ) → Prop},
  IsSemialgebraic {x | p x} → IsSemialgebraic {x | ¬p x}
@isSemialgebraic_setOf_forall : ∀ {ι : Type u_1} {κ : Type u_2} [Finite κ] {p : κ → (ι → ℝ) → Prop},
  (∀ (i : κ), IsSemialgebraic {x | p i x}) → IsSemialgebraic {x | ∀ (i : κ), p i x}
@isSemialgebraic_setOf_exists : ∀ {ι : Type u_1} {κ : Type u_2} [Finite κ] {p : κ → (ι → ℝ) → Prop},
  (∀ (i : κ), IsSemialgebraic {x | p i x}) → IsSemialgebraic {x | ∃ i, p i x}
@isSemialgebraic_eval_ne_zero : ∀ {ι : Type u_1} (p : MvPolynomial ι ℝ),
  IsSemialgebraic {x | (MvPolynomial.eval x) p ≠ 0}
@isSemialgebraic_eval_neg : ∀ {ι : Type u_1} (p : MvPolynomial ι ℝ), IsSemialgebraic {x | (MvPolynomial.eval x) p < 0}
@isSemialgebraic_eval_nonneg : ∀ {ι : Type u_1} (p : MvPolynomial ι ℝ),
  IsSemialgebraic {x | 0 ≤ (MvPolynomial.eval x) p}
@isSemialgebraic_eval_nonpos : ∀ {ι : Type u_1} (p : MvPolynomial ι ℝ),
  IsSemialgebraic {x | (MvPolynomial.eval x) p ≤ 0}
@isSemialgebraic_eval_lt : ∀ {ι : Type u_1} (p q : MvPolynomial ι ℝ),
  IsSemialgebraic {x | (MvPolynomial.eval x) p < (MvPolynomial.eval x) q}
@isSemialgebraic_eval_le : ∀ {ι : Type u_1} (p q : MvPolynomial ι ℝ),
  IsSemialgebraic {x | (MvPolynomial.eval x) p ≤ (MvPolynomial.eval x) q}
@isSemialgebraic_eval_eq : ∀ {ι : Type u_1} (p q : MvPolynomial ι ℝ),
  IsSemialgebraic {x | (MvPolynomial.eval x) p = (MvPolynomial.eval x) q}
@isSemialgebraic_eval_ne : ∀ {ι : Type u_1} (p q : MvPolynomial ι ℝ),
  IsSemialgebraic {x | (MvPolynomial.eval x) p ≠ (MvPolynomial.eval x) q}
@isSemialgebraic_sign_eval_eq : ∀ {ι : Type u_1} (p : MvPolynomial ι ℝ) (σ : SignType),
  IsSemialgebraic {x | SignType.sign ((MvPolynomial.eval x) p) = σ}
@IsSemialgebraic.exists_sign_normal_form : ∀ {ι : Type u_1} {s : Set (ι → ℝ)},
  IsSemialgebraic s → ∃ m p Φ, s = {x | Φ fun i => SignType.sign ((MvPolynomial.eval x) (p i))}
@signCell : {ι : Type u_1} → {m : ℕ} → (Fin m → MvPolynomial ι ℝ) → (Fin m → SignType) → Set (ι → ℝ)
@isSemialgebraic_signCell : ∀ {ι : Type u_1} {m : ℕ} (p : Fin m → MvPolynomial ι ℝ) (σ : Fin m → SignType),
  IsSemialgebraic (signCell p σ)
@disjoint_signCell : ∀ {ι : Type u_1} {m : ℕ} (p : Fin m → MvPolynomial ι ℝ) {σ τ : Fin m → SignType},
  σ ≠ τ → Disjoint (signCell p σ) (signCell p τ)
@iUnion_signCell : ∀ {ι : Type u_1} {m : ℕ} (p : Fin m → MvPolynomial ι ℝ), ⋃ σ, signCell p σ = Set.univ
@setOf_sign_eq_iUnion_signCell : ∀ {ι : Type u_1} {m : ℕ} (p : Fin m → MvPolynomial ι ℝ)
  (Φ : (Fin m → SignType) → Prop), {x | Φ fun i => SignType.sign ((MvPolynomial.eval x) (p i))} = ⋃ σ, signCell p ↑σ
@isSemialgebraic_setOf_sign : ∀ {ι : Type u_1} {m : ℕ} (p : Fin m → MvPolynomial ι ℝ) (Φ : (Fin m → SignType) → Prop),
  IsSemialgebraic {x | Φ fun i => SignType.sign ((MvPolynomial.eval x) (p i))}
@isSemialgebraic_iff_sign_normal_form : ∀ {ι : Type u_1} {s : Set (ι → ℝ)},
  IsSemialgebraic s ↔ ∃ m p Φ, s = {x | Φ fun i => SignType.sign ((MvPolynomial.eval x) (p i))}
@cellP : {ι : Type u_1} → {m : ℕ} → (Fin m → MvPolynomial ι ℝ) → (Fin m → SignType) → MvPolynomial ι ℝ
@cellQ : {ι : Type u_1} → {m : ℕ} → (Fin m → MvPolynomial ι ℝ) → (Fin m → SignType) → Fin m → MvPolynomial ι ℝ
@signCell_eq_basic : ∀ {ι : Type u_1} {m : ℕ} (p : Fin m → MvPolynomial ι ℝ) (σ : Fin m → SignType),
  signCell p σ = {x | (MvPolynomial.eval x) (cellP p σ) = 0 ∧ ∀ (i : Fin m), 0 < (MvPolynomial.eval x) (cellQ p σ i)}
@isBasicSA_signCell : ∀ {ι : Type u_1} {m : ℕ} (p : Fin m → MvPolynomial ι ℝ) (σ : Fin m → SignType),
  IsBasicSA (signCell p σ)
@isSemialgebraic_basic : ∀ {ι : Type u_1} (P : MvPolynomial ι ℝ) {k : ℕ} (Q : Fin k → MvPolynomial ι ℝ),
  IsSemialgebraic {x | (MvPolynomial.eval x) P = 0 ∧ ∀ (j : Fin k), 0 < (MvPolynomial.eval x) (Q j)}
@isBasicSA_isSemialgebraic : ∀ {ι : Type u_1} {s : Set (ι → ℝ)}, IsBasicSA s → IsSemialgebraic s
@IsSemialgebraic.exists_disjoint_uniform_basic : ∀ {ι : Type u_1} {s : Set (ι → ℝ)},
  IsSemialgebraic s →
    ∃ m k P Q,
      s = ⋃ i, {x | (MvPolynomial.eval x) (P i) = 0 ∧ ∀ (j : Fin k), 0 < (MvPolynomial.eval x) (Q i j)} ∧
        Pairwise
          (Disjoint on fun i =>
            {x | (MvPolynomial.eval x) (P i) = 0 ∧ ∀ (j : Fin k), 0 < (MvPolynomial.eval x) (Q i j)})
@IsSemialgebraic.exists_uniform_basic : ∀ {ι : Type u_1} {s : Set (ι → ℝ)},
  IsSemialgebraic s →
    ∃ m k P Q, s = ⋃ i, {x | (MvPolynomial.eval x) (P i) = 0 ∧ ∀ (j : Fin k), 0 < (MvPolynomial.eval x) (Q i j)}
@isSemialgebraic_iff_uniform_union_basic : ∀ {ι : Type u_1} {s : Set (ι → ℝ)},
  IsSemialgebraic s ↔
    ∃ m k P Q, s = ⋃ i, {x | (MvPolynomial.eval x) (P i) = 0 ∧ ∀ (j : Fin k), 0 < (MvPolynomial.eval x) (Q i j)}
@isSemialgebraic_iff_disjoint_union_basic : ∀ {ι : Type u_1} {s : Set (ι → ℝ)},
  IsSemialgebraic s ↔ ∃ m S, (∀ (i : Fin m), IsBasicSA (S i)) ∧ Pairwise (Disjoint on S) ∧ s = ⋃ i, S i
@isSemialgebraic_iff_finite_union_basic : ∀ {ι : Type u_1} {s : Set (ι → ℝ)},
  IsSemialgebraic s ↔ ∃ m S, (∀ (i : Fin m), IsBasicSA (S i)) ∧ s = ⋃ i, S i
@isSemialgebraic_iff_disjoint_uniform_union_basic : ∀ {ι : Type u_1} {s : Set (ι → ℝ)},
  IsSemialgebraic s ↔
    ∃ m k P Q,
      s = ⋃ i, {x | (MvPolynomial.eval x) (P i) = 0 ∧ ∀ (j : Fin k), 0 < (MvPolynomial.eval x) (Q i j)} ∧
        Pairwise
          (Disjoint on fun i =>
            {x | (MvPolynomial.eval x) (P i) = 0 ∧ ∀ (j : Fin k), 0 < (MvPolynomial.eval x) (Q i j)})
```
