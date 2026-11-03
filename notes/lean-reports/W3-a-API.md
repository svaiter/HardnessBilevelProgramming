# W3-a API: HardnessBilevel/Semialgebraic/Poly.lean and HardnessBilevel/Semialgebraic/Ext.lean (namespace Bilevel)

Poly imports Semialgebraic.Basic, Framework.Poly, Framework.Box; Ext imports Semialgebraic.Poly. Opens: MeasureTheory Function MvPolynomial.
All public declarations: #print axioms ⊆ {propext, Classical.choice, Quot.sound}.
IsExtSemialgebraic is a structure with fields top / bot / graph (as in the blueprint).

```
@IsSemialgebraic.preimage_poly : ∀ {ι : Type u_1} {κ : Type u_2} (F : κ → MvPolynomial ι ℝ) {S : Set (κ → ℝ)},
  IsSemialgebraic S → IsSemialgebraic ((fun x i => (MvPolynomial.eval x) (F i)) ⁻¹' S)
@IsSemialgebraic.preimage_of_poly : ∀ {ι : Type u_1} {κ : Type u_2} {φ : (ι → ℝ) → κ → ℝ} (F : κ → MvPolynomial ι ℝ),
  (∀ (x : ι → ℝ) (i : κ), φ x i = (MvPolynomial.eval x) (F i)) →
    ∀ {S : Set (κ → ℝ)}, IsSemialgebraic S → IsSemialgebraic (φ ⁻¹' S)
@IsSemialgebraic.reindex : ∀ {ι : Type u_1} {κ : Type u_2} (e : ι → κ) {S : Set (ι → ℝ)},
  IsSemialgebraic S → IsSemialgebraic ((fun x => x ∘ e) ⁻¹' S)
@IsSemialgebraic.preimage_equiv : ∀ {ι : Type u_1} {κ : Type u_2} (e : ι ≃ κ) {S : Set (ι → ℝ)},
  IsSemialgebraic S → IsSemialgebraic ((fun x => x ∘ ⇑e) ⁻¹' S)
@IsSemialgebraic.image_equiv : ∀ {ι : Type u_1} {κ : Type u_2} (e : ι ≃ κ) {S : Set (ι → ℝ)},
  IsSemialgebraic S → IsSemialgebraic ((fun x => x ∘ ⇑e.symm) '' S)
@IsSemialgebraic.image_comp_equiv : ∀ {ι : Type u_1} {κ : Type u_2} (e : κ ≃ ι) {S : Set (ι → ℝ)},
  IsSemialgebraic S → IsSemialgebraic ((fun x => x ∘ ⇑e) '' S)
@isSemialgebraic_reindex_equiv_iff : ∀ {ι : Type u_1} {κ : Type u_2} (e : ι ≃ κ) {S : Set (ι → ℝ)},
  IsSemialgebraic ((fun x => x ∘ ⇑e) ⁻¹' S) ↔ IsSemialgebraic S
@isSemialgebraic_cylinder_inl : ∀ {ι : Type u_1} {κ : Type u_2} {S : Set (ι → ℝ)},
  IsSemialgebraic S → IsSemialgebraic {z | z ∘ Sum.inl ∈ S}
@isSemialgebraic_cylinder_inr : ∀ {ι : Type u_1} {κ : Type u_2} {T : Set (κ → ℝ)},
  IsSemialgebraic T → IsSemialgebraic {z | z ∘ Sum.inr ∈ T}
@isSemialgebraic_cylinder : ∀ {ι : Type u_1} {κ : Type u_2} {S : Set (ι → ℝ)} {T : Set (κ → ℝ)},
  IsSemialgebraic S → IsSemialgebraic T → IsSemialgebraic {z | z ∘ Sum.inl ∈ S ∧ z ∘ Sum.inr ∈ T}
@isSemialgebraic_poly_graph : ∀ {ι : Type u_1} {κ : Type u_2} [Finite κ] (G : κ → MvPolynomial ι ℝ),
  IsSemialgebraic {z | ∀ (j : κ), z (Sum.inr j) = (MvPolynomial.eval (z ∘ Sum.inl)) (G j)}
@isSemialgebraicMap_eval : ∀ {ι : Type u_1} (p : MvPolynomial ι ℝ), IsSemialgebraicMap fun x => (MvPolynomial.eval x) p
@isSemialgebraic_const_le_coord : ∀ {ι : Type u_1} (a : ℝ) (i : ι), IsSemialgebraic {x | a ≤ x i}
@isSemialgebraic_coord_le_const : ∀ {ι : Type u_1} (i : ι) (a : ℝ), IsSemialgebraic {x | x i ≤ a}
@isSemialgebraic_coord_eq_const : ∀ {ι : Type u_1} (i : ι) (a : ℝ), IsSemialgebraic {x | x i = a}
@isSemialgebraic_ereal_le_coord : ∀ {ι : Type u_1} (a : EReal) (i : ι), IsSemialgebraic {x | a ≤ ↑(x i)}
@isSemialgebraic_coord_le_ereal : ∀ {ι : Type u_1} (i : ι) (b : EReal), IsSemialgebraic {x | ↑(x i) ≤ b}
@isSemialgebraic_boxSet : ∀ {ι : Type u_1} [Finite ι] (lo hi : ι → EReal), IsSemialgebraic (boxSet lo hi)
@isSemialgebraic_boundedBox : ∀ {ι : Type u_1} [Finite ι] (lo hi : ι → ℝ), IsSemialgebraic (boundedBox lo hi)
@IsBox.isSemialgebraic : ∀ {ι : Type u_1} [Finite ι] {S : Set (ι → ℝ)}, IsBox S → IsSemialgebraic S
@IsBoundedBox.isSemialgebraic : ∀ {ι : Type u_1} [Finite ι] {S : Set (ι → ℝ)}, IsBoundedBox S → IsSemialgebraic S
@IsUnboundedBox.isSemialgebraic : ∀ {ι : Type u_1} [Finite ι] {S : Set (ι → ℝ)}, IsUnboundedBox S → IsSemialgebraic S
@isSemialgebraic_singleton : ∀ {ι : Type u_1} [Finite ι] (a : ι → ℝ), IsSemialgebraic {a}
@isSemialgebraic_of_finite : ∀ {ι : Type u_1} [Finite ι] {s : Set (ι → ℝ)}, s.Finite → IsSemialgebraic s
@isSemialgebraic_sup_ball : ∀ {ι : Type u_1} [Finite ι] (c : ι → ℝ) (r : ℝ),
  IsSemialgebraic {x | ∀ (i : ι), |x i - c i| < r}
@isSemialgebraic_sup_closedBall : ∀ {ι : Type u_1} [Finite ι] (c : ι → ℝ) (r : ℝ),
  IsSemialgebraic {x | ∀ (i : ι), |x i - c i| ≤ r}
@isSemialgebraic_euclid_ball : ∀ {ι : Type u_1} [inst : Fintype ι] (ρ : ℝ), IsSemialgebraic {x | ∑ i, x i ^ 2 ≤ ρ}
@isSemialgebraic_euclid_ball_lt : ∀ {ι : Type u_1} [inst : Fintype ι] (ρ : ℝ), IsSemialgebraic {x | ∑ i, x i ^ 2 < ρ}
@one_le_one_add_sum_sq : ∀ {ι : Type u_1} [inst : Fintype ι] (x : ι → ℝ), 1 ≤ 1 + ∑ i, x i ^ 2
@abs_le_one_add_sum_sq : ∀ {ι : Type u_1} [inst : Fintype ι] (x : ι → ℝ) (i : ι), |x i| ≤ 1 + ∑ j, x j ^ 2
@exists_abs_eval_le : ∀ {ι : Type u_1} [inst : Fintype ι] (p : MvPolynomial ι ℝ),
  ∃ c M, ∀ (x : ι → ℝ), |(MvPolynomial.eval x) p| ≤ c * (1 + ∑ i, x i ^ 2) ^ M
@exists_abs_eval_le' : ∀ {ι : Type u_1} [inst : Fintype ι] (p : MvPolynomial ι ℝ),
  ∃ c M, 0 ≤ c ∧ ∀ (x : ι → ℝ), |(MvPolynomial.eval x) p| ≤ c * (1 + ∑ i, x i ^ 2) ^ M
@growth_shape_iff : ∀ {ι : Type u_1} [inst : Fintype ι] (f : (ι → ℝ) → ℝ),
  (∃ c M, ∀ (x : ι → ℝ), |f x| ≤ c * (1 + ∑ i, x i ^ 2) ^ M) ↔ ∃ B M, ∀ (x : ι → ℝ), |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M
@growth_shape_mul_to_add : ∀ {ι : Type u_1} [inst : Fintype ι] {f : (ι → ℝ) → ℝ},
  (∃ c M, ∀ (x : ι → ℝ), |f x| ≤ c * (1 + ∑ i, x i ^ 2) ^ M) → ∃ B M, ∀ (x : ι → ℝ), |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M
@growth_shape_add_to_mul : ∀ {ι : Type u_1} [inst : Fintype ι] {f : (ι → ℝ) → ℝ},
  (∃ B M, ∀ (x : ι → ℝ), |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M) → ∃ c M, ∀ (x : ι → ℝ), |f x| ≤ c * (1 + ∑ i, x i ^ 2) ^ M
@poly_bound : ∀ {ι : Type u_1} [inst : Fintype ι] (p : MvPolynomial ι ℝ),
  ∃ c M, ∀ (x : ι → ℝ), |(MvPolynomial.eval x) p| ≤ c * (1 + ∑ i, x i ^ 2) ^ M
@growth_shape : ∀ {ι : Type u_1} [inst : Fintype ι] (f : (ι → ℝ) → ℝ),
  (∃ c M, ∀ (x : ι → ℝ), |f x| ≤ c * (1 + ∑ i, x i ^ 2) ^ M) ↔ ∃ B M, ∀ (x : ι → ℝ), |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M
@IsExtSemialgebraic.dom : ∀ {ι : Type u_1} {h : (ι → ℝ) → EReal},
  IsExtSemialgebraic h → IsSemialgebraic {x | ∃ r, h x = ↑r}
@isExtSemialgebraic_coe_iff : ∀ {ι : Type u_1} (f : (ι → ℝ) → ℝ),
  (IsExtSemialgebraic fun x => ↑(f x)) ↔ IsSemialgebraicMap f
@IsSemialgebraicMap.isExtSemialgebraic : ∀ {ι : Type u_1} {f : (ι → ℝ) → ℝ},
  IsSemialgebraicMap f → IsExtSemialgebraic fun x => ↑(f x)
@IsExtSemialgebraic.const : ∀ {ι : Type u_1} (c : EReal), IsExtSemialgebraic fun x => c
@IsExtSemialgebraic.neg : ∀ {ι : Type u_1} {h : (ι → ℝ) → EReal},
  IsExtSemialgebraic h → IsExtSemialgebraic fun x => -h x
@isExtSemialgebraic_neg_iff : ∀ {ι : Type u_1} {h : (ι → ℝ) → EReal},
  (IsExtSemialgebraic fun x => -h x) ↔ IsExtSemialgebraic h
@extGraph : {ι : Type u_1} → ((ι → ℝ) → EReal) → Set (ι ⊕ Fin 2 → ℝ)
@isExtSemialgebraic_iff_extGraph : ∀ {ι : Type u_1} (h : (ι → ℝ) → EReal),
  IsExtSemialgebraic h ↔ IsSemialgebraic (extGraph h)
```
