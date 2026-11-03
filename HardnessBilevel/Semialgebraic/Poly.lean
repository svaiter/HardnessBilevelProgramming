/-
Copyright: HardnessBilevel project.

# Semialgebraic sets: polynomial preimages, reindexing, graphs, boxes, balls, polynomial growth

Implements blueprint §4.B.1 (`sa.preimage_poly` (L4) and its corollaries `sa.reindex`, `sa.cylinder`,
`sa.poly_graph`, `sa.box`, `sa.singleton`, `sa.finite_set`, `sa.sup_ball`, `sa.euclid_ball`) and the two
unconditional lemmas of §4.B.5: `sa.poly_bound` (L17) and `sa.growth_shape`.

Deviations / strengthenings:
* Statements that intersect over an index family (`isSemialgebraic_poly_graph`, `isSemialgebraic_singleton`,
  `isSemialgebraic_boxSet`, `isSemialgebraic_sup_ball`, …) take `[Finite _]` instead of `[Fintype _]`;
  the Euclidean ball and the growth lemmas use `[Fintype ι]` (they mention `∑ i`). Finiteness of the
  index type is necessary for these intersections (an element of the generated algebra depends on finitely
  many coordinates), so this is not an added hypothesis relative to the blueprint (which works on `Fin n`).
* `sa.growth_shape` is stated as an `Iff` for an arbitrary `f : (ι → ℝ) → ℝ`.
-/
import HardnessBilevel.Semialgebraic.Basic
import HardnessBilevel.Framework.Poly
import HardnessBilevel.Framework.Box

open MeasureTheory Function MvPolynomial

namespace Bilevel

section Preimage

variable {ι κ : Type*}

/-- `sa.preimage_poly` (L4): preimages of semialgebraic sets under polynomial maps are semialgebraic. -/
theorem IsSemialgebraic.preimage_poly (F : κ → MvPolynomial ι ℝ) {S : Set (κ → ℝ)}
    (hS : IsSemialgebraic S) :
    IsSemialgebraic ((fun x i => MvPolynomial.eval x (F i)) ⁻¹' S) := by
  unfold IsSemialgebraic at hS
  induction hS using generateSetAlgebra_induction with
  | base u hu =>
    rcases hu with ⟨p, rfl⟩ | ⟨p, rfl⟩
    · refine (isSemialgebraic_eval_eq_zero (bind₁ F p)).of_eq ?_
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, eval_bind₁']
    · refine (isSemialgebraic_eval_pos (bind₁ F p)).of_eq ?_
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, eval_bind₁']
  | empty => exact isSemialgebraic_empty
  | compl u _ ih => exact ih.compl
  | union u v _ _ ihu ihv => exact ihu.union ihv

/-- `sa.preimage_poly`, pointwise form: a map whose coordinates are given by polynomials. -/
theorem IsSemialgebraic.preimage_of_poly {φ : (ι → ℝ) → κ → ℝ} (F : κ → MvPolynomial ι ℝ)
    (hφ : ∀ x i, φ x i = MvPolynomial.eval x (F i)) {S : Set (κ → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic (φ ⁻¹' S) := by
  have : φ = fun x i => MvPolynomial.eval x (F i) := by funext x i; exact hφ x i
  subst this
  exact hS.preimage_poly F

/-- `sa.reindex`: precomposition with an arbitrary map of index types. -/
theorem IsSemialgebraic.reindex (e : ι → κ) {S : Set (ι → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic ((fun x : κ → ℝ => x ∘ e) ⁻¹' S) :=
  hS.preimage_of_poly (fun i => X (e i)) (fun x i => by simp)

/-- `sa.reindex`, equivalence/preimage form. -/
theorem IsSemialgebraic.preimage_equiv (e : ι ≃ κ) {S : Set (ι → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic ((fun x : κ → ℝ => x ∘ e) ⁻¹' S) :=
  hS.reindex e

/-- `sa.reindex`, equivalence/image form. -/
theorem IsSemialgebraic.image_equiv (e : ι ≃ κ) {S : Set (ι → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic ((fun x : ι → ℝ => x ∘ e.symm) '' S) := by
  refine (hS.reindex e).of_eq ?_
  ext y
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · intro hy
    exact ⟨y ∘ e, hy, by funext k; simp⟩
  · rintro ⟨x, hx, rfl⟩
    have : (x ∘ e.symm) ∘ e = x := by funext i; simp
    rw [this]; exact hx

/-- `sa.reindex`, equivalence/image form (precomposition by the equivalence itself). -/
theorem IsSemialgebraic.image_comp_equiv (e : κ ≃ ι) {S : Set (ι → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic ((fun x : ι → ℝ => x ∘ e) '' S) := by
  have h := hS.image_equiv e.symm
  simpa only [Equiv.symm_symm] using h

theorem isSemialgebraic_reindex_equiv_iff (e : ι ≃ κ) {S : Set (ι → ℝ)} :
    IsSemialgebraic ((fun x : κ → ℝ => x ∘ e) ⁻¹' S) ↔ IsSemialgebraic S := by
  refine ⟨fun h => ?_, fun h => h.reindex e⟩
  refine (h.reindex e.symm).of_eq ?_
  ext x
  simp only [Set.mem_preimage]
  have : (x ∘ e.symm) ∘ e = x := by funext i; simp
  rw [this]

end Preimage

section Cylinder

variable {ι κ : Type*}

/-- `sa.cylinder` (left factor). -/
theorem isSemialgebraic_cylinder_inl {S : Set (ι → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic {z : ι ⊕ κ → ℝ | z ∘ Sum.inl ∈ S} :=
  hS.reindex Sum.inl

/-- `sa.cylinder` (right factor). -/
theorem isSemialgebraic_cylinder_inr {T : Set (κ → ℝ)} (hT : IsSemialgebraic T) :
    IsSemialgebraic {z : ι ⊕ κ → ℝ | z ∘ Sum.inr ∈ T} :=
  hT.reindex Sum.inr

/-- `sa.cylinder` (product form). -/
theorem isSemialgebraic_cylinder {S : Set (ι → ℝ)} {T : Set (κ → ℝ)} (hS : IsSemialgebraic S)
    (hT : IsSemialgebraic T) :
    IsSemialgebraic {z : ι ⊕ κ → ℝ | z ∘ Sum.inl ∈ S ∧ z ∘ Sum.inr ∈ T} :=
  isSemialgebraic_setOf_and (isSemialgebraic_cylinder_inl hS) (isSemialgebraic_cylinder_inr hT)

/-- `sa.poly_graph`: the graph of a polynomial map is semialgebraic. -/
theorem isSemialgebraic_poly_graph [Finite κ] (G : κ → MvPolynomial ι ℝ) :
    IsSemialgebraic {z : ι ⊕ κ → ℝ | ∀ j, z (Sum.inr j) = MvPolynomial.eval (z ∘ Sum.inl) (G j)} := by
  refine isSemialgebraic_setOf_forall fun j => ?_
  refine (isSemialgebraic_eval_eq (X (Sum.inr j)) (rename Sum.inl (G j))).of_eq ?_
  ext z
  simp only [Set.mem_ofPred_eq, eval_X, eval_rename]

/-- `sa.poly_graph`: polynomial functions are semialgebraic maps. -/
theorem isSemialgebraicMap_eval (p : MvPolynomial ι ℝ) :
    IsSemialgebraicMap (fun x : ι → ℝ => MvPolynomial.eval x p) := by
  refine (isSemialgebraic_poly_graph (κ := Unit) (fun _ => p)).of_eq ?_
  ext z
  simp only [Set.mem_ofPred_eq, graphSet]
  exact ⟨fun h => (h ()).symm, fun h _ => h.symm⟩

end Cylinder

section Sets

variable {ι : Type*}

/-- Helper: `{x | a ≤ x i}` (real `a`). -/
theorem isSemialgebraic_const_le_coord (a : ℝ) (i : ι) :
    IsSemialgebraic {x : ι → ℝ | a ≤ x i} :=
  (isSemialgebraic_eval_le (C a) (X i)).of_eq (by ext x; simp)

/-- Helper: `{x | x i ≤ a}` (real `a`). -/
theorem isSemialgebraic_coord_le_const (i : ι) (a : ℝ) :
    IsSemialgebraic {x : ι → ℝ | x i ≤ a} :=
  (isSemialgebraic_eval_le (X i) (C a)).of_eq (by ext x; simp)

/-- Helper: `{x | x i = a}`. -/
theorem isSemialgebraic_coord_eq_const (i : ι) (a : ℝ) :
    IsSemialgebraic {x : ι → ℝ | x i = a} :=
  (isSemialgebraic_eval_eq (X i) (C a)).of_eq (by ext x; simp)

/-- Helper: `{x | a ≤ x i}` for an extended-real lower endpoint `a`. -/
theorem isSemialgebraic_ereal_le_coord (a : EReal) (i : ι) :
    IsSemialgebraic {x : ι → ℝ | a ≤ ((x i : ℝ) : EReal)} := by
  induction a using EReal.rec with
  | bot => exact isSemialgebraic_univ.of_eq (by ext x; simp)
  | top => exact isSemialgebraic_empty.of_eq (by ext x; simp)
  | coe a => exact (isSemialgebraic_const_le_coord a i).of_eq (by ext x; simp)

/-- Helper: `{x | x i ≤ b}` for an extended-real upper endpoint `b`. -/
theorem isSemialgebraic_coord_le_ereal (i : ι) (b : EReal) :
    IsSemialgebraic {x : ι → ℝ | ((x i : ℝ) : EReal) ≤ b} := by
  induction b using EReal.rec with
  | bot => exact isSemialgebraic_empty.of_eq (by ext x; simp)
  | top => exact isSemialgebraic_univ.of_eq (by ext x; simp)
  | coe b => exact (isSemialgebraic_coord_le_const i b).of_eq (by ext x; simp)

/-- `sa.box`: boxes with extended-real endpoints are semialgebraic. -/
theorem isSemialgebraic_boxSet [Finite ι] (lo hi : ι → EReal) :
    IsSemialgebraic (boxSet lo hi) :=
  isSemialgebraic_setOf_forall fun i =>
    isSemialgebraic_setOf_and (isSemialgebraic_ereal_le_coord (lo i) i)
      (isSemialgebraic_coord_le_ereal i (hi i))

/-- `sa.box` for real bounds. -/
theorem isSemialgebraic_boundedBox [Finite ι] (lo hi : ι → ℝ) :
    IsSemialgebraic (boundedBox lo hi) := by
  rw [boundedBox_eq_boxSet]; exact isSemialgebraic_boxSet _ _

/-- `sa.box` -/
theorem IsBox.isSemialgebraic [Finite ι] {S : Set (ι → ℝ)} (hS : IsBox S) : IsSemialgebraic S := by
  obtain ⟨lo, hi, rfl⟩ := hS; exact isSemialgebraic_boxSet lo hi

/-- `sa.box` -/
theorem IsBoundedBox.isSemialgebraic [Finite ι] {S : Set (ι → ℝ)} (hS : IsBoundedBox S) :
    IsSemialgebraic S :=
  hS.isBox.isSemialgebraic

/-- `sa.box` -/
theorem IsUnboundedBox.isSemialgebraic [Finite ι] {S : Set (ι → ℝ)} (hS : IsUnboundedBox S) :
    IsSemialgebraic S :=
  hS.isBox.isSemialgebraic

/-- `sa.singleton` -/
theorem isSemialgebraic_singleton [Finite ι] (a : ι → ℝ) : IsSemialgebraic ({a} : Set (ι → ℝ)) :=
  (isSemialgebraic_setOf_forall fun i => isSemialgebraic_coord_eq_const i (a i)).of_eq (by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun h => funext h, fun h i => h ▸ rfl⟩)

/-- `sa.finite_set` -/
theorem isSemialgebraic_of_finite [Finite ι] {s : Set (ι → ℝ)} (hs : s.Finite) :
    IsSemialgebraic s := by
  have h := isSemialgebraic_biUnion hs.toFinset (s := fun a => ({a} : Set (ι → ℝ)))
    (fun a _ => isSemialgebraic_singleton a)
  refine h.of_eq ?_
  ext x; simp

/-- `sa.sup_ball`: the open sup-norm ball. -/
theorem isSemialgebraic_sup_ball [Finite ι] (c : ι → ℝ) (r : ℝ) :
    IsSemialgebraic {x : ι → ℝ | ∀ i, |x i - c i| < r} := by
  refine isSemialgebraic_setOf_forall fun i => ?_
  refine (isSemialgebraic_setOf_and (isSemialgebraic_eval_lt (C (-r)) (X i - C (c i)))
    (isSemialgebraic_eval_lt (X i - C (c i)) (C r))).of_eq ?_
  ext x
  simp only [Set.mem_ofPred_eq, eval_C, eval_sub, eval_X, abs_lt]

/-- `sa.sup_ball`, closed version. -/
theorem isSemialgebraic_sup_closedBall [Finite ι] (c : ι → ℝ) (r : ℝ) :
    IsSemialgebraic {x : ι → ℝ | ∀ i, |x i - c i| ≤ r} := by
  refine isSemialgebraic_setOf_forall fun i => ?_
  refine (isSemialgebraic_setOf_and (isSemialgebraic_eval_le (C (-r)) (X i - C (c i)))
    (isSemialgebraic_eval_le (X i - C (c i)) (C r))).of_eq ?_
  ext x
  simp only [Set.mem_ofPred_eq, eval_C, eval_sub, eval_X, abs_le]

/-- `sa.euclid_ball`: the closed Euclidean ball `{∑ x_i² ≤ ρ}` (centred at `0`). -/
theorem isSemialgebraic_euclid_ball [Fintype ι] (ρ : ℝ) :
    IsSemialgebraic {x : ι → ℝ | ∑ i, x i ^ 2 ≤ ρ} :=
  (isSemialgebraic_eval_le (∑ i, X i ^ 2) (C ρ)).of_eq (by ext x; simp)

/-- `sa.euclid_ball`, open version. -/
theorem isSemialgebraic_euclid_ball_lt [Fintype ι] (ρ : ℝ) :
    IsSemialgebraic {x : ι → ℝ | ∑ i, x i ^ 2 < ρ} :=
  (isSemialgebraic_eval_lt (∑ i, X i ^ 2) (C ρ)).of_eq (by ext x; simp)

end Sets

section Growth

variable {ι : Type*} [Fintype ι]

theorem one_le_one_add_sum_sq (x : ι → ℝ) : 1 ≤ 1 + ∑ i, x i ^ 2 := by
  have : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

theorem abs_le_one_add_sum_sq (x : ι → ℝ) (i : ι) : |x i| ≤ 1 + ∑ j, x j ^ 2 := by
  have h1 : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : |x i| ≤ 1 + x i ^ 2 := by
    rw [← sq_abs (x i)]
    nlinarith [sq_nonneg (|x i| - 1), abs_nonneg (x i)]
  linarith

private theorem poly_bound_aux (p : MvPolynomial ι ℝ) :
    ∃ (c : ℝ) (M : ℕ), 0 ≤ c ∧ ∀ x : ι → ℝ, |MvPolynomial.eval x p| ≤ c * (1 + ∑ i, x i ^ 2) ^ M := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨|a|, 0, abs_nonneg a, fun x => by simp⟩
  | add p q hp hq =>
    obtain ⟨c₁, M₁, hc₁, h₁⟩ := hp
    obtain ⟨c₂, M₂, hc₂, h₂⟩ := hq
    refine ⟨c₁ + c₂, max M₁ M₂, add_nonneg hc₁ hc₂, fun x => ?_⟩
    have hS := one_le_one_add_sum_sq x
    have e₁ : (1 + ∑ i, x i ^ 2) ^ M₁ ≤ (1 + ∑ i, x i ^ 2) ^ max M₁ M₂ :=
      pow_le_pow_right₀ hS (le_max_left _ _)
    have e₂ : (1 + ∑ i, x i ^ 2) ^ M₂ ≤ (1 + ∑ i, x i ^ 2) ^ max M₁ M₂ :=
      pow_le_pow_right₀ hS (le_max_right _ _)
    rw [eval_add]
    calc |MvPolynomial.eval x p + MvPolynomial.eval x q|
        ≤ |MvPolynomial.eval x p| + |MvPolynomial.eval x q| := abs_add_le _ _
      _ ≤ c₁ * (1 + ∑ i, x i ^ 2) ^ M₁ + c₂ * (1 + ∑ i, x i ^ 2) ^ M₂ := add_le_add (h₁ x) (h₂ x)
      _ ≤ c₁ * (1 + ∑ i, x i ^ 2) ^ max M₁ M₂ + c₂ * (1 + ∑ i, x i ^ 2) ^ max M₁ M₂ :=
          add_le_add (mul_le_mul_of_nonneg_left e₁ hc₁) (mul_le_mul_of_nonneg_left e₂ hc₂)
      _ = (c₁ + c₂) * (1 + ∑ i, x i ^ 2) ^ max M₁ M₂ := by ring
  | mul_X p n hp =>
    obtain ⟨c, M, hc, h⟩ := hp
    refine ⟨c, M + 1, hc, fun x => ?_⟩
    have hS := one_le_one_add_sum_sq x
    rw [eval_mul, eval_X, abs_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (h x) (abs_le_one_add_sum_sq x n) (abs_nonneg _)
      (mul_nonneg hc (pow_nonneg (by linarith) _))

/-- `sa.poly_bound` (L17): polynomials have polynomial growth. -/
theorem exists_abs_eval_le (p : MvPolynomial ι ℝ) :
    ∃ (c : ℝ) (M : ℕ), ∀ x : ι → ℝ, |MvPolynomial.eval x p| ≤ c * (1 + ∑ i, x i ^ 2) ^ M := by
  obtain ⟨c, M, -, h⟩ := poly_bound_aux p
  exact ⟨c, M, h⟩

/-- `sa.poly_bound` with a nonnegative constant. -/
theorem exists_abs_eval_le' (p : MvPolynomial ι ℝ) :
    ∃ (c : ℝ) (M : ℕ), 0 ≤ c ∧ ∀ x : ι → ℝ, |MvPolynomial.eval x p| ≤ c * (1 + ∑ i, x i ^ 2) ^ M :=
  poly_bound_aux p

/-- `sa.growth_shape`: the shapes `c (1+∑x²)^M` and `B + (1+∑x²)^M` of a growth bound are equivalent. -/
theorem growth_shape_iff (f : (ι → ℝ) → ℝ) :
    (∃ (c : ℝ) (M : ℕ), ∀ x, |f x| ≤ c * (1 + ∑ i, x i ^ 2) ^ M) ↔
      (∃ (B : ℝ) (M : ℕ), ∀ x, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M) := by
  constructor
  · rintro ⟨c, M, h⟩
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt c (by norm_num : (1 : ℝ) < 2)
    refine ⟨max c 0 * 2 ^ M, K + M, fun x => ?_⟩
    set S := 1 + ∑ i, x i ^ 2 with hSdef
    have hS : 1 ≤ S := one_le_one_add_sum_sq x
    have hS0 : 0 ≤ S := by linarith
    have hSM : 0 ≤ S ^ M := pow_nonneg hS0 M
    have hc' : c * S ^ M ≤ max c 0 * S ^ M := mul_le_mul_of_nonneg_right (le_max_left _ _) hSM
    refine (h x).trans ?_
    rcases le_total S 2 with hS2 | hS2
    · have : max c 0 * S ^ M ≤ max c 0 * 2 ^ M :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS0 hS2 M) (le_max_right _ _)
      have : 0 ≤ S ^ (K + M) := pow_nonneg hS0 _
      linarith
    · have h2K : (2 : ℝ) ^ K ≤ S ^ K := pow_le_pow_left₀ (by norm_num) hS2 K
      have : c * S ^ M ≤ S ^ (K + M) := by
        rw [pow_add]
        exact mul_le_mul_of_nonneg_right (hK.le.trans h2K) hSM
      have : 0 ≤ max c 0 * 2 ^ M := mul_nonneg (le_max_right _ _) (by positivity)
      linarith
  · rintro ⟨B, M, h⟩
    refine ⟨|B| + 1, M, fun x => ?_⟩
    have hS : 1 ≤ 1 + ∑ i, x i ^ 2 := one_le_one_add_sum_sq x
    have h1 : 1 ≤ (1 + ∑ i, x i ^ 2) ^ M := one_le_pow₀ hS
    have hB : B ≤ |B| := le_abs_self B
    have hB0 : 0 ≤ |B| := abs_nonneg B
    refine (h x).trans ?_
    nlinarith

/-- `sa.growth_shape`, direction `c (1+∑x²)^M ⇒ B + (1+∑x²)^M`. -/
theorem growth_shape_mul_to_add {f : (ι → ℝ) → ℝ}
    (h : ∃ (c : ℝ) (M : ℕ), ∀ x, |f x| ≤ c * (1 + ∑ i, x i ^ 2) ^ M) :
    ∃ (B : ℝ) (M : ℕ), ∀ x, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M :=
  (growth_shape_iff f).1 h

/-- `sa.growth_shape`, direction `B + (1+∑x²)^M ⇒ c (1+∑x²)^M`. -/
theorem growth_shape_add_to_mul {f : (ι → ℝ) → ℝ}
    (h : ∃ (B : ℝ) (M : ℕ), ∀ x, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M) :
    ∃ (c : ℝ) (M : ℕ), ∀ x, |f x| ≤ c * (1 + ∑ i, x i ^ 2) ^ M :=
  (growth_shape_iff f).2 h

/-- `sa.poly_bound` (alias of `exists_abs_eval_le`). -/
theorem poly_bound (p : MvPolynomial ι ℝ) :
    ∃ (c : ℝ) (M : ℕ), ∀ x : ι → ℝ, |MvPolynomial.eval x p| ≤ c * (1 + ∑ i, x i ^ 2) ^ M :=
  exists_abs_eval_le p

/-- `sa.growth_shape` (alias of `growth_shape_iff`). -/
theorem growth_shape (f : (ι → ℝ) → ℝ) :
    (∃ (c : ℝ) (M : ℕ), ∀ x, |f x| ≤ c * (1 + ∑ i, x i ^ 2) ^ M) ↔
      (∃ (B : ℝ) (M : ℕ), ∀ x, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M) :=
  growth_shape_iff f

end Growth

end Bilevel
