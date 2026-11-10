import HardnessBilevel.Framework.Basic
import HardnessBilevel.Framework.Value
import HardnessBilevel.Framework.Poly
import HardnessBilevel.Convex.Toolkit

/-!
# Theorem 2.21: the linearization lemma (blueprint §4.H.1)

Blueprint ids implemented here:
* `t221.splitting`  — `Bilevel.t221_splitting`
* `t221.linearize`  — `Bilevel.t221_linearize_value`, `Bilevel.t221_linearize_pvalue`, `Bilevel.t221_linearize`
* `t221.cc_data` (a), (b), (c), (f) — `Bilevel.t221_cc_data_isPolyFun`, `Bilevel.t221_cc_data_convexLower`,
  `Bilevel.t221_cc_data_convex`, `Bilevel.t221_cc_data_nonempty`, bundled in `Bilevel.t221_cc_data`.
  (Claims 1 and 2 of the proof are `Bilevel.t221_claim1`, `Bilevel.t221_claim2`.)

Part (d) (compactness, `t221.hull_compact`) is in `HardnessBilevel/Convex/Hull.lean`; part (e) (semialgebraicity, `t221.hull_sa`) needs A1 and
is not provided here.

Setting: `S : Finset (Fin n ⊕ ι →₀ ℕ)` a finite set of exponent vectors, the moment map
`Msp S y d = ∏ j, y j ^ d (inr j)`, coefficients `cPoly p d x = coeff d p * ∏ i, x i ^ d (inl i)` and the linearization
`plin S p x λ = ∑ d : S, cPoly p d x * λ d`.
-/

namespace Bilevel

open MvPolynomial

section Defs

variable {n : ℕ} {ι : Type*}

/-- The moment map `y ↦ (∏ j, y j ^ d (inr j))_{d ∈ S}` (blueprint §4.H.1). -/
noncomputable def Msp [Fintype ι] (S : Finset (Fin n ⊕ ι →₀ ℕ)) (y : ι → ℝ) : S → ℝ :=
  fun d => ∏ j : ι, (y j) ^ (d.1 (Sum.inr j))

/-- The `x`-dependent coefficient of the moment `d` in `p` (blueprint §4.H.1, erratum E-15). -/
noncomputable def cPoly {S : Finset (Fin n ⊕ ι →₀ ℕ)} (p : MvPolynomial (Fin n ⊕ ι) ℝ) (d : S)
    (x : Fin n → ℝ) : ℝ :=
  p.coeff d.1 * ∏ i : Fin n, (x i) ^ (d.1 (Sum.inl i))

/-- The linearization `p^lin (x, λ) = ∑_{d ∈ S} c_p d x * λ d` (blueprint §4.H.1). -/
noncomputable def plin (S : Finset (Fin n ⊕ ι →₀ ℕ)) (p : MvPolynomial (Fin n ⊕ ι) ℝ)
    (x : Fin n → ℝ) (l : S → ℝ) : ℝ :=
  ∑ d : S, cPoly p d x * l d

/-- `plin S p x` as a linear map in `λ`. -/
noncomputable def plinLin (S : Finset (Fin n ⊕ ι →₀ ℕ)) (p : MvPolynomial (Fin n ⊕ ι) ℝ)
    (x : Fin n → ℝ) : (S → ℝ) →ₗ[ℝ] ℝ where
  toFun l := plin S p x l
  map_add' a b := by
    simp only [plin, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [plin, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => by ring

@[simp] theorem plinLin_apply (S : Finset (Fin n ⊕ ι →₀ ℕ)) (p : MvPolynomial (Fin n ⊕ ι) ℝ)
    (x : Fin n → ℝ) (l : S → ℝ) : plinLin S p x l = plin S p x l := rfl

/-- **t221.splitting** (L8). -/
theorem t221_splitting [Fintype ι] {S : Finset (Fin n ⊕ ι →₀ ℕ)} {p : MvPolynomial (Fin n ⊕ ι) ℝ}
    (hS : p.support ⊆ S) (x : Fin n → ℝ) (y : ι → ℝ) :
    MvPolynomial.eval (Sum.elim x y) p = plin S p x (Msp S y) := by
  rw [MvPolynomial.eval_eq']
  simp only [plin, cPoly, Msp, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_coe_sort S (fun d => p.coeff d * (∏ i : Fin n, x i ^ d (Sum.inl i)) *
      ∏ j : ι, y j ^ d (Sum.inr j))]
  rw [Finset.sum_subset hS]
  · refine Finset.sum_congr rfl fun d _ => by ring
  · intro d _ hd
    rw [MvPolynomial.notMem_support_iff.mp hd]
    ring

end Defs

section Linearize

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The real-valued function `(x, y) ↦ eval (Sum.elim x y) p`. -/
local notation "evF" p => fun (x : Fin n → ℝ) (y : ι → ℝ) => MvPolynomial.eval (Sum.elim x y) p

/-- Claim 1 of `t221.linearize`: `Msp '' A ⊆ A'`. -/
theorem t221_claim1 {S : Finset (Fin n ⊕ ι →₀ ℕ)} {Q : MvPolynomial (Fin n ⊕ ι) ℝ}
    (hQ : Q.support ⊆ S) (Y : Set (ι → ℝ)) (x : Fin n → ℝ) :
    Msp S '' argminSet (evF Q) Y x ⊆
      argminSet (fun x l => plin S Q x l) (convexHull ℝ (Msp S '' Y)) x := by
  rintro _ ⟨y, ⟨hyY, hymin⟩, rfl⟩
  refine ⟨subset_convexHull ℝ _ ⟨y, hyY, rfl⟩, fun l hl => ?_⟩
  obtain ⟨μ, ⟨y', hy', rfl⟩, hμ⟩ :=
    ((plinLin S Q x).concaveOn convex_univ).exists_le_of_mem_convexHull (Set.subset_univ _) hl
  simp only [plinLin_apply] at hμ
  have h1 := hymin y' hy'
  simp only [t221_splitting hQ] at h1
  exact h1.trans hμ

/-- Claim 2 of `t221.linearize`: `A' ⊆ convexHull (Msp '' A)` (positive weights, erratum E-16). -/
theorem t221_claim2 {S : Finset (Fin n ⊕ ι →₀ ℕ)} {Q : MvPolynomial (Fin n ⊕ ι) ℝ}
    (hQ : Q.support ⊆ S) (Y : Set (ι → ℝ)) (x : Fin n → ℝ) :
    argminSet (fun x l => plin S Q x l) (convexHull ℝ (Msp S '' Y)) x ⊆
      convexHull ℝ (Msp S '' argminSet (evF Q) Y x) := by
  rintro l ⟨hlY, hlmin⟩
  obtain ⟨ι₀, _, z, w, hz, -, hw0, hw1, rfl⟩ := eq_pos_convex_span_of_mem_convexHull hlY
  have hz' : ∀ i, ∃ y ∈ Y, Msp S y = z i := fun i => hz ⟨i, rfl⟩
  choose yv hyY hyz using hz'
  set ℓ := plinLin S Q x with hℓ
  set m := ℓ (∑ i, w i • z i) with hm
  have hge : ∀ i, m ≤ ℓ (z i) := fun i => by
    have := hlmin (z i) (subset_convexHull ℝ _ (hz ⟨i, rfl⟩))
    simpa only [hm, hℓ, plinLin_apply] using this
  have hsum : ∑ i, w i * (ℓ (z i) - m) = 0 := by
    have h2 : m = ∑ i, w i * ℓ (z i) := by
      rw [hm, map_sum]
      simp only [map_smul, smul_eq_mul]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul, ← h2, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    mul_nonneg (hw0 i).le (sub_nonneg.mpr (hge i)))).mp hsum
  have heq : ∀ i, ℓ (z i) = m := fun i => by
    have := hzero i (Finset.mem_univ i)
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (hw0 i).ne'
    · linarith
  have hmemA : ∀ i, yv i ∈ argminSet (evF Q) Y x := fun i => by
    refine ⟨hyY i, fun y' hy' => ?_⟩
    have h3 := hlmin (Msp S y') (subset_convexHull ℝ _ ⟨y', hy', rfl⟩)
    have h4 := heq i
    rw [← hyz i] at h4
    simp only [hℓ, plinLin_apply] at h4
    show MvPolynomial.eval (Sum.elim x (yv i)) Q ≤ MvPolynomial.eval (Sum.elim x y') Q
    rw [t221_splitting hQ, t221_splitting hQ, h4]
    simpa only [hm, hℓ, plinLin_apply] using h3
  refine (convex_convexHull ℝ _).sum_mem (fun i _ => (hw0 i).le) hw1 fun i _ => ?_
  exact subset_convexHull ℝ _ ⟨yv i, hmemA i, hyz i⟩

/-- **t221.linearize** (L9), optimistic half. -/
theorem t221_linearize_value {S : Finset (Fin n ⊕ ι →₀ ℕ)} {P Q : MvPolynomial (Fin n ⊕ ι) ℝ}
    (hS : P.support ∪ Q.support ⊆ S) (Y : Set (ι → ℝ)) (x : Fin n → ℝ) :
    valueFun (fun x l => plin S P x l) (fun x l => plin S Q x l) (convexHull ℝ (Msp S '' Y)) x =
      valueFun (evF P) (evF Q) Y x := by
  have hP : P.support ⊆ S := fun d hd => hS (Finset.mem_union_left _ hd)
  have hQ : Q.support ⊆ S := fun d hd => hS (Finset.mem_union_right _ hd)
  apply le_antisymm
  · refine le_iInf₂ fun y hy => ?_
    have := valueFun_le_coe_of_mem (P := fun x l => plin S P x l) (t221_claim1 hQ Y x ⟨y, hy, rfl⟩)
    rw [← t221_splitting hP] at this
    exact this
  · refine le_iInf₂ fun l hl => ?_
    obtain ⟨μ, ⟨y, hy, rfl⟩, hμ⟩ :=
      ((plinLin S P x).concaveOn convex_univ).exists_le_of_mem_convexHull (Set.subset_univ _)
        (t221_claim2 hQ Y x hl)
    simp only [plinLin_apply] at hμ
    refine (valueFun_le_coe_of_mem (P := evF P) hy).trans ?_
    rw [t221_splitting hP]
    exact EReal.coe_le_coe_iff.mpr hμ

/-- **t221.linearize** (L9), pessimistic half. -/
theorem t221_linearize_pvalue {S : Finset (Fin n ⊕ ι →₀ ℕ)} {P Q : MvPolynomial (Fin n ⊕ ι) ℝ}
    (hS : P.support ∪ Q.support ⊆ S) (Y : Set (ι → ℝ)) (x : Fin n → ℝ) :
    pvalueFun (fun x l => plin S P x l) (fun x l => plin S Q x l) (convexHull ℝ (Msp S '' Y)) x =
      pvalueFun (evF P) (evF Q) Y x := by
  have hP : P.support ⊆ S := fun d hd => hS (Finset.mem_union_left _ hd)
  have hQ : Q.support ⊆ S := fun d hd => hS (Finset.mem_union_right _ hd)
  apply le_antisymm
  · refine iSup₂_le fun l hl => ?_
    obtain ⟨μ, ⟨y, hy, rfl⟩, hμ⟩ :=
      ((plinLin S P x).convexOn convex_univ).exists_ge_of_mem_convexHull (Set.subset_univ _)
        (t221_claim2 hQ Y x hl)
    simp only [plinLin_apply] at hμ
    refine le_trans ?_ (coe_le_pvalueFun_of_mem (P := evF P) hy)
    rw [t221_splitting hP]
    exact EReal.coe_le_coe_iff.mpr hμ
  · refine iSup₂_le fun y hy => ?_
    have := coe_le_pvalueFun_of_mem (P := fun x l => plin S P x l) (t221_claim1 hQ Y x ⟨y, hy, rfl⟩)
    rw [← t221_splitting hP] at this
    exact this

/-- **t221.linearize** (L9), both halves. -/
theorem t221_linearize {S : Finset (Fin n ⊕ ι →₀ ℕ)} {P Q : MvPolynomial (Fin n ⊕ ι) ℝ}
    (hS : P.support ∪ Q.support ⊆ S) (Y : Set (ι → ℝ)) :
    (∀ x, valueFun (fun x l => plin S P x l) (fun x l => plin S Q x l)
        (convexHull ℝ (Msp S '' Y)) x = valueFun (evF P) (evF Q) Y x) ∧
    (∀ x, pvalueFun (fun x l => plin S P x l) (fun x l => plin S Q x l)
        (convexHull ℝ (Msp S '' Y)) x = pvalueFun (evF P) (evF Q) Y x) :=
  ⟨t221_linearize_value hS Y, t221_linearize_pvalue hS Y⟩

end Linearize

section CCData

variable {n : ℕ} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- **t221.cc_data** (a): the linearization is a polynomial in `(x, λ)` (lower index type `↥S`). -/
theorem t221_cc_data_isPolyFun (S : Finset (Fin n ⊕ ι →₀ ℕ)) (p : MvPolynomial (Fin n ⊕ ι) ℝ) :
    IsPolyFun (fun (x : Fin n → ℝ) (l : S → ℝ) => plin S p x l) := by
  have h : IsPolyFun (fun (x : Fin n → ℝ) (l : S → ℝ) => ∑ d ∈ (Finset.univ : Finset S),
      (p.coeff d.1 * ∏ i ∈ (Finset.univ : Finset (Fin n)), (x i) ^ (d.1 (Sum.inl i))) * l d) :=
    isPolyFun_finset_sum _ fun d _ =>
      ((isPolyFun_finset_prod _ fun i _ => (isPolyFun_x i).pow _).const_mul _).mul (isPolyFun_y d)
  exact h.of_eq fun x l => rfl

omit [Fintype ι] in
/-- **t221.cc_data** (b): `Q^lin (x, ·)` is linear, hence convex on `univ`. -/
theorem t221_cc_data_convexLower (S : Finset (Fin n ⊕ ι →₀ ℕ)) (q : MvPolynomial (Fin n ⊕ ι) ℝ) :
    ConvexLower (fun (x : Fin n → ℝ) (l : S → ℝ) => plin S q x l) :=
  fun x => (plinLin S q x).convexOn convex_univ

/-- **t221.cc_data** (c): `Y' = convexHull (Msp '' Y)` is convex. -/
theorem t221_cc_data_convex (S : Finset (Fin n ⊕ ι →₀ ℕ)) (Y : Set (ι → ℝ)) :
    Convex ℝ (convexHull ℝ (Msp S '' Y)) :=
  convex_convexHull ℝ _

/-- **t221.cc_data** (f): `Y'` is nonempty if `Y` is. -/
theorem t221_cc_data_nonempty (S : Finset (Fin n ⊕ ι →₀ ℕ)) {Y : Set (ι → ℝ)} (hY : Y.Nonempty) :
    (convexHull ℝ (Msp S '' Y)).Nonempty :=
  convexHull_nonempty_iff.mpr (hY.image _)

/-- **t221.cc_data** (a), (b), (c), (f) bundled, for `P Q` and a set `Y`. -/
theorem t221_cc_data (S : Finset (Fin n ⊕ ι →₀ ℕ)) (P Q : MvPolynomial (Fin n ⊕ ι) ℝ)
    (Y : Set (ι → ℝ)) :
    IsPolyFun (fun (x : Fin n → ℝ) (l : S → ℝ) => plin S P x l) ∧
    IsPolyFun (fun (x : Fin n → ℝ) (l : S → ℝ) => plin S Q x l) ∧
    ConvexLower (fun (x : Fin n → ℝ) (l : S → ℝ) => plin S Q x l) ∧
    Convex ℝ (convexHull ℝ (Msp S '' Y)) ∧
    (Y.Nonempty → (convexHull ℝ (Msp S '' Y)).Nonempty) :=
  ⟨t221_cc_data_isPolyFun S P, t221_cc_data_isPolyFun S Q, t221_cc_data_convexLower S Q,
    t221_cc_data_convex S Y, t221_cc_data_nonempty S⟩

end CCData

end Bilevel
