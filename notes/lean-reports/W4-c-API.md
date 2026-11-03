# W4-c API: HardnessBilevel/Convex/{Linearize,Hull}.lean (namespace Bilevel)

Imports: Linearize imports Framework.{Basic,Value,Poly} and Convex.Toolkit (for `ConvexLower`); Hull imports Linearize.
All theorems: `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.

Key facts:
* `Msp S y d = ∏ j, y j ^ d.1 (Sum.inr j)`; `cPoly p d x = p.coeff d.1 * ∏ i, x i ^ d.1 (Sum.inl i)` (d : ↥S);
  `plin S p x l = ∑ d : S, cPoly p d x * l d`; `plinLin S p x : (S → ℝ) →ₗ[ℝ] ℝ` with `plinLin_apply` (rfl, simp).
* The lower data of the linearized problem is `(fun x l => plin S P x l)`, lower set `convexHull ℝ (Msp S '' Y)`, lower index type `↥S : Type`.
* `hullWeights k` = the blueprint inline weight set `W k` (definitionally `{w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}`); `hullComb k wz = ∑ i, wz.1 i • wz.2 i`.

```lean
@Msp : {n : ℕ} → {ι : Type u_1} → [Fintype ι] → (S : Finset (Fin n ⊕ ι →₀ ℕ)) → (ι → ℝ) → ↥S → ℝ
@cPoly : {n : ℕ} → {ι : Type u_1} → {S : Finset (Fin n ⊕ ι →₀ ℕ)} → MvPolynomial (Fin n ⊕ ι) ℝ → ↥S → (Fin n → ℝ) → ℝ
@plin : {n : ℕ} →
  {ι : Type u_1} → (S : Finset (Fin n ⊕ ι →₀ ℕ)) → MvPolynomial (Fin n ⊕ ι) ℝ → (Fin n → ℝ) → (↥S → ℝ) → ℝ
@plinLin : {n : ℕ} →
  {ι : Type u_1} → (S : Finset (Fin n ⊕ ι →₀ ℕ)) → MvPolynomial (Fin n ⊕ ι) ℝ → (Fin n → ℝ) → (↥S → ℝ) →ₗ[ℝ] ℝ
@t221_splitting : ∀ {n : ℕ} {ι : Type u_1} [inst : Fintype ι] {S : Finset (Fin n ⊕ ι →₀ ℕ)}
  {p : MvPolynomial (Fin n ⊕ ι) ℝ},
  p.support ⊆ S → ∀ (x : Fin n → ℝ) (y : ι → ℝ), (MvPolynomial.eval (Sum.elim x y)) p = plin S p x (Msp S y)
@t221_claim1 : ∀ {n : ℕ} {ι : Type u_1} [inst : Fintype ι] {S : Finset (Fin n ⊕ ι →₀ ℕ)}
  {Q : MvPolynomial (Fin n ⊕ ι) ℝ},
  Q.support ⊆ S →
    ∀ (Y : Set (ι → ℝ)) (x : Fin n → ℝ),
      Msp S '' argminSet (fun x y => (MvPolynomial.eval (Sum.elim x y)) Q) Y x ⊆
        argminSet (fun x l => plin S Q x l) ((convexHull ℝ) (Msp S '' Y)) x
@t221_claim2 : ∀ {n : ℕ} {ι : Type u_1} [inst : Fintype ι] {S : Finset (Fin n ⊕ ι →₀ ℕ)}
  {Q : MvPolynomial (Fin n ⊕ ι) ℝ},
  Q.support ⊆ S →
    ∀ (Y : Set (ι → ℝ)) (x : Fin n → ℝ),
      argminSet (fun x l => plin S Q x l) ((convexHull ℝ) (Msp S '' Y)) x ⊆
        (convexHull ℝ) (Msp S '' argminSet (fun x y => (MvPolynomial.eval (Sum.elim x y)) Q) Y x)
@t221_linearize_value : ∀ {n : ℕ} {ι : Type u_1} [inst : Fintype ι] {S : Finset (Fin n ⊕ ι →₀ ℕ)}
  {P Q : MvPolynomial (Fin n ⊕ ι) ℝ},
  P.support ∪ Q.support ⊆ S →
    ∀ (Y : Set (ι → ℝ)) (x : Fin n → ℝ),
      valueFun (fun x l => plin S P x l) (fun x l => plin S Q x l) ((convexHull ℝ) (Msp S '' Y)) x =
        valueFun (fun x y => (MvPolynomial.eval (Sum.elim x y)) P) (fun x y => (MvPolynomial.eval (Sum.elim x y)) Q) Y x
@t221_linearize_pvalue : ∀ {n : ℕ} {ι : Type u_1} [inst : Fintype ι] {S : Finset (Fin n ⊕ ι →₀ ℕ)}
  {P Q : MvPolynomial (Fin n ⊕ ι) ℝ},
  P.support ∪ Q.support ⊆ S →
    ∀ (Y : Set (ι → ℝ)) (x : Fin n → ℝ),
      pvalueFun (fun x l => plin S P x l) (fun x l => plin S Q x l) ((convexHull ℝ) (Msp S '' Y)) x =
        pvalueFun (fun x y => (MvPolynomial.eval (Sum.elim x y)) P) (fun x y => (MvPolynomial.eval (Sum.elim x y)) Q) Y
          x
@t221_cc_data_isPolyFun : ∀ {n : ℕ} {ι : Type u_1} (S : Finset (Fin n ⊕ ι →₀ ℕ)) (p : MvPolynomial (Fin n ⊕ ι) ℝ),
  IsPolyFun fun x l => plin S p x l
@t221_cc_data_convexLower : ∀ {n : ℕ} {ι : Type u_1} (S : Finset (Fin n ⊕ ι →₀ ℕ)) (q : MvPolynomial (Fin n ⊕ ι) ℝ),
  ConvexLower fun x l => plin S q x l
@t221_cc_data_convex : ∀ {n : ℕ} {ι : Type u_1} [inst : Fintype ι] (S : Finset (Fin n ⊕ ι →₀ ℕ)) (Y : Set (ι → ℝ)),
  Convex ℝ ((convexHull ℝ) (Msp S '' Y))
@t221_cc_data_nonempty : ∀ {n : ℕ} {ι : Type u_1} [inst : Fintype ι] (S : Finset (Fin n ⊕ ι →₀ ℕ)) {Y : Set (ι → ℝ)},
  Y.Nonempty → ((convexHull ℝ) (Msp S '' Y)).Nonempty
hullWeights : (k : ℕ) → Set (Fin k → ℝ)
@hullComb : {E : Type u_1} → [inst : AddCommMonoid E] → [Module ℝ E] → (k : ℕ) → (Fin k → ℝ) × (Fin k → E) → E
@t221_caratheodory_union : ∀ {κ : Type u_1} [inst : Fintype κ] (s : Set (κ → ℝ)),
  (convexHull ℝ) s = ⋃ k ∈ Finset.range (Fintype.card κ + 2), hullComb k '' hullWeights k ×ˢ Set.univ.pi fun x => s
weights_isClosed : ∀ (k : ℕ), IsClosed (hullWeights k)
weights_isCompact : ∀ (k : ℕ), IsCompact (hullWeights k)
@continuous_hullComb : ∀ {κ : Type u_1} (k : ℕ), Continuous (hullComb k)
@isCompact_convexHull_of_isCompact : ∀ {κ : Type u_1} [Fintype κ] {s : Set (κ → ℝ)},
  IsCompact s → IsCompact ((convexHull ℝ) s)
@continuous_Msp : ∀ {n : ℕ} {ι : Type u_1} [inst : Fintype ι] (S : Finset (Fin n ⊕ ι →₀ ℕ)), Continuous (Msp S)
@isCompact_convexHull_Msp : ∀ {n : ℕ} {ι : Type u_1} [inst : Fintype ι] (S : Finset (Fin n ⊕ ι →₀ ℕ)) {Y : Set (ι → ℝ)},
  IsCompact Y → IsCompact ((convexHull ℝ) (Msp S '' Y))
```
