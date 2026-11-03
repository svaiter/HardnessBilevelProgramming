# W3-d API: HardnessBilevel/Semialgebraic/Value.lean and HardnessBilevel/Semialgebraic/Hull.lean (namespace Bilevel)

Value imports Framework.Classes, Semialgebraic.Projection, Semialgebraic.Ext; Hull imports Semialgebraic.Projection.
Both open MeasureTheory Function MvPolynomial and set `set_option linter.concreteInstances false`.
No instance of any assumption class. Every theorem: #print axioms = [propext, Classical.choice, Quot.sound].
Defs: `argminGraph Q Y := {z | (fun j => z (inr j)) ∈ Y ∧ ∀ y', y' ∈ Y → Q (fun i => z (inl i)) (fun j => z (inr j)) ≤ Q (fun i => z (inl i)) y'}`;
`hullSlice Y F N := {l | ∃ (c : Fin N → ℝ) (y : Fin N → m → ℝ), (∀ i, 0 ≤ c i) ∧ ∑ i, c i = 1 ∧ (∀ i, y i ∈ Y) ∧ ∀ k, l k = ∑ i, c i * eval (y i) (F k)}`.
Note: `SA n ∩ LSC n ∩ CB n` parses as `(SA n ∩ LSC n) ∩ CB n`.

```
@IsPolyFun.exists_eval_pick : ∀ {n : ℕ} {ι α : Type} {P : (Fin n → ℝ) → (ι → ℝ) → ℝ},
  IsPolyFun P →
    ∀ (a : Fin n → α) (b : ι → α), ∃ p, ∀ (w : α → ℝ), (P (fun i => w (a i)) fun j => w (b j)) = (MvPolynomial.eval w) p
@IsSemialgebraic.pick : ∀ {α β γ : Type} {S : Set (α ⊕ β → ℝ)},
  IsSemialgebraic S →
    ∀ (a : α → γ) (b : β → γ), IsSemialgebraic {w | (Sum.elim (fun i => w (a i)) fun j => w (b j)) ∈ S}
@argminGraph : {n : ℕ} → {ι : Type} → ((Fin n → ℝ) → (ι → ℝ) → ℝ) → Set (ι → ℝ) → Set (Fin n ⊕ ι → ℝ)
@sumElim_mem_argminGraph_iff : ∀ {n : ℕ} {ι : Type} {Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} {Y : Set (ι → ℝ)} {x : Fin n → ℝ}
  {y : ι → ℝ}, Sum.elim x y ∈ argminGraph Q Y ↔ y ∈ argminSet Q Y x
@isSemialgebraic_argminGraph : ∀ {n : ℕ} {ι : Type} [HasSemialgebraicProjections] [Fintype ι]
  {Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} {Y : Set (ι → ℝ)}, IsPolyFun Q → IsSemialgebraic Y → IsSemialgebraic (argminGraph Q Y)
@valueFun_isExtSemialgebraic : ∀ [HasSemialgebraicProjections] {n : ℕ} {ι : Type} [Fintype ι]
  {P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} {Y : Set (ι → ℝ)},
  IsPolyFun P → IsPolyFun Q → IsSemialgebraic Y → IsExtSemialgebraic (valueFun P Q Y)
@pvalueFun_isExtSemialgebraic : ∀ [HasSemialgebraicProjections] {n : ℕ} {ι : Type} [Fintype ι]
  {P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} {Y : Set (ι → ℝ)},
  IsPolyFun P → IsPolyFun Q → IsSemialgebraic Y → IsExtSemialgebraic (pvalueFun P Q Y)
@P_unbound_subset_SA : ∀ [HasSemialgebraicProjections] {n : ℕ}, P_unbound n ⊆ SA n
@P_bounded_subset_SA : ∀ [HasSemialgebraicProjections] {n : ℕ}, P_bounded n ⊆ SA n
@P_box_subset_SA : ∀ [HasSemialgebraicProjections] {n : ℕ}, P_box n ⊆ SA n
@C_unbound_subset_SA : ∀ [HasSemialgebraicProjections] {n : ℕ}, C_unbound n ⊆ SA n
@C_bounded_subset_SA : ∀ [HasSemialgebraicProjections] {n : ℕ}, C_bounded n ⊆ SA n
@C_cc_subset_SA : ∀ [HasSemialgebraicProjections] {n : ℕ}, C_cc n ⊆ SA n
@Pp_unbound_subset_SA : ∀ [HasSemialgebraicProjections] {n : ℕ}, Pp_unbound n ⊆ SA n
@Pp_bounded_subset_SA : ∀ [HasSemialgebraicProjections] {n : ℕ}, Pp_bounded n ⊆ SA n
@Pp_box_subset_SA : ∀ [HasSemialgebraicProjections] {n : ℕ}, Pp_box n ⊆ SA n
@Cp_unbound_subset_SA : ∀ [HasSemialgebraicProjections] {n : ℕ}, Cp_unbound n ⊆ SA n
@Cp_bounded_subset_SA : ∀ [HasSemialgebraicProjections] {n : ℕ}, Cp_bounded n ⊆ SA n
@Cp_cc_subset_SA : ∀ [HasSemialgebraicProjections] {n : ℕ}, Cp_cc n ⊆ SA n
@thm212_eq_SA : ∀ [HasSemialgebraicProjections] {n : ℕ}, P_unbound n = SA n
@thm212_eq_SA_pess : ∀ [HasSemialgebraicProjections] {n : ℕ}, Pp_unbound n = SA n
@thm218_main : ∀ [HasSemialgebraicProjections] {n : ℕ}, PPe n ⊆ C_unbound n ∧ C_unbound n ⊆ SA n
@thm218_main_pess : ∀ [HasSemialgebraicProjections] {n : ℕ}, PPe n ⊆ Cp_unbound n ∧ Cp_unbound n ⊆ SA n
@thm215_subset : ∀ [HasSemialgebraicProjections] {n : ℕ}, P_bounded n ⊆ SA n ∩ LSC n ∩ CB n
@thm220_subset : ∀ [HasSemialgebraicProjections] {n : ℕ}, C_bounded n ⊆ SA n ∩ LSC n ∩ CB n
@thm221_subset : ∀ [HasSemialgebraicProjections] {n : ℕ}, C_cc n ⊆ SA n ∩ LSC n ∩ CB n
@thm215_subset_pess : ∀ [HasSemialgebraicProjections] {n : ℕ}, Pp_bounded n ⊆ SA n ∩ USC n ∩ CB n
@thm220_subset_pess : ∀ [HasSemialgebraicProjections] {n : ℕ}, Cp_bounded n ⊆ SA n ∩ USC n ∩ CB n
@thm221_subset_pess : ∀ [HasSemialgebraicProjections] {n : ℕ}, Cp_cc n ⊆ SA n ∩ USC n ∩ CB n
@hullSlice : {m K : Type} → Set (m → ℝ) → (K → MvPolynomial m ℝ) → ℕ → Set (K → ℝ)
@hullSlice_subset_convexHull : ∀ {m K : Type} (Y : Set (m → ℝ)) (F : K → MvPolynomial m ℝ) (N : ℕ),
  hullSlice Y F N ⊆ (convexHull ℝ) ((fun y k => (MvPolynomial.eval y) (F k)) '' Y)
@convexHull_subset_iUnion_hullSlice : ∀ {m K : Type} [inst : Fintype K] (Y : Set (m → ℝ)) (F : K → MvPolynomial m ℝ),
  (convexHull ℝ) ((fun y k => (MvPolynomial.eval y) (F k)) '' Y) ⊆ ⋃ N, hullSlice Y F ↑N
@convexHull_eq_iUnion_hullSlice : ∀ {m K : Type} [inst : Fintype K] (Y : Set (m → ℝ)) (F : K → MvPolynomial m ℝ),
  (convexHull ℝ) ((fun y k => (MvPolynomial.eval y) (F k)) '' Y) = ⋃ N, hullSlice Y F ↑N
@isSemialgebraic_hullSlice : ∀ {m K : Type} [HasSemialgebraicProjections] [Fintype m] [Fintype K] {Y : Set (m → ℝ)},
  IsSemialgebraic Y → ∀ (F : K → MvPolynomial m ℝ) (N : ℕ), IsSemialgebraic (hullSlice Y F N)
@isSemialgebraic_convexHull_image : ∀ {m K : Type} [HasSemialgebraicProjections] [Fintype m] [Fintype K]
  {Y : Set (m → ℝ)},
  IsSemialgebraic Y →
    ∀ (F : K → MvPolynomial m ℝ), IsSemialgebraic ((convexHull ℝ) ((fun y k => (MvPolynomial.eval y) (F k)) '' Y))
```
