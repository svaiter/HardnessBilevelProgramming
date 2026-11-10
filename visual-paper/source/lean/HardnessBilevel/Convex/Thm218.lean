import HardnessBilevel.Convex.Lemma219
import HardnessBilevel.Semialgebraic.Basic

/-!
# Theorem 2.18, first inclusion — construction (blueprint §4.G.3) — id `t218.sum_indicator`

For any finite family `(S i, p i)_{i < N}` where each `S i = ⋃_{j < J i} T i j` is a finite union of basic
sets `T i j = {PT i j = 0 ∧ ∀ k, 0 < QT i j k}` (no disjointness assumed), the function
`x ↦ ∑ i, 1_{S i}(x) p_i(x)` is the (optimistic and pessimistic) value function of a polynomial bilevel problem
with lower level convex in `y` over an unbounded box, and `P` is constant on every (nonempty) argmin.

Construction: one Lemma-2.19 block per pair `b = ⟨i, j⟩`, lower index type
`t218Idx J K = Unit ⊕ Σ (b : Σ i, Fin (J i)), (Unit ⊕ Fin (K b.1 b.2))` (the leading `Unit` is a dummy free
coordinate with zero objective term, so the box is unconditionally unbounded), separable
`Q x y = ∑ b, gadQ_b x (y|_b)` and `P x y = ∑ i, p_i(x) (1 - ∏_j (1 - gadP_ij x (y|_ij)))`.

Versions: `sum_indicator` (basic sets given as polynomial data), `sum_indicator_basic` (each `S i` a finite union of
`IsBasicSA` sets), `sum_indicator_semialgebraic` (each `S i` semialgebraic). The class statement
`PP ⊆ C_unbound` belongs to a later unit.
-/

namespace Bilevel

open Set MvPolynomial

/-! ### Separable argmin helpers -/

/-- Argmin of an objective that ignores the `Sum.inl` coordinates, over a set that does not constrain them. -/
theorem mem_argminSet_comp_inr_iff {X α β : Type*} (B : X → (β → ℝ) → ℝ) (W : Set (β → ℝ)) (x : X)
    (y : α ⊕ β → ℝ) :
    y ∈ argminSet (fun x y => B x (y ∘ Sum.inr)) {y | y ∘ Sum.inr ∈ W} x ↔
      y ∘ Sum.inr ∈ argminSet B W x := by
  simp only [argminSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun z hz => ?_⟩
    have := h (Sum.elim (y ∘ Sum.inl) z) (by simpa using hz)
    simpa using this
  · rintro ⟨hy, h⟩
    exact ⟨hy, fun y' hy' => h _ hy'⟩

/-- Blockwise-separable argmin over a `Sigma` index type: the argmin is the product of the block argmins
(blueprint `fw.argmin_pi_sum`, transported along `Equiv.piCurry`). -/
theorem mem_argminSet_sigma_iff {X B : Type*} [Fintype B] {κ : B → Type*}
    (W : ∀ b, Set (κ b → ℝ)) (g : ∀ b, X → (κ b → ℝ) → ℝ) (x : X) (y : (Σ b, κ b) → ℝ) :
    y ∈ argminSet (fun x y => ∑ b, g b x (fun k => y ⟨b, k⟩)) {y | ∀ b, (fun k => y ⟨b, k⟩) ∈ W b} x ↔
      ∀ b, (fun k => y ⟨b, k⟩) ∈ argminSet (g b) (W b) x := by
  have h := argminSet_comp_equiv (fun x (z : ∀ b, κ b → ℝ) => ∑ b, g b x (z b)) (Set.pi univ W)
    (Equiv.piCurry (fun b (_ : κ b) => ℝ)) x
  rw [argminSet_pi_sum] at h
  have hW : {y : (Σ b, κ b) → ℝ | ∀ b, (fun k => y ⟨b, k⟩) ∈ W b} =
      (Equiv.piCurry (fun b (_ : κ b) => ℝ)) ⁻¹' Set.pi univ W := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
    exact Iff.rfl
  rw [hW]
  change y ∈ argminSet (fun x y' => ∑ b, g b x (Equiv.piCurry (fun b (_ : κ b) => ℝ) y' b)) _ x ↔ _
  rw [h]
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
  exact Iff.rfl

/-! ### The product formula for the indicator of a finite union -/

theorem one_sub_prod_one_sub_indicator {X κ : Type*} [Fintype κ] (T : κ → Set X) (x : X) :
    1 - ∏ j, (1 - (T j).indicator (1 : X → ℝ) x) = (⋃ j, T j).indicator 1 x := by
  classical
  by_cases hx : x ∈ ⋃ j, T j
  · rw [Set.indicator_of_mem hx]
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [Set.indicator_of_mem hj]), sub_zero]
    rfl
  · rw [Set.indicator_of_notMem hx]
    have : ∀ j, (T j).indicator (1 : X → ℝ) x = 0 := fun j =>
      Set.indicator_of_notMem (fun h => hx (Set.mem_iUnion.mpr ⟨j, h⟩)) _
    simp [this]

/-! ### The construction -/

section Construction

variable {n N : ℕ} (J : Fin N → ℕ) (K : (i : Fin N) → Fin (J i) → ℕ)

/-- Lower index type of the Thm 2.18 construction: dummy coordinate, then one Lemma-2.19 block per `⟨i, j⟩`. -/
abbrev t218Idx : Type := Unit ⊕ Σ b : (Σ i : Fin N, Fin (J i)), (Unit ⊕ Fin (K b.1 b.2))

/-- Projection of the lower variable onto block `b = ⟨i, j⟩`. -/
def t218Blk (b : Σ i : Fin N, Fin (J i)) (y : t218Idx J K → ℝ) : Unit ⊕ Fin (K b.1 b.2) → ℝ :=
  fun k => y (Sum.inr ⟨b, k⟩)

variable {J K}
variable (PT : (i : Fin N) → Fin (J i) → MvPolynomial (Fin n) ℝ)
  (QT : (i : Fin N) → (j : Fin (J i)) → Fin (K i j) → MvPolynomial (Fin n) ℝ)
  (p : Fin N → MvPolynomial (Fin n) ℝ)

/-- Lower-level objective: sum of the Lemma-2.19 objectives of the blocks. -/
noncomputable def t218Q : (Fin n → ℝ) → (t218Idx J K → ℝ) → ℝ :=
  fun x y => ∑ b, gadQ (PT b.1 b.2) (QT b.1 b.2) x (fun k => y (Sum.inr ⟨b, k⟩))

/-- Upper-level objective `∑ i, p_i(x) (1 - ∏_j (1 - P'_ij(x, y|_ij)))`. -/
noncomputable def t218P : (Fin n → ℝ) → (t218Idx J K → ℝ) → ℝ :=
  fun x y => ∑ i, eval x (p i) *
    (1 - ∏ j, (1 - gadP (PT i j) (QT i j) x (fun k => y (Sum.inr ⟨⟨i, j⟩, k⟩))))

variable (J K) in
/-- The mixed box: dummy and `t`-coordinates free, `u`-coordinates in `[0, ∞)`. -/
def t218Y : Set (t218Idx J K → ℝ) :=
  Set.pi Set.univ (Sum.elim (fun _ => Set.univ)
    (fun s => Sum.elim (fun _ => (Set.univ : Set ℝ)) (fun _ => Set.Ici 0) s.2))

theorem mem_argminSet_t218Q_iff (x : Fin n → ℝ) (y : t218Idx J K → ℝ) :
    y ∈ argminSet (t218Q PT QT) (t218Y J K) x ↔
      ∀ b, t218Blk J K b y ∈ argminSet (gadQ (PT b.1 b.2) (QT b.1 b.2)) (gadY _) x := by
  have hY : t218Y J K = {y : t218Idx J K → ℝ | y ∘ Sum.inr ∈
      {z : (Σ b : (Σ i : Fin N, Fin (J i)), (Unit ⊕ Fin (K b.1 b.2))) → ℝ |
        ∀ b, (fun k => z ⟨b, k⟩) ∈ gadY (Fin (K b.1 b.2))}} := by
    ext y
    simp only [t218Y, gadY, Set.mem_pi, Set.mem_univ, true_implies, Sum.forall, Sum.elim_inl,
      Sum.elim_inr, Sigma.forall, Set.mem_ofPred_eq, Function.comp_apply, implies_true, true_and]
  rw [hY]
  have h1 := mem_argminSet_comp_inr_iff (α := Unit)
    (fun x (z : (Σ b : (Σ i : Fin N, Fin (J i)), (Unit ⊕ Fin (K b.1 b.2))) → ℝ) =>
      ∑ b, gadQ (PT b.1 b.2) (QT b.1 b.2) x (fun k => z ⟨b, k⟩))
    {z | ∀ b, (fun k => z ⟨b, k⟩) ∈ gadY (Fin (K b.1 b.2))} x y
  have h2 := mem_argminSet_sigma_iff (fun b : (Σ i : Fin N, Fin (J i)) => gadY (Fin (K b.1 b.2)))
    (fun b => gadQ (PT b.1 b.2) (QT b.1 b.2)) x (y ∘ Sum.inr)
  exact h1.trans h2

theorem argminSet_t218Q_nonempty (x : Fin n → ℝ) :
    (argminSet (t218Q PT QT) (t218Y J K) x).Nonempty := by
  refine ⟨Sum.elim (fun _ => 0) (fun s => gadMin (PT s.1.1 s.1.2) (QT s.1.1 s.1.2) x s.2), ?_⟩
  rw [mem_argminSet_t218Q_iff]
  intro b
  exact gadMin_mem _ _ x

theorem t218P_eq_on_argmin (S : Fin N → Set (Fin n → ℝ))
    (hS : ∀ i, S i = ⋃ j, basicSet (PT i j) (QT i j)) {x : Fin n → ℝ} {y : t218Idx J K → ℝ}
    (hy : y ∈ argminSet (t218Q PT QT) (t218Y J K) x) :
    t218P PT QT p x y = ∑ i, (S i).indicator 1 x * eval x (p i) := by
  rw [mem_argminSet_t218Q_iff] at hy
  unfold t218P
  refine Finset.sum_congr rfl fun i _ => ?_
  have hb : ∀ j, gadP (PT i j) (QT i j) x (fun k => y (Sum.inr ⟨⟨i, j⟩, k⟩)) =
      (basicSet (PT i j) (QT i j)).indicator 1 x := fun j => gadP_eq_indicator _ _ (hy ⟨i, j⟩)
  simp only [hb]
  rw [one_sub_prod_one_sub_indicator, ← hS i, mul_comm]

theorem isPolyFun_t218Q : IsPolyFun (t218Q PT QT) := by
  unfold t218Q
  exact isPolyFun_finset_sum Finset.univ fun b _ =>
    (isPolyFun_gadQ (PT b.1 b.2) (QT b.1 b.2)).rename (fun k => (Sum.inr ⟨b, k⟩ : t218Idx J K))

theorem isPolyFun_t218P : IsPolyFun (t218P PT QT p) := by
  unfold t218P
  exact isPolyFun_finset_sum Finset.univ fun i _ =>
    (IsPolyFun.of_upper_only (p i)).mul ((isPolyFun_const 1).sub
      (isPolyFun_finset_prod Finset.univ fun j _ => (isPolyFun_const 1).sub
        ((isPolyFun_gadP (PT i j) (QT i j)).rename (fun k => (Sum.inr ⟨⟨i, j⟩, k⟩ : t218Idx J K)))))

theorem convexLower_t218Q : ConvexLower (t218Q PT QT) := by
  unfold t218Q
  exact ConvexLower.finset_sum Finset.univ fun b _ =>
    (convexLower_gadQ (PT b.1 b.2) (QT b.1 b.2)).comp_reindex (fun k => (Sum.inr ⟨b, k⟩ : t218Idx J K))

variable (J K) in
theorem isUnboundedBox_t218Y : IsUnboundedBox (t218Y J K) := by
  refine isUnboundedBox_pi_univ_or_Ici _ ?_ ⟨Sum.inl (), rfl⟩
  rintro (_ | ⟨b, _ | _⟩)
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

end Construction

/-- **`t218.sum_indicator`** (Thm 2.18 first inclusion, strengthened): basic sets given as polynomial data. -/
theorem sum_indicator {n N : ℕ} (J : Fin N → ℕ) (K : (i : Fin N) → Fin (J i) → ℕ)
    (PT : (i : Fin N) → Fin (J i) → MvPolynomial (Fin n) ℝ)
    (QT : (i : Fin N) → (j : Fin (J i)) → Fin (K i j) → MvPolynomial (Fin n) ℝ)
    (S : Fin N → Set (Fin n → ℝ)) (hS : ∀ i, S i = ⋃ j, basicSet (PT i j) (QT i j))
    (p : Fin N → MvPolynomial (Fin n) ℝ) :
    ∃ (ι : Type) (_ : Fintype ι) (P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ) (Y : Set (ι → ℝ)),
      IsPolyFun P ∧ IsPolyFun Q ∧ ConvexLower Q ∧ IsUnboundedBox Y ∧
      (∀ x, (argminSet Q Y x).Nonempty ∧
        ∀ y ∈ argminSet Q Y x, P x y = ∑ i, (S i).indicator 1 x * eval x (p i)) ∧
      valueFun P Q Y = (fun x => ((∑ i, (S i).indicator 1 x * eval x (p i) : ℝ) : EReal)) ∧
      pvalueFun P Q Y = (fun x => ((∑ i, (S i).indicator 1 x * eval x (p i) : ℝ) : EReal)) :=
  ⟨t218Idx J K, inferInstance, t218P PT QT p, t218Q PT QT, t218Y J K,
    isPolyFun_t218P PT QT p, isPolyFun_t218Q PT QT, convexLower_t218Q PT QT, isUnboundedBox_t218Y J K,
    fun x => ⟨argminSet_t218Q_nonempty PT QT x, fun _ hy => t218P_eq_on_argmin PT QT p S hS hy⟩,
    funext fun x => valueFun_eq_of_const (argminSet_t218Q_nonempty PT QT x)
      (fun _ hy => t218P_eq_on_argmin PT QT p S hS hy),
    funext fun x => pvalueFun_eq_of_const (argminSet_t218Q_nonempty PT QT x)
      (fun _ hy => t218P_eq_on_argmin PT QT p S hS hy)⟩

/-- `t218.sum_indicator`, version with each `S i` a finite union of `IsBasicSA` sets. -/
theorem sum_indicator_basic {n N : ℕ} (S : Fin N → Set (Fin n → ℝ))
    (hS : ∀ i, ∃ (m : ℕ) (T : Fin m → Set (Fin n → ℝ)), (∀ j, IsBasicSA (T j)) ∧ S i = ⋃ j, T j)
    (p : Fin N → MvPolynomial (Fin n) ℝ) :
    ∃ (ι : Type) (_ : Fintype ι) (P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ) (Y : Set (ι → ℝ)),
      IsPolyFun P ∧ IsPolyFun Q ∧ ConvexLower Q ∧ IsUnboundedBox Y ∧
      (∀ x, (argminSet Q Y x).Nonempty ∧
        ∀ y ∈ argminSet Q Y x, P x y = ∑ i, (S i).indicator 1 x * eval x (p i)) ∧
      valueFun P Q Y = (fun x => ((∑ i, (S i).indicator 1 x * eval x (p i) : ℝ) : EReal)) ∧
      pvalueFun P Q Y = (fun x => ((∑ i, (S i).indicator 1 x * eval x (p i) : ℝ) : EReal)) := by
  choose J T hT hST using hS
  choose PT K QT hPT using hT
  exact sum_indicator J K PT QT S (fun i => (hST i).trans (Set.iUnion_congr fun j => hPT i j)) p

/-- `t218.sum_indicator`, version with each `S i` semialgebraic (decomposed by `sa.finite_union_basic`). -/
theorem sum_indicator_semialgebraic {n N : ℕ} (S : Fin N → Set (Fin n → ℝ))
    (hS : ∀ i, IsSemialgebraic (S i)) (p : Fin N → MvPolynomial (Fin n) ℝ) :
    ∃ (ι : Type) (_ : Fintype ι) (P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ) (Y : Set (ι → ℝ)),
      IsPolyFun P ∧ IsPolyFun Q ∧ ConvexLower Q ∧ IsUnboundedBox Y ∧
      (∀ x, (argminSet Q Y x).Nonempty ∧
        ∀ y ∈ argminSet Q Y x, P x y = ∑ i, (S i).indicator 1 x * eval x (p i)) ∧
      valueFun P Q Y = (fun x => ((∑ i, (S i).indicator 1 x * eval x (p i) : ℝ) : EReal)) ∧
      pvalueFun P Q Y = (fun x => ((∑ i, (S i).indicator 1 x * eval x (p i) : ℝ) : EReal)) :=
  sum_indicator_basic S (fun i => isSemialgebraic_iff_finite_union_basic.mp (hS i)) p

end Bilevel
