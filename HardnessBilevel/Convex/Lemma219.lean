import HardnessBilevel.Convex.Toolkit

/-!
# Lemma 2.19 (simplified gadget, blueprint §4.G.2) — id `t219.main`

For a basic set `S = {x | P(x) = 0 ∧ ∀ j, 0 < Q_j(x)}` (`basicSet P Q`), lower variable `y : Unit ⊕ J → ℝ`
(`t = y (inl ())`, `u j = y (inr j)`), box `gadY J = ℝ × [0,∞)^J` and
* `gadQ P Q x y = (1 - t P(x))^2 + ∑ j (1 - Q_j(x) u_j)^2`,
* `gadP P Q x y = (1 - t P(x)) * ∏ j (Q_j(x) u_j)`,

the lower level is polynomial and convex, the box is unbounded (because of the free coordinate `t`, even if
`J = ∅`), every argmin is nonempty, and `gadP` is **constant** on the argmin with value `1_S x`; hence
`valueFun = pvalueFun = ↑(1_S x)` (`lemma219`, `lemma219_exists`).
-/

namespace Bilevel

open Set MvPolynomial

section Lemma219

variable {n : ℕ} {J : Type*} [Fintype J]

/-- The basic semialgebraic set `{x | P(x) = 0 ∧ ∀ j, 0 < Q_j(x)}`. -/
def basicSet (P : MvPolynomial (Fin n) ℝ) (Q : J → MvPolynomial (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | eval x P = 0 ∧ ∀ j, 0 < eval x (Q j)}

/-- Lower-level objective `Q'` of the Lemma 2.19 gadget. -/
noncomputable def gadQ (P : MvPolynomial (Fin n) ℝ) (Q : J → MvPolynomial (Fin n) ℝ) :
    (Fin n → ℝ) → (Unit ⊕ J → ℝ) → ℝ :=
  fun x y => (1 - y (Sum.inl ()) * eval x P) ^ 2 + ∑ j, (1 - eval x (Q j) * y (Sum.inr j)) ^ 2

/-- Upper-level objective `P'` of the Lemma 2.19 gadget. -/
noncomputable def gadP (P : MvPolynomial (Fin n) ℝ) (Q : J → MvPolynomial (Fin n) ℝ) :
    (Fin n → ℝ) → (Unit ⊕ J → ℝ) → ℝ :=
  fun x y => (1 - y (Sum.inl ()) * eval x P) * ∏ j, (eval x (Q j) * y (Sum.inr j))

/-- The box `ℝ × [0,∞)^J` of the Lemma 2.19 gadget. -/
def gadY (J : Type*) : Set (Unit ⊕ J → ℝ) :=
  Set.pi Set.univ (Sum.elim (fun _ => Set.univ) (fun _ => Set.Ici 0))

theorem mem_argminSet_gadQ_iff (P : MvPolynomial (Fin n) ℝ) (Q : J → MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (y : Unit ⊕ J → ℝ) :
    y ∈ argminSet (gadQ P Q) (gadY J) x ↔
      (∀ t, (1 - eval x P * y (Sum.inl ())) ^ 2 ≤ (1 - eval x P * t) ^ 2) ∧
        ∀ j, 0 ≤ y (Sum.inr j) ∧
          ∀ u, 0 ≤ u → (1 - eval x (Q j) * y (Sum.inr j)) ^ 2 ≤ (1 - eval x (Q j) * u) ^ 2 := by
  let g : (Fin n → ℝ) → (Unit ⊕ J) → ℝ → ℝ := fun x =>
    Sum.elim (fun _ v => (1 - eval x P * v) ^ 2) (fun j v => (1 - eval x (Q j) * v) ^ 2)
  have hQ : gadQ P Q = fun x y => ∑ c, g x c (y c) := by
    funext x y
    simp [gadQ, g, Fintype.sum_sum_type, mul_comm]
  rw [hQ, gadY, argminSet_pi_sum]
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Sum.forall, argminSet, Set.mem_ofPred_eq,
    Sum.elim_inl, Sum.elim_inr, g, Set.mem_Ici, true_and]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1 (), h2⟩, fun ⟨h1, h2⟩ => ⟨fun _ => h1, h2⟩⟩

/-- Witness of a minimiser of the gadget. -/
noncomputable def gadMin (P : MvPolynomial (Fin n) ℝ) (Q : J → MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) : Unit ⊕ J → ℝ :=
  Sum.elim (fun _ => if eval x P = 0 then 0 else (eval x P)⁻¹)
    (fun j => if 0 < eval x (Q j) then (eval x (Q j))⁻¹ else 0)

theorem gadMin_mem (P : MvPolynomial (Fin n) ℝ) (Q : J → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    gadMin P Q x ∈ argminSet (gadQ P Q) (gadY J) x := by
  rw [mem_argminSet_gadQ_iff]
  exact ⟨isMin_univ_witness _, fun j => isMin_Ici_witness _⟩

theorem argminSet_gadQ_nonempty (P : MvPolynomial (Fin n) ℝ) (Q : J → MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) : (argminSet (gadQ P Q) (gadY J) x).Nonempty :=
  ⟨_, gadMin_mem P Q x⟩

/-- `t219.main`, core: `P'` is constant on the argmin, equal to `1_S x`. -/
theorem gadP_eq_indicator (P : MvPolynomial (Fin n) ℝ) (Q : J → MvPolynomial (Fin n) ℝ)
    {x : Fin n → ℝ} {y : Unit ⊕ J → ℝ} (hy : y ∈ argminSet (gadQ P Q) (gadY J) x) :
    gadP P Q x y = (basicSet P Q).indicator 1 x := by
  classical
  rw [mem_argminSet_gadQ_iff] at hy
  obtain ⟨h1, h2⟩ := hy
  have e1 := mul_eq_of_isMin_univ h1
  have e2 : ∀ j, eval x (Q j) * y (Sum.inr j) = if 0 < eval x (Q j) then 1 else 0 :=
    fun j => mul_eq_of_isMin_Ici (h2 j).1 (h2 j).2
  have hP : gadP P Q x y = (1 - (if eval x P = 0 then 0 else 1)) *
      ∏ j, (if 0 < eval x (Q j) then (1 : ℝ) else 0) := by
    simp only [gadP, e2, mul_comm (y (Sum.inl ())), e1]
  rw [hP]
  by_cases hx : x ∈ basicSet P Q
  · rw [Set.indicator_of_mem hx]
    obtain ⟨hx1, hx2⟩ := hx
    simp [hx1, hx2]
  · rw [Set.indicator_of_notMem hx]
    simp only [basicSet, Set.mem_ofPred_eq, not_and_or, not_forall] at hx
    rcases hx with hx | ⟨j, hj⟩
    · simp [hx]
    · rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero]

theorem isPolyFun_gadQ (P : MvPolynomial (Fin n) ℝ) (Q : J → MvPolynomial (Fin n) ℝ) :
    IsPolyFun (gadQ P Q) := by
  unfold gadQ
  exact (((isPolyFun_const 1).sub ((isPolyFun_y (Sum.inl ())).mul
      (IsPolyFun.of_upper_only P))).pow 2).add
    (isPolyFun_finset_sum Finset.univ fun j _ => ((isPolyFun_const 1).sub
      ((IsPolyFun.of_upper_only (Q j)).mul (isPolyFun_y (Sum.inr j)))).pow 2)

theorem isPolyFun_gadP (P : MvPolynomial (Fin n) ℝ) (Q : J → MvPolynomial (Fin n) ℝ) :
    IsPolyFun (gadP P Q) := by
  unfold gadP
  exact ((isPolyFun_const 1).sub ((isPolyFun_y (Sum.inl ())).mul
      (IsPolyFun.of_upper_only P))).mul
    (isPolyFun_finset_prod Finset.univ fun j _ =>
      (IsPolyFun.of_upper_only (Q j)).mul (isPolyFun_y (Sum.inr j)))

theorem convexLower_gadQ (P : MvPolynomial (Fin n) ℝ) (Q : J → MvPolynomial (Fin n) ℝ) :
    ConvexLower (gadQ P Q) := fun x =>
  ((convexOn_sq_one_sub_mul_coord (eval x P) (Sum.inl ())).add
    (convexOn_finset_sum convex_univ Finset.univ fun j _ =>
      convexOn_sq_one_sub_mul_coord (eval x (Q j)) (Sum.inr j))).congr
    (fun y _ => by simp [gadQ, mul_comm])

theorem isUnboundedBox_gadY (J : Type*) : IsUnboundedBox (gadY J) :=
  isUnboundedBox_sum_univ_Ici

/-- **Lemma 2.19** (`t219.main`, simplified gadget). -/
theorem lemma219 (P : MvPolynomial (Fin n) ℝ) (Q : J → MvPolynomial (Fin n) ℝ) :
    IsPolyFun (gadP P Q) ∧ IsPolyFun (gadQ P Q) ∧ ConvexLower (gadQ P Q) ∧ IsUnboundedBox (gadY J) ∧
      (∀ x, (argminSet (gadQ P Q) (gadY J) x).Nonempty ∧
        ∀ y ∈ argminSet (gadQ P Q) (gadY J) x, gadP P Q x y = (basicSet P Q).indicator 1 x) ∧
      valueFun (gadP P Q) (gadQ P Q) (gadY J) = (fun x => (((basicSet P Q).indicator 1 x : ℝ) : EReal)) ∧
      pvalueFun (gadP P Q) (gadQ P Q) (gadY J) = (fun x => (((basicSet P Q).indicator 1 x : ℝ) : EReal)) :=
  ⟨isPolyFun_gadP P Q, isPolyFun_gadQ P Q, convexLower_gadQ P Q, isUnboundedBox_gadY J,
    fun x => ⟨argminSet_gadQ_nonempty P Q x, fun _ hy => gadP_eq_indicator P Q hy⟩,
    funext fun x => valueFun_eq_of_const (argminSet_gadQ_nonempty P Q x)
      (fun _ hy => gadP_eq_indicator P Q hy),
    funext fun x => pvalueFun_eq_of_const (argminSet_gadQ_nonempty P Q x)
      (fun _ hy => gadP_eq_indicator P Q hy)⟩

/-- **Lemma 2.19**, existential form (paper statement, with constancy of `P'` on the argmin). -/
theorem lemma219_exists {J : Type} [Fintype J] (P : MvPolynomial (Fin n) ℝ)
    (Q : J → MvPolynomial (Fin n) ℝ) :
    ∃ (ι : Type) (_ : Fintype ι) (P' Q' : (Fin n → ℝ) → (ι → ℝ) → ℝ) (Y : Set (ι → ℝ)),
      IsPolyFun P' ∧ IsPolyFun Q' ∧ ConvexLower Q' ∧ IsUnboundedBox Y ∧
      (∀ x, (argminSet Q' Y x).Nonempty ∧
        ∀ y ∈ argminSet Q' Y x, P' x y = (basicSet P Q).indicator 1 x) ∧
      valueFun P' Q' Y = (fun x => (((basicSet P Q).indicator 1 x : ℝ) : EReal)) ∧
      pvalueFun P' Q' Y = (fun x => (((basicSet P Q).indicator 1 x : ℝ) : EReal)) :=
  ⟨Unit ⊕ J, inferInstance, gadP P Q, gadQ P Q, gadY J, lemma219 P Q⟩

end Lemma219

end Bilevel
