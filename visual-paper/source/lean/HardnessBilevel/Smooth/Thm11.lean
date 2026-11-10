/-
Blueprint §4.C — Theorem 1.1 (smooth data realize every lower semicontinuous function).
Ids: `t11.T0` (construction `thm11P`, `thm11Q`), `t11.smooth` (`contDiff_thm11P`, `contDiff_thm11Q`),
`t11.nonneg` (`thm11Q_nonneg`), `t11.case_finite` (`valueFun_thm11_of_ne_top`),
`t11.case_top` (`argminSet_thm11Q_of_eq_top`, `valueFun_thm11_of_eq_top`),
`t11.main` (`exists_smooth_of_lowerSemicontinuous`), `t11.main_paper`
(`exists_smooth_of_lowerSemicontinuous_proper`), `t11.main_pess`
(`exists_smooth_of_upperSemicontinuous`). `t11.whitney` is in `Smooth/Whitney.lean`;
`t11.isClosed_realEpigraph` is `Bilevel.isClosed_realEpigraph` in `Framework/Semicont.lean`.

Remark: the domain hypothesis is `IsClosed {x | f x ≠ ⊤}` and NOT "`{x | f x ∈ ℝ}` closed": the
function `g` must vanish exactly on `{f < +∞}`. Values `-∞` are allowed; "proper" is not needed.
Smoothness is `ContDiff ℝ ∞` (C^∞), never `ContDiff ℝ ⊤` (analytic; the theorem is false there).
-/
import HardnessBilevel.Smooth.Whitney
import HardnessBilevel.Framework.Basic
import HardnessBilevel.Framework.Value
import HardnessBilevel.Framework.Semicont

open scoped ContDiff

namespace Bilevel

variable {n : ℕ}

/-- `t11.T0`: the leader objective `P(x,y) = y₀`. -/
def thm11P : (Fin n → ℝ) → (Fin 3 → ℝ) → ℝ := fun _ y => y 0

/-- `t11.T0`: the follower objective `Q(x,y) = h(x,y₀)² + (g(x) y₁)² + (1 - y₁ y₂)²`. -/
def thm11Q (h : (Fin n → ℝ) × ℝ → ℝ) (g : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → (Fin 3 → ℝ) → ℝ :=
  fun x y => h (x, y 0) ^ 2 + (g x * y 1) ^ 2 + (1 - y 1 * y 2) ^ 2

/-- `t11.smooth` (leader). -/
theorem contDiff_thm11P : ContDiff ℝ ∞ (Function.uncurry (thm11P (n := n))) := by
  unfold thm11P Function.uncurry
  fun_prop

/-- `t11.smooth` (follower). -/
theorem contDiff_thm11Q {h : (Fin n → ℝ) × ℝ → ℝ} {g : (Fin n → ℝ) → ℝ}
    (hh : ContDiff ℝ ∞ h) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (Function.uncurry (thm11Q h g)) := by
  unfold thm11Q Function.uncurry
  fun_prop

/-- `t11.nonneg`. -/
theorem thm11Q_nonneg (h : (Fin n → ℝ) × ℝ → ℝ) (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (y : Fin 3 → ℝ) : 0 ≤ thm11Q h g x y :=
  add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)

section Cases

variable {f : (Fin n → ℝ) → EReal} {h : (Fin n → ℝ) × ℝ → ℝ} {g : (Fin n → ℝ) → ℝ}

/-- `t11.case_finite`, step (iv): on `{f ≠ ⊤}` the follower's argmin is
`Z = {y | f x ≤ y₀ ∧ y₁ y₂ = 1}`. -/
theorem argminSet_thm11Q_of_ne_top (hh : ∀ p, h p = 0 ↔ f p.1 ≤ (p.2 : EReal))
    (hg : ∀ x, g x = 0 ↔ f x ≠ ⊤) {x : Fin n → ℝ} (hx : f x ≠ ⊤) :
    argminSet (thm11Q h g) Set.univ x = {y | f x ≤ ((y 0 : ℝ) : EReal) ∧ y 1 * y 2 = 1} := by
  have hg0 : g x = 0 := (hg x).2 hx
  have key : ∀ y : Fin 3 → ℝ,
      thm11Q h g x y = 0 ↔ f x ≤ ((y 0 : ℝ) : EReal) ∧ y 1 * y 2 = 1 := by
    intro y
    have e : thm11Q h g x y = h (x, y 0) ^ 2 + (1 - y 1 * y 2) ^ 2 := by
      simp only [thm11Q, hg0, zero_mul]; ring
    rw [e, add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _), sq_eq_zero_iff, sq_eq_zero_iff,
      hh, sub_eq_zero, eq_comm]
  have hmem : thm11Q h g x ![(f x).toReal, 1, 1] = 0 := by
    rw [key]
    refine ⟨?_, ?_⟩
    · simp only [Matrix.cons_val_zero]
      exact EReal.le_coe_toReal hx
    · simp
  rw [argminSet_eq_zeroSet (fun y _ => thm11Q_nonneg h g x y) ⟨_, Set.mem_univ _, hmem⟩]
  ext y
  simp only [Set.mem_univ, true_and, Set.mem_ofPred_eq, key]

/-- `t11.case_finite`: on `{f ≠ ⊤}` the optimistic value is `f x` (including `f x = ⊥`). -/
theorem valueFun_thm11_of_ne_top (hh : ∀ p, h p = 0 ↔ f p.1 ≤ (p.2 : EReal))
    (hg : ∀ x, g x = 0 ↔ f x ≠ ⊤) {x : Fin n → ℝ} (hx : f x ≠ ⊤) :
    valueFun thm11P (thm11Q h g) Set.univ x = f x := by
  rw [valueFun, argminSet_thm11Q_of_ne_top hh hg hx]
  generalize he : f x = e at hx ⊢
  induction e using EReal.rec with
  | bot =>
    rw [EReal.eq_bot_iff_forall_lt]
    intro r
    calc _ ≤ ((thm11P x ![r - 1, 1, 1] : ℝ) : EReal) :=
          iInf₂_le (f := fun y (_ : y ∈ {y : Fin 3 → ℝ | (⊥ : EReal) ≤ ((y 0 : ℝ) : EReal) ∧
            y 1 * y 2 = 1}) => ((thm11P x y : ℝ) : EReal)) ![r - 1, 1, 1] ⟨bot_le, by simp⟩
      _ < (r : EReal) := by
          simp only [thm11P, Matrix.cons_val_zero]
          exact EReal.coe_lt_coe_iff.2 (by linarith)
  | coe r =>
    refine le_antisymm ?_ (le_iInf₂ fun y hy => hy.1)
    exact iInf₂_le (f := fun y (_ : y ∈ {y : Fin 3 → ℝ | ((r : ℝ) : EReal) ≤ ((y 0 : ℝ) : EReal) ∧
            y 1 * y 2 = 1}) => ((thm11P x y : ℝ) : EReal)) ![r, 1, 1] ⟨by simp, by simp⟩
  | top => exact absurd rfl hx

/-- `t11.case_top`: off `{f ≠ ⊤}` the follower problem has no minimiser. -/
theorem argminSet_thm11Q_of_eq_top (hg : ∀ x, g x = 0 ↔ f x ≠ ⊤) {x : Fin n → ℝ}
    (hx : f x = ⊤) : argminSet (thm11Q h g) Set.univ x = ∅ := by
  have hg0 : g x ≠ 0 := fun h0 => (hg x).1 h0 hx
  rw [argminSet_eq_empty_iff]
  intro y _
  set v := (g x * y 1) ^ 2 + (1 - y 1 * y 2) ^ 2 with hv
  have hvpos : 0 < v := by
    by_cases hy1 : y 1 = 0
    · simp [hv, hy1]
    · have : g x * y 1 ≠ 0 := mul_ne_zero hg0 hy1
      exact add_pos_of_pos_of_nonneg (by positivity) (sq_nonneg _)
  set ε := min 1 (v / (2 * (g x ^ 2 + 1))) with hεdef
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ v / (2 * (g x ^ 2 + 1)) := min_le_right _ _
  have hlt : (g x * ε) ^ 2 < v := by
    have hεε : ε ^ 2 ≤ ε := by nlinarith
    have h1 : (g x * ε) ^ 2 ≤ (g x ^ 2 + 1) * ε := by
      nlinarith [mul_le_mul_of_nonneg_left hεε (sq_nonneg (g x))]
    have h2 : ε * (2 * (g x ^ 2 + 1)) ≤ v := (le_div_iff₀ (by positivity)).1 hε2
    nlinarith
  refine ⟨![y 0, ε, 1 / ε], Set.mem_univ _, ?_⟩
  have e1 : thm11Q h g x ![y 0, ε, 1 / ε] = h (x, y 0) ^ 2 + (g x * ε) ^ 2 := by
    simp only [thm11Q, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [mul_one_div_cancel hε.ne', sub_self]
    ring
  have e2 : thm11Q h g x y = h (x, y 0) ^ 2 + v := by
    simp only [thm11Q, hv]; ring
  rw [e1, e2]
  linarith

/-- `t11.case_top`: off `{f ≠ ⊤}` the optimistic value is `⊤`. -/
theorem valueFun_thm11_of_eq_top (hg : ∀ x, g x = 0 ↔ f x ≠ ⊤) {x : Fin n → ℝ}
    (hx : f x = ⊤) : valueFun thm11P (thm11Q h g) Set.univ x = ⊤ :=
  valueFun_eq_top_iff.2 (argminSet_thm11Q_of_eq_top hg hx)

end Cases

/-- `t11.main` (Theorem 1.1, strengthened): every lower semicontinuous `f : ℝⁿ → [-∞, +∞]` whose
domain `{f ≠ ⊤}` is closed is the optimistic value function of a bilevel problem with `C^∞` data
and lower-level feasible set `ℝ³`. -/
theorem exists_smooth_of_lowerSemicontinuous {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : LowerSemicontinuous f) (hdom : IsClosed {x | f x ≠ ⊤}) :
    ∃ P Q : (Fin n → ℝ) → (Fin 3 → ℝ) → ℝ,
      ContDiff ℝ ∞ (Function.uncurry P) ∧ ContDiff ℝ ∞ (Function.uncurry Q) ∧
      valueFun P Q Set.univ = f := by
  obtain ⟨h, hhs, hh⟩ := exists_contDiff_zeroSet_eq (isClosed_realEpigraph hf)
  obtain ⟨g, hgs, hg⟩ := exists_contDiff_zeroSet_eq hdom
  refine ⟨thm11P, thm11Q h g, contDiff_thm11P, contDiff_thm11Q hhs hgs, ?_⟩
  funext x
  by_cases hx : f x = ⊤
  · rw [hx]
    exact valueFun_thm11_of_eq_top (h := h) hg hx
  · exact valueFun_thm11_of_ne_top hh hg hx

/-- `t11.main_paper` (Theorem 1.1 as stated in the paper, for proper `f`). The extra hypotheses
(`f` never `⊥`, `f` not identically `⊤`) are not needed. -/
theorem exists_smooth_of_lowerSemicontinuous_proper {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : LowerSemicontinuous f) (hdom : IsClosed {x | f x ≠ ⊤})
    (_hbot : ∀ x, f x ≠ ⊥) (_hproper : ∃ x, f x ≠ ⊤) :
    ∃ P Q : (Fin n → ℝ) → (Fin 3 → ℝ) → ℝ,
      ContDiff ℝ ∞ (Function.uncurry P) ∧ ContDiff ℝ ∞ (Function.uncurry Q) ∧
      valueFun P Q Set.univ = f :=
  exists_smooth_of_lowerSemicontinuous f hf hdom

/-- `t11.main_pess` (Theorem 1.1′, pessimistic twin): every upper semicontinuous
`f : ℝⁿ → [-∞, +∞]` with `{f ≠ ⊥}` closed is the pessimistic value function of a bilevel problem
with `C^∞` data and lower-level feasible set `ℝ³`. -/
theorem exists_smooth_of_upperSemicontinuous {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : UpperSemicontinuous f) (hdom : IsClosed {x | f x ≠ ⊥}) :
    ∃ P Q : (Fin n → ℝ) → (Fin 3 → ℝ) → ℝ,
      ContDiff ℝ ∞ (Function.uncurry P) ∧ ContDiff ℝ ∞ (Function.uncurry Q) ∧
      pvalueFun P Q Set.univ = f := by
  have hf' : LowerSemicontinuous fun x => -f x :=
    (upperSemicontinuous_iff_lowerSemicontinuous_neg f).1 hf
  have hdom' : IsClosed {x | -f x ≠ ⊤} := by
    simpa only [ne_eq, EReal.neg_eq_top_iff] using hdom
  obtain ⟨P, Q, hP, hQ, hval⟩ := exists_smooth_of_lowerSemicontinuous (fun x => -f x) hf' hdom'
  refine ⟨fun x y => -P x y, Q, hP.neg, hQ, ?_⟩
  funext x
  rw [pvalueFun_eq_neg_valueFun_neg]
  simp only [neg_neg]
  rw [hval, neg_neg]

end Bilevel
