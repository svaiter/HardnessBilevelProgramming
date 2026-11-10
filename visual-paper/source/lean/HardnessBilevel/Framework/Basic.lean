/-
Copyright: HardnessBilevel project.

# Framework: argmin sets and value functions (blueprint §4.A.1–§4.A.3)

Implements blueprint §2.2 / §4.A:
* definitions `argminSet`, `valueFun`, `pvalueFun`, `optVal` (§4.A.1);
* argmin lemmas F1 (`mem_argminSet_iff`), F2 (`argminSet_subset`), `mem_argminSet_univ`,
  F3 (`argminSet_eq_empty_iff`), F4 (`argminSet_eq_zeroSet`), F4′ (`mem_argminSet_of_nonneg_zero`),
  F6 (`argminSet_mul_pos`, `argminSet_add_left`), F8 (`argminSet_isClosed`, `argminSet_isCompact`),
  `fw.argmin_empty_of_pos_inf` (§4.E.1, A2; `argminSet_empty_of_pos_inf`, stated for a general `S`);
* value-function lemmas V1 (`valueFun_eq_top_iff`, twin `pvalueFun_eq_bot_iff`), V2
  (`valueFun_eq_of_isMinOn`, twin `pvalueFun_eq_of_isMaxOn`), F0 (`valueFun_eq_of_isLeast`, twin
  `pvalueFun_eq_of_isGreatest`), V5 (`valueFun_eq_of_const`, `pvalueFun_eq_of_const`), V5′
  (`valueFun_unique`), A5 (`valueFun_eq_bot_of_unbounded`, twin `pvalueFun_eq_top_of_unbounded`),
  the order helpers `valueFun_le_coe_of_mem`, `coe_le_valueFun_of_forall` (and twins);
* `fw.value_shift_attained` (§4.G.1) as `value_shift_attained`.

No assumption (A1–A3) is used.
-/
import Mathlib

namespace Bilevel

variable {X Y : Type*}

/-- Θ(x): the set of lower-level minimisers (blueprint §4.A.1). -/
def argminSet (Q : X → Y → ℝ) (S : Set Y) (x : X) : Set Y :=
  {y | y ∈ S ∧ ∀ y' ∈ S, Q x y ≤ Q x y'}

/-- Optimistic value function φ_o; `⊤` if Θ(x) = ∅, `⊥` if `P x` is unbounded below on Θ(x)
(blueprint §4.A.1). -/
noncomputable def valueFun (P Q : X → Y → ℝ) (S : Set Y) (x : X) : EReal :=
  ⨅ y ∈ argminSet Q S x, ((P x y : ℝ) : EReal)

/-- Pessimistic value function φ_p; `⊥` if Θ(x) = ∅ (blueprint §4.A.1). -/
noncomputable def pvalueFun (P Q : X → Y → ℝ) (S : Set Y) (x : X) : EReal :=
  ⨆ y ∈ argminSet Q S x, ((P x y : ℝ) : EReal)

/-- Optimal value of the whole bilevel problem over all upper-level points (blueprint §4.A.1). -/
noncomputable def optVal (P Q : X → Y → ℝ) (S : Set Y) : EReal :=
  ⨅ x, valueFun P Q S x

/-! ### Argmin sets -/

section Argmin

variable {Q : X → Y → ℝ} {S : Set Y} {x : X} {y : Y}

/-- fw.mem_argmin_iff (F1). -/
theorem mem_argminSet_iff : y ∈ argminSet Q S x ↔ y ∈ S ∧ IsMinOn (Q x) S y := by
  simp only [argminSet, isMinOn_iff, Set.mem_ofPred_eq]

/-- fw.argmin_subset (F2). -/
theorem argminSet_subset : argminSet Q S x ⊆ S := fun _ hy => hy.1

/-- fw.mem_argmin_univ. -/
@[simp]
theorem mem_argminSet_univ : y ∈ argminSet Q Set.univ x ↔ ∀ y', Q x y ≤ Q x y' := by
  simp [argminSet]

/-- fw.argmin_eq_empty_iff (F3). -/
theorem argminSet_eq_empty_iff :
    argminSet Q S x = ∅ ↔ ∀ y ∈ S, ∃ y' ∈ S, Q x y' < Q x y := by
  simp only [Set.eq_empty_iff_forall_notMem, argminSet, Set.mem_ofPred_eq, not_and, not_forall,
    not_le, exists_prop]

/-- fw.argmin_eq_zeroSet (F4). -/
theorem argminSet_eq_zeroSet (hnn : ∀ y ∈ S, 0 ≤ Q x y) (hz : ∃ y₀ ∈ S, Q x y₀ = 0) :
    argminSet Q S x = {y ∈ S | Q x y = 0} := by
  obtain ⟨y₀, hy₀, hq₀⟩ := hz
  ext y
  constructor
  · rintro ⟨hy, hmin⟩
    exact ⟨hy, le_antisymm (hq₀ ▸ hmin y₀ hy₀) (hnn y hy)⟩
  · rintro ⟨hy, hq⟩
    exact ⟨hy, fun y' hy' => hq ▸ hnn y' hy'⟩

/-- fw.mem_argmin_of_nonneg_zero (F4′). -/
theorem mem_argminSet_of_nonneg_zero (hnn : ∀ y ∈ S, 0 ≤ Q x y) (hy : y ∈ S) (hq : Q x y = 0) :
    y ∈ argminSet Q S x :=
  ⟨hy, fun y' hy' => hq ▸ hnn y' hy'⟩

/-- fw.argmin_mul_pos (F6). -/
theorem argminSet_mul_pos {c : X → ℝ} (hc : 0 < c x) :
    argminSet (fun x y => c x * Q x y) S x = argminSet Q S x := by
  ext y
  simp only [argminSet, Set.mem_ofPred_eq, mul_le_mul_iff_right₀ hc]

/-- fw.argmin_add_left (F6). -/
theorem argminSet_add_left (a : X → ℝ) :
    argminSet (fun x y => a x + Q x y) S x = argminSet Q S x := by
  ext y
  simp only [argminSet, Set.mem_ofPred_eq, add_le_add_iff_left]

/-- Θ(x) as an intersection of sublevel sets. -/
theorem argminSet_eq_inter : argminSet Q S x = S ∩ ⋂ y' ∈ S, {y | Q x y ≤ Q x y'} := by
  ext y
  simp [argminSet]

/-- fw.argmin_isClosed (F8). -/
theorem argminSet_isClosed [TopologicalSpace Y] (hQ : Continuous (Q x)) (hS : IsClosed S) :
    IsClosed (argminSet Q S x) := by
  rw [argminSet_eq_inter]
  exact hS.inter (isClosed_biInter fun y' _ => isClosed_le hQ continuous_const)

/-- fw.argmin_isCompact (F8). -/
theorem argminSet_isCompact [TopologicalSpace Y] (hQ : Continuous (Q x)) (hS : IsCompact S) :
    IsCompact (argminSet Q S x) := by
  rw [argminSet_eq_inter]
  exact hS.inter_right (isClosed_biInter fun y' _ => isClosed_le hQ continuous_const)

/-- fw.argmin_empty_of_pos_inf (§4.E.1, A2): a positive objective whose infimum over `S` is `0`
has no minimiser. -/
theorem argminSet_empty_of_pos_inf (hpos : ∀ y ∈ S, 0 < Q x y)
    (hinf : ∀ ε > 0, ∃ y ∈ S, Q x y < ε) : argminSet Q S x = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨hy, hmin⟩
  obtain ⟨y', hy', hlt⟩ := hinf (Q x y) (hpos y hy)
  exact absurd (hmin y' hy') (not_le.2 hlt)

/-- fw.argmin_empty_of_pos_inf, the `S = univ` case. -/
theorem argminSet_univ_empty_of_pos_inf (hpos : ∀ y, 0 < Q x y)
    (hinf : ∀ ε > 0, ∃ y, Q x y < ε) : argminSet Q Set.univ x = ∅ :=
  argminSet_empty_of_pos_inf (fun y _ => hpos y)
    (fun ε hε => (hinf ε hε).imp fun y hy => ⟨Set.mem_univ y, hy⟩)

end Argmin

/-! ### Value functions -/

section Value

variable {P Q : X → Y → ℝ} {S : Set Y} {x : X}

/-- `valueFun ≤ ↑(P x y)` for every minimiser `y`. -/
theorem valueFun_le_coe_of_mem {y : Y} (hy : y ∈ argminSet Q S x) :
    valueFun P Q S x ≤ ((P x y : ℝ) : EReal) :=
  iInf₂_le y hy

/-- `↑(P x y) ≤ pvalueFun` for every minimiser `y`. -/
theorem coe_le_pvalueFun_of_mem {y : Y} (hy : y ∈ argminSet Q S x) :
    ((P x y : ℝ) : EReal) ≤ pvalueFun P Q S x :=
  le_iSup₂ (f := fun y _ => ((P x y : ℝ) : EReal)) y hy

/-- A real lower bound on `P x` over Θ(x) bounds `valueFun` from below. -/
theorem coe_le_valueFun_of_forall {r : ℝ} (h : ∀ y ∈ argminSet Q S x, r ≤ P x y) :
    ((r : ℝ) : EReal) ≤ valueFun P Q S x :=
  le_iInf₂ fun y hy => EReal.coe_le_coe_iff.2 (h y hy)

/-- A real upper bound on `P x` over Θ(x) bounds `pvalueFun` from above. -/
theorem pvalueFun_le_coe_of_forall {r : ℝ} (h : ∀ y ∈ argminSet Q S x, P x y ≤ r) :
    pvalueFun P Q S x ≤ ((r : ℝ) : EReal) :=
  iSup₂_le fun y hy => EReal.coe_le_coe_iff.2 (h y hy)

/-- fw.value_eq_top_iff (V1). -/
theorem valueFun_eq_top_iff : valueFun P Q S x = ⊤ ↔ argminSet Q S x = ∅ := by
  constructor
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    have := valueFun_le_coe_of_mem (P := P) hy
    rw [h] at this
    exact absurd this (not_le.2 (EReal.coe_lt_top _))
  · intro h
    simp only [valueFun, h, iInf_emptyset]

/-- fw.pvalue_eq_bot_iff (V1, pessimistic twin). -/
theorem pvalueFun_eq_bot_iff : pvalueFun P Q S x = ⊥ ↔ argminSet Q S x = ∅ := by
  constructor
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    have := coe_le_pvalueFun_of_mem (P := P) hy
    rw [h] at this
    exact absurd this (not_le.2 (EReal.bot_lt_coe _))
  · intro h
    simp only [pvalueFun, h, iSup_emptyset]

/-- fw.value_eq_of_isMinOn (V2). -/
theorem valueFun_eq_of_isMinOn {y₀ : Y} (hy₀ : y₀ ∈ argminSet Q S x)
    (hmin : IsMinOn (P x) (argminSet Q S x) y₀) :
    valueFun P Q S x = ((P x y₀ : ℝ) : EReal) :=
  le_antisymm (valueFun_le_coe_of_mem hy₀)
    (coe_le_valueFun_of_forall fun _ hy => isMinOn_iff.1 hmin _ hy)

/-- fw.value_eq_of_isMinOn (V2, pessimistic twin). -/
theorem pvalueFun_eq_of_isMaxOn {y₀ : Y} (hy₀ : y₀ ∈ argminSet Q S x)
    (hmax : IsMaxOn (P x) (argminSet Q S x) y₀) :
    pvalueFun P Q S x = ((P x y₀ : ℝ) : EReal) :=
  le_antisymm (pvalueFun_le_coe_of_forall fun _ hy => isMaxOn_iff.1 hmax _ hy)
    (coe_le_pvalueFun_of_mem hy₀)

/-- fw.value_eq_of_isLeast (F0): the main interface for construction directions. -/
theorem valueFun_eq_of_isLeast {r : ℝ} (h : IsLeast (P x '' argminSet Q S x) r) :
    valueFun P Q S x = ((r : ℝ) : EReal) := by
  obtain ⟨⟨y₀, hy₀, rfl⟩, hlow⟩ := h
  exact valueFun_eq_of_isMinOn hy₀ (isMinOn_iff.2 fun y hy => hlow ⟨y, hy, rfl⟩)

/-- fw.value_eq_of_isLeast (F0, pessimistic twin). -/
theorem pvalueFun_eq_of_isGreatest {r : ℝ} (h : IsGreatest (P x '' argminSet Q S x) r) :
    pvalueFun P Q S x = ((r : ℝ) : EReal) := by
  obtain ⟨⟨y₀, hy₀, rfl⟩, hup⟩ := h
  exact pvalueFun_eq_of_isMaxOn hy₀ (isMaxOn_iff.2 fun y hy => hup ⟨y, hy, rfl⟩)

/-- fw.value_eq_of_const (V5). -/
theorem valueFun_eq_of_const {v : ℝ} (hne : (argminSet Q S x).Nonempty)
    (hc : ∀ y ∈ argminSet Q S x, P x y = v) : valueFun P Q S x = ((v : ℝ) : EReal) := by
  obtain ⟨y₀, hy₀⟩ := hne
  rw [← hc y₀ hy₀]
  exact valueFun_eq_of_isMinOn hy₀ (isMinOn_iff.2 fun y hy => (hc y hy).symm ▸ (hc y₀ hy₀).le)

/-- fw.value_eq_of_const (V5, pessimistic form). -/
theorem pvalueFun_eq_of_const {v : ℝ} (hne : (argminSet Q S x).Nonempty)
    (hc : ∀ y ∈ argminSet Q S x, P x y = v) : pvalueFun P Q S x = ((v : ℝ) : EReal) := by
  obtain ⟨y₀, hy₀⟩ := hne
  rw [← hc y₀ hy₀]
  exact pvalueFun_eq_of_isMaxOn hy₀ (isMaxOn_iff.2 fun y hy => (hc y hy).symm ▸ (hc y₀ hy₀).ge)

/-- fw.value_unique (V5′). -/
theorem valueFun_unique {y₀ : Y} (h : argminSet Q S x = {y₀}) :
    valueFun P Q S x = ((P x y₀ : ℝ) : EReal) ∧ pvalueFun P Q S x = ((P x y₀ : ℝ) : EReal) := by
  simp only [valueFun, pvalueFun, h, iInf_singleton, iSup_singleton, and_self]

/-- fw.value_eq_bot_of_unbounded (§4.E.1, A5). -/
theorem valueFun_eq_bot_of_unbounded (h : ∀ r : ℝ, ∃ y ∈ argminSet Q S x, P x y ≤ r) :
    valueFun P Q S x = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro r
  obtain ⟨y, hy, hle⟩ := h (r - 1)
  calc valueFun P Q S x ≤ ((P x y : ℝ) : EReal) := valueFun_le_coe_of_mem hy
    _ < ((r : ℝ) : EReal) := EReal.coe_lt_coe_iff.2 (by linarith)

/-- fw.value_eq_bot_of_unbounded (A5, pessimistic twin). -/
theorem pvalueFun_eq_top_of_unbounded (h : ∀ r : ℝ, ∃ y ∈ argminSet Q S x, r ≤ P x y) :
    pvalueFun P Q S x = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro r
  obtain ⟨y, hy, hle⟩ := h (r + 1)
  calc ((r : ℝ) : EReal) < ((P x y : ℝ) : EReal) := EReal.coe_lt_coe_iff.2 (by linarith)
    _ ≤ pvalueFun P Q S x := coe_le_pvalueFun_of_mem hy

end Value

/-- fw.value_shift_attained (§4.G.1): shifting the upper objective by `g x` shifts an attained
minimum. -/
theorem value_shift_attained {P : X → Y → ℝ} {g : X → ℝ} {Θ : Set Y} {x : X} {r : ℝ}
    (h : IsLeast (P x '' Θ) r) : IsLeast ((fun y => P x y + g x) '' Θ) (r + g x) := by
  obtain ⟨⟨y₀, hy₀, rfl⟩, hlow⟩ := h
  refine ⟨⟨y₀, hy₀, rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact add_le_add_left (hlow ⟨y, hy, rfl⟩) _

end Bilevel
