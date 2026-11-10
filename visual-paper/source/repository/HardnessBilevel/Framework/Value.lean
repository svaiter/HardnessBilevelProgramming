/-
Copyright: HardnessBilevel project.

# Framework: characterisations of value functions (blueprint §4.A.3)

Implements:
* V3 `fw.value_eq_coe_iff` as `valueFun_eq_coe_iff` (δ/ε characterisation, no attainment);
  pessimistic twin `pvalueFun_eq_coe_iff`;
* V4 `fw.value_eq_bot_iff` as `valueFun_eq_bot_iff`; pessimistic twin `pvalueFun_eq_top_iff`;
* V8 `fw.pvalue_eq_neg_value_neg` as `pvalueFun_eq_neg_valueFun_neg`, and the symmetric
  `valueFun_eq_neg_pvalueFun_neg`;
* optional V9 `fw.value_real_iff` as `valueFun_real_iff`.

No assumption (A1–A3) is used.
-/
import HardnessBilevel.Framework.Basic

namespace Bilevel

variable {X Y : Type*} {P Q : X → Y → ℝ} {S : Set Y} {x : X}

/-- fw.value_eq_coe_iff (V3). -/
theorem valueFun_eq_coe_iff {r : ℝ} :
    valueFun P Q S x = ((r : ℝ) : EReal) ↔
      (∀ y ∈ argminSet Q S x, r ≤ P x y) ∧ ∀ ε > 0, ∃ y ∈ argminSet Q S x, P x y < r + ε := by
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun ε hε => ?_⟩
    · have := valueFun_le_coe_of_mem (P := P) hy
      rw [h] at this
      exact EReal.coe_le_coe_iff.1 this
    · by_contra hne
      push Not at hne
      have := coe_le_valueFun_of_forall (P := P) (r := r + ε) hne
      rw [h, EReal.coe_le_coe_iff] at this
      linarith
  · rintro ⟨hlow, happ⟩
    refine le_antisymm ?_ (coe_le_valueFun_of_forall hlow)
    by_contra hlt
    push Not at hlt
    obtain ⟨s, hrs, hsv⟩ := EReal.exists_between_coe_real hlt
    have hrs' : r < s := EReal.coe_lt_coe_iff.1 hrs
    obtain ⟨y, hy, hPy⟩ := happ (s - r) (by linarith)
    have h1 := valueFun_le_coe_of_mem (P := P) hy
    have h2 : ((P x y : ℝ) : EReal) < ((s : ℝ) : EReal) := EReal.coe_lt_coe_iff.2 (by linarith)
    exact absurd (h1.trans_lt h2) (not_lt.2 hsv.le)

/-- fw.value_eq_bot_iff (V4). -/
theorem valueFun_eq_bot_iff :
    valueFun P Q S x = ⊥ ↔ ∀ r : ℝ, ∃ y ∈ argminSet Q S x, P x y < r := by
  constructor
  · intro h r
    by_contra hne
    push Not at hne
    have := coe_le_valueFun_of_forall (P := P) hne
    rw [h] at this
    exact absurd this (not_le.2 (EReal.bot_lt_coe r))
  · intro h
    rw [EReal.eq_bot_iff_forall_lt]
    intro r
    obtain ⟨y, hy, hlt⟩ := h r
    exact (valueFun_le_coe_of_mem hy).trans_lt (EReal.coe_lt_coe_iff.2 hlt)

/-- fw.pvalue_eq_neg_value_neg (V8). -/
theorem pvalueFun_eq_neg_valueFun_neg :
    pvalueFun P Q S x = -(valueFun (fun x y => -P x y) Q S x) := by
  apply le_antisymm
  · refine iSup₂_le fun y hy => ?_
    rw [EReal.le_neg, ← EReal.coe_neg]
    exact valueFun_le_coe_of_mem (P := fun x y => -P x y) hy
  · rw [EReal.neg_le]
    refine le_iInf₂ fun y hy => ?_
    rw [EReal.coe_neg, EReal.neg_le_neg_iff]
    exact coe_le_pvalueFun_of_mem hy

/-- fw.pvalue_eq_neg_value_neg (V8), symmetric form. -/
theorem valueFun_eq_neg_pvalueFun_neg :
    valueFun P Q S x = -(pvalueFun (fun x y => -P x y) Q S x) := by
  rw [pvalueFun_eq_neg_valueFun_neg (P := fun x y => -P x y)]
  simp only [neg_neg]

/-- fw.value_eq_coe_iff (V3), pessimistic twin. -/
theorem pvalueFun_eq_coe_iff {r : ℝ} :
    pvalueFun P Q S x = ((r : ℝ) : EReal) ↔
      (∀ y ∈ argminSet Q S x, P x y ≤ r) ∧ ∀ ε > 0, ∃ y ∈ argminSet Q S x, r - ε < P x y := by
  rw [pvalueFun_eq_neg_valueFun_neg, neg_eq_iff_eq_neg, ← EReal.coe_neg, valueFun_eq_coe_iff]
  refine and_congr (forall₂_congr fun y _ => neg_le_neg_iff) (forall₂_congr fun ε _ => ?_)
  refine exists_congr fun y => and_congr_right fun _ => ?_
  constructor <;> intro h <;> linarith

/-- fw.value_eq_bot_iff (V4), pessimistic twin. -/
theorem pvalueFun_eq_top_iff :
    pvalueFun P Q S x = ⊤ ↔ ∀ r : ℝ, ∃ y ∈ argminSet Q S x, r < P x y := by
  rw [pvalueFun_eq_neg_valueFun_neg, neg_eq_iff_eq_neg, EReal.neg_top, valueFun_eq_bot_iff]
  constructor
  · intro h r
    obtain ⟨y, hy, hlt⟩ := h (-r)
    exact ⟨y, hy, by linarith⟩
  · intro h r
    obtain ⟨y, hy, hlt⟩ := h (-r)
    exact ⟨y, hy, by linarith⟩

/-- fw.value_real_iff (V9, optional). -/
theorem valueFun_real_iff :
    (valueFun P Q S x ≠ ⊤ ∧ valueFun P Q S x ≠ ⊥) ↔
      (argminSet Q S x).Nonempty ∧ BddBelow (P x '' argminSet Q S x) := by
  rw [Ne, valueFun_eq_top_iff, ← Set.not_nonempty_iff_eq_empty, not_not, Ne, valueFun_eq_bot_iff]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun ⟨r, hr⟩ => ?_⟩
  · push Not at h
    obtain ⟨r, hr⟩ := h
    exact ⟨r, by rintro _ ⟨y, hy, rfl⟩; exact hr y hy⟩
  · push Not
    exact ⟨r, fun y hy => hr ⟨y, hy, rfl⟩⟩

end Bilevel
