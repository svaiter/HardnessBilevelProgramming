import Mathlib

/-!
# Boxes (blueprint §2.3, §4.A.1, `fw.box_lemmas`)

Boxes with extended-real endpoints `boxSet lo hi = {y | ∀ i, lo i ≤ ↑(y i) ≤ hi i}` (covering
`Icc`, `Ici`, `Iic`, `univ` coordinatewise), bounded boxes with real endpoints, and the predicates
`IsBoundedBox`, `IsUnboundedBox` (literal paper definition, §2) and `IsBox`.

Provides `fw.box_lemmas`: `boundedBox_eq_boxSet`, `IsBoundedBox.isBox`, `IsBoundedBox.isCompact`,
`IsBoundedBox.nonempty`, `IsBoundedBox.convex`, `IsBoundedBox.isClosed`, `IsBox.isClosed`,
`IsBox.convex`, `boxSet_bot_top`, the `IsUnboundedBox` witnesses `isUnboundedBox_univ` and
`isUnboundedBox_sum_univ_Ici` (mixed box of Thm 2.18), and `IsUnboundedBox.nonempty`.
-/

namespace Bilevel

section Defs

variable {ι : Type*}

/-- Boxes: `lo i ≤ y i ≤ hi i` with extended-real bounds (covers Icc, Ici, Iic, univ). -/
def boxSet (lo hi : ι → EReal) : Set (ι → ℝ) :=
  {y | ∀ i, lo i ≤ ((y i : ℝ) : EReal) ∧ ((y i : ℝ) : EReal) ≤ hi i}

/-- Bounded box with real bounds. -/
def boundedBox (lo hi : ι → ℝ) : Set (ι → ℝ) := Set.pi Set.univ fun i => Set.Icc (lo i) (hi i)

/-- A bounded box: real bounds with `lo ≤ hi` (so nonempty). -/
def IsBoundedBox (S : Set (ι → ℝ)) : Prop :=
  ∃ lo hi : ι → ℝ, (∀ i, lo i ≤ hi i) ∧ S = boundedBox lo hi

/-- Literal paper definition (§2): all intervals nonempty and at least one coordinate unbounded. -/
def IsUnboundedBox (S : Set (ι → ℝ)) : Prop :=
  ∃ lo hi : ι → EReal, (∀ i, lo i ≠ ⊤ ∧ hi i ≠ ⊥ ∧ lo i ≤ hi i) ∧ (∃ i, lo i = ⊥ ∨ hi i = ⊤) ∧
    S = boxSet lo hi

/-- A (possibly empty, possibly unbounded) box with extended-real endpoints. -/
def IsBox (S : Set (ι → ℝ)) : Prop := ∃ lo hi : ι → EReal, S = boxSet lo hi

end Defs

section Lemmas

variable {ι : Type*}

@[simp] theorem mem_boxSet {lo hi : ι → EReal} {y : ι → ℝ} :
    y ∈ boxSet lo hi ↔ ∀ i, lo i ≤ ((y i : ℝ) : EReal) ∧ ((y i : ℝ) : EReal) ≤ hi i :=
  Iff.rfl

@[simp] theorem mem_boundedBox {lo hi : ι → ℝ} {y : ι → ℝ} :
    y ∈ boundedBox lo hi ↔ ∀ i, lo i ≤ y i ∧ y i ≤ hi i := by
  simp only [boundedBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]

/-- `boxSet` as a product of preimages of extended-real intervals. -/
theorem boxSet_pi (lo hi : ι → EReal) :
    boxSet lo hi = Set.pi Set.univ fun i => (fun t : ℝ => (t : EReal)) ⁻¹' Set.Icc (lo i) (hi i) := by
  ext y; simp [Set.mem_pi]

theorem boundedBox_eq_boxSet (lo hi : ι → ℝ) :
    boundedBox lo hi = boxSet (fun i => ((lo i : ℝ) : EReal)) (fun i => ((hi i : ℝ) : EReal)) := by
  ext y; simp

theorem IsBoundedBox.isBox {S : Set (ι → ℝ)} (h : IsBoundedBox S) : IsBox S := by
  obtain ⟨lo, hi, -, rfl⟩ := h
  exact ⟨_, _, boundedBox_eq_boxSet lo hi⟩

theorem isCompact_boundedBox [Finite ι] (lo hi : ι → ℝ) : IsCompact (boundedBox lo hi) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem IsBoundedBox.isCompact [Finite ι] {S : Set (ι → ℝ)} (h : IsBoundedBox S) : IsCompact S := by
  obtain ⟨lo, hi, -, rfl⟩ := h
  exact isCompact_boundedBox lo hi

theorem IsBoundedBox.nonempty {S : Set (ι → ℝ)} (h : IsBoundedBox S) : S.Nonempty := by
  obtain ⟨lo, hi, hle, rfl⟩ := h
  exact ⟨lo, mem_boundedBox.2 fun i => ⟨le_rfl, hle i⟩⟩

theorem convex_boundedBox (lo hi : ι → ℝ) : Convex ℝ (boundedBox lo hi) :=
  convex_pi fun _ _ => convex_Icc _ _

theorem IsBoundedBox.convex {S : Set (ι → ℝ)} (h : IsBoundedBox S) : Convex ℝ S := by
  obtain ⟨lo, hi, -, rfl⟩ := h
  exact convex_boundedBox lo hi

theorem isClosed_boxSet (lo hi : ι → EReal) : IsClosed (boxSet lo hi) := by
  rw [boxSet_pi]
  exact isClosed_set_pi fun _ _ => isClosed_Icc.preimage continuous_coe_real_ereal

theorem IsBox.isClosed {S : Set (ι → ℝ)} (h : IsBox S) : IsClosed S := by
  obtain ⟨lo, hi, rfl⟩ := h
  exact isClosed_boxSet lo hi

theorem isClosed_boundedBox (lo hi : ι → ℝ) : IsClosed (boundedBox lo hi) := by
  rw [boundedBox_eq_boxSet]; exact isClosed_boxSet _ _

theorem IsBoundedBox.isClosed {S : Set (ι → ℝ)} (h : IsBoundedBox S) : IsClosed S :=
  h.isBox.isClosed

theorem convex_boxSet (lo hi : ι → EReal) : Convex ℝ (boxSet lo hi) := by
  rw [boxSet_pi]
  refine convex_pi fun i _ => ?_
  have : ((fun t : ℝ => (t : EReal)) ⁻¹' Set.Icc (lo i) (hi i)).OrdConnected :=
    (Set.ordConnected_Icc).preimage_mono EReal.coe_strictMono.monotone
  exact this.convex

theorem IsBox.convex {S : Set (ι → ℝ)} (h : IsBox S) : Convex ℝ S := by
  obtain ⟨lo, hi, rfl⟩ := h
  exact convex_boxSet lo hi

theorem boxSet_bot_top : boxSet (fun _ : ι => (⊥ : EReal)) (fun _ => ⊤) = Set.univ := by
  ext y; simp

theorem isBox_univ : IsBox (Set.univ : Set (ι → ℝ)) := ⟨_, _, boxSet_bot_top.symm⟩

theorem isUnboundedBox_univ [Nonempty ι] : IsUnboundedBox (Set.univ : Set (ι → ℝ)) := by
  refine ⟨fun _ => ⊥, fun _ => ⊤, fun _ => ⟨bot_ne_top, top_ne_bot, bot_le⟩, ?_,
    boxSet_bot_top.symm⟩
  exact ⟨Classical.arbitrary ι, Or.inl rfl⟩

/-- A real number in a nonempty extended-real interval `[a, b]` with `a ≠ ⊤`, `b ≠ ⊥`. -/
theorem exists_real_mem_Icc {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊥) (hab : a ≤ b) :
    ∃ t : ℝ, a ≤ (t : EReal) ∧ (t : EReal) ≤ b := by
  induction a using EReal.rec with
  | bot =>
    induction b using EReal.rec with
    | bot => exact absurd rfl hb
    | coe s => exact ⟨s, bot_le, le_rfl⟩
    | top => exact ⟨0, bot_le, le_top⟩
  | coe r => exact ⟨r, le_rfl, hab⟩
  | top => exact absurd rfl ha

theorem boxSet_nonempty {lo hi : ι → EReal} (h : ∀ i, lo i ≠ ⊤ ∧ hi i ≠ ⊥ ∧ lo i ≤ hi i) :
    (boxSet lo hi).Nonempty := by
  choose y hy using fun i => exists_real_mem_Icc (h i).1 (h i).2.1 (h i).2.2
  exact ⟨y, fun i => hy i⟩

theorem IsUnboundedBox.nonempty {S : Set (ι → ℝ)} (h : IsUnboundedBox S) : S.Nonempty := by
  obtain ⟨lo, hi, hint, -, rfl⟩ := h
  exact boxSet_nonempty hint

theorem IsUnboundedBox.isBox {S : Set (ι → ℝ)} (h : IsUnboundedBox S) : IsBox S := by
  obtain ⟨lo, hi, -, -, rfl⟩ := h
  exact ⟨lo, hi, rfl⟩

theorem IsUnboundedBox.isClosed {S : Set (ι → ℝ)} (h : IsUnboundedBox S) : IsClosed S :=
  h.isBox.isClosed

theorem IsUnboundedBox.convex {S : Set (ι → ℝ)} (h : IsUnboundedBox S) : Convex ℝ S :=
  h.isBox.convex

end Lemmas

/-- The mixed box of Thm 2.18: free coordinates indexed by `α`, nonnegative ones by `β`. -/
theorem isUnboundedBox_sum_univ_Ici {α β : Type*} [Nonempty α] :
    IsUnboundedBox (Set.pi Set.univ (Sum.elim (fun _ : α => (Set.univ : Set ℝ))
      (fun _ : β => Set.Ici (0 : ℝ)))) := by
  refine ⟨Sum.elim (fun _ => ⊥) (fun _ => ((0 : ℝ) : EReal)), fun _ => ⊤, ?_,
    ⟨Sum.inl (Classical.arbitrary α), Or.inl rfl⟩, ?_⟩
  · rintro (i | i)
    · exact ⟨bot_ne_top, top_ne_bot, bot_le⟩
    · exact ⟨EReal.coe_ne_top 0, top_ne_bot, le_top⟩
  · ext y
    simp only [Set.mem_pi, Set.mem_univ, true_implies, mem_boxSet, le_top, and_true]
    constructor
    · rintro hy (i | i)
      · exact bot_le
      · simpa [EReal.coe_le_coe_iff] using hy (Sum.inr i)
    · rintro hy (i | i)
      · trivial
      · simpa [EReal.coe_le_coe_iff] using hy (Sum.inr i)

end Bilevel
