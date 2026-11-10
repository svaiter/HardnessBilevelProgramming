import HardnessBilevel.Framework.Poly

/-!
# The `≥`-gadgets (blueprint §4.F.1, `gad.G6`, `gad.G7`)

* `gad.G6`: the scalar gadget `gadgetGe p z = (p - (p^2+1) z)^2`, which has a zero
  `z ∈ [0, 1/2]` iff `0 ≤ p` (`exists_gadgetGe_eq_zero_iff`, explicit witness
  `gadgetGe_witness p = p / (p^2+1)`).
* `gad.G7`: the box union gadget `unionGadget p̃ u z = ∏ i, ∑ j, gadgetGe (p̃ i j u) (z (i,j))`
  over the box `gadgetBox α β = [0, 1/2]^(α × β)`; it is nonnegative and
  `(∃ z ∈ gadgetBox α β, unionGadget p̃ u z = 0) ↔ ∃ i, ∀ j, 0 ≤ p̃ i j u` (this is (★★)).

Deviations / choices:
* The blueprint uses `Fin a × Fin b`; we state everything for arbitrary finite types `α β`
  (strengthening). The box is a named definition `gadgetBox α β`
  (`= Set.pi Set.univ (fun _ : α × β => Set.Icc 0 (1/2))`, by `rfl`), with simp lemma
  `mem_gadgetBox`.
* Polynomiality (`gad.G7(d)`) is given in two forms:
  - `isPolyFun_unionGadget` (general, composable): for `P i j` and `Zc ij` all `IsPolyFun` on the
    same `(Fin n → ℝ) × (ι → ℝ)`, the function
    `fun x y => unionGadget (fun i j (u : (Fin n → ℝ) × (ι → ℝ)) => P i j u.1 u.2) (x, y) (fun ij => Zc ij x y)`
    is `IsPolyFun`. Use `IsPolyFun.rename`/`comp` to produce the hypotheses.
  - `isPolyFun_unionGadget_sum` (the form used by Thm 2.15): for
    `p̃ : α → β → (Fin n → ℝ) → ℝ → ℝ` with each `fun x (t : Unit → ℝ) => p̃ i j x (t ())`
    `IsPolyFun`, the function
    `fun x (y : Unit ⊕ (α × β) → ℝ) => unionGadget (fun i j (u : (Fin n → ℝ) × ℝ) => p̃ i j u.1 u.2)
       (x, y (Sum.inl ())) (fun ij => y (Sum.inr ij))` is `IsPolyFun`.
-/

namespace Bilevel

/-! ### gad.G6: the scalar `≥`-gadget -/

/-- The scalar `≥`-gadget `G p z = (p - (p^2+1) z)^2` (`gad.G6`). -/
def gadgetGe (p z : ℝ) : ℝ := (p - (p ^ 2 + 1) * z) ^ 2

theorem gadgetGe_nonneg (p z : ℝ) : 0 ≤ gadgetGe p z := sq_nonneg _

theorem gadgetGe_eq_zero_iff {p z : ℝ} : gadgetGe p z = 0 ↔ p = (p ^ 2 + 1) * z := by
  unfold gadgetGe
  rw [sq_eq_zero_iff, sub_eq_zero]

/-- The explicit zero of the gadget: `p / (p^2+1)`. -/
noncomputable def gadgetGe_witness (p : ℝ) : ℝ := p / (p ^ 2 + 1)

theorem gadgetGe_witness_eq_zero (p : ℝ) : gadgetGe p (gadgetGe_witness p) = 0 := by
  rw [gadgetGe_eq_zero_iff, gadgetGe_witness, mul_div_cancel₀]
  positivity

theorem gadgetGe_witness_mem {p : ℝ} (hp : 0 ≤ p) :
    gadgetGe_witness p ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  have hpos : (0 : ℝ) < p ^ 2 + 1 := by positivity
  refine ⟨div_nonneg hp hpos.le, ?_⟩
  rw [gadgetGe_witness, div_le_iff₀ hpos]
  nlinarith [sq_nonneg (p - 1)]

theorem nonneg_of_gadgetGe_eq_zero {p z : ℝ} (hz : 0 ≤ z) (h : gadgetGe p z = 0) : 0 ≤ p := by
  rw [gadgetGe_eq_zero_iff.mp h]
  exact mul_nonneg (by positivity) hz

theorem exists_gadgetGe_eq_zero_iff {p : ℝ} :
    (∃ z ∈ Set.Icc (0 : ℝ) (1 / 2), gadgetGe p z = 0) ↔ 0 ≤ p := by
  constructor
  · rintro ⟨z, hz, h⟩
    exact nonneg_of_gadgetGe_eq_zero hz.1 h
  · intro hp
    exact ⟨_, gadgetGe_witness_mem hp, gadgetGe_witness_eq_zero p⟩

theorem gadgetGe_pos_of_neg {p z : ℝ} (hp : p < 0) (hz : 0 ≤ z) : 0 < gadgetGe p z := by
  rcases (gadgetGe_nonneg p z).lt_or_eq with h | h
  · exact h
  · exact absurd (nonneg_of_gadgetGe_eq_zero hz h.symm) (not_le.mpr hp)

/-! ### gad.G7: the box union gadget -/

section Union

variable {α β U : Type*} [Fintype α] [Fintype β]

/-- The gadget box `[0, 1/2]^(α × β)`. -/
noncomputable def gadgetBox (α β : Type*) : Set (α × β → ℝ) :=
  Set.pi Set.univ (fun _ : α × β => Set.Icc (0 : ℝ) (1 / 2))

omit [Fintype α] [Fintype β] in
@[simp] theorem mem_gadgetBox {z : α × β → ℝ} :
    z ∈ gadgetBox α β ↔ ∀ ij, z ij ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  simp only [gadgetBox, Set.mem_pi, Set.mem_univ, true_implies]

/-- The box union gadget `R u z = ∏ i, ∑ j, G (p̃ i j u) (z (i,j))` (`gad.G7`). -/
def unionGadget (p : α → β → U → ℝ) (u : U) (z : α × β → ℝ) : ℝ :=
  ∏ i, ∑ j, gadgetGe (p i j u) (z (i, j))

theorem unionGadget_nonneg (p : α → β → U → ℝ) (u : U) (z : α × β → ℝ) :
    0 ≤ unionGadget p u z :=
  Finset.prod_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => gadgetGe_nonneg _ _

theorem unionGadget_eq_zero_iff {p : α → β → U → ℝ} {u : U} {z : α × β → ℝ} :
    unionGadget p u z = 0 ↔ ∃ i, ∀ j, gadgetGe (p i j u) (z (i, j)) = 0 := by
  unfold unionGadget
  rw [Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and]
  refine exists_congr fun i => ?_
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => gadgetGe_nonneg _ _]
  simp only [Finset.mem_univ, true_implies]

/-- (★★): the union gadget has a zero in the box iff some row of `p̃` is nonnegative. -/
theorem exists_unionGadget_eq_zero_iff {p : α → β → U → ℝ} {u : U} :
    (∃ z ∈ gadgetBox α β, unionGadget p u z = 0) ↔ ∃ i, ∀ j, 0 ≤ p i j u := by
  classical
  constructor
  · rintro ⟨z, hz, h⟩
    obtain ⟨i, hi⟩ := unionGadget_eq_zero_iff.mp h
    exact ⟨i, fun j => nonneg_of_gadgetGe_eq_zero (mem_gadgetBox.mp hz (i, j)).1 (hi j)⟩
  · rintro ⟨i₀, hi₀⟩
    refine ⟨fun ij => if ij.1 = i₀ then gadgetGe_witness (p i₀ ij.2 u) else 0, ?_, ?_⟩
    · rw [mem_gadgetBox]
      intro ij
      split_ifs
      · exact gadgetGe_witness_mem (hi₀ _)
      · exact ⟨le_rfl, by norm_num⟩
    · refine unionGadget_eq_zero_iff.mpr ⟨i₀, fun j => ?_⟩
      simp only [ite_true]
      exact gadgetGe_witness_eq_zero _

/-! ### Polynomiality (`gad.G7(d)`) -/

theorem isPolyFun_gadgetGe {n : ℕ} {ι : Type*} {F G : (Fin n → ℝ) → (ι → ℝ) → ℝ}
    (hF : IsPolyFun F) (hG : IsPolyFun G) :
    IsPolyFun fun x y => gadgetGe (F x y) (G x y) := by
  unfold gadgetGe
  exact (hF.sub (((hF.pow 2).add (isPolyFun_const 1)).mul hG)).pow 2

/-- General polynomiality of the union gadget: parameters and box coordinates are arbitrary
polynomial functions of `(x, y)`. -/
theorem isPolyFun_unionGadget {n : ℕ} {ι : Type*}
    {P : α → β → (Fin n → ℝ) → (ι → ℝ) → ℝ} {Zc : α × β → (Fin n → ℝ) → (ι → ℝ) → ℝ}
    (hP : ∀ i j, IsPolyFun (P i j)) (hZ : ∀ ij, IsPolyFun (Zc ij)) :
    IsPolyFun fun x y =>
      unionGadget (fun i j (u : (Fin n → ℝ) × (ι → ℝ)) => P i j u.1 u.2) (x, y)
        (fun ij => Zc ij x y) := by
  unfold unionGadget
  exact isPolyFun_finset_prod _ fun i _ =>
    isPolyFun_finset_sum _ fun j _ => isPolyFun_gadgetGe (hP i j) (hZ (i, j))

/-- Polynomiality in the form used by Thm 2.15: lower variables `y : Unit ⊕ (α × β) → ℝ`,
`y (inl ())` is the scalar `t`, `y (inr (i,j))` the box coordinates. -/
theorem isPolyFun_unionGadget_sum {n : ℕ} {p : α → β → (Fin n → ℝ) → ℝ → ℝ}
    (hp : ∀ i j, IsPolyFun fun x (t : Unit → ℝ) => p i j x (t ())) :
    IsPolyFun fun x (y : Unit ⊕ (α × β) → ℝ) =>
      unionGadget (fun i j (u : (Fin n → ℝ) × ℝ) => p i j u.1 u.2) (x, y (Sum.inl ()))
        (fun ij => y (Sum.inr ij)) := by
  have h := isPolyFun_unionGadget (n := n) (ι := Unit ⊕ (α × β))
    (P := fun i j x y => p i j x (y (Sum.inl ())))
    (Zc := fun ij _ y => y (Sum.inr ij))
    (fun i j => (hp i j).rename (fun _ => Sum.inl ()))
    (fun ij => isPolyFun_lower (Sum.inr ij))
  exact h.of_eq fun x y => rfl

end Union

end Bilevel
