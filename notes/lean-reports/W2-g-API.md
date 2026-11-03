# W2-g API: HardnessBilevel/Gadgets/Box.lean (namespace Bilevel, imports HardnessBilevel.Framework.Poly)

All declarations: #print axioms ⊆ {propext, Classical.choice, Quot.sound}. gadgetGe_witness and gadgetBox are noncomputable defs. gadgetBox α β = Set.pi Set.univ (fun _ : α × β => Set.Icc (0:ℝ) (1/2)) (by rfl). mem_gadgetBox is @[simp].

```
gadgetGe : ℝ → ℝ → ℝ
gadgetGe_nonneg : ∀ (p z : ℝ), 0 ≤ gadgetGe p z
@gadgetGe_eq_zero_iff : ∀ {p z : ℝ}, gadgetGe p z = 0 ↔ p = (p ^ 2 + 1) * z
gadgetGe_witness : ℝ → ℝ
gadgetGe_witness_eq_zero : ∀ (p : ℝ), gadgetGe p (gadgetGe_witness p) = 0
@gadgetGe_witness_mem : ∀ {p : ℝ}, 0 ≤ p → gadgetGe_witness p ∈ Set.Icc 0 (1 / 2)
@nonneg_of_gadgetGe_eq_zero : ∀ {p z : ℝ}, 0 ≤ z → gadgetGe p z = 0 → 0 ≤ p
@exists_gadgetGe_eq_zero_iff : ∀ {p : ℝ}, (∃ z ∈ Set.Icc 0 (1 / 2), gadgetGe p z = 0) ↔ 0 ≤ p
@gadgetGe_pos_of_neg : ∀ {p z : ℝ}, p < 0 → 0 ≤ z → 0 < gadgetGe p z
gadgetBox : (α : Type u_1) → (β : Type u_2) → Set (α × β → ℝ)
@mem_gadgetBox : ∀ {α : Type u_1} {β : Type u_2} {z : α × β → ℝ},
  z ∈ gadgetBox α β ↔ ∀ (ij : α × β), z ij ∈ Set.Icc 0 (1 / 2)
@unionGadget : {α : Type u_1} →
  {β : Type u_2} → {U : Type u_3} → [Fintype α] → [Fintype β] → (α → β → U → ℝ) → U → (α × β → ℝ) → ℝ
@unionGadget_nonneg : ∀ {α : Type u_1} {β : Type u_2} {U : Type u_3} [inst : Fintype α] [inst_1 : Fintype β]
  (p : α → β → U → ℝ) (u : U) (z : α × β → ℝ), 0 ≤ unionGadget p u z
@unionGadget_eq_zero_iff : ∀ {α : Type u_1} {β : Type u_2} {U : Type u_3} [inst : Fintype α] [inst_1 : Fintype β]
  {p : α → β → U → ℝ} {u : U} {z : α × β → ℝ}, unionGadget p u z = 0 ↔ ∃ i, ∀ (j : β), gadgetGe (p i j u) (z (i, j)) = 0
@exists_unionGadget_eq_zero_iff : ∀ {α : Type u_1} {β : Type u_2} {U : Type u_3} [inst : Fintype α] [inst_1 : Fintype β]
  {p : α → β → U → ℝ} {u : U}, (∃ z ∈ gadgetBox α β, unionGadget p u z = 0) ↔ ∃ i, ∀ (j : β), 0 ≤ p i j u
@isPolyFun_gadgetGe : ∀ {n : ℕ} {ι : Type u_1} {F G : (Fin n → ℝ) → (ι → ℝ) → ℝ},
  IsPolyFun F → IsPolyFun G → IsPolyFun fun x y => gadgetGe (F x y) (G x y)
@isPolyFun_unionGadget : ∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : Fintype β] {n : ℕ} {ι : Type u_3}
  {P : α → β → (Fin n → ℝ) → (ι → ℝ) → ℝ} {Zc : α × β → (Fin n → ℝ) → (ι → ℝ) → ℝ},
  (∀ (i : α) (j : β), IsPolyFun (P i j)) →
    (∀ (ij : α × β), IsPolyFun (Zc ij)) →
      IsPolyFun fun x y => unionGadget (fun i j u => P i j u.1 u.2) (x, y) fun ij => Zc ij x y
@isPolyFun_unionGadget_sum : ∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : Fintype β] {n : ℕ}
  {p : α → β → (Fin n → ℝ) → ℝ → ℝ},
  (∀ (i : α) (j : β), IsPolyFun fun x t => p i j x (t ())) →
    IsPolyFun fun x y => unionGadget (fun i j u => p i j u.1 u.2) (x, y (Sum.inl ())) fun ij => y (Sum.inr ij)
```
