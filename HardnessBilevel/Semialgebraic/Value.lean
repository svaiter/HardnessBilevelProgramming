/-
Copyright: HardnessBilevel project.

# Value functions are extended-real semialgebraic (Prop 2.6) and the A1-dependent class results

Implements blueprint §4.B.6 (`sa.value_semialgebraic`, `sa.class_sub_SA`), §4.E.2 `t212.eq_SA`,
§4.G.3 `t218.Cunbound_sub_SA` / `t218.main`, and the A1 halves of Theorems 2.15, 2.20, 2.21
(`P_bounded ⊆ SA ∩ LSC ∩ CB`, `C_bounded ⊆ …`, `C_cc ⊆ …`, with pessimistic twins).

Everything derived from assumption A1 takes `[HasSemialgebraicProjections]` as an explicit binder
(no instance of the class exists anywhere).

Proof route (blueprint §4.B.6, corrected Prop 2.6, no attainment used): the argmin graph
`Θ = {(x,y) | y ∈ Y ∧ ∀ y' ∈ Y, Q x y ≤ Q x y'}` is semialgebraic; then
`{φ = ⊤} = {x | ∀ y, (x,y) ∉ Θ}`, `{φ = ⊥} = {x | ∀ δ, ∃ y, (x,y) ∈ Θ ∧ P x y < δ}`, and the graph is
`{(x,t) | (∀ y, (x,y) ∈ Θ → t ≤ P x y) ∧ ∀ ε > 0, ∃ y, (x,y) ∈ Θ ∧ P x y < t + ε}`.
Enlarged spaces are explicit left-nested sums; quantified blocks are always the last summand.
-/
import HardnessBilevel.Framework.Classes
import HardnessBilevel.Semialgebraic.Projection
import HardnessBilevel.Semialgebraic.Ext

open MeasureTheory Function MvPolynomial

namespace Bilevel

-- No instance of the A1 class exists (by policy), so the assumption is deliberately a local binder.
set_option linter.concreteInstances false

section Helpers

/-- A polynomial function evaluated at coordinates picked out of a bigger vector is a polynomial. -/
theorem IsPolyFun.exists_eval_pick {n : ℕ} {ι α : Type} {P : (Fin n → ℝ) → (ι → ℝ) → ℝ}
    (hP : IsPolyFun P) (a : Fin n → α) (b : ι → α) :
    ∃ p : MvPolynomial α ℝ, ∀ w : α → ℝ, P (fun i => w (a i)) (fun j => w (b j)) = eval w p := by
  obtain ⟨p, hp⟩ := hP
  refine ⟨MvPolynomial.rename (Sum.elim a b) p, fun w => ?_⟩
  rw [hp, eval_rename]
  congr 1
  funext k
  cases k <;> rfl

/-- Pulling a semialgebraic set back along a "picking" map `w ↦ (w ∘ a, w ∘ b)`. -/
theorem IsSemialgebraic.pick {α β γ : Type} {S : Set (α ⊕ β → ℝ)} (hS : IsSemialgebraic S)
    (a : α → γ) (b : β → γ) :
    IsSemialgebraic {w : γ → ℝ | Sum.elim (fun i => w (a i)) (fun j => w (b j)) ∈ S} := by
  refine (hS.reindex (Sum.elim a b)).of_eq ?_
  ext w
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  have : w ∘ Sum.elim a b = Sum.elim (fun i => w (a i)) (fun j => w (b j)) := by
    funext k; cases k <;> rfl
  rw [this]

end Helpers

section Prop26

variable {n : ℕ} {ι : Type}

/-- The argmin graph `Θ ⊆ ℝ^n × ℝ^ι` of the lower level problem. -/
def argminGraph (Q : (Fin n → ℝ) → (ι → ℝ) → ℝ) (Y : Set (ι → ℝ)) : Set (Fin n ⊕ ι → ℝ) :=
  {z | (fun j => z (Sum.inr j)) ∈ Y ∧
    ∀ y', y' ∈ Y → Q (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j)) ≤ Q (fun i => z (Sum.inl i)) y'}

theorem sumElim_mem_argminGraph_iff {Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} {Y : Set (ι → ℝ)}
    {x : Fin n → ℝ} {y : ι → ℝ} : Sum.elim x y ∈ argminGraph Q Y ↔ y ∈ argminSet Q Y x := by
  simp only [argminGraph, argminSet, Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr]

theorem isSemialgebraic_argminGraph [HasSemialgebraicProjections] [Fintype ι] {Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} {Y : Set (ι → ℝ)}
    (hQ : IsPolyFun Q) (hY : IsSemialgebraic Y) : IsSemialgebraic (argminGraph Q Y) := by
  -- the inner set in the variables `(x, y) ⊕ y'`
  obtain ⟨q₁, hq₁⟩ := hQ.exists_eval_pick (α := (Fin n ⊕ ι) ⊕ ι)
    (fun i => Sum.inl (Sum.inl i)) (fun j => Sum.inl (Sum.inr j))
  obtain ⟨q₂, hq₂⟩ := hQ.exists_eval_pick (α := (Fin n ⊕ ι) ⊕ ι)
    (fun i => Sum.inl (Sum.inl i)) (fun j => Sum.inr j)
  have hA : IsSemialgebraic {w : (Fin n ⊕ ι) ⊕ ι → ℝ |
      (fun j => w (Sum.inr j)) ∈ Y →
        Q (fun i => w (Sum.inl (Sum.inl i))) (fun j => w (Sum.inl (Sum.inr j))) ≤
          Q (fun i => w (Sum.inl (Sum.inl i))) (fun j => w (Sum.inr j))} := by
    have h1 : IsSemialgebraic {w : (Fin n ⊕ ι) ⊕ ι → ℝ | ¬ (fun j => w (Sum.inr j)) ∈ Y} :=
      isSemialgebraic_setOf_not (isSemialgebraic_cylinder_inr (ι := Fin n ⊕ ι) hY)
    have h2 := isSemialgebraic_eval_le q₁ q₂
    refine (isSemialgebraic_setOf_or h1 h2).of_eq ?_
    ext w
    simp only [Set.mem_ofPred_eq, hq₁, hq₂]
    tauto
  have hB := hA.forall_sumElim
  have hC := isSemialgebraic_setOf_and (isSemialgebraic_cylinder_inr (ι := Fin n) hY) hB
  refine hC.of_eq ?_
  ext z
  simp only [argminGraph, Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun y' hy' => h2 y' hy'⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun y' hy' => h2 y' hy'⟩

end Prop26

end Bilevel
