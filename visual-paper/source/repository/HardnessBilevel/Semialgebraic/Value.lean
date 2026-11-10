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
  congr 2
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


/-- `sa.value_semialgebraic` (Prop 2.6, corrected; blueprint §4.B.6), for ANY semialgebraic lower-level set `Y`:
the optimistic value function of a polynomial bilevel problem is extended-real semialgebraic. -/
theorem valueFun_isExtSemialgebraic [HasSemialgebraicProjections]
    {n : ℕ} {ι : Type} [Fintype ι] {P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} {Y : Set (ι → ℝ)}
    (hP : IsPolyFun P) (hQ : IsPolyFun Q) (hY : IsSemialgebraic Y) :
    IsExtSemialgebraic (valueFun P Q Y) := by
  have hΘ := isSemialgebraic_argminGraph hQ hY
  refine ⟨?_, ?_, ?_⟩
  · -- `{φ = ⊤} = {x | ∀ y, (x,y) ∉ Θ}`
    refine hΘ.compl.forall_sumElim.of_eq ?_
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, sumElim_mem_argminGraph_iff,
      valueFun_eq_top_iff, Set.eq_empty_iff_forall_notMem]
  · -- `{φ = ⊥} = {x | ∀ δ, ∃ y, (x,y) ∈ Θ ∧ P x y < δ}`; variables `(x, δ) ⊕ y`
    obtain ⟨p, hp⟩ := hP.exists_eval_pick (α := (Fin n ⊕ Unit) ⊕ ι)
      (fun i => Sum.inl (Sum.inl i)) (fun j => Sum.inr j)
    have h1 := hΘ.pick (γ := (Fin n ⊕ Unit) ⊕ ι) (fun i => Sum.inl (Sum.inl i)) (fun j => Sum.inr j)
    have h2 := isSemialgebraic_eval_lt p (X (Sum.inl (Sum.inr ())))
    have h3 := (isSemialgebraic_setOf_and h1 h2).exists_sumElim.forall_real
    refine h3.of_eq ?_
    ext x
    simp only [Set.mem_ofPred_eq, ← hp, eval_X, Sum.elim_inl, Sum.elim_inr, valueFun_eq_bot_iff,
      sumElim_mem_argminGraph_iff]
  · -- the graph; variables `(x, t)`
    -- part A: `∀ y, (x,y) ∈ Θ → t ≤ P x y`, variables `(x, t) ⊕ y`
    obtain ⟨p, hp⟩ := hP.exists_eval_pick (α := (Fin n ⊕ Unit) ⊕ ι)
      (fun i => Sum.inl (Sum.inl i)) (fun j => Sum.inr j)
    have hA1 := hΘ.pick (γ := (Fin n ⊕ Unit) ⊕ ι) (fun i => Sum.inl (Sum.inl i)) (fun j => Sum.inr j)
    have hA2 := isSemialgebraic_eval_le (X (Sum.inl (Sum.inr ()))) p
    have hA := (isSemialgebraic_setOf_or (isSemialgebraic_setOf_not hA1) hA2).forall_sumElim
    -- part B: `∀ ε > 0, ∃ y, (x,y) ∈ Θ ∧ P x y < t + ε`, variables `((x, t) ⊕ ε) ⊕ y`
    obtain ⟨p', hp'⟩ := hP.exists_eval_pick (α := ((Fin n ⊕ Unit) ⊕ Unit) ⊕ ι)
      (fun i => Sum.inl (Sum.inl (Sum.inl i))) (fun j => Sum.inr j)
    have hB1 := hΘ.pick (γ := ((Fin n ⊕ Unit) ⊕ Unit) ⊕ ι)
      (fun i => Sum.inl (Sum.inl (Sum.inl i))) (fun j => Sum.inr j)
    have hB2 := isSemialgebraic_eval_lt p'
      (X (Sum.inl (Sum.inl (Sum.inr ()))) + X (Sum.inl (Sum.inr ())))
    have hB := (isSemialgebraic_setOf_and hB1 hB2).exists_sumElim.forall_pos
    refine (isSemialgebraic_setOf_and hA hB).of_eq ?_
    ext z
    simp only [Set.mem_ofPred_eq, ← hp, ← hp', eval_X, map_add, Sum.elim_inl, Sum.elim_inr,
      sumElim_mem_argminGraph_iff]
    rw [show z ∘ Sum.inl = fun i => z (Sum.inl i) from rfl, valueFun_eq_coe_iff]
    simp only [imp_iff_not_or, gt_iff_lt]

/-- `sa.value_semialgebraic`, pessimistic twin: via `pvalueFun P Q Y = -valueFun (-P) Q Y`. -/
theorem pvalueFun_isExtSemialgebraic [HasSemialgebraicProjections]
    {n : ℕ} {ι : Type} [Fintype ι] {P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} {Y : Set (ι → ℝ)}
    (hP : IsPolyFun P) (hQ : IsPolyFun Q) (hY : IsSemialgebraic Y) :
    IsExtSemialgebraic (pvalueFun P Q Y) := by
  have h := (valueFun_isExtSemialgebraic hP.neg hQ hY).neg
  have he : pvalueFun P Q Y = fun x => -valueFun (fun x y => -P x y) Q Y x := by
    funext x; exact pvalueFun_eq_neg_valueFun_neg
  rw [he]; exact h

end Prop26

section Classes

variable [HasSemialgebraicProjections] {n : ℕ}

/-! ### `sa.class_sub_SA` (Corollary of Prop 2.6) -/

/-- `sa.class_sub_SA`: `𝒫_unbound ⊆ SA`. -/
theorem P_unbound_subset_SA : P_unbound n ⊆ SA n := by
  rintro h ⟨ι, _, P, Q, S, hP, hQ, hS, -, rfl⟩
  exact valueFun_isExtSemialgebraic hP hQ hS.isSemialgebraic

/-- `sa.class_sub_SA`: `𝒫_bounded ⊆ SA`. -/
theorem P_bounded_subset_SA : P_bounded n ⊆ SA n := by
  rintro h ⟨ι, _, P, Q, S, hP, hQ, hS, -, rfl⟩
  exact valueFun_isExtSemialgebraic hP hQ hS.isSemialgebraic

/-- `sa.class_sub_SA`: `𝒫_box ⊆ SA` (arbitrary boxes). -/
theorem P_box_subset_SA : P_box n ⊆ SA n := by
  rintro h ⟨ι, _, P, Q, S, hP, hQ, hS, -, rfl⟩
  exact valueFun_isExtSemialgebraic hP hQ hS.isSemialgebraic

/-- `sa.class_sub_SA`: `𝒞_unbound ⊆ SA` (this is `t218.Cunbound_sub_SA`). -/
theorem C_unbound_subset_SA : C_unbound n ⊆ SA n := by
  rintro h ⟨ι, _, P, Q, S, hP, hQ, hS, -, rfl⟩
  exact valueFun_isExtSemialgebraic hP hQ hS.isSemialgebraic

/-- `sa.class_sub_SA`: `𝒞_bounded ⊆ SA`. -/
theorem C_bounded_subset_SA : C_bounded n ⊆ SA n := by
  rintro h ⟨ι, _, P, Q, S, hP, hQ, hS, -, rfl⟩
  exact valueFun_isExtSemialgebraic hP hQ hS.isSemialgebraic

/-- `sa.class_sub_SA`: `𝒞_cc ⊆ SA` (needs Prop 2.6 for a general semialgebraic `Y`). -/
theorem C_cc_subset_SA : C_cc n ⊆ SA n := by
  rintro h ⟨ι, _, P, Q, S, hP, hQ, hS, -, rfl⟩
  exact valueFun_isExtSemialgebraic hP hQ hS.2.2.2

/-- `sa.class_sub_SA`, pessimistic: `𝒫^p_unbound ⊆ SA`. -/
theorem Pp_unbound_subset_SA : Pp_unbound n ⊆ SA n := by
  rintro h ⟨ι, _, P, Q, S, hP, hQ, hS, -, rfl⟩
  exact pvalueFun_isExtSemialgebraic hP hQ hS.isSemialgebraic

/-- `sa.class_sub_SA`, pessimistic: `𝒫^p_bounded ⊆ SA`. -/
theorem Pp_bounded_subset_SA : Pp_bounded n ⊆ SA n := by
  rintro h ⟨ι, _, P, Q, S, hP, hQ, hS, -, rfl⟩
  exact pvalueFun_isExtSemialgebraic hP hQ hS.isSemialgebraic

/-- `sa.class_sub_SA`, pessimistic: `𝒫^p_box ⊆ SA`. -/
theorem Pp_box_subset_SA : Pp_box n ⊆ SA n := by
  rintro h ⟨ι, _, P, Q, S, hP, hQ, hS, -, rfl⟩
  exact pvalueFun_isExtSemialgebraic hP hQ hS.isSemialgebraic

/-- `sa.class_sub_SA`, pessimistic: `𝒞^p_unbound ⊆ SA`. -/
theorem Cp_unbound_subset_SA : Cp_unbound n ⊆ SA n := by
  rintro h ⟨ι, _, P, Q, S, hP, hQ, hS, -, rfl⟩
  exact pvalueFun_isExtSemialgebraic hP hQ hS.isSemialgebraic

/-- `sa.class_sub_SA`, pessimistic: `𝒞^p_bounded ⊆ SA`. -/
theorem Cp_bounded_subset_SA : Cp_bounded n ⊆ SA n := by
  rintro h ⟨ι, _, P, Q, S, hP, hQ, hS, -, rfl⟩
  exact pvalueFun_isExtSemialgebraic hP hQ hS.isSemialgebraic

/-- `sa.class_sub_SA`, pessimistic: `𝒞^p_cc ⊆ SA`. -/
theorem Cp_cc_subset_SA : Cp_cc n ⊆ SA n := by
  rintro h ⟨ι, _, P, Q, S, hP, hQ, hS, -, rfl⟩
  exact pvalueFun_isExtSemialgebraic hP hQ hS.2.2.2

/-! ### Theorem 2.12: `𝒫_unbound = SA` -/

/-- `t212.eq_SA` (Theorem 2.12): `𝒫_unbound = SA` (⊇ is assumption-free, ⊆ uses A1). -/
theorem thm212_eq_SA : P_unbound n = SA n :=
  Set.Subset.antisymm P_unbound_subset_SA thm212_supset

/-- `t212.eq_SA`, pessimistic: `𝒫^p_unbound = SA`. -/
theorem thm212_eq_SA_pess : Pp_unbound n = SA n :=
  Set.Subset.antisymm Pp_unbound_subset_SA thm212_supset_pess

/-! ### Theorem 2.18: `PP ⊆ 𝒞_unbound ⊆ SA` -/

/-- `t218.main` (Theorem 2.18): `PP ⊆ 𝒞_unbound ⊆ SA` (`PP` viewed in `EReal` as `PPe`). -/
theorem thm218_main : PPe n ⊆ C_unbound n ∧ C_unbound n ⊆ SA n :=
  ⟨thm218_PP_subset, C_unbound_subset_SA⟩

/-- `t218.main`, pessimistic: `PP ⊆ 𝒞^p_unbound ⊆ SA`. -/
theorem thm218_main_pess : PPe n ⊆ Cp_unbound n ∧ Cp_unbound n ⊆ SA n :=
  ⟨thm218_PP_subset_pess, Cp_unbound_subset_SA⟩

/-! ### The `⊆` halves of Theorems 2.15, 2.20, 2.21 -/

/-- Theorem 2.15 (`⊆` half): `𝒫_bounded ⊆ SA ∩ LSC ∩ CB`. -/
theorem thm215_subset : P_bounded n ⊆ SA n ∩ LSC n ∩ CB n := fun _ hh =>
  ⟨⟨P_bounded_subset_SA hh, (P_bounded_subset_LSC_CB hh).1⟩, (P_bounded_subset_LSC_CB hh).2⟩

/-- Theorem 2.20 (`⊆` half): `𝒞_bounded ⊆ SA ∩ LSC ∩ CB`. -/
theorem thm220_subset : C_bounded n ⊆ SA n ∩ LSC n ∩ CB n := fun _ hh =>
  ⟨⟨C_bounded_subset_SA hh, (C_bounded_subset_LSC_CB hh).1⟩, (C_bounded_subset_LSC_CB hh).2⟩

/-- Theorem 2.21 (`⊆` half): `𝒞_cc ⊆ SA ∩ LSC ∩ CB` (Prop 2.6 + Cor 2.9; erratum E-6). -/
theorem thm221_subset : C_cc n ⊆ SA n ∩ LSC n ∩ CB n := fun _ hh =>
  ⟨⟨C_cc_subset_SA hh, (C_cc_subset_LSC_CB hh).1⟩, (C_cc_subset_LSC_CB hh).2⟩

/-- Theorem 2.15 (`⊆` half), pessimistic: `𝒫^p_bounded ⊆ SA ∩ USC ∩ CB`. -/
theorem thm215_subset_pess : Pp_bounded n ⊆ SA n ∩ USC n ∩ CB n := fun _ hh =>
  ⟨⟨Pp_bounded_subset_SA hh, (Pp_bounded_subset_USC_CB hh).1⟩, (Pp_bounded_subset_USC_CB hh).2⟩

/-- Theorem 2.20 (`⊆` half), pessimistic: `𝒞^p_bounded ⊆ SA ∩ USC ∩ CB`. -/
theorem thm220_subset_pess : Cp_bounded n ⊆ SA n ∩ USC n ∩ CB n := fun _ hh =>
  ⟨⟨Cp_bounded_subset_SA hh, (Cp_bounded_subset_USC_CB hh).1⟩, (Cp_bounded_subset_USC_CB hh).2⟩

/-- Theorem 2.21 (`⊆` half), pessimistic: `𝒞^p_cc ⊆ SA ∩ USC ∩ CB`. -/
theorem thm221_subset_pess : Cp_cc n ⊆ SA n ∩ USC n ∩ CB n := fun _ hh =>
  ⟨⟨Cp_cc_subset_SA hh, (Cp_cc_subset_USC_CB hh).1⟩, (Cp_cc_subset_USC_CB hh).2⟩

end Classes

end Bilevel
