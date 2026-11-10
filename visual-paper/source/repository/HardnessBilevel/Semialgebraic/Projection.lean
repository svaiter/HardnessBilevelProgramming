/-
Copyright: HardnessBilevel project.

# Tarski–Seidenberg consequences: the quantifier calculus

Implements blueprint §4.B.3: ids `sa.exists_sumElim`, `sa.forall_sumElim`, `sa.quantifier_calculus`
(concrete helper lemmas), `sa.closure` / `sa.interior` (optional), and `t215.epi_sa` (epigraph / hypograph of a
semialgebraic function).

Everything in this file is derived from assumption A1 and takes `[HasSemialgebraicProjections]` as an explicit
instance-implicit binder (no instance of the class exists anywhere, blueprint §2.5).

Conventions: enlarged spaces are written as explicit nested sums; re-bracketing is done only through
`IsSemialgebraic.preimage_equiv` along `Equiv.sumAssoc`. Quantified variables are always the LAST block.

`sa.closure` / `sa.interior` (optional in the blueprint) are implemented: `IsSemialgebraic.closure`,
`IsSemialgebraic.interior` (sup metric on `ι → ℝ`, `Metric.mem_closure_iff`, `dist_pi_lt_iff`).

Strengthenings: `isSemialgebraic_epigraph` / `isSemialgebraic_hypograph` are stated over any `ι : Type` with
`[Fintype ι]` (the blueprint's `Fin n` is a special case).
-/
import HardnessBilevel.Assumptions.Classes
import HardnessBilevel.Semialgebraic.Poly

open MeasureTheory Function MvPolynomial

namespace Bilevel

-- No instance of the A1 class exists (by policy), so the assumption is deliberately a local binder.
set_option linter.concreteInstances false

section Quantifiers

variable [HasSemialgebraicProjections] {α β γ : Type} [Fintype α]

/-- A1 in `Fin.tail`-free notation: the image of a semialgebraic set under `z ↦ z ∘ Sum.inl`. -/
theorem IsSemialgebraic.image_comp_inl [Finite β] {S : Set (α ⊕ β → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic ((fun z : α ⊕ β → ℝ => z ∘ Sum.inl) '' S) :=
  HasSemialgebraicProjections.image_comp_inl hS

/-- `sa.exists_sumElim` (A1 verbatim: the set is the image `(· ∘ Sum.inl) '' S`). -/
theorem IsSemialgebraic.exists_sumElim [Finite β] {S : Set (α ⊕ β → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic {v : α → ℝ | ∃ u : β → ℝ, Sum.elim v u ∈ S} := by
  refine hS.image_comp_inl.of_eq ?_
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z ∘ Sum.inr, by rwa [Sum.elim_comp_inl_inr]⟩
  · rintro ⟨u, hu⟩
    exact ⟨Sum.elim v u, hu, Sum.elim_comp_inl _ _⟩

/-- `sa.forall_sumElim`: `{v | ∀ u, Sum.elim v u ∈ S} = {v | ∃ u, Sum.elim v u ∈ Sᶜ}ᶜ`. -/
theorem IsSemialgebraic.forall_sumElim [Finite β] {S : Set (α ⊕ β → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic {v : α → ℝ | ∀ u : β → ℝ, Sum.elim v u ∈ S} := by
  refine hS.compl.exists_sumElim.compl.of_eq ?_
  ext v
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_not]

/-- Existential quantifier over the `inr` block, phrased with `z ∘ Sum.inl = v`. -/
theorem IsSemialgebraic.exists_inr [Finite β] {S : Set (α ⊕ β → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic {v : α → ℝ | ∃ z : α ⊕ β → ℝ, z ∘ Sum.inl = v ∧ z ∈ S} := by
  refine hS.image_comp_inl.of_eq ?_
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, rfl, hz⟩
  · rintro ⟨z, rfl, hz⟩; exact ⟨z, hz, rfl⟩

/-- Universal quantifier over the `inr` block, phrased with `z ∘ Sum.inl = v`. -/
theorem IsSemialgebraic.forall_inr [Finite β] {S : Set (α ⊕ β → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic {v : α → ℝ | ∀ z : α ⊕ β → ℝ, z ∘ Sum.inl = v → z ∈ S} := by
  refine hS.compl.exists_inr.compl.of_eq ?_
  ext v
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_and, not_not]

/-- Bounded existential quantifier `∃ u ∈ T`. -/
theorem IsSemialgebraic.exists_mem_sumElim [Finite β] {S : Set (α ⊕ β → ℝ)} (hS : IsSemialgebraic S)
    {T : Set (β → ℝ)} (hT : IsSemialgebraic T) :
    IsSemialgebraic {v : α → ℝ | ∃ u : β → ℝ, u ∈ T ∧ Sum.elim v u ∈ S} := by
  have h : IsSemialgebraic ({z : α ⊕ β → ℝ | z ∘ Sum.inr ∈ T} ∩ S) :=
    (isSemialgebraic_cylinder_inr hT).inter hS
  refine h.exists_sumElim.of_eq ?_
  ext v
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Sum.elim_comp_inr]

/-- Bounded universal quantifier `∀ u ∈ T`. -/
theorem IsSemialgebraic.forall_mem_sumElim [Finite β] {S : Set (α ⊕ β → ℝ)} (hS : IsSemialgebraic S)
    {T : Set (β → ℝ)} (hT : IsSemialgebraic T) :
    IsSemialgebraic {v : α → ℝ | ∀ u : β → ℝ, u ∈ T → Sum.elim v u ∈ S} := by
  have h : IsSemialgebraic ({z : α ⊕ β → ℝ | z ∘ Sum.inr ∈ T}ᶜ ∪ S) :=
    (isSemialgebraic_cylinder_inr hT).compl.union hS
  refine h.forall_sumElim.of_eq ?_
  ext v
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, Sum.elim_comp_inr, imp_iff_not_or]

/-- Two nested existential blocks, `α ⊕ (β ⊕ γ)`. -/
theorem IsSemialgebraic.exists_exists_sumElim [Finite β] [Finite γ] {S : Set (α ⊕ (β ⊕ γ) → ℝ)}
    (hS : IsSemialgebraic S) :
    IsSemialgebraic {v : α → ℝ | ∃ (u : β → ℝ) (w : γ → ℝ), Sum.elim v (Sum.elim u w) ∈ S} := by
  refine hS.exists_sumElim.of_eq ?_
  ext v
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x ∘ Sum.inl, x ∘ Sum.inr, by rwa [Sum.elim_comp_inl_inr]⟩
  · rintro ⟨u, w, h⟩
    exact ⟨_, h⟩

/-- Two nested universal blocks, `α ⊕ (β ⊕ γ)`. -/
theorem IsSemialgebraic.forall_forall_sumElim [Finite β] [Finite γ] {S : Set (α ⊕ (β ⊕ γ) → ℝ)}
    (hS : IsSemialgebraic S) :
    IsSemialgebraic {v : α → ℝ | ∀ (u : β → ℝ) (w : γ → ℝ), Sum.elim v (Sum.elim u w) ∈ S} := by
  refine hS.compl.exists_exists_sumElim.compl.of_eq ?_
  ext v
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_not]

/-- Two nested existential blocks, `(α ⊕ β) ⊕ γ`. -/
theorem IsSemialgebraic.exists_exists_sumElim' [Fintype β] [Finite γ] {S : Set ((α ⊕ β) ⊕ γ → ℝ)}
    (hS : IsSemialgebraic S) :
    IsSemialgebraic {v : α → ℝ | ∃ (u : β → ℝ) (w : γ → ℝ), Sum.elim (Sum.elim v u) w ∈ S} := by
  have h := hS.exists_sumElim (α := α ⊕ β)
  exact h.exists_sumElim.of_eq (by
    ext v
    simp only [Set.mem_ofPred_eq])

/-- Two nested universal blocks, `(α ⊕ β) ⊕ γ`. -/
theorem IsSemialgebraic.forall_forall_sumElim' [Fintype β] [Finite γ] {S : Set ((α ⊕ β) ⊕ γ → ℝ)}
    (hS : IsSemialgebraic S) :
    IsSemialgebraic {v : α → ℝ | ∀ (u : β → ℝ) (w : γ → ℝ), Sum.elim (Sum.elim v u) w ∈ S} := by
  have h := hS.forall_sumElim (α := α ⊕ β)
  exact h.forall_sumElim.of_eq (by
    ext v
    simp only [Set.mem_ofPred_eq])

/-- Eliminate the LAST block of `α ⊕ (β ⊕ γ)`, result on `α ⊕ β` (re-bracketing via `Equiv.sumAssoc`). -/
theorem IsSemialgebraic.exists_sumElim_assoc [Fintype β] [Finite γ] {S : Set (α ⊕ (β ⊕ γ) → ℝ)}
    (hS : IsSemialgebraic S) :
    IsSemialgebraic {w : α ⊕ β → ℝ |
      ∃ u : γ → ℝ, Sum.elim (w ∘ Sum.inl) (Sum.elim (w ∘ Sum.inr) u) ∈ S} := by
  have h := (hS.preimage_equiv (Equiv.sumAssoc α β γ).symm).exists_sumElim (α := α ⊕ β)
  refine h.of_eq ?_
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  refine exists_congr fun u => ?_
  have : (Sum.elim w u ∘ ⇑(Equiv.sumAssoc α β γ).symm) =
      Sum.elim (w ∘ Sum.inl) (Sum.elim (w ∘ Sum.inr) u) := by
    funext x
    rcases x with a | b | c <;> rfl
  rw [this]

/-- Universal twin of `exists_sumElim_assoc`. -/
theorem IsSemialgebraic.forall_sumElim_assoc [Fintype β] [Finite γ] {S : Set (α ⊕ (β ⊕ γ) → ℝ)}
    (hS : IsSemialgebraic S) :
    IsSemialgebraic {w : α ⊕ β → ℝ |
      ∀ u : γ → ℝ, Sum.elim (w ∘ Sum.inl) (Sum.elim (w ∘ Sum.inr) u) ∈ S} := by
  refine hS.compl.exists_sumElim_assoc.compl.of_eq ?_
  ext w
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_not]

/-- Eliminate the LAST block of `(α ⊕ β) ⊕ γ` (no re-bracketing needed), result on `α ⊕ β`. -/
theorem IsSemialgebraic.exists_sumElim_last [Fintype β] [Finite γ] {S : Set ((α ⊕ β) ⊕ γ → ℝ)}
    (hS : IsSemialgebraic S) :
    IsSemialgebraic {w : α ⊕ β → ℝ | ∃ u : γ → ℝ, Sum.elim w u ∈ S} :=
  hS.exists_sumElim

/-- Universal twin of `exists_sumElim_last`. -/
theorem IsSemialgebraic.forall_sumElim_last [Fintype β] [Finite γ] {S : Set ((α ⊕ β) ⊕ γ → ℝ)}
    (hS : IsSemialgebraic S) :
    IsSemialgebraic {w : α ⊕ β → ℝ | ∀ u : γ → ℝ, Sum.elim w u ∈ S} :=
  hS.forall_sumElim

end Quantifiers

section OneVariable

variable [HasSemialgebraicProjections] {α : Type} [Fintype α]

/-- One real variable, unbounded `∃ t`. -/
theorem IsSemialgebraic.exists_real {S : Set (α ⊕ Unit → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic {v : α → ℝ | ∃ t : ℝ, Sum.elim v (fun _ : Unit => t) ∈ S} := by
  refine hS.exists_sumElim.of_eq ?_
  ext v
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u (), ?_⟩
    have : (fun _ : Unit => u ()) = u := funext fun _ => rfl
    rwa [this]
  · rintro ⟨t, ht⟩
    exact ⟨_, ht⟩

/-- One real variable, unbounded `∀ t`. -/
theorem IsSemialgebraic.forall_real {S : Set (α ⊕ Unit → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic {v : α → ℝ | ∀ t : ℝ, Sum.elim v (fun _ : Unit => t) ∈ S} := by
  refine hS.compl.exists_real.compl.of_eq ?_
  ext v
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_not]

/-- One real variable, bounded `∃ ε > 0`. -/
theorem IsSemialgebraic.exists_pos {S : Set (α ⊕ Unit → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic {v : α → ℝ | ∃ ε : ℝ, 0 < ε ∧ Sum.elim v (fun _ : Unit => ε) ∈ S} := by
  have h : IsSemialgebraic ({z : α ⊕ Unit → ℝ | z (Sum.inr ()) ≤ 0}ᶜ ∩ S) :=
    (isSemialgebraic_coord_le_const _ 0).compl.inter hS
  refine h.exists_real.of_eq ?_
  ext v
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, Sum.elim_inr, not_le]

/-- One real variable, bounded `∀ ε > 0`. -/
theorem IsSemialgebraic.forall_pos {S : Set (α ⊕ Unit → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic {v : α → ℝ | ∀ ε : ℝ, 0 < ε → Sum.elim v (fun _ : Unit => ε) ∈ S} := by
  refine hS.compl.exists_pos.compl.of_eq ?_
  ext v
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_and, not_not]

end OneVariable

section Epigraph

variable [HasSemialgebraicProjections] {ι : Type} [Fintype ι]

/-- Substituting the value of a semialgebraic function: if `T` is semialgebraic on `(ι ⊕ Unit) ⊕ Unit`, then
so is `{z | (z, f (z ∘ Sum.inl)) ∈ T}` (one projection). -/
theorem isSemialgebraic_setOf_sumElim_value {f : (ι → ℝ) → ℝ} (hf : IsSemialgebraicMap f)
    {T : Set ((ι ⊕ Unit) ⊕ Unit → ℝ)} (hT : IsSemialgebraic T) :
    IsSemialgebraic {z : ι ⊕ Unit → ℝ | Sum.elim z (fun _ : Unit => f (z ∘ Sum.inl)) ∈ T} := by
  let e : ι ⊕ Unit → (ι ⊕ Unit) ⊕ Unit := Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun _ => Sum.inr ())
  have hG : IsSemialgebraic ((fun w : (ι ⊕ Unit) ⊕ Unit → ℝ => w ∘ e) ⁻¹' graphSet f) := hf.reindex e
  refine (hG.inter hT).exists_real.of_eq ?_
  ext z
  simp only [Set.mem_inter_iff, Set.mem_preimage, mem_graphSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht, hT⟩
    have : f (z ∘ Sum.inl) = t := ht
    rwa [this]
  · intro h
    exact ⟨_, rfl, h⟩

/-- `t215.epi_sa`: the epigraph of a semialgebraic function is semialgebraic (one projection). -/
theorem isSemialgebraic_epigraph {f : (ι → ℝ) → ℝ} (hf : IsSemialgebraicMap f) :
    IsSemialgebraic {z : ι ⊕ Unit → ℝ | f (z ∘ Sum.inl) ≤ z (Sum.inr ())} :=
  (isSemialgebraic_setOf_sumElim_value hf
    (isSemialgebraic_eval_le (X (Sum.inr ())) (X (Sum.inl (Sum.inr ()))))).of_eq (by
      ext z; simp only [Set.mem_ofPred_eq, eval_X, Sum.elim_inr, Sum.elim_inl])

/-- Hypograph twin of `isSemialgebraic_epigraph`. -/
theorem isSemialgebraic_hypograph {f : (ι → ℝ) → ℝ} (hf : IsSemialgebraicMap f) :
    IsSemialgebraic {z : ι ⊕ Unit → ℝ | z (Sum.inr ()) ≤ f (z ∘ Sum.inl)} :=
  (isSemialgebraic_setOf_sumElim_value hf
    (isSemialgebraic_eval_le (X (Sum.inl (Sum.inr ()))) (X (Sum.inr ())))).of_eq (by
      ext z; simp only [Set.mem_ofPred_eq, eval_X, Sum.elim_inr, Sum.elim_inl])

/-- Strict epigraph. -/
theorem isSemialgebraic_strictEpigraph {f : (ι → ℝ) → ℝ} (hf : IsSemialgebraicMap f) :
    IsSemialgebraic {z : ι ⊕ Unit → ℝ | f (z ∘ Sum.inl) < z (Sum.inr ())} :=
  (isSemialgebraic_setOf_sumElim_value hf
    (isSemialgebraic_eval_lt (X (Sum.inr ())) (X (Sum.inl (Sum.inr ()))))).of_eq (by
      ext z; simp only [Set.mem_ofPred_eq, eval_X, Sum.elim_inr, Sum.elim_inl])

/-- Strict hypograph. -/
theorem isSemialgebraic_strictHypograph {f : (ι → ℝ) → ℝ} (hf : IsSemialgebraicMap f) :
    IsSemialgebraic {z : ι ⊕ Unit → ℝ | z (Sum.inr ()) < f (z ∘ Sum.inl)} :=
  (isSemialgebraic_setOf_sumElim_value hf
    (isSemialgebraic_eval_lt (X (Sum.inl (Sum.inr ()))) (X (Sum.inr ())))).of_eq (by
      ext z; simp only [Set.mem_ofPred_eq, eval_X, Sum.elim_inr, Sum.elim_inl])

end Epigraph

section Closure

variable [HasSemialgebraicProjections] {ι : Type} [Fintype ι]

/-- `sa.closure` (optional): the closure of a semialgebraic set is semialgebraic.
`y ∈ closure s ↔ ∀ ε > 0, ∃ x ∈ s, ∀ i, |y i - x i| < ε`. -/
theorem IsSemialgebraic.closure {s : Set (ι → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic (closure s) := by
  have h0 : IsSemialgebraic {w : (ι ⊕ Unit) ⊕ ι → ℝ |
      ∀ i, |w (Sum.inl (Sum.inl i)) - w (Sum.inr i)| < w (Sum.inl (Sum.inr ()))} := by
    refine isSemialgebraic_setOf_forall fun i => ?_
    refine (isSemialgebraic_setOf_and
      (isSemialgebraic_eval_lt (X (Sum.inl (Sum.inl i)) - X (Sum.inr i)) (X (Sum.inl (Sum.inr ()))))
      (isSemialgebraic_eval_lt (X (Sum.inr i) - X (Sum.inl (Sum.inl i))) (X (Sum.inl (Sum.inr ())))))
      |>.of_eq ?_
    ext w
    simp only [Set.mem_ofPred_eq, eval_sub, eval_X, abs_sub_lt_iff]
  have h1 := (h0.exists_mem_sumElim (α := ι ⊕ Unit) hs).forall_pos
  refine h1.of_eq ?_
  ext y
  simp only [Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr, Metric.mem_closure_iff]
  refine forall_congr' fun ε => imp_congr_right fun hε => exists_congr fun x => and_congr_right fun _ => ?_
  rw [dist_pi_lt_iff hε]
  simp only [Real.dist_eq]

/-- `sa.interior` (optional): `interior s = (closure sᶜ)ᶜ`. -/
theorem IsSemialgebraic.interior {s : Set (ι → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic (interior s) :=
  hs.compl.closure.compl.of_eq (by rw [closure_compl, compl_compl])

end Closure

end Bilevel
