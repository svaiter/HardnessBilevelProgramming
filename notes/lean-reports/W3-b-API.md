# W3-b API: HardnessBilevel/Assumptions/Classes.lean and HardnessBilevel/Semialgebraic/Projection.lean (namespace Bilevel)

Classes imports Semialgebraic.Basic; Projection imports Assumptions.Classes, Semialgebraic.Poly (opens MeasureTheory Function MvPolynomial).
NO instance of any of the three classes exists; consumers take `[HasSemialgebraicProjections]` / `[HasFinitenessTheorem]` /
`[HasGrowthBound]` as binders. Both files set `set_option linter.concreteInstances false` (that linter otherwise warns
"add a global instance" on every such binder) — consumers will want the same option in their files.
All theorems: #print axioms = [propext, Classical.choice, Quot.sound].

Classes (exact blueprint §2.5 statements):
```
class HasSemialgebraicProjections : Prop  -- field image_comp_inl {α β : Type} [Fintype α] [Finite β] {S : Set (α ⊕ β → ℝ)} :
                                           --   IsSemialgebraic S → IsSemialgebraic ((fun z => z ∘ Sum.inl) '' S)
class HasFinitenessTheorem : Prop         -- field exists_eq_iUnion_iInter_nonneg {ι : Type} [Fintype ι] {s} :
                                           --   IsSemialgebraic s → IsClosed s → ∃ I J P, s = ⋃ i, ⋂ j, {x | 0 ≤ eval x (P i j)}
class HasGrowthBound : Prop               -- field growth {n} {f : (Fin n → ℝ) → ℝ} : IsSemialgebraic {z | f (z ∘ inl) = z (inr ())} →
                                           --   (∀ r, ∃ B, ∀ x, ∑ i, x i ^ 2 ≤ r → |f x| ≤ B) → ∃ B M, ∀ x, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M
```
Theorems:
```
@Bilevel.HasGrowthBound.growth' : ∀ [Bilevel.HasGrowthBound] {n : ℕ} {f : (Fin n → ℝ) → ℝ},
  Bilevel.IsSemialgebraicMap f →
    (∀ (r : ℝ), ∃ B, ∀ (x : Fin n → ℝ), ∑ i, x i ^ 2 ≤ r → |f x| ≤ B) →
      ∃ B M, ∀ (x : Fin n → ℝ), |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M
@Bilevel.IsSemialgebraic.image_comp_inl : ∀ [Bilevel.HasSemialgebraicProjections] {α β : Type} [Fintype α] [Finite β]
  {S : Set (α ⊕ β → ℝ)}, Bilevel.IsSemialgebraic S → Bilevel.IsSemialgebraic ((fun z => z ∘ Sum.inl) '' S)
@Bilevel.IsSemialgebraic.exists_sumElim : ∀ [Bilevel.HasSemialgebraicProjections] {α β : Type} [Fintype α] [Finite β]
  {S : Set (α ⊕ β → ℝ)}, Bilevel.IsSemialgebraic S → Bilevel.IsSemialgebraic {v | ∃ u, Sum.elim v u ∈ S}
@Bilevel.IsSemialgebraic.forall_sumElim : ∀ [Bilevel.HasSemialgebraicProjections] {α β : Type} [Fintype α] [Finite β]
  {S : Set (α ⊕ β → ℝ)}, Bilevel.IsSemialgebraic S → Bilevel.IsSemialgebraic {v | ∀ (u : β → ℝ), Sum.elim v u ∈ S}
@Bilevel.IsSemialgebraic.exists_inr : ∀ [Bilevel.HasSemialgebraicProjections] {α β : Type} [Fintype α] [Finite β]
  {S : Set (α ⊕ β → ℝ)}, Bilevel.IsSemialgebraic S → Bilevel.IsSemialgebraic {v | ∃ z, z ∘ Sum.inl = v ∧ z ∈ S}
@Bilevel.IsSemialgebraic.forall_inr : ∀ [Bilevel.HasSemialgebraicProjections] {α β : Type} [Fintype α] [Finite β]
  {S : Set (α ⊕ β → ℝ)},
  Bilevel.IsSemialgebraic S → Bilevel.IsSemialgebraic {v | ∀ (z : α ⊕ β → ℝ), z ∘ Sum.inl = v → z ∈ S}
@Bilevel.IsSemialgebraic.exists_mem_sumElim : ∀ [Bilevel.HasSemialgebraicProjections] {α β : Type} [Fintype α]
  [Finite β] {S : Set (α ⊕ β → ℝ)},
  Bilevel.IsSemialgebraic S →
    ∀ {T : Set (β → ℝ)}, Bilevel.IsSemialgebraic T → Bilevel.IsSemialgebraic {v | ∃ u ∈ T, Sum.elim v u ∈ S}
@Bilevel.IsSemialgebraic.forall_mem_sumElim : ∀ [Bilevel.HasSemialgebraicProjections] {α β : Type} [Fintype α]
  [Finite β] {S : Set (α ⊕ β → ℝ)},
  Bilevel.IsSemialgebraic S →
    ∀ {T : Set (β → ℝ)}, Bilevel.IsSemialgebraic T → Bilevel.IsSemialgebraic {v | ∀ u ∈ T, Sum.elim v u ∈ S}
@Bilevel.IsSemialgebraic.exists_exists_sumElim : ∀ [Bilevel.HasSemialgebraicProjections] {α β γ : Type} [Fintype α]
  [Finite β] [Finite γ] {S : Set (α ⊕ β ⊕ γ → ℝ)},
  Bilevel.IsSemialgebraic S → Bilevel.IsSemialgebraic {v | ∃ u w, Sum.elim v (Sum.elim u w) ∈ S}
@Bilevel.IsSemialgebraic.forall_forall_sumElim : ∀ [Bilevel.HasSemialgebraicProjections] {α β γ : Type} [Fintype α]
  [Finite β] [Finite γ] {S : Set (α ⊕ β ⊕ γ → ℝ)},
  Bilevel.IsSemialgebraic S → Bilevel.IsSemialgebraic {v | ∀ (u : β → ℝ) (w : γ → ℝ), Sum.elim v (Sum.elim u w) ∈ S}
@Bilevel.IsSemialgebraic.exists_exists_sumElim' : ∀ [Bilevel.HasSemialgebraicProjections] {α β γ : Type} [Fintype α]
  [Fintype β] [Finite γ] {S : Set ((α ⊕ β) ⊕ γ → ℝ)},
  Bilevel.IsSemialgebraic S → Bilevel.IsSemialgebraic {v | ∃ u w, Sum.elim (Sum.elim v u) w ∈ S}
@Bilevel.IsSemialgebraic.forall_forall_sumElim' : ∀ [Bilevel.HasSemialgebraicProjections] {α β γ : Type} [Fintype α]
  [Fintype β] [Finite γ] {S : Set ((α ⊕ β) ⊕ γ → ℝ)},
  Bilevel.IsSemialgebraic S → Bilevel.IsSemialgebraic {v | ∀ (u : β → ℝ) (w : γ → ℝ), Sum.elim (Sum.elim v u) w ∈ S}
@Bilevel.IsSemialgebraic.exists_sumElim_assoc : ∀ [Bilevel.HasSemialgebraicProjections] {α β γ : Type} [Fintype α]
  [Fintype β] [Finite γ] {S : Set (α ⊕ β ⊕ γ → ℝ)},
  Bilevel.IsSemialgebraic S → Bilevel.IsSemialgebraic {w | ∃ u, Sum.elim (w ∘ Sum.inl) (Sum.elim (w ∘ Sum.inr) u) ∈ S}
@Bilevel.IsSemialgebraic.forall_sumElim_assoc : ∀ [Bilevel.HasSemialgebraicProjections] {α β γ : Type} [Fintype α]
  [Fintype β] [Finite γ] {S : Set (α ⊕ β ⊕ γ → ℝ)},
  Bilevel.IsSemialgebraic S →
    Bilevel.IsSemialgebraic {w | ∀ (u : γ → ℝ), Sum.elim (w ∘ Sum.inl) (Sum.elim (w ∘ Sum.inr) u) ∈ S}
@Bilevel.IsSemialgebraic.exists_sumElim_last : ∀ [Bilevel.HasSemialgebraicProjections] {α β γ : Type} [Fintype α]
  [Fintype β] [Finite γ] {S : Set ((α ⊕ β) ⊕ γ → ℝ)},
  Bilevel.IsSemialgebraic S → Bilevel.IsSemialgebraic {w | ∃ u, Sum.elim w u ∈ S}
@Bilevel.IsSemialgebraic.forall_sumElim_last : ∀ [Bilevel.HasSemialgebraicProjections] {α β γ : Type} [Fintype α]
  [Fintype β] [Finite γ] {S : Set ((α ⊕ β) ⊕ γ → ℝ)},
  Bilevel.IsSemialgebraic S → Bilevel.IsSemialgebraic {w | ∀ (u : γ → ℝ), Sum.elim w u ∈ S}
@Bilevel.IsSemialgebraic.exists_real : ∀ [Bilevel.HasSemialgebraicProjections] {α : Type} [Fintype α]
  {S : Set (α ⊕ Unit → ℝ)}, Bilevel.IsSemialgebraic S → Bilevel.IsSemialgebraic {v | ∃ t, (Sum.elim v fun x => t) ∈ S}
@Bilevel.IsSemialgebraic.forall_real : ∀ [Bilevel.HasSemialgebraicProjections] {α : Type} [Fintype α]
  {S : Set (α ⊕ Unit → ℝ)},
  Bilevel.IsSemialgebraic S → Bilevel.IsSemialgebraic {v | ∀ (t : ℝ), (Sum.elim v fun x => t) ∈ S}
@Bilevel.IsSemialgebraic.exists_pos : ∀ [Bilevel.HasSemialgebraicProjections] {α : Type} [Fintype α]
  {S : Set (α ⊕ Unit → ℝ)},
  Bilevel.IsSemialgebraic S → Bilevel.IsSemialgebraic {v | ∃ ε, 0 < ε ∧ (Sum.elim v fun x => ε) ∈ S}
@Bilevel.IsSemialgebraic.forall_pos : ∀ [Bilevel.HasSemialgebraicProjections] {α : Type} [Fintype α]
  {S : Set (α ⊕ Unit → ℝ)},
  Bilevel.IsSemialgebraic S → Bilevel.IsSemialgebraic {v | ∀ (ε : ℝ), 0 < ε → (Sum.elim v fun x => ε) ∈ S}
@Bilevel.isSemialgebraic_setOf_sumElim_value : ∀ [Bilevel.HasSemialgebraicProjections] {ι : Type} [Fintype ι]
  {f : (ι → ℝ) → ℝ},
  Bilevel.IsSemialgebraicMap f →
    ∀ {T : Set ((ι ⊕ Unit) ⊕ Unit → ℝ)},
      Bilevel.IsSemialgebraic T → Bilevel.IsSemialgebraic {z | (Sum.elim z fun x => f (z ∘ Sum.inl)) ∈ T}
@Bilevel.isSemialgebraic_epigraph : ∀ [Bilevel.HasSemialgebraicProjections] {ι : Type} [Fintype ι] {f : (ι → ℝ) → ℝ},
  Bilevel.IsSemialgebraicMap f → Bilevel.IsSemialgebraic {z | f (z ∘ Sum.inl) ≤ z (Sum.inr ())}
@Bilevel.isSemialgebraic_hypograph : ∀ [Bilevel.HasSemialgebraicProjections] {ι : Type} [Fintype ι] {f : (ι → ℝ) → ℝ},
  Bilevel.IsSemialgebraicMap f → Bilevel.IsSemialgebraic {z | z (Sum.inr ()) ≤ f (z ∘ Sum.inl)}
@Bilevel.isSemialgebraic_strictEpigraph : ∀ [Bilevel.HasSemialgebraicProjections] {ι : Type} [Fintype ι]
  {f : (ι → ℝ) → ℝ}, Bilevel.IsSemialgebraicMap f → Bilevel.IsSemialgebraic {z | f (z ∘ Sum.inl) < z (Sum.inr ())}
@Bilevel.isSemialgebraic_strictHypograph : ∀ [Bilevel.HasSemialgebraicProjections] {ι : Type} [Fintype ι]
  {f : (ι → ℝ) → ℝ}, Bilevel.IsSemialgebraicMap f → Bilevel.IsSemialgebraic {z | z (Sum.inr ()) < f (z ∘ Sum.inl)}
@Bilevel.IsSemialgebraic.closure : ∀ [Bilevel.HasSemialgebraicProjections] {ι : Type} [Fintype ι] {s : Set (ι → ℝ)},
  Bilevel.IsSemialgebraic s → Bilevel.IsSemialgebraic (closure s)
@Bilevel.IsSemialgebraic.interior : ∀ [Bilevel.HasSemialgebraicProjections] {ι : Type} [Fintype ι] {s : Set (ι → ℝ)},
  Bilevel.IsSemialgebraic s → Bilevel.IsSemialgebraic (interior s)
```
