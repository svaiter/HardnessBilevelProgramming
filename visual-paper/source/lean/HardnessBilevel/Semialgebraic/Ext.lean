/-
Copyright: HardnessBilevel project.

# Extended-real-valued semialgebraic functions (paper Def 2.2)

Implements blueprint §4.B.2: `IsExtSemialgebraic` (fields `top`, `bot`, `graph`), `sa.ext_dom`
(`IsExtSemialgebraic.dom`), `sa.ext_coe` (`isExtSemialgebraic_coe_iff`), `sa.ext_neg`
(`IsExtSemialgebraic.neg`, proved without Tarski–Seidenberg: the graph of `-h` is a polynomial preimage of
the graph of `h`), plus `IsExtSemialgebraic.const` and the optional `sa.ext_graph_equiv`
(`isExtSemialgebraic_iff_extGraph`, with the encoding set `extGraph h ⊆ ι ⊕ Fin 2 → ℝ`).

Deviations: none.
-/
import HardnessBilevel.Semialgebraic.Poly

open MeasureTheory Function MvPolynomial

namespace Bilevel

/-- Def 2.2. The domain is derived (`IsExtSemialgebraic.dom`), not a field. The graph is the graph of
`h` restricted to its domain, in `ι ⊕ Unit → ℝ`. -/
structure IsExtSemialgebraic {ι : Type*} (h : (ι → ℝ) → EReal) : Prop where
  top : IsSemialgebraic {x | h x = ⊤}
  bot : IsSemialgebraic {x | h x = ⊥}
  graph : IsSemialgebraic {z : ι ⊕ Unit → ℝ | h (z ∘ Sum.inl) = ((z (Sum.inr ()) : ℝ) : EReal)}

variable {ι : Type*}

/-- `sa.ext_dom`: the (real) domain of an extended-real semialgebraic function is semialgebraic. -/
theorem IsExtSemialgebraic.dom {h : (ι → ℝ) → EReal} (hh : IsExtSemialgebraic h) :
    IsSemialgebraic {x | ∃ r : ℝ, h x = r} := by
  refine (hh.top.union hh.bot).compl.of_eq ?_
  ext x
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or]
  induction h x using EReal.rec with
  | bot => simp
  | top => simp
  | coe r => simp

/-- `sa.ext_coe`: a real function, viewed as extended-real, is semialgebraic iff its graph is. -/
theorem isExtSemialgebraic_coe_iff (f : (ι → ℝ) → ℝ) :
    IsExtSemialgebraic (fun x => (f x : EReal)) ↔ IsSemialgebraicMap f := by
  have hg : {z : ι ⊕ Unit → ℝ | ((f (z ∘ Sum.inl) : ℝ) : EReal) = ((z (Sum.inr ()) : ℝ) : EReal)} =
      graphSet f := by
    ext z; simp only [Set.mem_ofPred_eq, EReal.coe_eq_coe_iff, mem_graphSet]
  constructor
  · intro hh
    have := hh.graph
    rw [hg] at this
    exact this
  · intro hf
    refine ⟨isSemialgebraic_empty.of_eq (by ext x; simp),
      isSemialgebraic_empty.of_eq (by ext x; simp), ?_⟩
    rw [hg]; exact hf

theorem IsSemialgebraicMap.isExtSemialgebraic {f : (ι → ℝ) → ℝ} (hf : IsSemialgebraicMap f) :
    IsExtSemialgebraic (fun x => (f x : EReal)) :=
  (isExtSemialgebraic_coe_iff f).2 hf

/-- Constant extended-real functions are semialgebraic. -/
theorem IsExtSemialgebraic.const (c : EReal) : IsExtSemialgebraic (fun _ : ι → ℝ => c) := by
  induction c using EReal.rec with
  | bot =>
    exact ⟨isSemialgebraic_empty.of_eq (by ext x; simp), isSemialgebraic_univ.of_eq (by ext x; simp),
      isSemialgebraic_empty.of_eq (by ext z; simp)⟩
  | top =>
    exact ⟨isSemialgebraic_univ.of_eq (by ext x; simp), isSemialgebraic_empty.of_eq (by ext x; simp),
      isSemialgebraic_empty.of_eq (by ext z; simp)⟩
  | coe r =>
    refine IsSemialgebraicMap.isExtSemialgebraic (f := fun _ => r) ?_
    exact (isSemialgebraicMap_eval (C r)).of_eq (by ext z; simp [graphSet])

/-- `sa.ext_neg`: negation preserves extended-real semialgebraicity (no Tarski–Seidenberg needed). -/
theorem IsExtSemialgebraic.neg {h : (ι → ℝ) → EReal} (hh : IsExtSemialgebraic h) :
    IsExtSemialgebraic (fun x => -h x) := by
  refine ⟨hh.bot.of_eq (by ext x; simp [EReal.neg_eq_top_iff]),
    hh.top.of_eq (by ext x; simp [EReal.neg_eq_bot_iff]), ?_⟩
  have := hh.graph.preimage_of_poly
    (φ := fun z : ι ⊕ Unit → ℝ => Sum.elim (z ∘ Sum.inl) (fun _ => -z (Sum.inr ())))
    (Sum.elim (fun j => X (Sum.inl j)) (fun _ => -X (Sum.inr ())))
    (fun z i => by cases i <;> simp)
  refine this.of_eq ?_
  ext z
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_inr, EReal.coe_neg]
  rw [neg_eq_iff_eq_neg]

theorem isExtSemialgebraic_neg_iff {h : (ι → ℝ) → EReal} :
    IsExtSemialgebraic (fun x => -h x) ↔ IsExtSemialgebraic h := by
  refine ⟨fun hh => ?_, IsExtSemialgebraic.neg⟩
  simpa only [neg_neg] using hh.neg

/-- Encoding of the full extended-real graph of `h` in `ι ⊕ Fin 2 → ℝ`: an extended real is encoded as a
pair `(value, tag)` with tag `0` (finite, value `= h`), `1` (`h = ⊤`, value `0`) or `-1` (`h = ⊥`, value `0`). -/
def extGraph (h : (ι → ℝ) → EReal) : Set (ι ⊕ Fin 2 → ℝ) :=
  {z | (z (Sum.inr 1) = 0 ∧ h (z ∘ Sum.inl) = ((z (Sum.inr 0) : ℝ) : EReal)) ∨
    (z (Sum.inr 1) = 1 ∧ z (Sum.inr 0) = 0 ∧ h (z ∘ Sum.inl) = ⊤) ∨
    (z (Sum.inr 1) = -1 ∧ z (Sum.inr 0) = 0 ∧ h (z ∘ Sum.inl) = ⊥)}

/-- `sa.ext_graph_equiv` (optional): Def 2.2 agrees with semialgebraicity of the encoded graph. -/
theorem isExtSemialgebraic_iff_extGraph (h : (ι → ℝ) → EReal) :
    IsExtSemialgebraic h ↔ IsSemialgebraic (extGraph h) := by
  constructor
  · intro hh
    have h1 : IsSemialgebraic {z : ι ⊕ Fin 2 → ℝ | z (Sum.inr 1) = 0 ∧
        h (z ∘ Sum.inl) = ((z (Sum.inr 0) : ℝ) : EReal)} := by
      refine isSemialgebraic_setOf_and (isSemialgebraic_coord_eq_const _ _) ?_
      refine (hh.graph.preimage_of_poly
        (φ := fun z : ι ⊕ Fin 2 → ℝ => Sum.elim (z ∘ Sum.inl) (fun _ => z (Sum.inr 0)))
        (Sum.elim (fun j => X (Sum.inl j)) (fun _ => X (Sum.inr 0)))
        (fun z i => by cases i <;> simp)).of_eq ?_
      ext z; simp
    have h2 : IsSemialgebraic {z : ι ⊕ Fin 2 → ℝ | z (Sum.inr 1) = 1 ∧ z (Sum.inr 0) = 0 ∧
        h (z ∘ Sum.inl) = ⊤} :=
      isSemialgebraic_setOf_and (isSemialgebraic_coord_eq_const _ _)
        (isSemialgebraic_setOf_and (isSemialgebraic_coord_eq_const _ _) (hh.top.reindex Sum.inl))
    have h3 : IsSemialgebraic {z : ι ⊕ Fin 2 → ℝ | z (Sum.inr 1) = -1 ∧ z (Sum.inr 0) = 0 ∧
        h (z ∘ Sum.inl) = ⊥} :=
      isSemialgebraic_setOf_and (isSemialgebraic_coord_eq_const _ _)
        (isSemialgebraic_setOf_and (isSemialgebraic_coord_eq_const _ _) (hh.bot.reindex Sum.inl))
    exact isSemialgebraic_setOf_or h1 (isSemialgebraic_setOf_or h2 h3)
  · intro hE
    refine ⟨?_, ?_, ?_⟩
    · refine (hE.preimage_of_poly (φ := fun x : ι → ℝ => Sum.elim x ![0, 1])
        (Sum.elim X ![C 0, C 1]) (fun x i => by
          rcases i with j | j
          · simp
          · fin_cases j <;> simp)).of_eq ?_
      ext x; simp [extGraph]; norm_num
    · refine (hE.preimage_of_poly (φ := fun x : ι → ℝ => Sum.elim x ![0, -1])
        (Sum.elim X ![C 0, C (-1)]) (fun x i => by
          rcases i with j | j
          · simp
          · fin_cases j <;> simp)).of_eq ?_
      ext x; simp [extGraph]; norm_num
    · refine (hE.preimage_of_poly
        (φ := fun z : ι ⊕ Unit → ℝ => Sum.elim (z ∘ Sum.inl) ![z (Sum.inr ()), 0])
        (Sum.elim (fun j => X (Sum.inl j)) ![X (Sum.inr ()), C 0]) (fun z i => by
          rcases i with j | j
          · simp
          · fin_cases j <;> simp)).of_eq ?_
      ext z; simp [extGraph]

end Bilevel
