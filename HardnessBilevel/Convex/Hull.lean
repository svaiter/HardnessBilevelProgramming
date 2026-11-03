import HardnessBilevel.Convex.Linearize

/-!
# Theorem 2.21: compactness of convex hulls in `κ → ℝ` (blueprint §4.H.2)

Blueprint ids implemented here:
* `t221.caratheodory_union` — `Bilevel.t221_caratheodory_union`
* `t221.weights_compact`    — `Bilevel.weights_isClosed`, `Bilevel.weights_isCompact`
* `t221.hull_compact`       — `Bilevel.isCompact_convexHull_of_isCompact`, `Bilevel.continuous_Msp`,
  `Bilevel.isCompact_convexHull_Msp` (this is `t221.cc_data` (d))

`t221.hull_sa` (needs A1) is not provided here.

The inline weight set `W k = {w : Fin k → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}` of the blueprint is given the name
`Bilevel.hullWeights k` (a one-line abbreviation, definitionally the blueprint's set; the deprecated `stdSimplex` is not
used). The map `(w, z) ↦ ∑ i, w i • z i` is `Bilevel.hullComb k`.
-/

namespace Bilevel

open Set

/-- The inline weight set `W k := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}` (blueprint §4.H.2). -/
def hullWeights (k : ℕ) : Set (Fin k → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

/-- The convex-combination map `(w, z) ↦ ∑ i, w i • z i`. -/
def hullComb {E : Type*} [AddCommMonoid E] [Module ℝ E] (k : ℕ) :
    (Fin k → ℝ) × (Fin k → E) → E :=
  fun wz => ∑ i, wz.1 i • wz.2 i

section Caratheodory

variable {κ : Type*} [Fintype κ]

/-- **t221.caratheodory_union** (L11a): the convex hull in `κ → ℝ` is a finite union of images of
`W k × s^k`, `k < card κ + 2` (no zero-weight padding needed). -/
theorem t221_caratheodory_union (s : Set (κ → ℝ)) :
    convexHull ℝ s = ⋃ k ∈ Finset.range (Fintype.card κ + 2),
      hullComb k '' (hullWeights k ×ˢ Set.pi Set.univ (fun _ : Fin k => s)) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨ι₀, _, z, w, hz, hai, hw0, hw1, rfl⟩ := eq_pos_convex_span_of_mem_convexHull hx
    have hcard : Fintype.card ι₀ ≤ Fintype.card κ + 1 := by
      have h1 := hai.card_le_finrank_succ
      have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
      rw [Module.finrank_fintype_fun_eq_card] at h2
      omega
    set e := Fintype.equivFin ι₀
    simp only [mem_iUnion]
    refine ⟨Fintype.card ι₀, Finset.mem_range.mpr (by omega), (w ∘ e.symm, z ∘ e.symm), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact fun i => (hw0 _).le
    · simpa only [Function.comp_apply] using (Equiv.sum_comp e.symm w).trans hw1
    · exact fun i _ => hz ⟨_, rfl⟩
    · simp only [hullComb, Function.comp_apply]
      exact Equiv.sum_comp e.symm (fun j => w j • z j)
  · simp only [iUnion_subset_iff]
    rintro k - _ ⟨⟨w, z⟩, ⟨⟨hw0, hw1⟩, hz⟩, rfl⟩
    exact (convex_convexHull ℝ s).sum_mem (fun i _ => hw0 i) hw1
      fun i _ => subset_convexHull ℝ s (hz i (mem_univ i))

end Caratheodory

/-- **t221.weights_compact**, closedness. -/
theorem weights_isClosed (k : ℕ) : IsClosed (hullWeights k) := by
  have : hullWeights k = (⋂ i, {w : Fin k → ℝ | 0 ≤ w i}) ∩ {w | ∑ i, w i = 1} := by
    ext w
    simp only [hullWeights, mem_inter_iff, mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

/-- **t221.weights_compact**: `W k` is compact. -/
theorem weights_isCompact (k : ℕ) : IsCompact (hullWeights k) := by
  refine (isCompact_univ_pi fun _ : Fin k => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
    (weights_isClosed k) ?_
  rintro w ⟨hw0, hw1⟩ i -
  exact ⟨hw0 i, hw1 ▸ Finset.single_le_sum (fun j _ => hw0 j) (Finset.mem_univ i)⟩

/-- The convex-combination map is continuous. -/
theorem continuous_hullComb {κ : Type*} (k : ℕ) :
    Continuous (hullComb (E := κ → ℝ) k) :=
  continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_fst).smul ((continuous_apply i).comp continuous_snd)

/-- **t221.hull_compact** (L11b): in `κ → ℝ` (finite `κ`), the convex hull of a compact set is compact. -/
theorem isCompact_convexHull_of_isCompact {κ : Type*} [Fintype κ] {s : Set (κ → ℝ)} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  rw [t221_caratheodory_union s]
  exact (Finset.range _).isCompact_biUnion fun k _ =>
    ((weights_isCompact k).prod (isCompact_univ_pi fun _ => hs)).image (continuous_hullComb k)

/-- The moment map is continuous. -/
theorem continuous_Msp {n : ℕ} {ι : Type*} [Fintype ι] (S : Finset (Fin n ⊕ ι →₀ ℕ)) :
    Continuous (Msp S) :=
  continuous_pi fun _ => continuous_finsetProd _ fun j _ => (continuous_apply j).pow _

/-- **t221.hull_compact** applied to the moment image (`t221.cc_data` (d)): if `Y` is compact, so is
`Y' = convexHull ℝ (Msp S '' Y)`. -/
theorem isCompact_convexHull_Msp {n : ℕ} {ι : Type*} [Fintype ι] (S : Finset (Fin n ⊕ ι →₀ ℕ))
    {Y : Set (ι → ℝ)} (hY : IsCompact Y) : IsCompact (convexHull ℝ (Msp S '' Y)) :=
  isCompact_convexHull_of_isCompact (hY.image (continuous_Msp S))

end Bilevel
