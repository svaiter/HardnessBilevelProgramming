/-
Copyright: HardnessBilevel project.

# Convex hull of a polynomial image of a semialgebraic set (for Theorem 2.21)

Implements blueprint §4.B.7, id `sa.hull_semialgebraic` (S8), from assumption A1
(`[HasSemialgebraicProjections]` is an explicit binder; no instance of the class exists anywhere).

Statement (generalised from `Fin m` / `Fin K` to arbitrary finite index types `m`, `K`): for `Y ⊆ ℝ^m`
semialgebraic and `F : K → MvPolynomial m ℝ`, `convexHull ℝ ((fun y k => eval y (F k)) '' Y)` is semialgebraic.

Proof route (blueprint): Carathéodory (`eq_pos_convex_span_of_mem_convexHull`,
`AffineIndependent.card_le_finrank_succ`, `Module.finrank_fintype_fun_eq_card`). Instead of padding to exactly
`card K + 1` points we use the (allowed) variant: the hull is the finite union over `N ≤ card K + 1` of the sets
`hullSlice Y F N` of convex combinations of exactly `N` image points; each slice is the projection along the block
`Fin N ⊕ (Fin N × m)` (weights and points) of a Boolean combination of polynomial conditions and cylinders over `Y`.
-/
import HardnessBilevel.Semialgebraic.Projection

open MeasureTheory Function MvPolynomial

namespace Bilevel

-- No instance of the A1 class exists (by policy), so the assumption is deliberately a local binder.
set_option linter.concreteInstances false

variable {m K : Type}

/-- Convex combinations of exactly `N` points of the polynomial image `(fun y k => eval y (F k)) '' Y`,
written with the weights `c` and the preimage points `y` as explicit variables. -/
def hullSlice (Y : Set (m → ℝ)) (F : K → MvPolynomial m ℝ) (N : ℕ) : Set (K → ℝ) :=
  {l | ∃ (c : Fin N → ℝ) (y : Fin N → m → ℝ), (∀ i, 0 ≤ c i) ∧ ∑ i, c i = 1 ∧ (∀ i, y i ∈ Y) ∧
    ∀ k, l k = ∑ i, c i * eval (y i) (F k)}

theorem hullSlice_subset_convexHull (Y : Set (m → ℝ)) (F : K → MvPolynomial m ℝ) (N : ℕ) :
    hullSlice Y F N ⊆ convexHull ℝ ((fun y k => eval y (F k)) '' Y) := by
  rintro l ⟨c, y, hc0, hc1, hy, hl⟩
  have hl' : l = ∑ i, c i • (fun k => eval (y i) (F k)) := by
    funext k
    rw [hl k, Finset.sum_apply]
    rfl
  rw [hl']
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hc0 i) hc1
    (fun i _ => subset_convexHull ℝ _ ⟨y i, hy i, rfl⟩)

/-- Carathéodory: every point of the hull is a convex combination of at most `card K + 1` image points. -/
theorem convexHull_subset_iUnion_hullSlice [Fintype K] (Y : Set (m → ℝ)) (F : K → MvPolynomial m ℝ) :
    convexHull ℝ ((fun y k => eval y (F k)) '' Y) ⊆
      ⋃ N : Fin (Fintype.card K + 2), hullSlice Y F N := by
  intro l hl
  obtain ⟨ι, _, z, w, hzA, hz, hw0, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hl
  have hcard : Fintype.card ι < Fintype.card K + 2 := by
    have h1 := hz.card_le_finrank_succ
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ Module.finrank ℝ (K → ℝ) :=
      Submodule.finrank_le _
    rw [Module.finrank_fintype_fun_eq_card] at h2
    omega
  have hzY : ∀ i, ∃ y ∈ Y, (fun k => eval y (F k)) = z i := fun i => hzA ⟨i, rfl⟩
  choose y hyY hyz using hzY
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine Set.mem_iUnion.2 ⟨⟨Fintype.card ι, hcard⟩, ?_⟩
  refine ⟨fun j => w (e j), fun j => y (e j), fun j => (hw0 _).le, ?_, fun j => hyY _, fun k => ?_⟩
  · rw [Equiv.sum_comp e w]; exact hw1
  · rw [Equiv.sum_comp e (fun i => w i * eval (y i) (F k)), ← hwz, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hyz i]
    rfl

theorem convexHull_eq_iUnion_hullSlice [Fintype K] (Y : Set (m → ℝ)) (F : K → MvPolynomial m ℝ) :
    convexHull ℝ ((fun y k => eval y (F k)) '' Y) =
      ⋃ N : Fin (Fintype.card K + 2), hullSlice Y F N :=
  Set.Subset.antisymm (convexHull_subset_iUnion_hullSlice Y F)
    (Set.iUnion_subset fun N => hullSlice_subset_convexHull Y F N)

/-- Each slice is semialgebraic (projection along the block `Fin N ⊕ (Fin N × m)`). -/
theorem isSemialgebraic_hullSlice [HasSemialgebraicProjections] [Fintype m] [Fintype K]
    {Y : Set (m → ℝ)} (hY : IsSemialgebraic Y) (F : K → MvPolynomial m ℝ) (N : ℕ) :
    IsSemialgebraic (hullSlice Y F N) := by
  -- variables: `K ⊕ (Fin N ⊕ (Fin N × m))`, i.e. `(l, c, y)`
  let cI : Fin N → K ⊕ (Fin N ⊕ (Fin N × m)) := fun i => Sum.inr (Sum.inl i)
  let yI : Fin N → m → K ⊕ (Fin N ⊕ (Fin N × m)) := fun i a => Sum.inr (Sum.inr (i, a))
  have h1 : IsSemialgebraic {z : K ⊕ (Fin N ⊕ (Fin N × m)) → ℝ | ∀ i, 0 ≤ z (cI i)} :=
    isSemialgebraic_setOf_forall fun i => isSemialgebraic_const_le_coord 0 (cI i)
  have h2 : IsSemialgebraic {z : K ⊕ (Fin N ⊕ (Fin N × m)) → ℝ | ∑ i, z (cI i) = 1} := by
    refine (isSemialgebraic_eval_eq (∑ i, X (cI i)) 1).of_eq ?_
    ext z
    simp only [Set.mem_ofPred_eq, map_sum, eval_X, map_one]
  have h3 : IsSemialgebraic {z : K ⊕ (Fin N ⊕ (Fin N × m)) → ℝ | ∀ i, (fun a => z (yI i a)) ∈ Y} :=
    isSemialgebraic_setOf_forall fun i => (hY.reindex (yI i)).of_eq rfl
  have h4 : IsSemialgebraic {z : K ⊕ (Fin N ⊕ (Fin N × m)) → ℝ |
      ∀ k, z (Sum.inl k) = ∑ i, z (cI i) * eval (fun a => z (yI i a)) (F k)} := by
    refine isSemialgebraic_setOf_forall fun k => ?_
    refine (isSemialgebraic_eval_eq (X (Sum.inl k))
      (∑ i, X (cI i) * MvPolynomial.rename (yI i) (F k))).of_eq ?_
    ext z
    simp only [Set.mem_ofPred_eq, map_sum, map_mul, eval_X, eval_rename]
    rfl
  have h := (isSemialgebraic_setOf_and h1 (isSemialgebraic_setOf_and h2
    (isSemialgebraic_setOf_and h3 h4))).exists_sumElim
  refine h.of_eq ?_
  ext l
  simp only [hullSlice, Set.mem_ofPred_eq, cI, yI, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨u, hu0, hu1, huY, hul⟩
    exact ⟨fun i => u (Sum.inl i), fun i a => u (Sum.inr (i, a)), hu0, hu1, huY, hul⟩
  · rintro ⟨c, y, hc0, hc1, hy, hl⟩
    exact ⟨Sum.elim c (fun p => y p.1 p.2), hc0, hc1, hy, hl⟩

/-- `sa.hull_semialgebraic` (S8, blueprint §4.B.7): the convex hull of a polynomial image of a semialgebraic
set is semialgebraic (assumption A1). -/
theorem isSemialgebraic_convexHull_image [HasSemialgebraicProjections] [Fintype m] [Fintype K]
    {Y : Set (m → ℝ)} (hY : IsSemialgebraic Y) (F : K → MvPolynomial m ℝ) :
    IsSemialgebraic (convexHull ℝ ((fun y k => eval y (F k)) '' Y)) := by
  rw [convexHull_eq_iUnion_hullSlice]
  exact isSemialgebraic_iUnion fun N => isSemialgebraic_hullSlice hY F N

end Bilevel
