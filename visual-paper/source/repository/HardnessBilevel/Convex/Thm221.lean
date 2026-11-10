/-
Copyright: HardnessBilevel project.

# Theorem 2.21 (convex lower level, compact semialgebraic lower sets): `𝒞_cc = SA ∩ LSC ∩ CB`

Implements blueprint §4.H.3 and the specialisation `t221.hull_sa` of `sa.hull_semialgebraic`:
* `t221.hull_sa` — `thm221_hull_sa` `[A1]`: `convexHull (Msp S '' Y)` is semialgebraic for semialgebraic `Y`;
* `t221.compact_sa_incl` — `thm221_compact_sa_incl` `[A1]` (and the pessimistic `thm221_compact_sa_incl_pess`):
  every polynomial bilevel problem with nonempty compact semialgebraic lower set has its value function in
  `𝒞_cc` (resp. `𝒞^p_cc`), by linearisation (`t221_linearize_value`/`_pvalue`, `t221_cc_data_*`);
* `t221.supset` — `thm221_supset` `[A1, A2, A3]` (via `thm215_supset`);
* `t221.eq` — `thm221_eq` `[A1, A2, A3]`.
`t221.subset` is `thm221_subset` `[A1]` in `HardnessBilevel.Semialgebraic.Value`.

Assumptions are taken only as instance-implicit binders; no instance of any assumption class exists.

Deviations: none (the lower index type of `thm221_compact_sa_incl` is in `Type`, as required by the classes).
-/
import HardnessBilevel.Bounded.Thm215
import HardnessBilevel.Convex.Hull
import HardnessBilevel.Semialgebraic.Hull

open MeasureTheory Function MvPolynomial

namespace Bilevel

-- No instance of the assumption classes exists (by policy), so they are deliberately local binders.
set_option linter.concreteInstances false

/-- The moment map is the evaluation of the monomials `∏ j, X j ^ d (inr j)`. -/
theorem Msp_eq_eval {n : ℕ} {ι : Type} [Fintype ι] (S : Finset (Fin n ⊕ ι →₀ ℕ)) (y : ι → ℝ) :
    Msp S y = fun d : S => eval y (∏ j : ι, (X j : MvPolynomial ι ℝ) ^ (d.1 (Sum.inr j))) := by
  funext d
  simp only [Msp, map_prod, map_pow, eval_X]

/-- **t221.hull_sa** `[A1]`: the convex hull of the moment image of a semialgebraic set is semialgebraic. -/
theorem thm221_hull_sa [HasSemialgebraicProjections] {n : ℕ} {ι : Type} [Fintype ι]
    (S : Finset (Fin n ⊕ ι →₀ ℕ)) {Y : Set (ι → ℝ)} (hY : IsSemialgebraic Y) :
    IsSemialgebraic (convexHull ℝ (Msp S '' Y)) := by
  have h := isSemialgebraic_convexHull_image (K := S) hY
    (fun d : S => ∏ j : ι, (X j : MvPolynomial ι ℝ) ^ (d.1 (Sum.inr j)))
  have hM : (Msp S : (ι → ℝ) → S → ℝ) =
      fun y (d : S) => eval y (∏ j : ι, (X j : MvPolynomial ι ℝ) ^ (d.1 (Sum.inr j))) :=
    funext fun y => Msp_eq_eval S y
  rw [hM]
  exact h

/-- **t221.compact_sa_incl** `[A1]`: a polynomial bilevel problem with nonempty compact semialgebraic lower set
has its (optimistic) value function in `𝒞_cc`. -/
theorem thm221_compact_sa_incl [HasSemialgebraicProjections] {n : ℕ} {ι : Type} [Fintype ι]
    {P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} (hP : IsPolyFun P) (hQ : IsPolyFun Q) {Y : Set (ι → ℝ)}
    (hYc : IsCompact Y) (hYn : Y.Nonempty) (hYs : IsSemialgebraic Y) :
    valueFun P Q Y ∈ C_cc n := by
  obtain ⟨pP, rfl⟩ := isPolyFun_iff_exists_polyFun.1 hP
  obtain ⟨pQ, rfl⟩ := isPolyFun_iff_exists_polyFun.1 hQ
  set S : Finset (Fin n ⊕ ι →₀ ℕ) := pP.support ∪ pQ.support
  refine ⟨S, inferInstance, fun x l => plin S pP x l, fun x l => plin S pQ x l,
    convexHull ℝ (Msp S '' Y), t221_cc_data_isPolyFun S pP, t221_cc_data_isPolyFun S pQ,
    ⟨t221_cc_data_nonempty S hYn, isCompact_convexHull_Msp S hYc, t221_cc_data_convex S Y,
      thm221_hull_sa S hYs⟩, t221_cc_data_convexLower S pQ, ?_⟩
  funext x
  exact (t221_linearize_value (S := S) (P := pP) (Q := pQ) le_rfl Y x).symm

/-- Pessimistic **t221.compact_sa_incl** `[A1]`: the pessimistic value function lies in `𝒞^p_cc`. -/
theorem thm221_compact_sa_incl_pess [HasSemialgebraicProjections] {n : ℕ} {ι : Type} [Fintype ι]
    {P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} (hP : IsPolyFun P) (hQ : IsPolyFun Q) {Y : Set (ι → ℝ)}
    (hYc : IsCompact Y) (hYn : Y.Nonempty) (hYs : IsSemialgebraic Y) :
    pvalueFun P Q Y ∈ Cp_cc n := by
  obtain ⟨pP, rfl⟩ := isPolyFun_iff_exists_polyFun.1 hP
  obtain ⟨pQ, rfl⟩ := isPolyFun_iff_exists_polyFun.1 hQ
  set S : Finset (Fin n ⊕ ι →₀ ℕ) := pP.support ∪ pQ.support
  refine ⟨S, inferInstance, fun x l => plin S pP x l, fun x l => plin S pQ x l,
    convexHull ℝ (Msp S '' Y), t221_cc_data_isPolyFun S pP, t221_cc_data_isPolyFun S pQ,
    ⟨t221_cc_data_nonempty S hYn, isCompact_convexHull_Msp S hYc, t221_cc_data_convex S Y,
      thm221_hull_sa S hYs⟩, t221_cc_data_convexLower S pQ, ?_⟩
  funext x
  exact (t221_linearize_pvalue (S := S) (P := pP) (Q := pQ) le_rfl Y x).symm

/-- **t221.supset** (Thm 2.21 ⊇) `[A1, A2, A3]`: `SA ∩ LSC ∩ CB ⊆ 𝒞_cc`. -/
theorem thm221_supset [HasSemialgebraicProjections] [HasFinitenessTheorem] [HasGrowthBound] {n : ℕ} :
    SA n ∩ LSC n ∩ CB n ⊆ C_cc n := by
  intro h hh
  obtain ⟨f, rfl, hsa, hlsc, hcb⟩ := exists_real_of_mem_SA_LSC_CB hh
  obtain ⟨ι, hι, P, Q, a, b, hP, hQ, hab, hv⟩ := thm215_supset f hsa hlsc hcb
  have hY : (boundedBox a b).Nonempty := ⟨a, mem_boundedBox.2 fun k => ⟨le_rfl, hab k⟩⟩
  have hmem := thm221_compact_sa_incl hP hQ (isCompact_boundedBox a b) hY (isSemialgebraic_boundedBox a b)
  have heq : valueFun P Q (boundedBox a b) = coeFun f := funext hv
  rw [heq] at hmem
  exact hmem

/-- **t221.eq** (Thm 2.21) `[A1, A2, A3]`: `𝒞_cc = SA ∩ LSC ∩ CB`. -/
theorem thm221_eq [HasSemialgebraicProjections] [HasFinitenessTheorem] [HasGrowthBound] {n : ℕ} :
    C_cc n = SA n ∩ LSC n ∩ CB n :=
  Set.Subset.antisymm thm221_subset thm221_supset

end Bilevel
