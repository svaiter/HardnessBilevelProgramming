/-
Copyright: HardnessBilevel project.

# Theorem 2.15 (bounded boxes): `𝒫_bounded = SA ∩ LSC ∩ CB`

Implements blueprint §4.F.3: `t215.supset` (`thm215_supset`, assumptions A1 + A2 + A3), the class form
`thm215_mem_P_bounded`, and `t215.eq` (`thm215_eq`, A1 + A2 + A3). The core construction (`t215.core`,
`t215.epi_closed`, the rescaling and packaging) lives in `HardnessBilevel.Bounded.Thm215Core`; `t215.subset`
is `thm215_subset` in `HardnessBilevel.Semialgebraic.Value` (A1 only); `t215.epi_sa` is
`isSemialgebraic_epigraph` (A1) in `HardnessBilevel.Semialgebraic.Projection`.

Assumptions are taken only as instance-implicit binders; no instance of any assumption class exists.

Deviations: the semialgebraicity hypothesis of `thm215_supset` is `IsSemialgebraicMap f`, which is by
definition `IsSemialgebraic (graphSet f)` (the blueprint's form).
-/
import HardnessBilevel.Bounded.Thm215Core
import HardnessBilevel.Semialgebraic.Value

open MeasureTheory Function MvPolynomial

namespace Bilevel

-- No instance of the assumption classes exists (by policy), so they are deliberately local binders.
set_option linter.concreteInstances false

/-- Points of the sum-of-squares ball `{∑ x_i² ≤ r}` lie in the compact box `[-(|r|+1), |r|+1]ⁿ`. -/
theorem mem_boundedBox_of_sum_sq_le {n : ℕ} {r : ℝ} {x : Fin n → ℝ} (hx : ∑ i, x i ^ 2 ≤ r) :
    x ∈ boundedBox (fun _ => -(|r| + 1)) (fun _ => |r| + 1) := by
  rw [mem_boundedBox]
  intro i
  have hi : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have h1 : x i ^ 2 ≤ |r| := le_trans (le_trans hi hx) (le_abs_self r)
  have h0 : 0 ≤ |r| := abs_nonneg r
  constructor <;> nlinarith [sq_nonneg (x i + 1), sq_nonneg (x i - 1)]

/-- A function bounded on compacts is bounded on every sum-of-squares ball (hypothesis of A3). -/
theorem bdd_sum_sq_of_bdd_compact {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hcb : ∀ K : Set (Fin n → ℝ), IsCompact K → ∃ B, ∀ x ∈ K, |f x| ≤ B) :
    ∀ r : ℝ, ∃ B : ℝ, ∀ x, ∑ i, x i ^ 2 ≤ r → |f x| ≤ B := by
  intro r
  obtain ⟨B, hB⟩ := hcb _ (isCompact_boundedBox (fun _ : Fin n => -(|r| + 1)) (fun _ => |r| + 1))
  exact ⟨B, fun x hx => hB x (mem_boundedBox_of_sum_sq_le hx)⟩

/-- **t215.supset** (Thm 2.15 ⊇) `[A1, A2, A3]`. Every real semialgebraic, lower semicontinuous function
bounded on compacts is the value function of a polynomial bilevel problem over a bounded box. -/
theorem thm215_supset [HasSemialgebraicProjections] [HasFinitenessTheorem] [HasGrowthBound]
    {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hsa : IsSemialgebraicMap f)
    (hlsc : LowerSemicontinuous f)
    (hcb : ∀ K : Set (Fin n → ℝ), IsCompact K → ∃ B, ∀ x ∈ K, |f x| ≤ B) :
    ∃ (ι : Type) (_ : Fintype ι) (P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ) (a b : ι → ℝ),
      IsPolyFun P ∧ IsPolyFun Q ∧ (∀ k, a k ≤ b k) ∧
      ∀ x, valueFun P Q (boundedBox a b) x = ((f x : ℝ) : EReal) := by
  -- (1) growth bound (A3)
  obtain ⟨B, M, hBM⟩ := HasGrowthBound.growth' hsa (bdd_sum_sq_of_bdd_compact hcb)
  set wq : MvPolynomial (Fin n) ℝ := C (|B| + 1) + (1 + ∑ i, X i ^ 2) ^ M with hwq
  have hev : ∀ x : Fin n → ℝ, eval x wq = (|B| + 1) + (1 + ∑ i, x i ^ 2) ^ M := by
    intro x
    simp only [hwq, eval_add, eval_C, eval_pow, eval_X, map_sum, map_one]
  have hw0 : ∀ x : Fin n → ℝ, 0 < eval x wq := by
    intro x; rw [hev]; positivity
  have hfw : ∀ x : Fin n → ℝ, |f x| ≤ eval x wq := by
    intro x; rw [hev]; linarith [hBM x, le_abs_self B]
  -- (2) the epigraph: closed and semialgebraic (A1)
  set E : Set (Fin n ⊕ Unit → ℝ) := {z | f (z ∘ Sum.inl) ≤ z (Sum.inr ())} with hEdef
  have hEc : IsClosed E := isClosed_epigraph_sum hlsc
  have hEs : IsSemialgebraic E := isSemialgebraic_epigraph hsa
  -- (3) finiteness theorem (A2)
  obtain ⟨I, J, p, hEp⟩ := HasFinitenessTheorem.exists_eq_iUnion_iInter_nonneg hEs hEc
  have hmem : ∀ z : Fin n ⊕ Unit → ℝ, z ∈ E ↔ ∃ i, ∀ j, 0 ≤ eval z (p i j) := by
    intro z
    rw [hEp]
    simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq]
  -- (4) apply the core
  refine thm215_of_presentation f wq hw0 hfw p ?_ ?_
  · intro x
    refine (hmem _).1 ?_
    show f (Sum.elim x (fun _ => f x) ∘ Sum.inl) ≤ Sum.elim x (fun _ => f x) (Sum.inr ())
    simp
  · intro x τ h
    have h' := (hmem _).2 h
    have : f (Sum.elim x (fun _ => τ) ∘ Sum.inl) ≤ Sum.elim x (fun _ => τ) (Sum.inr ()) := h'
    simpa using this

/-- Class form of `t215.supset` `[A1, A2, A3]`. -/
theorem thm215_mem_P_bounded [HasSemialgebraicProjections] [HasFinitenessTheorem] [HasGrowthBound]
    {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hsa : IsSemialgebraicMap f)
    (hlsc : LowerSemicontinuous f)
    (hcb : ∀ K : Set (Fin n → ℝ), IsCompact K → ∃ B, ∀ x ∈ K, |f x| ≤ B) :
    coeFun f ∈ P_bounded n := by
  obtain ⟨ι, hι, P, Q, a, b, hP, hQ, hab, hv⟩ := thm215_supset f hsa hlsc hcb
  exact ⟨ι, hι, P, Q, boundedBox a b, hP, hQ, ⟨a, b, hab, rfl⟩, trivial,
    funext fun x => (hv x).symm⟩

/-- A function in `CB n` is the coercion of its real part. -/
theorem eq_coeFun_toReal_of_mem_CB {n : ℕ} {h : (Fin n → ℝ) → EReal} (hh : h ∈ CB n) :
    h = coeFun (fun x => (h x).toReal) := by
  funext x
  obtain ⟨ht, hb⟩ := CB_real hh x
  exact (EReal.coe_toReal ht hb).symm

/-- Data extraction for `SA ∩ LSC ∩ CB` (used by Thm 2.15 and Thm 2.21 ⊇): a member is `coeFun f` for a real
semialgebraic, lower semicontinuous `f` bounded on compacts. -/
theorem exists_real_of_mem_SA_LSC_CB {n : ℕ} {h : (Fin n → ℝ) → EReal}
    (hh : h ∈ SA n ∩ LSC n ∩ CB n) :
    ∃ f : (Fin n → ℝ) → ℝ, h = coeFun f ∧ IsSemialgebraicMap f ∧ LowerSemicontinuous f ∧
      ∀ K : Set (Fin n → ℝ), IsCompact K → ∃ B, ∀ x ∈ K, |f x| ≤ B := by
  obtain ⟨⟨hsa, hlsc⟩, hcb⟩ := hh
  set f : (Fin n → ℝ) → ℝ := fun x => (h x).toReal
  have hf : h = coeFun f := eq_coeFun_toReal_of_mem_CB hcb
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · have : IsExtSemialgebraic (fun x => ((f x : ℝ) : EReal)) := by
      have h1 : IsExtSemialgebraic h := hsa
      rw [hf] at h1; exact h1
    exact (isExtSemialgebraic_coe_iff f).1 this
  · have h1 : LowerSemicontinuous h := hlsc
    rw [hf] at h1
    exact (lowerSemicontinuous_coe_iff f).1 h1
  · intro K hK
    obtain ⟨B, hB⟩ := hcb K hK
    refine ⟨B, fun x hx => ?_⟩
    obtain ⟨h1, h2⟩ := hB x hx
    rw [hf] at h1 h2
    have h1' : -B ≤ f x := EReal.coe_le_coe_iff.1 h1
    have h2' : f x ≤ B := EReal.coe_le_coe_iff.1 h2
    exact abs_le.2 ⟨h1', h2'⟩

/-- **t215.eq** (Thm 2.15) `[A1, A2, A3]`: `𝒫_bounded = SA ∩ LSC ∩ CB`. -/
theorem thm215_eq [HasSemialgebraicProjections] [HasFinitenessTheorem] [HasGrowthBound] {n : ℕ} :
    P_bounded n = SA n ∩ LSC n ∩ CB n := by
  refine Set.Subset.antisymm thm215_subset ?_
  intro h hh
  obtain ⟨f, rfl, hsa, hlsc, hcb⟩ := exists_real_of_mem_SA_LSC_CB hh
  exact thm215_mem_P_bounded f hsa hlsc hcb

end Bilevel
