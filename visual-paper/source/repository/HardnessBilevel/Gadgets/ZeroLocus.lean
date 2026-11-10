/-
Copyright: HardnessBilevel project.

# Zero-locus gadgets (blueprint §4.E.1)

* `gad.ZeroGadget` — the structure `ZeroGadget S τ` (a nonnegative polynomial `W` in `(w, ξ)` whose
  zero locus projects onto `S`, with an explicit selector `sel`), with the derived lemmas
  `ZeroGadget.mem_of_eval_eq_zero` and `ZeroGadget.mem_iff` (Remark 2.14).
* `gad.G2` — `ZeroGadget.basic`: the gadget of a basic set `{w | P w = 0 ∧ ∀ j, 0 < Q j w}`
  (polynomial `basicW`, eval identity `eval_basicW`).
* `gad.G3` — `ZeroGadget.iUnion` (finite union, `τ' := Σ i, τ i`) and the uniform variant
  `ZeroGadget.iUnionUniform` (`τ' := ι × κ`).
* `gad.G4` — `ZeroGadget.of_isSemialgebraic`: every semialgebraic set has a gadget with
  `τ := Fin m × Fin k`, via `IsSemialgebraic.exists_uniform_basic` + G2 + G3.

No assumption (A1–A3) is used.
-/
import HardnessBilevel.Gadgets.Scalar
import HardnessBilevel.Framework.Poly
import HardnessBilevel.Semialgebraic.Basic

namespace Bilevel

open MvPolynomial

/-- gad.ZeroGadget: a nonnegative polynomial `W(w, ξ)` that vanishes for `ξ = sel w` when `w ∈ S`
and is strictly positive (for every `ξ`) when `w ∉ S`. -/
structure ZeroGadget {σ : Type*} (S : Set (σ → ℝ)) (τ : Type*) where
  /-- the gadget polynomial in the variables `(w, ξ)` -/
  W : MvPolynomial (σ ⊕ τ) ℝ
  /-- explicit witness map -/
  sel : (σ → ℝ) → (τ → ℝ)
  nonneg : ∀ w ξ, 0 ≤ MvPolynomial.eval (Sum.elim w ξ) W
  sel_zero : ∀ w ∈ S, MvPolynomial.eval (Sum.elim w (sel w)) W = 0
  pos_of_notMem : ∀ w ∉ S, ∀ ξ, 0 < MvPolynomial.eval (Sum.elim w ξ) W

namespace ZeroGadget

variable {σ : Type*}

section derived

variable {τ : Type*} {S : Set (σ → ℝ)} (𝒢 : ZeroGadget S τ)

/-- A zero of the gadget lies over `S`. -/
theorem mem_of_eval_eq_zero {w : σ → ℝ} {ξ : τ → ℝ}
    (h : MvPolynomial.eval (Sum.elim w ξ) 𝒢.W = 0) : w ∈ S := by
  by_contra hw
  exact (𝒢.pos_of_notMem w hw ξ).ne' h

/-- `S` is the projection of the zero locus of `W` (Remark 2.14). -/
theorem mem_iff {w : σ → ℝ} : w ∈ S ↔ ∃ ξ, MvPolynomial.eval (Sum.elim w ξ) 𝒢.W = 0 :=
  ⟨fun h => ⟨_, 𝒢.sel_zero w h⟩, fun ⟨_, h⟩ => 𝒢.mem_of_eval_eq_zero h⟩

end derived

/-! ### gad.G2: basic sets -/

section basic

variable {κ : Type*} [Fintype κ]

/-- gad.G2: `W_B = P(w)² + ∑ j (1 - Q_j(w) ξ_j²)²`. -/
noncomputable def basicW (P : MvPolynomial σ ℝ) (Q : κ → MvPolynomial σ ℝ) :
    MvPolynomial (σ ⊕ κ) ℝ :=
  (rename Sum.inl P) ^ 2 + ∑ j, (1 - rename Sum.inl (Q j) * X (Sum.inr j) ^ 2) ^ 2

theorem eval_basicW (P : MvPolynomial σ ℝ) (Q : κ → MvPolynomial σ ℝ) (w : σ → ℝ) (ξ : κ → ℝ) :
    MvPolynomial.eval (Sum.elim w ξ) (basicW P Q) =
      (MvPolynomial.eval w P) ^ 2 + ∑ j, gadgetStrict (MvPolynomial.eval w (Q j)) (ξ j) := by
  simp only [basicW, gadgetStrict, map_add, map_pow, map_sum, map_sub, map_mul, map_one,
    eval_X, eval_rename, Sum.elim_comp_inl, Sum.elim_inr]

/-- gad.G2: the gadget of a basic set, with `τ := κ`. -/
noncomputable def basic (P : MvPolynomial σ ℝ) (Q : κ → MvPolynomial σ ℝ) :
    ZeroGadget {w | MvPolynomial.eval w P = 0 ∧ ∀ j, 0 < MvPolynomial.eval w (Q j)} κ where
  W := basicW P Q
  sel w := fun j => Real.sqrt (MvPolynomial.eval w (Q j))⁻¹
  nonneg w ξ := by
    rw [eval_basicW]
    exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => gadgetStrict_nonneg _ _)
  sel_zero w hw := by
    rw [eval_basicW, hw.1]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
    exact Finset.sum_eq_zero fun j _ => gadgetStrict_eq_zero_of_pos (hw.2 j)
  pos_of_notMem w hw ξ := by
    rw [eval_basicW]
    have hs : 0 ≤ ∑ j, gadgetStrict (MvPolynomial.eval w (Q j)) (ξ j) :=
      Finset.sum_nonneg fun j _ => gadgetStrict_nonneg _ _
    by_cases hP : MvPolynomial.eval w P = 0
    · have : ¬ ∀ j, 0 < MvPolynomial.eval w (Q j) := fun h => hw ⟨hP, h⟩
      push Not at this
      obtain ⟨j₀, hj₀⟩ := this
      have h1 := one_le_gadgetStrict_of_nonpos hj₀ (ξ j₀)
      have h2 : gadgetStrict (MvPolynomial.eval w (Q j₀)) (ξ j₀) ≤
          ∑ j, gadgetStrict (MvPolynomial.eval w (Q j)) (ξ j) :=
        Finset.single_le_sum (f := fun j => gadgetStrict (MvPolynomial.eval w (Q j)) (ξ j))
          (fun j _ => gadgetStrict_nonneg _ _) (Finset.mem_univ j₀)
      have := sq_nonneg (MvPolynomial.eval w P)
      linarith
    · have : 0 < (MvPolynomial.eval w P) ^ 2 := by positivity
      linarith

end basic

/-! ### gad.G3: finite unions -/

section iUnion

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem sumElim_comp_sumMap_sigma {τ : ι → Type*} (w : σ → ℝ) (ξ : (Σ i, τ i) → ℝ) (i : ι) :
    Sum.elim w ξ ∘ Sum.map id (Sigma.mk i) = Sum.elim w (fun j => ξ ⟨i, j⟩) := by
  funext a; rcases a with a | b <;> rfl

/-- gad.G3: the gadget of a finite union, `W_U = ∏ i W_i(w, ξ_i)`, with `τ' := Σ i, τ i`. -/
noncomputable def iUnion {τ : ι → Type*} {S : ι → Set (σ → ℝ)} (𝒢 : ∀ i, ZeroGadget (S i) (τ i)) :
    ZeroGadget (⋃ i, S i) (Σ i, τ i) where
  W := ∏ i, rename (Sum.map id (Sigma.mk i)) (𝒢 i).W
  sel w := fun p => (𝒢 p.1).sel w p.2
  nonneg w ξ := by
    simp only [map_prod, eval_rename, sumElim_comp_sumMap_sigma]
    exact Finset.prod_nonneg fun i _ => (𝒢 i).nonneg _ _
  sel_zero w hw := by
    obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.1 hw
    simp only [map_prod, eval_rename, sumElim_comp_sumMap_sigma]
    exact Finset.prod_eq_zero (Finset.mem_univ i₀) ((𝒢 i₀).sel_zero w hi₀)
  pos_of_notMem w hw ξ := by
    simp only [map_prod, eval_rename, sumElim_comp_sumMap_sigma]
    refine Finset.prod_pos fun i _ => (𝒢 i).pos_of_notMem w ?_ _
    exact fun h => hw (Set.mem_iUnion.2 ⟨i, h⟩)

theorem iUnion_W_eval {τ : ι → Type*} {S : ι → Set (σ → ℝ)} (𝒢 : ∀ i, ZeroGadget (S i) (τ i))
    (w : σ → ℝ) (ξ : (Σ i, τ i) → ℝ) :
    MvPolynomial.eval (Sum.elim w ξ) (iUnion 𝒢).W =
      ∏ i, MvPolynomial.eval (Sum.elim w (fun j => ξ ⟨i, j⟩)) (𝒢 i).W := by
  simp only [iUnion, map_prod, eval_rename, sumElim_comp_sumMap_sigma]

omit [Fintype ι] in
theorem sumElim_comp_sumMap_prod {κ : Type*} (w : σ → ℝ) (ξ : ι × κ → ℝ) (i : ι) :
    Sum.elim w ξ ∘ Sum.map id (Prod.mk i) = Sum.elim w (fun j => ξ (i, j)) := by
  funext a; rcases a with a | b <;> rfl

/-- gad.G3 (uniform variant): all blocks share the auxiliary index type `κ`; `τ' := ι × κ`. -/
noncomputable def iUnionUniform {κ : Type*} {S : ι → Set (σ → ℝ)}
    (𝒢 : ∀ i, ZeroGadget (S i) κ) : ZeroGadget (⋃ i, S i) (ι × κ) where
  W := ∏ i, rename (Sum.map id (Prod.mk i)) (𝒢 i).W
  sel w := fun p => (𝒢 p.1).sel w p.2
  nonneg w ξ := by
    simp only [map_prod, eval_rename, sumElim_comp_sumMap_prod]
    exact Finset.prod_nonneg fun i _ => (𝒢 i).nonneg _ _
  sel_zero w hw := by
    obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.1 hw
    simp only [map_prod, eval_rename, sumElim_comp_sumMap_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i₀) ((𝒢 i₀).sel_zero w hi₀)
  pos_of_notMem w hw ξ := by
    simp only [map_prod, eval_rename, sumElim_comp_sumMap_prod]
    refine Finset.prod_pos fun i _ => (𝒢 i).pos_of_notMem w ?_ _
    exact fun h => hw (Set.mem_iUnion.2 ⟨i, h⟩)

end iUnion

/-! ### gad.G4: every semialgebraic set has a gadget -/

/-- gad.G4: a semialgebraic set admits a zero gadget with a finite auxiliary index type
(`τ := Fin m × Fin k`). -/
theorem of_isSemialgebraic {S : Set (σ → ℝ)} (hS : IsSemialgebraic S) :
    ∃ (τ : Type) (_ : Fintype τ), Nonempty (ZeroGadget S τ) := by
  obtain ⟨m, k, P, Q, rfl⟩ := hS.exists_uniform_basic
  exact ⟨Fin m × Fin k, inferInstance, ⟨iUnionUniform fun i => basic (P i) (Q i)⟩⟩

end ZeroGadget

end Bilevel
