import HardnessBilevel.Framework.Basic
import HardnessBilevel.Framework.Box
import HardnessBilevel.Framework.Poly
import HardnessBilevel.Gadgets.Box

/-!
# Theorem 2.15: the assumption-free core (blueprint §4.F.2, §4.F.3 steps 2, 5–7)

Provides:
* `t215.core`: `t215_core` (on `ℝ × (ζ → ℝ)`), with the attained form `t215_core_isLeast`.
  Both are instances of the generic `t215_core_gen` (any lower-level type `Θ` with a
  "`t`-coordinate" `T : Θ → ℝ`), proved via `argminSet_eq_zeroSet` + `valueFun_eq_of_isLeast`.
* the transported form on `Unit ⊕ ζ`: `t215_core_sum` (lower set `sumBox Z`), and
  `sumBox_gadgetBox` showing `sumBox (gadgetBox α β) = boundedBox t215Lo t215Hi`.
* `t215.epi_closed`: `isClosed_epigraph_sum`.
* step 5 (rescaling): `rescaledPoly`, `isPolyFun_rescaledPoly`, `exists_rescaledPoly_iff`.
* steps 6–7 (packaging, modulo A1–A3): `thm215_of_presentation` — given a polynomial weight
  `w ≥ |f|`, `w > 0`, and a finite union-of-intersections presentation `p` of a set `E`
  with `graph f ⊆ E ⊆ epi f`, `f` is the value function of a polynomial bilevel problem over
  a bounded box.

No assumption class is used anywhere in this file.

Deviations: none in statements. `t215_core_sum` is proved directly from `t215_core_gen` rather
than via `valueFun_comp_equiv` (same statement, simpler). In `thm215_of_presentation` the row
and column index types `α β` are arbitrary `Fintype`s in `Type` (strengthening of
`Fin a`, `Fin b`).
-/

namespace Bilevel

/-! ### t215.core -/

/-- Generic core lemma: lower-level variable `θ ∈ S` with a distinguished real coordinate
`T θ`; upper objective `T θ * w x`; lower objective `R x θ ≥ 0`, whose zeros in `S` project
(via `T`) exactly onto `{t ∈ [-1,1] | E x (t * w x)}`. -/
theorem t215_core_gen {X Θ : Type*} (f w : X → ℝ)
    (hw : ∀ x, 0 < w x) (hfw : ∀ x, |f x| ≤ w x)
    (E : X → ℝ → Prop) (hE1 : ∀ x, E x (f x)) (hE2 : ∀ x τ, E x τ → f x ≤ τ)
    (S : Set Θ) (T : Θ → ℝ) (R : X → Θ → ℝ) (hR0 : ∀ x θ, 0 ≤ R x θ)
    (hS : ∀ x, ∀ θ ∈ S, R x θ = 0 → E x (T θ * w x))
    (hS' : ∀ x, ∀ t ∈ Set.Icc (-1 : ℝ) 1, E x (t * w x) → ∃ θ ∈ S, T θ = t ∧ R x θ = 0)
    (x : X) :
    IsLeast ((fun θ => T θ * w x) '' argminSet R S x) (f x) := by
  have hwx := hw x
  obtain ⟨h1, h2⟩ := abs_le.mp (hfw x)
  set t₀ := f x / w x with ht₀
  have ht₀w : t₀ * w x = f x := div_mul_cancel₀ (f x) hwx.ne'
  have ht₀I : t₀ ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · rw [ht₀, le_div_iff₀ hwx]; linarith
    · rw [ht₀, div_le_iff₀ hwx]; linarith
  have hEt₀ : E x (t₀ * w x) := by rw [ht₀w]; exact hE1 x
  obtain ⟨θ₀, hθ₀S, hθ₀T, hθ₀R⟩ := hS' x t₀ ht₀I hEt₀
  have hargmin : argminSet R S x = {θ | θ ∈ S ∧ R x θ = 0} :=
    argminSet_eq_zeroSet (fun θ _ => hR0 x θ) ⟨θ₀, hθ₀S, hθ₀R⟩
  refine ⟨⟨θ₀, ?_, ?_⟩, ?_⟩
  · rw [hargmin]; exact ⟨hθ₀S, hθ₀R⟩
  · simp only [hθ₀T, ht₀w]
  · rintro _ ⟨θ, hθ, rfl⟩
    rw [hargmin] at hθ
    exact hE2 _ _ (hS x θ hθ.1 hθ.2)

/-- Generic core lemma, value form. -/
theorem t215_core_gen_value {X Θ : Type*} (f w : X → ℝ)
    (hw : ∀ x, 0 < w x) (hfw : ∀ x, |f x| ≤ w x)
    (E : X → ℝ → Prop) (hE1 : ∀ x, E x (f x)) (hE2 : ∀ x τ, E x τ → f x ≤ τ)
    (S : Set Θ) (T : Θ → ℝ) (R : X → Θ → ℝ) (hR0 : ∀ x θ, 0 ≤ R x θ)
    (hS : ∀ x, ∀ θ ∈ S, R x θ = 0 → E x (T θ * w x))
    (hS' : ∀ x, ∀ t ∈ Set.Icc (-1 : ℝ) 1, E x (t * w x) → ∃ θ ∈ S, T θ = t ∧ R x θ = 0)
    (x : X) :
    valueFun (fun x θ => T θ * w x) R S x = ((f x : ℝ) : EReal) :=
  valueFun_eq_of_isLeast (t215_core_gen f w hw hfw E hE1 hE2 S T R hR0 hS hS' x)

section core
variable {n : ℕ} {ζ : Type} (f w : (Fin n → ℝ) → ℝ)
    (hw : ∀ x, 0 < w x) (hfw : ∀ x, |f x| ≤ w x)
    (E : (Fin n → ℝ) → ℝ → Prop)
    (hE1 : ∀ x, E x (f x)) (hE2 : ∀ x τ, E x τ → f x ≤ τ)
    (Z : Set (ζ → ℝ)) (R : (Fin n → ℝ) → ℝ → (ζ → ℝ) → ℝ) (hR0 : ∀ x t z, 0 ≤ R x t z)
    (hRE : ∀ x t, E x (t * w x) ↔ ∃ z ∈ Z, R x t z = 0)
include hw hfw hE1 hE2 hR0 hRE

/-- `t215.core`, attained form: on the argmin set, the upper objective attains its infimum
`f x`. -/
theorem t215_core_isLeast (x : Fin n → ℝ) :
    IsLeast ((fun y : ℝ × (ζ → ℝ) => y.1 * w x) ''
      argminSet (fun x y => R x y.1 y.2) (Set.Icc (-1) 1 ×ˢ Z) x) (f x) :=
  t215_core_gen f w hw hfw E hE1 hE2 (Set.Icc (-1) 1 ×ˢ Z) Prod.fst
    (fun x y => R x y.1 y.2) (fun x y => hR0 x y.1 y.2)
    (fun x θ hθ h0 => (hRE x θ.1).mpr ⟨θ.2, hθ.2, h0⟩)
    (fun x t ht hE => by
      obtain ⟨z, hz, h0⟩ := (hRE x t).mp hE
      exact ⟨(t, z), ⟨ht, hz⟩, rfl, h0⟩) x

/-- `t215.core` (blueprint §4.F.2, L6). -/
theorem t215_core :
    ∀ x, valueFun (fun x (y : ℝ × (ζ → ℝ)) => y.1 * w x) (fun x y => R x y.1 y.2)
           (Set.Icc (-1) 1 ×ˢ Z) x = ((f x : ℝ) : EReal) := fun x =>
  valueFun_eq_of_isLeast (t215_core_isLeast f w hw hfw E hE1 hE2 Z R hR0 hRE x)

/-- The lower-level set on the sum index type `Unit ⊕ ζ`: `y (inl ()) ∈ [-1,1]`,
`y ∘ inr ∈ Z`. -/
def sumBox (Z : Set (ζ → ℝ)) : Set (Unit ⊕ ζ → ℝ) :=
  {y | y (Sum.inl ()) ∈ Set.Icc (-1 : ℝ) 1 ∧ y ∘ Sum.inr ∈ Z}

/-- `t215.core` transported to the lower index type `Unit ⊕ ζ` (`t = y (inl ())`,
`z = y ∘ inr`). -/
theorem t215_core_sum :
    ∀ x, valueFun (fun x (y : Unit ⊕ ζ → ℝ) => y (Sum.inl ()) * w x)
           (fun x y => R x (y (Sum.inl ())) (y ∘ Sum.inr)) (sumBox Z) x
         = ((f x : ℝ) : EReal) :=
  t215_core_gen_value f w hw hfw E hE1 hE2 (sumBox Z) (fun y => y (Sum.inl ()))
    (fun x y => R x (y (Sum.inl ())) (y ∘ Sum.inr)) (fun x y => hR0 _ _ _)
    (fun x θ hθ h0 => (hRE x _).mpr ⟨_, hθ.2, h0⟩)
    (fun x t ht hE => by
      obtain ⟨z, hz, h0⟩ := (hRE x t).mp hE
      refine ⟨Sum.elim (fun _ => t) z, ⟨ht, ?_⟩, rfl, ?_⟩
      · rw [Sum.elim_comp_inr]; exact hz
      · simp only [Sum.elim_inl, Sum.elim_comp_inr]; exact h0)

end core

/-- Lower box bounds for Theorem 2.15: `-1` on the `t`-coordinate, `0` on gadget coordinates. -/
def t215Lo {ζ : Type*} : Unit ⊕ ζ → ℝ := Sum.elim (fun _ => -1) (fun _ => 0)

/-- Upper box bounds for Theorem 2.15: `1` on the `t`-coordinate, `1/2` on gadget coordinates. -/
noncomputable def t215Hi {ζ : Type*} : Unit ⊕ ζ → ℝ := Sum.elim (fun _ => 1) (fun _ => 1 / 2)

theorem t215Lo_le_t215Hi {ζ : Type*} : ∀ k : Unit ⊕ ζ, t215Lo k ≤ t215Hi k := by
  rintro (_ | _) <;> simp only [t215Lo, t215Hi, Sum.elim_inl, Sum.elim_inr] <;> norm_num

/-- With `Z = gadgetBox α β`, the sum-type lower set is a bounded box. -/
theorem sumBox_gadgetBox {α β : Type} :
    sumBox (gadgetBox α β) = boundedBox t215Lo t215Hi := by
  ext y
  simp only [sumBox, Set.mem_ofPred_eq, mem_gadgetBox, mem_boundedBox, Function.comp_apply,
    Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩ (u | ij)
    · cases u; exact h1
    · exact h2 ij
  · intro h
    exact ⟨h (Sum.inl ()), fun ij => h (Sum.inr ij)⟩

/-! ### t215.epi_closed -/

/-- `t215.epi_closed`: the epigraph of a lower semicontinuous `f`, as a subset of
`Fin n ⊕ Unit → ℝ`, is closed. -/
theorem isClosed_epigraph_sum {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : LowerSemicontinuous f) :
    IsClosed {z : Fin n ⊕ Unit → ℝ | f (z ∘ Sum.inl) ≤ z (Sum.inr ())} := by
  have hc : Continuous fun z : Fin n ⊕ Unit → ℝ => (z ∘ Sum.inl, z (Sum.inr ())) := by
    fun_prop
  exact hf.isClosed_epigraph.preimage hc

/-! ### Step 5: rescaling `τ = t * w x` -/

/-- The rescaled polynomial function `p̃ (x, t) = p (x, t * w x)`, `w x = eval x wq`. -/
noncomputable def rescaledPoly {n : ℕ} (wq : MvPolynomial (Fin n) ℝ)
    (q : MvPolynomial (Fin n ⊕ Unit) ℝ) (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  MvPolynomial.eval (Sum.elim x (fun _ => t * MvPolynomial.eval x wq)) q

theorem isPolyFun_rescaledPoly {n : ℕ} (wq : MvPolynomial (Fin n) ℝ)
    (q : MvPolynomial (Fin n ⊕ Unit) ℝ) :
    IsPolyFun fun x (t : Unit → ℝ) => rescaledPoly wq q x (t ()) := by
  have h := (isPolyFun_polyFun q).comp (n' := n) (ι' := Unit)
    (τ := fun i x' _ => x' i) (σ := fun _ x' y' => y' () * MvPolynomial.eval x' wq)
    (fun i => isPolyFun_upper i)
    (fun _ => (isPolyFun_lower ()).mul (IsPolyFun.of_upper_only wq))
  exact h.of_eq fun x t => by simp only [rescaledPoly, polyFun_apply]

theorem exists_rescaledPoly_iff {n : ℕ} {α β : Type*} (wq : MvPolynomial (Fin n) ℝ)
    (p : α → β → MvPolynomial (Fin n ⊕ Unit) ℝ) (x : Fin n → ℝ) (t : ℝ) :
    (∃ i, ∀ j, 0 ≤ MvPolynomial.eval
        (Sum.elim x (fun _ => t * MvPolynomial.eval x wq)) (p i j)) ↔
      ∃ i, ∀ j, 0 ≤ rescaledPoly wq (p i j) x t :=
  Iff.rfl

/-! ### Steps 6–7: packaging -/

/-- Theorem 2.15 (⊇) modulo producing the weight `w` (A3) and the presentation `p` (A1 + A2):
if `|f| ≤ w`, `w > 0` polynomial, and `E = ⋃ᵢ ⋂ⱼ {p i j ≥ 0}` satisfies
`graph f ⊆ E ⊆ epi f`, then `f` is the value function of a polynomial bilevel problem over a
bounded box. -/
theorem thm215_of_presentation {n : ℕ} (f : (Fin n → ℝ) → ℝ) (wq : MvPolynomial (Fin n) ℝ)
    (hw : ∀ x, 0 < MvPolynomial.eval x wq) (hfw : ∀ x, |f x| ≤ MvPolynomial.eval x wq)
    {α β : Type} [Fintype α] [Fintype β] (p : α → β → MvPolynomial (Fin n ⊕ Unit) ℝ)
    (hE1 : ∀ x, ∃ i, ∀ j, 0 ≤ MvPolynomial.eval (Sum.elim x (fun _ => f x)) (p i j))
    (hE2 : ∀ x τ, (∃ i, ∀ j, 0 ≤ MvPolynomial.eval (Sum.elim x (fun _ => τ)) (p i j)) →
      f x ≤ τ) :
    ∃ (ι : Type) (_ : Fintype ι) (P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ) (a b : ι → ℝ),
      IsPolyFun P ∧ IsPolyFun Q ∧ (∀ k, a k ≤ b k) ∧
      ∀ x, valueFun P Q (boundedBox a b) x = ((f x : ℝ) : EReal) := by
  set w : (Fin n → ℝ) → ℝ := fun x => MvPolynomial.eval x wq
  let p' : α → β → (Fin n → ℝ) → ℝ → ℝ := fun i j x t => rescaledPoly wq (p i j) x t
  let R : (Fin n → ℝ) → ℝ → (α × β → ℝ) → ℝ := fun x t z =>
    unionGadget (fun i j (u : (Fin n → ℝ) × ℝ) => p' i j u.1 u.2) (x, t) z
  have hcore := t215_core_sum f w hw hfw
    (fun x τ => ∃ i, ∀ j, 0 ≤ MvPolynomial.eval (Sum.elim x (fun _ => τ)) (p i j))
    hE1 hE2 (gadgetBox α β) R (fun x t z => unionGadget_nonneg _ _ _)
    (fun x t => exists_unionGadget_eq_zero_iff.symm)
  refine ⟨Unit ⊕ (α × β), inferInstance, fun x y => y (Sum.inl ()) * w x,
    fun x y => R x (y (Sum.inl ())) (y ∘ Sum.inr), t215Lo, t215Hi, ?_, ?_,
    t215Lo_le_t215Hi, ?_⟩
  · exact (isPolyFun_lower _).mul (IsPolyFun.of_upper_only wq)
  · exact isPolyFun_unionGadget_sum (p := p') fun i j => isPolyFun_rescaledPoly wq (p i j)
  · intro x
    rw [← sumBox_gadgetBox]
    exact hcore x

end Bilevel
