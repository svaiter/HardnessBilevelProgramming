/-
Copyright: HardnessBilevel project.

# Framework: separability and reindexing of argmin sets (blueprint §4.A.2, §4.G.1)

Implements:
* F5 `fw.argmin_prod_add` as `argminSet_prod_add` (binary products, no nonemptiness);
* F7 `fw.comp_equiv` as `argminSet_comp_equiv`, `valueFun_comp_equiv`, `pvalueFun_comp_equiv`
  (for `e : Y' ≃ Y`);
* `fw.argmin_pi_sum` (§4.G.1) as `argminSet_pi_sum` (stated for an argmin set whose objective may
  depend on the upper variable; the literal blueprint set equation is `pi_sum_min_eq`);
* convenience `argminSet_sum_elim`: separability for `y : α ⊕ β → Z` split into `y ∘ Sum.inl`,
  `y ∘ Sum.inr`.

No assumption (A1–A3) is used.
-/
import HardnessBilevel.Framework.Basic

namespace Bilevel

variable {X : Type*}

/-- fw.argmin_prod_add (F5): argmin of a separable sum over a product set is the product of the
argmins. No nonemptiness is needed. -/
theorem argminSet_prod_add {Y₁ Y₂ : Type*} (A : X → Y₁ → ℝ) (B : X → Y₂ → ℝ) (S₁ : Set Y₁)
    (S₂ : Set Y₂) (x : X) :
    argminSet (fun x (y : Y₁ × Y₂) => A x y.1 + B x y.2) (S₁ ×ˢ S₂) x =
      argminSet A S₁ x ×ˢ argminSet B S₂ x := by
  ext ⟨y₁, y₂⟩
  simp only [argminSet, Set.mem_prod, Set.mem_ofPred_eq, Prod.forall]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, hmin⟩
    refine ⟨⟨h₁, fun y₁' hy₁' => ?_⟩, ⟨h₂, fun y₂' hy₂' => ?_⟩⟩
    · have := hmin y₁' y₂ ⟨hy₁', h₂⟩
      linarith
    · have := hmin y₁ y₂' ⟨h₁, hy₂'⟩
      linarith
  · rintro ⟨⟨h₁, hm₁⟩, ⟨h₂, hm₂⟩⟩
    exact ⟨⟨h₁, h₂⟩, fun a b ⟨ha, hb⟩ => add_le_add (hm₁ a ha) (hm₂ b hb)⟩

section CompEquiv

variable {Y Y' : Type*}

/-- fw.comp_equiv (F7), argmin part. -/
theorem argminSet_comp_equiv (Q : X → Y → ℝ) (S : Set Y) (e : Y' ≃ Y) (x : X) :
    argminSet (fun x y' => Q x (e y')) (e ⁻¹' S) x = e ⁻¹' argminSet Q S x := by
  ext y'
  simp only [argminSet, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hy, hmin⟩
    refine ⟨hy, fun y hy' => ?_⟩
    have := hmin (e.symm y) (by simpa using hy')
    simpa using this
  · rintro ⟨hy, hmin⟩
    exact ⟨hy, fun y'' hy'' => hmin (e y'') hy''⟩

/-- fw.comp_equiv (F7), optimistic value function. -/
theorem valueFun_comp_equiv (P Q : X → Y → ℝ) (S : Set Y) (e : Y' ≃ Y) :
    valueFun (fun x y' => P x (e y')) (fun x y' => Q x (e y')) (e ⁻¹' S) = valueFun P Q S := by
  funext x
  simp only [valueFun]
  rw [argminSet_comp_equiv, ← Equiv.image_symm_eq_preimage]
  exact Equiv.biInf_comp (g := fun y => ((P x y : ℝ) : EReal)) e (argminSet Q S x)

/-- fw.comp_equiv (F7), pessimistic value function. -/
theorem pvalueFun_comp_equiv (P Q : X → Y → ℝ) (S : Set Y) (e : Y' ≃ Y) :
    pvalueFun (fun x y' => P x (e y')) (fun x y' => Q x (e y')) (e ⁻¹' S) = pvalueFun P Q S := by
  funext x
  simp only [pvalueFun]
  rw [argminSet_comp_equiv, ← Equiv.image_symm_eq_preimage]
  exact Equiv.biSup_comp (g := fun y => ((P x y : ℝ) : EReal)) e (argminSet Q S x)

end CompEquiv

section Pi

variable {ι : Type*} [Fintype ι] {E : ι → Type*}

/-- fw.argmin_pi_sum (§4.G.1): argmin of a coordinatewise separable sum over a product set is the
product of the coordinatewise argmins. No nonemptiness is needed. -/
theorem argminSet_pi_sum (Y : ∀ i, Set (E i)) (g : X → ∀ i, E i → ℝ) (x : X) :
    argminSet (fun x (y : ∀ i, E i) => ∑ i, g x i (y i)) (Set.pi Set.univ Y) x =
      Set.pi Set.univ (fun i => argminSet (fun x v => g x i v) (Y i) x) := by
  classical
  ext y
  simp only [argminSet, Set.mem_univ_pi, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hy, hmin⟩ k
    refine ⟨hy k, fun v' hv' => ?_⟩
    set y' := Function.update y k v' with hy'def
    have hy' : ∀ i, y' i ∈ Y i := by
      intro i
      by_cases hik : i = k
      · subst hik
        simpa [y'] using hv'
      · simpa [y', Function.update_of_ne hik] using hy i
    have hle := hmin y' hy'
    have hf : (fun i => g x i (y' i)) =
        Function.update (fun i => g x i (y i)) k (g x k v') := by
      funext i
      by_cases hik : i = k
      · subst hik
        simp [y']
      · simp [y', Function.update_of_ne hik]
    have h1 : ∑ i, g x i (y' i) = g x k v' + ∑ i ∈ Finset.univ \ {k}, g x i (y i) := by
      rw [show (∑ i, g x i (y' i)) = ∑ i, (fun i => g x i (y' i)) i from rfl, hf,
        Finset.sum_update_of_mem (Finset.mem_univ k)]
    have h2 : ∑ i, g x i (y i) = g x k (y k) + ∑ i ∈ Finset.univ \ {k}, g x i (y i) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
    linarith
  · intro h
    refine ⟨fun i => (h i).1, fun y' hy' => ?_⟩
    exact Finset.sum_le_sum fun i _ => (h i).2 (y' i) (hy' i)

/-- fw.argmin_pi_sum (§4.G.1), the literal blueprint set equation. -/
theorem pi_sum_min_eq (Y : ∀ i, Set (E i)) (g : ∀ i, E i → ℝ) :
    {y ∈ Set.pi Set.univ Y | ∀ y' ∈ Set.pi Set.univ Y, ∑ i, g i (y i) ≤ ∑ i, g i (y' i)} =
      Set.pi Set.univ (fun i => {v ∈ Y i | ∀ v' ∈ Y i, g i v ≤ g i v'}) :=
  argminSet_pi_sum (X := Unit) Y (fun _ => g) ()

end Pi

/-- Separability for lower variables `y : α ⊕ β → Z`, split via `Sum.inl`/`Sum.inr`
(convenience form of `argminSet_prod_add` transported along `Equiv.sumArrowEquivProdArrow`). -/
theorem argminSet_sum_elim {α β Z : Type*} (A : X → (α → Z) → ℝ) (B : X → (β → Z) → ℝ)
    (S₁ : Set (α → Z)) (S₂ : Set (β → Z)) (x : X) :
    argminSet (fun x (y : α ⊕ β → Z) => A x (y ∘ Sum.inl) + B x (y ∘ Sum.inr))
        {y | y ∘ Sum.inl ∈ S₁ ∧ y ∘ Sum.inr ∈ S₂} x =
      {y | y ∘ Sum.inl ∈ argminSet A S₁ x ∧ y ∘ Sum.inr ∈ argminSet B S₂ x} := by
  have := argminSet_comp_equiv (fun x (p : (α → Z) × (β → Z)) => A x p.1 + B x p.2) (S₁ ×ˢ S₂)
    (Equiv.sumArrowEquivProdArrow α β Z) x
  rw [argminSet_prod_add] at this
  exact this

end Bilevel
