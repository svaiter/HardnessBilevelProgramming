/-
Copyright: HardnessBilevel project.

# The quarantined assumptions A1–A3

Implements blueprint §2.5 and the class statements of §4.B.3 (A1, Tarski–Seidenberg), §4.B.4 (A2, finiteness
theorem, paper Prop 2.4) and §4.B.5 (A3, growth bound, CORRECTED paper Prop 2.5), with exactly the statements
of blueprint §2.5.

## No-unproved-instance policy (binding, blueprint §2.5 / PLAN §1 rule 4)

* The core library `HardnessBilevel` declares **no `instance`** of `HasSemialgebraicProjections`,
  `HasFinitenessTheorem` or `HasGrowthBound`, and no unproved (`sorry`ed, axiomatized) instance may exist
  anywhere: typeclass search would silently use it.
* Every theorem of the core library that needs an assumption takes it as an explicit instance-implicit binder
  (`[HasSemialgebraicProjections]`, `[HasFinitenessTheorem]`, `[HasGrowthBound]`), so the assumption is
  visible in its signature and `#print axioms` stays ⊆ {propext, Classical.choice, Quot.sound}.
* A theorem of the core library that secretly used an assumption without the binder fails to elaborate, since
  no instance is in scope there. (Where other files of the core library say "no instance exists", read: in the
  core library.)
* **Proved** instances of the three classes are declared in the separate library
  `HardnessBilevelUnconditional` (`HardnessBilevelUnconditional/Instances.lean`), from the `Semialgebraic`
  companion library built on TauCeti; the assumption-free corollaries of the main theorems are in
  `HardnessBilevelUnconditional/Main.lean`. The core library does not import them.

Note on A3: the hypothesis is stated with the explicit graph set
`{z : Fin n ⊕ Unit → ℝ | f (z ∘ Sum.inl) = z (Sum.inr ())}`, which is `graphSet f` by definition
(so it is the same as `IsSemialgebraicMap f`, see `HasGrowthBound.growth'`).
-/
import HardnessBilevel.Semialgebraic.Basic

namespace Bilevel

-- No instance of these classes exists (by policy), so they are deliberately local binders.
set_option linter.concreteInstances false

/-- A1 (Tarski–Seidenberg, blueprint §2.5 / §4.B.3). Projection form: forgetting finitely many coordinates
preserves semialgebraicity. -/
class HasSemialgebraicProjections : Prop where
  image_comp_inl {α β : Type} [Fintype α] [Finite β] {S : Set (α ⊕ β → ℝ)} :
    IsSemialgebraic S → IsSemialgebraic ((fun z : α ⊕ β → ℝ => z ∘ Sum.inl) '' S)

/-- A2 (finiteness theorem; paper Prop 2.4; BCR Thm 2.7.2; blueprint §2.5 / §4.B.4). Over any finite index
type. -/
class HasFinitenessTheorem : Prop where
  exists_eq_iUnion_iInter_nonneg {ι : Type} [Fintype ι] {s : Set (ι → ℝ)} :
    IsSemialgebraic s → IsClosed s →
    ∃ (I J : ℕ) (P : Fin I → Fin J → MvPolynomial ι ℝ),
      s = ⋃ i, ⋂ j, {x | 0 ≤ MvPolynomial.eval x (P i j)}

/-- A3 (growth bound, CORRECTED paper Prop 2.5; blueprint §2.5 / §4.B.5). The paper's version is false for
`n ≥ 2`; this version assumes local boundedness. Shape: `B + (1 + ∑ x_i²)^M`. -/
class HasGrowthBound : Prop where
  growth {n : ℕ} {f : (Fin n → ℝ) → ℝ} :
    IsSemialgebraic {z : Fin n ⊕ Unit → ℝ | f (z ∘ Sum.inl) = z (Sum.inr ())} →
    (∀ r : ℝ, ∃ B : ℝ, ∀ x, ∑ i, x i ^ 2 ≤ r → |f x| ≤ B) →
    ∃ (B : ℝ) (M : ℕ), ∀ x, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M

/-- A3 restated with `IsSemialgebraicMap` (definitionally the same hypothesis). -/
theorem HasGrowthBound.growth' [HasGrowthBound] {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsSemialgebraicMap f) (hb : ∀ r : ℝ, ∃ B : ℝ, ∀ x, ∑ i, x i ^ 2 ≤ r → |f x| ≤ B) :
    ∃ (B : ℝ) (M : ℕ), ∀ x, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M :=
  HasGrowthBound.growth hf hb

end Bilevel
