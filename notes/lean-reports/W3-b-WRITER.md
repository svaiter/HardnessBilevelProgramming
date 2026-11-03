# W3-b WRITER report

## Files delivered
* /home/user/HardnessBilevelProgramming/HardnessBilevel/Assumptions/Classes.lean (imports Semialgebraic.Basic)
* /home/user/HardnessBilevelProgramming/HardnessBilevel/Semialgebraic/Projection.lean (imports Assumptions.Classes, Semialgebraic.Poly)
* API summary: <SCRATCH>/reports/W3-b-API.md

## Blueprint ids implemented
* A1 `HasSemialgebraicProjections`, A2 `HasFinitenessTheorem`, A3 `HasGrowthBound`: verbatim blueprint §2.5 statements
  (A3 uses the explicit graph-set hypothesis of §2.5; §4.B.5 writes `IsSemialgebraicMap f`, which is definitionally the
  same — `HasGrowthBound.growth'` restates A3 with `IsSemialgebraicMap f`). Module docstring states the no-instance policy.
* `sa.exists_sumElim` → `IsSemialgebraic.exists_sumElim`; `sa.forall_sumElim` → `IsSemialgebraic.forall_sumElim`.
* `sa.quantifier_calculus` (helpers): `IsSemialgebraic.image_comp_inl` (A1 restated, Fin.tail-free), `exists_inr`, `forall_inr`,
  `exists_mem_sumElim` / `forall_mem_sumElim` (bounded by semialgebraic `T`), nested blocks `exists_exists_sumElim`,
  `forall_forall_sumElim` (α ⊕ (β ⊕ γ)), `exists_exists_sumElim'`, `forall_forall_sumElim'` ((α ⊕ β) ⊕ γ),
  last-block elimination `exists_sumElim_assoc` / `forall_sumElim_assoc` (α ⊕ (β ⊕ γ) → result on α ⊕ β, via
  `preimage_equiv (Equiv.sumAssoc α β γ).symm`), `exists_sumElim_last` / `forall_sumElim_last` ((α ⊕ β) ⊕ γ);
  one real variable: `exists_real`, `forall_real`, `exists_pos` (∃ ε, 0 < ε ∧ …), `forall_pos` (∀ ε, 0 < ε → …).
* `t215.epi_sa` → `isSemialgebraic_epigraph`, plus `isSemialgebraic_hypograph`, `isSemialgebraic_strictEpigraph`,
  `isSemialgebraic_strictHypograph`, and the general substitution lemma `isSemialgebraic_setOf_sumElim_value`
  (`{z | Sum.elim z (fun _ => f (z ∘ inl)) ∈ T}` semialgebraic for semialgebraic `T`, one projection).
* `sa.closure` / `sa.interior` (optional) → `IsSemialgebraic.closure`, `IsSemialgebraic.interior`.

## Deviations
* Strengthening: epigraph/hypograph lemmas are over any `ι : Type` with `[Fintype ι]` instead of `Fin n`.
* All derived lemmas are for index types in `Type` (universe 0), as forced by A1's statement.
* `set_option linter.concreteInstances false` in both files: this Mathlib linter warns "add a global instance" on every
  `[HasSemialgebraicProjections]` binder (the class has no parameters). Downstream consumer files will see the same
  warning and may want the same option. Not an error.
* No instance of any class is declared (grep-checked).

## Mathlib names that differed
None relevant (`Metric.mem_closure_iff`, `dist_pi_lt_iff`, `closure_compl`, `abs_sub_lt_iff`, `Sum.elim_comp_inl_inr` as expected).

## Not done
Nothing omitted.

## Build
`lake build HardnessBilevel.Semialgebraic.Projection` → "Build completed successfully" (also builds Assumptions.Classes);
no warnings in these two files. `#print axioms` of all 27 theorems (both files): [propext, Classical.choice, Quot.sound].
