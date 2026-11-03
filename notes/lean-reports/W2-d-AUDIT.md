# W2-d AUDIT: HardnessBilevel/Semialgebraic/Basic.lean

## 1. Verdict: ACCEPT
* Build clean, no sorry/axiom/etc., all 52 public declarations depend only on {propext, Classical.choice, Quot.sound}.
* All definitions and theorems match blueprint §2.4 / §4.B.1 exactly (IDENTICAL, or STRENGTHENED only via `[Finite κ]`, universe-polymorphic `ι : Type*`).
* Scratch usability test (derive SA of `{x0^2+x1^2<1 ∨ x0=3}` and apply `exists_uniform_basic`) compiles.

## 2. Build / hygiene / axioms
* `lake build HardnessBilevel.Semialgebraic.Basic` -> "Build completed successfully (18241 jobs)" (only the generic "consider adding `module`" lint warning).
* grep for sorry|axiom|native_decide|unsafe|admit|maxHeartbeats|open Classical|decide|instance: only hit is the word "decided" in the header comment. `classical` used only inside a proof. No `Set.mem_setOf_eq`.
* Scratch file <SCRATCH>/lean/W2d_audit.lean: `#print axioms` on all 52 theorems/defs: 52/52 report exactly [propext, Classical.choice, Quot.sound]. (`lake env lean` produced no errors.)

## 3. Faithfulness
| blueprint id | Lean name | verdict | note |
|---|---|---|---|
| §2.4 def | `IsSemialgebraic` | IDENTICAL | `s ∈ generateSetAlgebra (range (fun p => {x | eval x p = 0}) ∪ range (fun p => {x | 0 < eval x p}))`, `MvPolynomial ι ℝ`, `MvPolynomial.eval`; `ι : Type*` |
| IsBasicSA | `IsBasicSA` | IDENTICAL | `∃ P k Q : Fin k → _, s = {x | eval x P = 0 ∧ ∀ j, 0 < eval x (Q j)}`: one equation, k strict ineqs |
| graph | `graphSet`, `IsSemialgebraicMap` | IDENTICAL | `{z : ι ⊕ Unit → ℝ | f (z ∘ Sum.inl) = z (Sum.inr ())}`; map := IsSemialgebraic graph |
| sa.gen | `isSemialgebraic_eval_eq_zero/_pos` | IDENTICAL | |
| sa.bool | empty/univ/compl/union/inter/sdiff, biUnion/biInter (Finset), iUnion/iInter, setOf_* | IDENTICAL / STRENGTHENED | iUnion/iInter over `[Finite κ]` (weaker than Fintype) |
| sa.sign_sets | `_eval_ne_zero/neg/nonneg/nonpos/lt/le/eq/ne`, `isSemialgebraic_sign_eval_eq` | IDENTICAL | all listed sets covered, sign by cases on SignType |
| sa.sign_normal_form | `isSemialgebraic_iff_sign_normal_form` | IDENTICAL | `IsSemialgebraic s ↔ ∃ m (p : Fin m → MvPolynomial ι ℝ) (Φ : (Fin m → SignType) → Prop), s = {x | Φ fun i => sign (eval x (p i))}`; Φ is unrestricted Prop, as specified |
| sa.cell_basic | `signCell`, `cellP`, `cellQ`, `signCell_eq_basic`, `disjoint_signCell`, `iUnion_signCell`, `isBasicSA_signCell` | IDENTICAL | cellP = ∑ i, if σ i = 0 then p i ^ 2 else 0; cellQ i = if σ i = 1 then p i else if σ i = -1 then -p i else 1 (exactly the blueprint's data, uniform, no filter/equivFin); disjointness for σ ≠ τ; ⋃σ cell = univ. Proofs checked: correct (sum-of-squares via `Finset.sum_eq_zero_iff_of_nonneg`, case aux lemma). |
| sa.finite_union_basic | `isSemialgebraic_iff_finite_union_basic` | IDENTICAL | `∃ m S, (∀ i, IsBasicSA (S i)) ∧ s = ⋃ i, S i`, Fin m index |
| sa.disjoint_basic (Prop C.1) | `isSemialgebraic_iff_disjoint_union_basic` | IDENTICAL | adds `Pairwise (Disjoint on S)` |
| sa.finite_union_basic_uniform | `IsSemialgebraic.exists_uniform_basic` | IDENTICAL | exact shape `∃ (m k : ℕ) (P : Fin m → MvPolynomial ι ℝ) (Q : Fin m → Fin k → MvPolynomial ι ℝ), s = ⋃ i, {x | eval x (P i) = 0 ∧ ∀ j, 0 < eval x (Q i j)}` (verified in source and by usage test). Padding not needed (m = #sign vectors satisfying Φ, k = number of polynomials; m=0 gives empty union) so the blueprint's E-13 padding worry is moot. |
| uniform + disjoint | `IsSemialgebraic.exists_disjoint_uniform_basic`, `isSemialgebraic_iff_disjoint_uniform_union_basic` | IDENTICAL (strengthened conjunction) | `Pairwise (Disjoint on fun i => {…})`; needs `open Function` for `on`, present in-file |
| E-2 | | addressed | membership decided by sign vector; cells basic via sum of squares / -h>0 |

Usage test (scratch, compiles): `{x : Fin 2 → ℝ | x 0 ^ 2 + x 1 ^ 2 < 1 ∨ x 0 = 3}` derived `IsSemialgebraic` from `isSemialgebraic_eval_lt`, `isSemialgebraic_eval_eq`, `isSemialgebraic_setOf_or` (+ `simpa`), then `h.exists_uniform_basic` gives the required ∃ (m k P Q) statement.

## 4. Required fixes
None.

## 5. Optional improvements
1. Header mentions `setOf_sign_cell_eq`, which does not exist; the actual lemma is `setOf_sign_eq_iUnion_signCell`. Fix the comment.
2. Several auxiliary declarations lack docstrings (`isSemialgebraic_compl_iff`, `IsSemialgebraic.of_eq`, setOf_and/or/not/forall/exists).
3. Consider `module` keyword warning is shared by all files; ignore.
4. E: `isSemialgebraic_iUnion/iInter/setOf_forall` use `[Finite κ]` (fine for `Fin k`/`Fin m`); names of exports match blueprint ids (sa.gen/bool/sign_sets/…); the preimage/reindex/cylinder/box items belong to Poly.lean (not this unit), correctly omitted per the writer.
