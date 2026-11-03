# W3-b AUDIT (Assumptions/Classes.lean, Semialgebraic/Projection.lean)

## 1. Verdict: ACCEPT
- Three classes are character-for-character the blueprint §2.5 statements (binders, image, union/intersection shape, growth shape).
- No instance of any class anywhere in the repo, no axiom/sorry; all 27 theorems (+ scratch derivation) have axioms = {propext, Classical.choice, Quot.sound}.
- Quantifier calculus, epigraph/hypograph, closure/interior all present with downstream-ready shapes; closure derived from A1.

## 2. Build / hygiene / axioms
- `lake build HardnessBilevel.Assumptions.Classes HardnessBilevel.Semialgebraic.Projection` -> Build completed successfully (only unrelated `module` warnings).
- grep sorry|axiom|native_decide|unsafe|admit|maxHeartbeats|open Classical over Assumptions/ and Projection.lean: only prose mentions of "axioms" in docstrings; no code hits.
- `grep -rn "instance" HardnessBilevel/`: only an unrelated `noncomputable instance : DecidablePred (IsBinary ..)` in Hardness/Analysis.lean and prose; NO instance of HasSemialgebraicProjections/HasFinitenessTheorem/HasGrowthBound. Assumptions/ contains only Classes.lean (no Unsafe.lean).
- Scratch /scratchpad/lean/AuditW3b.lean: `#print axioms` on all 27 theorems -> all [propext, Classical.choice, Quot.sound] (27/27).
- Scratch derivation under `variable [HasSemialgebraicProjections]` (not an instance declaration): `{x : Fin 1 → ℝ | ∃ y : ℝ, x 0 = y ^ 2}` semialgebraic via `isSemialgebraic_eval_eq` + `IsSemialgebraic.exists_real`; `#print axioms sq_sa` = [propext, Classical.choice, Quot.sound]. (Class is a hypothesis binder, not an axiom.)

## 3. Faithfulness
| blueprint | Lean | verdict | note |
|---|---|---|---|
| A1 (§2.5/4.B.3) | HasSemialgebraicProjections.image_comp_inl | IDENTICAL | `{α β : Type} [Fintype α] [Finite β]`, image `(fun z : α ⊕ β → ℝ => z ∘ Sum.inl) '' S` |
| A2 (§2.5/4.B.4) | HasFinitenessTheorem.exists_eq_iUnion_iInter_nonneg | IDENTICAL | `{ι : Type} [Fintype ι]`, ∃ I J P : Fin I → Fin J → MvPolynomial ι ℝ, `s = ⋃ i, ⋂ j, {x | 0 ≤ MvPolynomial.eval x (P i j)}` (blueprint 4.B.4 writes `eval`, same) |
| A3 (§2.5) | HasGrowthBound.growth | IDENTICAL | explicit graph set (=§2.5); bounded-on-bounded-sets hyp; conclusion `B + (1 + ∑ i, x i ^ 2) ^ M`. §4.B.5 uses `IsSemialgebraicMap f` = defeq (graphSet unfolds); `growth'` provides that form |
| sa.exists_sumElim | IsSemialgebraic.exists_sumElim | IDENTICAL | `{v | ∃ u, Sum.elim v u ∈ S}`, [Finite β], [Fintype α] |
| sa.forall_sumElim | IsSemialgebraic.forall_sumElim | IDENTICAL | |
| quantifier calculus | exists/forall_{inr,mem_sumElim,exists_sumElim(')…,_assoc,_last,real,pos} | OK | bounded `exists_pos` = ∃ ε, 0<ε ∧ …; `forall_pos` = ∀ ε, 0<ε → … ; nested variants both bracketings; all `[Fintype α]` Type-valued |
| t215.epi_sa | isSemialgebraic_epigraph | STRENGTHENED | `IsSemialgebraicMap f → IsSemialgebraic {z : ι ⊕ Unit → ℝ | f (z ∘ Sum.inl) ≤ z (Sum.inr ())}` exactly the needed shape; general ι (Fintype) instead of Fin n; also hypograph, strict versions |
| sa.closure/interior | IsSemialgebraic.closure/.interior | OK | closure proved via exists_mem_sumElim + forall_pos + Metric.mem_closure_iff, i.e. derived from A1 (not assumed); interior = (closure sᶜ)ᶜ |

Every Projection.lean theorem takes `[HasSemialgebraicProjections]` (section `variable`); the `#check` of epigraph shows the binder.

`set_option linter.concreteInstances false`: only silences a Mathlib style linter ("assumption does not contain free variables, add a global instance"). Affects no elaboration or soundness; since it is scoped to the file (not `scoped`/global to importers) downstream files will see the warning and may repeat it. Harmless. (In Classes.lean it is redundant—no binder there—but harmless.)

## 4. Required fixes
None.

## 5. Optional improvements
- Remove the unneeded `set_option linter.concreteInstances false` from Classes.lean (and its misleading comment).
- `open MeasureTheory Function MvPolynomial` in Projection.lean seems more than necessary (MeasureTheory unused?); cosmetic.
- Downstream files will emit the concreteInstances warning; consider a project-level lakefile option `linter.concreteInstances=false` (orchestrator decision; do not edit lakefile in a unit).
