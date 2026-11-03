# W1-cd AUDIT (Framework/Box.lean, Framework/Semicont.lean)

## 1. Verdict: ACCEPT
- Both modules build; no sorry/axiom/etc.; all 39 public declarations depend only on propext, Classical.choice, Quot.sound.
- Definitions boxSet, boundedBox, IsBoundedBox, IsUnboundedBox, IsBox are verbatim the blueprint's; all lemma statements match or strengthen.
- Usability confirmed by instantiation in a scratch file; no required fixes.

## 2. Build / hygiene / axioms
- `lake build HardnessBilevel.Framework.Box HardnessBilevel.Framework.Semicont` -> Build completed successfully (only "consider adding `module`" warning).
- grep for sorry|axiom|native_decide|unsafe|admit|instance Has*|maxHeartbeats|open Classical|stdSimplex: no hits.
- `#print axioms` on all 39 theorems/defs (scratch: <SCRATCH>/lean/W1cdAudit.lean, `lake env lean`): 39 "depends on axioms: [propext, Classical.choice, Quot.sound]", no sorryAx, no errors.
- Usability examples in the same file compile: `IsBoundedBox.isCompact` for `Fin 3 → ℝ` (via h.isCompact), `isClosed_realEpigraph hf` for X Type, `isUnboundedBox_sum_univ_Ici` at `α β : Type`, `lowerSemicontinuous_coe_iff f`, `upperSemicontinuous_iff_lowerSemicontinuous_neg h`.

## 3. Faithfulness
| blueprint id | Lean | verdict | note |
|---|---|---|---|
| boxSet | boxSet | IDENTICAL | EReal endpoints, `lo i ≤ ↑(y i) ∧ ↑(y i) ≤ hi i` |
| boundedBox, IsBoundedBox | same | IDENTICAL | Set.pi univ Icc; real lo ≤ hi |
| IsUnboundedBox | same | IDENTICAL | all i: lo i ≠ ⊤ ∧ hi i ≠ ⊥ ∧ lo i ≤ hi i; ∃ i, lo i = ⊥ ∨ hi i = ⊤; S = boxSet lo hi |
| IsBox | same | IDENTICAL | |
| boundedBox_eq_boxSet, IsBoundedBox.isBox/nonempty/convex | same | IDENTICAL | |
| IsBoundedBox.isCompact | same | STRENGTHENED | `[Finite ι]` instead of Fintype |
| IsBox.isClosed, IsBox.convex | same | IDENTICAL | |
| boxSet_bot_top | same | IDENTICAL | |
| IsUnboundedBox witnesses | isUnboundedBox_univ [Nonempty ι]; isUnboundedBox_sum_univ_Ici [Nonempty α] | IDENTICAL | set is exactly `Set.pi univ (Sum.elim (fun _ => univ) (fun _ => Ici 0))` (verified in #check output and by example) |
| (extra) IsUnboundedBox.nonempty | same | really proved | via exists_real_mem_Icc / boxSet_nonempty, no sorry |
| fw.lsc_real_bridge | lowerSemicontinuous_coe_iff | IDENTICAL | exact form requested; usc twin extra |
| fw.usc_neg / lsc_neg | upperSemicontinuous_iff_lowerSemicontinuous_neg, lowerSemicontinuous_iff_upperSemicontinuous_neg | IDENTICAL | `h : X → EReal`, `fun x => -h x` |
| real neg helpers | lowerSemicontinuous_neg_iff_real etc. | extra | Mathlib re-exports |
| t11.isClosed_realEpigraph | isClosed_realEpigraph | IDENTICAL | `{p : X × ℝ | f p.1 ≤ ↑p.2}`, only lsc hypothesis; hypograph twin extra |

## 4. Required fixes
None.

## 5. Optional
- `isUnboundedBox_sum_univ_Ici` could drop `[Nonempty α]` only if β nonempty case is wanted (then not unbounded in the ⊥ sense; Ici 0 has hi=⊤ so β nonempty also suffices) — a `Nonempty β` variant could help Thm 2.18 if α may be empty.
- Files lack `module` header (project-wide warning only).
