# W3-d AUDIT (Value.lean, Hull.lean)

## 1. Verdict: ACCEPT
- Both modules build; no sorry/axiom/native_decide/unsafe/maxHeartbeats/open Classical; no instance of A1-A3 anywhere in HardnessBilevel/.
- `valueFun_isExtSemialgebraic` has exactly the blueprint signature, works for ANY semialgebraic Y, uses only the attainment-free characterisations (top/bot/coe iff); no IsCompact/Nonempty hypotheses.
- All 35 theorems print only {propext, Classical.choice, Quot.sound}; the n=1 scratch application (P=y0, Q=(y0-x0)^2, Y=univ) type-checks with standard axioms.

## 2. Build / hygiene / axioms
- `lake build HardnessBilevel.Semialgebraic.Value` and `...Hull`: "Build completed successfully" (only module-system warnings on imported files).
- grep for sorry|axiom|native_decide|unsafe|admit|maxHeartbeats|open Classical in both files: no hits.
- grep of whole HardnessBilevel/ for `instance`/`attribute [instance]` of HasSemialgebraicProjections/HasFinitenessTheorem/HasGrowthBound: no hits.
- `lake env lean <SCRATCH>/lean/W3dAudit.lean` (#print axioms of all 35 public decls incl. helpers, plus `scratch1`): all [propext, Classical.choice, Quot.sound]. Only a linter warning (concreteInstances) in the scratch file, which the unit files disable locally via `set_option linter.concreteInstances false` (harmless).

## 3. Faithfulness
| blueprint id | Lean name | verdict | note |
|---|---|---|---|
| sa.value_semialgebraic | valueFun_isExtSemialgebraic | IDENTICAL | #check matches blueprint. Proof: Θ=argminGraph semialgebraic (cylinder of Y, polynomial ≤ in (x,y,y'), forall_sumElim); {⊤}={x|∀y,(x,y)∉Θ} via valueFun_eq_top_iff; {⊥}={x|∀δ∃y,(x,y)∈Θ∧P<δ} via valueFun_eq_bot_iff; graph = part A (∀y, Θ→t≤P) ∧ part B (∀ε>0 ∃y, Θ ∧ P<t+ε) via valueFun_eq_coe_iff. No attainment. |
| sa.value_semialgebraic (pess.) | pvalueFun_isExtSemialgebraic | IDENTICAL | via pvalueFun = -valueFun(-P) and IsExtSemialgebraic.neg; same signature. |
| sa.class_sub_SA | P_/C_ unbound/bounded/box/cc _subset_SA, Pp_/Cp_ twins | IDENTICAL | class defs (Framework/Classes) quantify ∃ ι Fintype; C_cc uses general semialgebraic Y (hS.2.2.2). |
| t212.eq_SA | thm212_eq_SA, thm212_eq_SA_pess | IDENTICAL | `P_unbound n = SA n` under [HasSemialgebraicProjections] only. |
| t218.Cunbound_sub_SA / main | C_unbound_subset_SA, thm218_main (+_pess) | IDENTICAL | `PPe n ⊆ C_unbound n ∧ C_unbound n ⊆ SA n`. |
| t215/t220/t221 ⊆ halves | thm215_subset, thm220_subset, thm221_subset (+_pess, USC) | IDENTICAL | `⊆ SA n ∩ LSC n ∩ CB n`, A1 only (LSC/CB parts from earlier unit). |
| sa.hull_semialgebraic | isSemialgebraic_convexHull_image | STRENGTHENED | arbitrary finite index types m, K instead of Fin m, Fin K; Fintype hypotheses only. Carathéodory argument checked: eq_pos_convex_span_of_mem_convexHull gives finite ι, affinely independent z, positive weights; card ι ≤ finrank(vectorSpan)+1 ≤ card K +1 < card K+2; reindex via Fintype.equivFin; slices for N<card K+2 each semialgebraic (exists block Fin N ⊕ (Fin N × m), N=0 slice empty and harmless); reverse inclusion by Convex.sum_mem. Sound. Route variant (finite union rather than padding) is declared. |

## 4. Required fixes
None.

## 5. Optional improvements
- A `Msp`-specialised corollary of the hull lemma is left to the consumer (declared by the writer).
- `P_*_subset_SA` proofs are copy-pasted rintro patterns; could be factored (cosmetic).
