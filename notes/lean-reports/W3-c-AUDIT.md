# W3-c AUDIT (HardnessBilevel/Framework/Classes.lean)

## 1. Verdict: ACCEPT
- All classes, targets, PP, and class-level corollaries match the blueprint; no weakening or retyping found.
- Build clean, no sorry/axiom/instances of A1-A3, all 58 declarations depend only on {propext, Classical.choice, Quot.sound}.
- Scratch examples (x 0 in P_unbound 1 via thm212_supset; coeFun x0 in C_unbound 1 via thm218_PP_subset with one-piece partition) compile.

## 2. Build / hygiene / axioms
- `lake build HardnessBilevel.Framework.Classes` -> Build completed successfully (only module-system warnings).
- grep for sorry|axiom|native_decide|unsafe|admit|Has(Semialg|Finite|Growth)|maxHeartbeats|open Classical -> no hits.
- Scratch <SCRATCH>/lean/W3c.lean: 58 `#print axioms` (every def/theorem in the file); all 58 print `[propext, Classical.choice, Quot.sound]` (defs included).
- Examples in same scratch file compile with no errors.

## 3. Faithfulness
| blueprint id | Lean | verdict | note |
|---|---|---|---|
| valueFunClass | valueFunClass | IDENTICAL | `∃ (ι:Type) (_:Fintype ι) P Q S`, IsPolyFun P ∧ IsPolyFun Q ∧ boxOK ∧ qOK ∧ h = V P Q S |
| P_unbound / P_bounded | same | IDENTICAL | valueFun, IsUnboundedBox / IsBoundedBox, qOK True (IsUnboundedBox literal: lo≠⊤, hi≠⊥, lo≤hi, ∃i lo=⊥∨hi=⊤; Box.lean) |
| C_unbound / C_bounded / C_cc | same | IDENTICAL | ConvexLower Q (univ); C_cc: Nonempty ∧ IsCompact ∧ Convex ℝ ∧ IsSemialgebraic |
| pessimistic twins | Pp_*, Cp_* | IDENTICAL | pvalueFun |
| LSC, USC, CB, SA | same | IDENTICAL | CB two-sided real bound on every compact; SA = IsExtSemialgebraic |
| PP (Def 2.17) | PP | IDENTICAL | real-valued, N, Fin N pieces, semialgebraic, Pairwise Disjoint, ⋃ = univ, f = eval on piece |
| coercion convention | coeFun, PPe := coeFun '' PP n | IDENTICAL | |
| fw.class_incl | valueFunClass_mono + 10 inclusions (P_box aux = IsBox) | IDENTICAL | |
| fw.CB_real | CB_real | IDENTICAL | |
| fw.pvalue_class_neg | mem_pvalueFunClass_iff_neg, mem_Pp_*_iff, mem_Cp_*_iff | IDENTICAL | `h ∈ Pp_* ↔ (-h) ∈ P_*`; also neg_mem_SA/CB/LSC/USC |
| berge.rem210 | P_bounded_subset_LSC_CB, C_cc_subset_LSC_CB, C_bounded_subset_LSC_CB + pess. twins (USC ∩ CB) | IDENTICAL | uses Nonempty ∧ Compact only |
| t212.thm212_sup | thm212_supset : SA n ⊆ P_unbound n | IDENTICAL | no added hypothesis; box = Set.univ over `Thm212.Idx τΓ τm`, shown Nonempty (Sum.inl ()), via isUnboundedBox_univ; polys via isPolyFun_polyFun |
| pess. twin | thm212_supset_pess : SA n ⊆ Pp_unbound n | IDENTICAL | via negation |
| t218.PP_sub_Cunbound | thm218_PP_subset : PPe n ⊆ C_unbound n (+ pointwise ', pess twin) | IDENTICAL | box from sum_indicator_semialgebraic is IsUnboundedBox (literal) |
| partition identity | PP_eq_sum_indicator | correct | disjoint+cover => f x = Σ indicator·eval (single nonzero term) |

## 4. Required fixes
None.

## 5. Optional
- Docstrings missing on the pessimistic inclusion/neg lemmas (cosmetic).
- `t212.reindex` (Fin m version) not provided; blueprint marks it optional.
