# AUDIT W4-asm + W5-a (Thm215, Thm220, Thm221, Pessimistic)

## 1. Verdict: ACCEPT
- All four modules build; no sorry/axiom/instance of A1-A3 in the whole library; every public declaration depends only on {propext, Classical.choice, Quot.sound}.
- Statements of thm215_supset/eq, thm220_supset/main, thm221_eq, compact_sa_incl and all pess_* match the blueprint; binder sets are exactly the blueprint §1 table (no missing, no superfluous binder).
- thm215_supset proof follows the prescribed route (A3 growth bound from hcb, closed epigraph, isSemialgebraic_epigraph [A1], A2 presentation, thm215_of_presentation).

## 2. Build / hygiene / axioms
- `lake build HardnessBilevel.Bounded.Thm215 HardnessBilevel.Convex.Thm220 HardnessBilevel.Convex.Thm221 HardnessBilevel.Pessimistic` -> "Build completed successfully (18303 jobs)" (only module-system linter warnings in unrelated files).
- grep `sorry|axiom|native_decide|unsafe|admit|maxHeartbeats|^open Classical` over the four files: no hits.
- grep over all of HardnessBilevel/ for `instance.*Has(...)`, `haveI/letI`, `attribute [instance]`, `: HasX :=`, `sorry`, `axiom`, `native_decide`, `admit`: only docstring mentions in Assumptions/Classes.lean and an unrelated docstring in Gadgets/ZeroLocus.lean. No instance of A1-A3 exists. Assumptions/ contains only Classes.lean (no Unsafe.lean).
- `#print axioms` (scratch file $S/lean/ax_w4asm_aud.lean, `lake env lean`): all 26 declarations (mem_boundedBox_of_sum_sq_le, bdd_sum_sq_of_bdd_compact, thm215_supset, thm215_mem_P_bounded, eq_coeFun_toReal_of_mem_CB, exists_real_of_mem_SA_LSC_CB, thm215_eq, thm220_supset, thm220_main, Msp_eq_eval, thm221_hull_sa, thm221_compact_sa_incl, thm221_compact_sa_incl_pess, thm221_supset, thm221_eq, neg_mem_PP, neg_mem_PP_iff, coeFun_neg, neg_mem_SA_LSC_CB, pess_thm11, pess_cor29, pess_thm212, pess_thm218, pess_thm215, pess_thm220, pess_thm221) = [propext, Classical.choice, Quot.sound].

## 3. Faithfulness table (binders verified by `#check @name`)
| blueprint id | Lean | binders (actual) | verdict | note |
|---|---|---|---|---|
| t215.supset | thm215_supset | A1,A2,A3 exactly, then {n} f, IsSemialgebraicMap f, LowerSemicontinuous f, bounded-on-compacts | IDENTICAL | IsSemialgebraicMap f := IsSemialgebraic (graphSet f) by definition (graphSet = {z \| f (z∘inl) = z (inr ())}); conclusion verbatim (ι : Type, Fintype, polys, a ≤ b, valueFun over boundedBox a b = ↑(f x)); no extra hypotheses |
| t215.supset class form | thm215_mem_P_bounded | A1,A2,A3 | IDENTICAL | P_bounded witness uses IsBoundedBox via ⟨a,b,hab,rfl⟩ |
| t215.eq | thm215_eq : P_bounded n = SA n ∩ LSC n ∩ CB n | exactly A1,A2,A3, no other hypotheses | IDENTICAL | ⊆ via thm215_subset (A1), ⊇ via exists_real_of_mem_SA_LSC_CB + thm215_mem_P_bounded |
| t220.supset | thm220_supset : f ∈ PP n → LowerSemicontinuous f → coeFun f ∈ C_bounded n | ONLY [HasFinitenessTheorem] (confirmed #check) | IDENTICAL | no A1; uses t220_D_sa/t220_D_closed, A2 per piece, t220_mem_C_bounded_of_presentations |
| t220.main | thm220_main | A1, A2 | IDENTICAL | conjunction; A1 only for ⊆ half (thm220_subset), A2 only for first |
| t221.hull_sa | thm221_hull_sa | A1 | IDENTICAL | specialisation of sa.hull_semialgebraic to Msp S |
| t221.compact_sa_incl | thm221_compact_sa_incl | A1 only | IDENTICAL/STRENGTHENED | ∀ IsPolyFun P Q, Y compact nonempty semialgebraic (ι : Type, Fintype) ⇒ valueFun P Q Y ∈ C_cc n; data: κ = ↥S, S = supports union, Y' = convexHull (Msp S '' Y) (nonempty, compact, convex, semialgebraic), ConvexLower Q'; equality via t221_linearize_value. Pessimistic twin thm221_compact_sa_incl_pess ∈ Cp_cc n |
| t221.supset | thm221_supset : SA ∩ LSC ∩ CB ⊆ C_cc n | A1,A2,A3 | IDENTICAL | via thm215_supset + compact_sa_incl on boundedBox a b |
| t221.eq | thm221_eq : C_cc n = SA n ∩ LSC n ∩ CB n | A1,A2,A3 exactly | IDENTICAL | |
| pess.target_neg (PP etc.) | neg_mem_PP(_iff), coeFun_neg, neg_mem_SA_LSC_CB | none | IDENTICAL | other target-neg lemmas are in Framework/Classes |
| pess.t11 | pess_thm11 | none (confirmed) | IDENTICAL | USC f, {f ≠ ⊥} closed ⇒ ContDiff ℝ ∞ P,Q : Fin 3 lower space, pvalueFun P Q univ = f (∞ is the smooth, not analytic, order) |
| pess.berge | pess_cor29 | none (confirmed) | IDENTICAL | usc, real-valued, bounded on compacts |
| pess.t212 | pess_thm212 : Pp_unbound n = SA n | A1 | IDENTICAL | A1 needed for ⊆ only (equality statement) |
| pess.t218 | pess_thm218 : PPe n ⊆ Cp_unbound n ∧ Cp_unbound n ⊆ SA n | A1 | IDENTICAL | A1 for second conjunct |
| pess.t215 | pess_thm215 : Pp_bounded n = SA n ∩ USC n ∩ CB n | A1,A2,A3 | IDENTICAL | via negation + thm215_eq |
| pess.t220 | pess_thm220 | A1,A2 | IDENTICAL | via thm220_supset on -f |
| pess.t221 | pess_thm221 : Cp_cc n = SA n ∩ USC n ∩ CB n | A1,A2,A3 | IDENTICAL | |
Writer's binder table matches reality for every row. Class definitions (C_cc nonempty/compact/convex/semialgebraic; ι : Type; PP; CB; SA) checked in Framework/Classes.lean: faithful. A1-A3 class statements in Assumptions/Classes.lean match blueprint §2.5/§4.B (A3 stated with explicit graph set = graphSet f, growth' wrapper with IsSemialgebraicMap is the blueprint form).

Assumption-usage cross-check vs blueprint §1: 2.15 ⊇ uses A1 (isSemialgebraic_epigraph) + A2 (HasFinitenessTheorem.exists_eq_iUnion_iInter_nonneg) + A3 (growth'); 2.20 ⊇ A2 only; 2.21 ⊇ A1 (hull) + whatever 2.15 uses; all ⊆ halves A1 only; pess_thm11/pess_cor29 none. No superfluous binder found (each binder is consumed in the proof; since no instances exist, an unneeded binder could not be detected by elaboration, so this was checked by reading the proofs and the binders of the lemmas they cite).

(8) thm215_supset proof read: `HasGrowthBound.growth' hsa (bdd_sum_sq_of_bdd_compact hcb)`, where the ball hypothesis is derived from hcb via {∑x² ≤ r} ⊆ boundedBox(-(|r|+1), |r|+1) (compact, isCompact_boundedBox); wq = C(|B|+1) + (1+∑X_i²)^M with eval wq > 0 and |f| ≤ eval wq (uses le_abs_self B); epigraph E closed by isClosed_epigraph_sum (LowerSemicontinuous.isClosed_epigraph), semialgebraic by isSemialgebraic_epigraph hsa (A1); A2 gives presentation; thm215_of_presentation (hE1 f x ≤ f x, hE2 definitional) finishes. Matches blueprint steps 1-7.

## 4. Required fixes
None.

## 5. Optional improvements
- pess_thm212/pess_thm218/thm220_main/pess_thm220 are conjunction/equality statements carrying A1 for the ⊆ half; splitting off assumption-free ⊇ halves (e.g. a standalone thm218 PP ⊆ Cp_unbound without A1) would sharpen the assumption footprint, but is not required (statements are the blueprint's).
- Root HardnessBilevel.lean must import the four modules (writer notes this; orchestrator task).
