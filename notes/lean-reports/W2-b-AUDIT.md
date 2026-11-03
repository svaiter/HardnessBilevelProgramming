# W2-b AUDIT (Berge.lean, blueprint §4.D)

## 1. Verdict: ACCEPT
- Builds clean, no sorry/axiom/etc., all 21 public declarations have axioms ⊆ {propext, Classical.choice, Quot.sound}.
- All statements are identical to or strictly stronger than the blueprint (B6/B7 and ne_bot unconditional in S.Nonempty; no T2Space Y; filter form of outer_semicont).
- `berge.rem210` absent (deferred to Wave 3 per PLAN, declared by writer); the ℝ instantiation of `cor29` typechecks.

## 2. Build / hygiene / axioms
- `lake build HardnessBilevel.Framework.Berge`: "Build completed successfully (18247 jobs)" (only the pre-existing module-system warning on Semicont.lean).
- grep for `sorry|axiom|native_decide|unsafe|admit|maxHeartbeats|open Classical|instance|T2Space|stdSimplex|mem_setOf_eq`: only hit is the word `T2Space` in the header docstring (line 26). No `set_option`, no instance.
- `#print axioms` on all 21 declarations (scratch: <SCRATCH>/lean/W2bAudit.lean, `lake env lean`): every one is `[propext, Classical.choice, Quot.sound]`.
- Instantiation test (same scratch file), compiled without errors:
  `example : LowerSemicontinuous (valueFun (fun x y : ℝ => x*y) (fun x y : ℝ => (y-x)^2) (Set.Icc 0 1)) := (cor29 (P:=…) (Q:=…) (S:=Set.Icc 0 1) (by fun_prop) (by fun_prop) isCompact_Icc ⟨0, by simp⟩).1`

## 3. Faithfulness
Definitions used (Basic.lean): `argminSet Q S x = {y | y∈S ∧ ∀ y'∈S, Q x y ≤ Q x y'}`, `valueFun = ⨅ y ∈ argminSet Q S x, ((P x y:ℝ):EReal)`, `pvalueFun = ⨆ …` — correct, EReal-valued.
Typeclass: only `[TopologicalSpace X] [TopologicalSpace Y]`; no T2Space anywhere (also none in instance arguments). Confirmed not needed: `isClosed_argminSet_graph` takes `IsClosed S` as explicit hypothesis (this is the only place closedness is used, and it is not used downstream), B6 works in X × ↥S with CompactSpace ↥S from `IsCompact S` (no T2 needed for `isClosedMap_fst_of_compactSpace`).

| blueprint id | Lean name | verdict | note |
|---|---|---|---|
| (helper) | continuous_section_of_uncurry | IDENTICAL | |
| berge.isClosed_graph | isClosed_argminSet_graph | IDENTICAL | hyps: Continuous (uncurry Q), IsClosed S only; `{p : X×Y | p.2 ∈ argminSet Q S p.1}` |
| berge.outer_semicont | argminSet_outer_semicont | STRENGTHENED | arbitrary `l.NeBot` filter on any index type (covers atTop on ℕ) |
| berge.argmin_nonempty | argminSet_nonempty_of_isCompact | IDENTICAL | has S.Nonempty, IsCompact S |
| berge.argmin_isCompact | argminSet_isCompact_of_continuous | IDENTICAL | |
| berge.exists_isMinOn | exists_isMinOn_argminSet | IDENTICAL | |
| berge.value_attained | valueFun_attained, valueFun_ne_top_of_isCompact (S.Nonempty), valueFun_ne_bot_of_isCompact | IDENTICAL / STRENGTHENED (ne_bot) | ne_bot proof splits S=∅ (value ⊤) vs nonempty: sound |
| berge.isClosed_sublevel | isClosed_valueFun_sublevel | STRENGTHENED | no S.Nonempty; S=∅ branch: set is ∅ because valueFun = ⊤ (via `valueFun_eq_top_iff`, argminSet ⊆ S = ∅) and `(r:EReal) ≠ ⊤`; nonempty branch via closed image under fst of closed C ⊆ X×↥S; both inclusions checked |
| berge.lsc | lowerSemicontinuous_valueFun | IDENTICAL (unconditional as required) | hyps exactly hP, hQ, IsCompact S; ⊥ case uses ne_bot (unconditional), ⊤ case univ |
| berge.lsc_real | (Semicont `lowerSemicontinuous_coe_iff`) | MISSING-by-reference | acceptable, blueprint says = fw.lsc_real_bridge |
| berge.bdd_on_compact | valueFun_bddOn_compact (+ generic bddOn_compact_of_attained) | IDENTICAL | `∃ M:ℝ, ∀ x∈K, ((-M:ℝ):EReal) ≤ φ x ∧ φ x ≤ (M:EReal)` literal blueprint form; has S.Nonempty; real-valuedness separately via B5 |
| berge.cor29 | cor29 | IDENTICAL | lsc ∧ (∀x, ≠⊤ ∧ ≠⊥) ∧ (∀ K compact, bounded) ; hyps hP hQ IsCompact S, S.Nonempty |
| berge.pess | upperSemicontinuous_pvalueFun (unconditional), pvalueFun_attained, pvalueFun_ne_top_of_isCompact (unconditional; S=∅ gives ⊥), pvalueFun_ne_bot_of_isCompact (needs Nonempty), pvalueFun_bddOn_compact, cor29_pess | IDENTICAL/STRENGTHENED | derived via pvalueFun_eq_neg_valueFun_neg and `upperSemicontinuous_iff_lowerSemicontinuous_neg`, no extra hypotheses; correct |
| berge.rem210 | — | MISSING (justified) | PLAN moves it to Wave 3 (per writer report; it needs semialgebraic classes) |

## 4. Required fixes
None.

## 5. Optional improvements
- `mem_ofPred_eq` appears in `simp only` calls (builds; name is unusual, may be fragile across Mathlib bumps; `Set.mem_setOf_eq` is banned by PLAN so acceptable).
- `continuous_uncurry_neg` and `pvalueFun_*` lack docstring on the first; trivial.
- `berge.lsc_real` could get an alias in this file if later waves expect a `berge`-named export (check consumers use `lowerSemicontinuous_coe_iff`).
