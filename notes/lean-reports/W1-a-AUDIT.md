# W1-a AUDIT (Framework/Basic, Value, Separable)

## 1. Verdict: ACCEPT
- All definitions are verbatim the blueprint's; every checked lemma is identical or strictly stronger; no undeclared deviation.
- Build green, hygiene clean, `#print axioms` of all 47 public declarations = {propext, Classical.choice, Quot.sound}.
- API smoke test (Q x y=(y-x)^2, P x y=y, valueFun = ↑x) works via both F0 and F4+V5 routes with no friction.

## 2. Build / hygiene / axioms
- `lake build HardnessBilevel.Framework.Basic .Value .Separable` -> "Build completed successfully (18245 jobs)" (only the generic `module` warning for `import Mathlib`).
- grep for sorry/axiom/native_decide/unsafe/admit/Has*/maxHeartbeats/open Classical/set_option: no hits. Only `import Mathlib` / `import ...Basic`; `classical` used inside one proof only.
- Scratch `lean/W1a_axioms.lean`: `#print axioms` on all 47 def/theorems (extracted by grep) -> 47 outputs, all within the standard three (non-matching lines filtered: none).

## 3. Faithfulness
| blueprint id | Lean name | verdict | note |
|---|---|---|---|
| argminSet | argminSet | IDENTICAL | `{y | y ∈ S ∧ ∀ y' ∈ S, Q x y ≤ Q x y'}` |
| valueFun | valueFun | IDENTICAL | `⨅ y ∈ argminSet Q S x, ((P x y:ℝ):EReal)` |
| pvalueFun | pvalueFun | IDENTICAL | `⨆ ...` |
| optVal | optVal | IDENTICAL | `⨅ x, valueFun P Q S x` |
| F1/F2/mem_argmin_univ/F3 | mem_argminSet_iff, argminSet_subset, mem_argminSet_univ (simp), argminSet_eq_empty_iff | IDENTICAL | |
| F4/F4′ | argminSet_eq_zeroSet, mem_argminSet_of_nonneg_zero | IDENTICAL | both hypotheses present |
| F6 | argminSet_mul_pos, argminSet_add_left | IDENTICAL | |
| F8 | argminSet_isClosed/isCompact | STRENGTHENED | no T2 needed |
| argmin_empty_of_pos_inf | argminSet_empty_of_pos_inf (+ univ corollary) | STRENGTHENED | general S |
| V1 | valueFun_eq_top_iff (+pvalueFun_eq_bot_iff) | IDENTICAL | |
| V2 | valueFun_eq_of_isMinOn (+IsMaxOn twin) | IDENTICAL | |
| F0 | valueFun_eq_of_isLeast | IDENTICAL | `IsLeast (P x '' argminSet Q S x) r → valueFun P Q S x = ↑r`; twin isGreatest |
| V3 | valueFun_eq_coe_iff | IDENTICAL | exactly `(∀ y∈Θ, r ≤ P x y) ∧ ∀ ε>0, ∃ y∈Θ, P x y < r+ε`; no attainment/nonemptiness hyp |
| V4 | valueFun_eq_bot_iff | IDENTICAL | |
| V5/V5′ | valueFun_eq_of_const, valueFun_unique | IDENTICAL | |
| V8 | pvalueFun_eq_neg_valueFun_neg | IDENTICAL | no hypotheses; covers empty argmin (`-⊤=⊥`) |
| V9 (opt) | valueFun_real_iff | IDENTICAL | |
| A5 value_eq_bot_of_unbounded | valueFun_eq_bot_of_unbounded | IDENTICAL | hyp `∀ r, ∃ y∈Θ, P x y ≤ r`, general S (strengthened from univ) |
| F5 | argminSet_prod_add | IDENTICAL | set equality on `S₁ ×ˢ S₂`, no nonemptiness |
| F7 | argminSet_comp_equiv, valueFun_comp_equiv, pvalueFun_comp_equiv | IDENTICAL | function equality exactly as blueprint |
| argmin_pi_sum | argminSet_pi_sum, pi_sum_min_eq | IDENTICAL/STRENGTHENED | pi version, x-dependent g, `Fintype ι` (blueprint "ι finite"), no nonemptiness, no DecidableEq in statement; pi_sum_min_eq is the literal set equation |
| value_shift_attained | value_shift_attained | IDENTICAL | |
| V6/V7, pvalue_class_neg | — | MISSING (justified) | optional/no consumer; classes later wave |
Typeclasses: no `[DecidableEq]`/`[Nonempty]` in any statement; only `[TopologicalSpace Y]` (F8) and `[Fintype ι]` (pi).
Extras (helpers, pessimistic twins, argminSet_sum_elim): harmless additions.

## 4. Required fixes
None.

## 5. Optional improvements
- Blueprint mentions `fw.pvalue_eq_bot_iff`/`pvalue_eq_neg...` name style; Lean uses `pvalueFun_*` consistently (fine, per PLAN naming rule).
- API file notes names "printed with open Bilevel" — all in namespace `Bilevel`, matches PLAN.
- Proofs are robust (no heartbeat options, `simp` uses are small); `Set.mem_ofPred_eq` used consistently with current Mathlib.
- Smoke exercise (`<SCRATCH>/lean/W1a_exercise.lean`): both routes (F0 via mem_argminSet_univ; F4 argminSet_eq_zeroSet + valueFun_eq_of_const) compiled; smooth (only my own nlinarith steps needed fiddling).
