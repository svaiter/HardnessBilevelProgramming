# W4-b-core WRITER report

## File delivered
* /home/user/HardnessBilevelProgramming/HardnessBilevel/Convex/Thm220Core.lean (namespace `Bilevel`;
  imports Convex.Toolkit, Semialgebraic.Basic, Framework.Classes). No sorry/axiom/native_decide; no A1–A3 classes.
  `#print axioms` of all 24 public declarations ⊆ {propext, Classical.choice, Quot.sound} (checked from a scratch file).

## Blueprint ids → Lean names
* `t220.normalise` → `t220_normalise`, `lowerSemicontinuous_sub_poly`
* `t220.core` → `t220_core` (statement verbatim from §4.G.4), corollary `t220_core_valueFun`
  * construction: `t220A`, `t220B`, `t220Q`, `t220P` (lower index `L ⊕ Σ l, K l`, box `boundedBox 0 1`)
  * Step 2 argmin: `boundedBox_sum_eq`, `mem_argminSet_t220A_iff`, `mem_argminSet_t220B_iff`,
    `mem_argminSet_t220Q_iff`, `mem_argminSet_t220Q_iff'`
  * Step 3: `le_t220P_of_mem`; Step 4: `exists_mem_argminSet_t220P_eq`; Step 5: `isLeast_t220P_of_nonpos`
  * Step 6: `convexLower_t220Q`; Step 7: `isPolyFun_t220Q`, `isPolyFun_t220P`
* `t220.D_closed` → `t220_D_closed`
* `t220.D_sa` → `t220_D_eq` (+ general `t220_D_eq_of_poly`), `t220_D_sa`
* `t220.supset` (c)–(e) assumption-free part → `t220_isLeast_of_presentation`, `t220_of_presentations`
  (conclusion = that of `t220_core_valueFun`), extra `t220_mem_C_bounded_of_presentations` (`coeFun f ∈ C_bounded n`)
* `t220.eq13` (optional) → `t220_eq13`, `t220_eq13_nonempty`
* NOT done (by assignment): `t220.supset` (needs A2), `t220.subset`, `t220.main` (need A1 / Prop 2.6).

## Deviations
* `t220_normalise`: `L : Type*` (generalisation).
* Presentation lemmas: no semialgebraicity/disjointness hypotheses on `S i` (unused → dropped = strengthening).
  Closed-basic presentation of `D_i` given as `J : Fin N → ℕ`, `K : (i : Fin N) → Fin (J i) → ℕ`,
  `R i j k`, hypothesis `∀ i, {x | f x ≤ eval x (p i)} = ⋃ j, ⋂ k, {x | 0 ≤ eval x (R i j k)}` — matches the output
  of `HasFinitenessTheorem.exists_eq_iUnion_iInter_nonneg` (use `K := fun i _ => J' i`).
* Route: Step 7 needed no `comp_equiv` transport — `ι := L ⊕ Σ l, K l` is used directly (it is existential).
  Argmin via `argminSet_sum_elim` + `argminSet_pi_sum` as in the blueprint.

## Mathlib names that differed
* `if_pos`/`if_neg`/`if_true` flagged deprecated in this Mathlib → used `simp only [h, ↓reduceIte]`.
* `push_neg` deprecated → `push Not`. `LinearMap.coeFn_sum` absent → `LinearMap.sum_apply`.
* `ContinuousAt.eventually_lt`, `mem_closure_iff_frequently`, `Filter.Frequently.and_eventually`,
  `LowerSemicontinuous.isClosed_preimage`, `LowerSemicontinuous.add`, `Finset.prod_le_one₀` as in the blueprint.

## Last build
`lake build HardnessBilevel.Convex.Thm220Core` → "Build completed successfully" (no warnings from this file).
