# W2-f AUDIT (Convex/Toolkit, Convex/Lemma219, Convex/Thm218)

## 1. Verdict: ACCEPT
* Builds; no sorry/axiom/etc.; `#print axioms` of all 52 top-level decls is within {propext, Classical.choice, Quot.sound} (t218Idx: none).
* `ConvexLower`, `lemma219`, `sum_indicator{,_basic,_semialgebraic}` are faithful (IDENTICAL or marginally STRENGTHENED); no extra hypotheses
  (no DecidableEq / Nonempty / disjointness / covering); `ι : Type` with `Fintype ι` existential; Y literal mixed box, unbounded also for J = ∅.
* Consumer check done: `sum_indicator_semialgebraic` instantiated for n=1, N=2 (S0={0<x0}, S1={x0≤0}, p0=X0, p1=0) giving a convex-lower
  polynomial bilevel problem with value AND pvalue function `↑(max (x 0) 0)`; API was fully sufficient (≈25 lines, scratch file clean).

## 2. Build / hygiene / axioms
* `lake build HardnessBilevel.Convex.Toolkit / .Lemma219 / .Thm218` -> "Build completed successfully (18257 jobs)" (only the generic
  Mathlib "module system" lint warnings on upstream files).
* grep for `sorry|axiom|native_decide|unsafe|admit|instance.*Has(...)|maxHeartbeats|open Classical|DecidableEq`: no hits in the three files.
  (`Nonempty` appears only in conclusions `(argminSet …).Nonempty`.)
* Axioms: scratch file `<SCRATCH>/lean/W2f.lean` (52 `#print axioms Bilevel.<name>` for every def/theorem/abbrev of the 3 files),
  `lake env lean` -> every line "depends on axioms: [propext, Classical.choice, Quot.sound]" (filtered), `t218Idx` "does not depend on any axioms".
  Only warning was my own deliberate `sorry` in that scratch's example; the sorry-free version `<SCRATCH>/lean/W2fInst.lean`
  (`posPart_convex_poly`) compiles with axioms [propext, Classical.choice, Quot.sound].

## 3. Faithfulness
| blueprint id | Lean | verdict | note |
|---|---|---|---|
| §2.3 ConvexLower | `Bilevel.ConvexLower` | IDENTICAL | `∀ x, ConvexOn ℝ Set.univ (fun y => Q x y)`; `ι : Type*`, `Q : (Fin n→ℝ)→(ι→ℝ)→ℝ`. `Framework/Classes.lean` imports it (no redefinition; only def in repo). |
| fw.argmin_scalar (i) | `argmin_scalar_univ`, `mul_eq_of_isMin_univ`, `isMin_univ_witness` | IDENTICAL (set equality, `c*t` order) | correct |
| (ii) | `argmin_scalar_Ici`, `mul_eq_of_isMin_Ici`, `isMin_Ici_witness` | IDENTICAL | `if 0<c then {c⁻¹} else if c=0 then Ici 0 else {0}`; consequences `c*u = if 0<c then 1 else 0` (stronger than needed) |
| (iii) | `isMin_one_Icc_iff`, `eq_zero_of_isMin_Icc` | IDENTICAL | correct |
| fw.convex_toolkit | `convexOn_sq_affine` (general `E`, `ℓ : E →ₗ[ℝ] ℝ`, `(c-ℓ v)^2` on univ), `convexOn_finset_sum` (any convex `t`, Finset, no extra hyps), `convexOn_linear_coord`, `convexOn_sq_one_sub_mul_coord`, `ConvexLower.{add,finset_sum,comp_reindex,convexOn}`, `convexLower_const` | IDENTICAL / STRENGTHENED (extras) | correct statements |
| fw.value_shift_attained, const_on_argmin | reused from W1-a (`value_shift_attained`, `valueFun_eq_of_const`) | OK | not restated |
| t219.main | `lemma219` (+ `lemma219_exists`, `ι : Type`, `Fintype ι`) | IDENTICAL | gives IsPolyFun P', Q'; ConvexLower Q'; IsUnboundedBox (gadY J); ∀x nonempty argmin ∧ P' = (basicSet P Q).indicator 1 x on argmin; valueFun = pvalueFun = ↑(1_S x). `Q' = (1 - t·P(x))^2 + ∑(1 - Q_j(x)u_j)^2`, `P' = (1 - tP)∏(Q_j u_j)`, `Y = pi univ (Sum.elim univ Ici0)` over `Unit ⊕ J`: exactly blueprint. `J : Type*`, `[Fintype J]` possibly empty; `isUnboundedBox_gadY` has no hypothesis on J. |
| basicSet | `basicSet P Q = {x | eval x P = 0 ∧ ∀ j, 0 < eval x (Q j)}` | IDENTICAL | literally equal to the `IsBasicSA` set shape |
| t218.sum_indicator | `sum_indicator` (data form: `S i = ⋃ j, basicSet (PT i j) (QT i j)`) | IDENTICAL | no disjointness/covering |
| | `sum_indicator_basic` | IDENTICAL | hyp `∀ i, ∃ m T, (∀ j, IsBasicSA (T j)) ∧ S i = ⋃ j, T j` |
| | `sum_indicator_semialgebraic` | IDENTICAL | hyp only `∀ i, IsSemialgebraic (S i)`; conclusion `∃ (ι : Type) (_ : Fintype ι) P Q Y, IsPolyFun P ∧ IsPolyFun Q ∧ ConvexLower Q ∧ IsUnboundedBox Y ∧ (∀ x, argmin nonempty ∧ ∀ y ∈ argmin, P x y = ∑ i, (S i).indicator 1 x * eval x (p i)) ∧ valueFun = … ∧ pvalueFun = …` as in the blueprint |
| construction | `t218Idx/Blk/Q/P/Y` | OK | dummy `Unit` free coordinate present, so box unconditionally unbounded (J-all-zero case covered); mixed box literal; `t218Idx ∈ Type`; Sigma not flattened (ι existential — blueprint allows) |
| t218.PP_sub_Cunbound, main | absent | EXPECTED (Wave 3) | |

## 4. Required fixes
None.

## 5. Optional improvements
1. Could add a corollary `sum_indicator_PP`-style statement or a ready-made lemma for the `max(x,0)` demo? Not needed.
2. `ConvexLower` currently lives in a "Toolkit" file; fine, but W3-c already imports it so keep name stable.
3. Writer's note: `PP ⊆ C_unbound` still needs the closure of the construction output under `IsUnboundedBox` / `C_unbound` membership (needs `ι : Type` as provided — satisfied).

## Consumer test (item requested)
`<SCRATCH>/lean/W2fInst.lean`: `posPart_convex_poly : ∃ (ι : Type) (_ : Fintype ι) P Q Y, IsPolyFun P ∧ IsPolyFun Q ∧ ConvexLower Q ∧
IsUnboundedBox Y ∧ valueFun P Q Y = (fun x => ↑(max (x 0) 0)) ∧ pvalueFun P Q Y = (fun x => ↑(max (x 0) 0))` — compiles. Needed only:
`isSemialgebraic_eval_pos`, `IsSemialgebraic.compl`/`.of_eq`, and `simp [Fin.sum_univ_two, Set.indicator]` for the sum. Feasible; API adequate.
