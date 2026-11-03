# W2-e AUDIT (Section 3: Lemma 3.3 and the reduction)

## 1. Verdict: ACCEPT
- All four modules build; no sorry/axiom/native_decide/decide/maxHeartbeats/instances; all 87 `#print axioms` results are within {propext, Classical.choice, Quot.sound}.
- Definitions (`SSI`, `Yes`, `Hfun/Lfun/Ffun/Gfun`, `Pp/Qp`, `box`, `BilevelInstance`, `reduce`) match the blueprint literally; `lemma33`, `lemma33_no`, `valueFun_eq`, `reduce_correct`, `totalDegree_Pp/Qp ≤ 5` are stated exactly as specified and proved honestly.
- Concrete instance (k=1, q=![1], R=1, r=1) check passes with explicit witness S=2, and `reduce_correct` composes.

## 2. Build / hygiene / axioms
- `lake build HardnessBilevel.Hardness.{SSI,Construction,Analysis,Reduction}` : each "Build completed successfully" (only the generic "imports Mathlib ... module" linter warning).
- grep `sorry|axiom|native_decide|unsafe|admit|\bdecide\b|maxHeartbeats|open Classical|instance.*Has(...)|stdSimplex` over Hardness/*.lean: only hit is the doc comment text "without `open Classical`" (Analysis.lean:31). The only `instance` is a `DecidablePred (IsBinary)` (noncomputable, harmless).
- Scratch `<SCRATCH>/lean/W2eAudit.lean` (`lake env lean`): `#print axioms` on every public def/theorem of the unit (87 lines, incl. the three scratch theorems): all `[propext, Classical.choice, Quot.sound]` except `SSI.subsetSum`, `SSI.Yes` which use `[propext, Quot.sound]`. No errors.

## 3. Faithfulness
| blueprint id | Lean name | verdict | note |
|---|---|---|---|
| Problem 3.1 / SSI | `SSI`, `SSI.subsetSum`, `SSI.Yes` | IDENTICAL to blueprint (paper modulo declared omission of positivity, r ≤ k: superset of instances, E-24) | `Yes := ∃ S, R ≤ S ∧ S < R + 2^r ∧ ¬ subsetSum S`; `subsetSum S := ∃ T : Finset (Fin k), ∑ i∈T, q i = S`. Verified verbatim. |
| F,G,H,L,Q,P real functions | `Ffun, Gfun, Hfun, Lfun, Qfun, Pfun` | IDENTICAL | F = R+∑ 2^j x_j (0-indexed), G=∑ t_i q_i, H=∑(t(1−t))²+(F−G)², L = z((z−1)²+∑((1−x_j)x_j)²), Q=L(x,y0)+H(x,tail y), P=1−y0(H+1). No sign/index error. |
| integer polynomials | `Fp,Gp,Hp,Lp,Qp,Pp : MvPolynomial (Fin r ⊕ Fin (k+1)) ℤ` | IDENTICAL | z = `X (Sum.inr 0)`, t_i = `X (Sum.inr i.succ)`, x_j = `X (Sum.inl j)`, coefficients `C (2^j)`, `C (q i)`, `C R`. |
| evaluation encoding | `aeval_Fp/Gp/Hp/Lp`, `Qfun_eq_aeval`, `Pfun_eq_aeval`, `aeval_eq_eval_map`, `isPolyFun_P/Qfun` | IDENTICAL | polynomials evaluate (via `aeval (Sum.elim x y)`) to the real functions with `Fin.tail y`; scratch `example ... := rfl` confirms Pfun unfolds to 1 − y0(H+1) with H spelled out. |
| box 𝒴=[0,1]^(k+1) | `SSI.box`, `box_eq_cube`, `mem_box_iff` | IDENTICAL | `Set.pi univ (Icc 0 1)` on `Fin (k+1) → ℝ`; `mem_box_iff`: `y 0 ∈ Icc 0 1 ∧ Fin.tail y ∈ cube k`. |
| s3.L0 | `isMinOn_cons_iff`, `argminSet_cons` | IDENTICAL (set form unconditional) | |
| s3.L1 (a)–(e) | `Lfun_nonneg`, `Lfun_zero`, `Lfun_eq_zero_iff`, `isMinOn_Lfun_iff`, `Zset`, `mem_Zset_iff`, `Zset_eq` | IDENTICAL | `Zset` defined as argminSet (equivalent to blueprint set by `mem_argminSet_iff`, declared). |
| s3.L2 (a)–(e) | `Hfun_nonneg`, `Hfun_eq_zero_iff`, `continuous_Hfun`, `Tset_nonempty`, `Hfun_eq_mval`, `mval_nonneg`, `mval_eq_zero_iff` | IDENTICAL | `mval := sInf (H x '' cube k)`, shown attained. |
| s3.L3 | `argminSet_Qfun`, `mem_argminSet_Qfun_iff`, `argminSet_Qfun_nonempty` | IDENTICAL | |
| s3.L4 | `isBinary_iff_exists_fin_two`, `Ffun_fin_two`, `exists_nat_of_isBinary`, `exists_isBinary_Ffun_eq` | IDENTICAL | via `finFunctionFinEquiv`. |
| s3.L5 | `tInd`, `tInd_mem_cube`, `isBinary_tInd`, `Gfun_tInd`, `Gfun_of_isBinary` | IDENTICAL | |
| s3.L6 (eq. 21) | `valueFun_eq` | IDENTICAL | `valueFun Pfun Qfun box x = ↑(if IsBinary x then −mval x else 1)`; `valueFun` is the framework `⨅ y ∈ argminSet…, ↑(P x y)` (checked in Framework/Basic.lean). Proof uses `valueFun_eq_of_isLeast`/`_of_const`, not `biInf_const`. Matches corrected (21). |
| s3.L7 | `optVal_lt_zero_of_yes` | IDENTICAL | |
| s3.L8 | `valueFun_nonneg_of_not_yes`, `valueFun_zero_of_not_yes`, `lemma33_no` | IDENTICAL | `lemma33_no (I) (h : ¬ I.Yes) : optVal … = 0`. |
| s3.lemma33 | `SSI.lemma33` | IDENTICAL | `optVal I.Pfun I.Qfun I.box < (0 : EReal) ↔ I.Yes` (EReal-valued, as required). Namespace `Bilevel.SSI` with dot notation, rather than blueprint's bare `Pfun I`; cosmetic. |
| BilevelInstance | `BilevelInstance` with `n m P Q degP degQ lo hi c` | IDENTICAL | `degP : P.totalDegree ≤ 5`, `degQ` likewise, integer `lo hi c`; `box`, `Pfun`, `Qfun` (via `aeval`), `optVal := ⨅ x, valueFun …`, `Yes := optVal < ((c:ℝ):EReal)` (cast through ℝ). |
| reduce | `reduce` | IDENTICAL | `n=r, m=k+1, P=Pp, Q=Qp, lo=0, hi=1, c=0`. |
| s3.reduce_correct | `reduce_correct (I) : (reduce I).Yes ↔ I.Yes` | IDENTICAL | via `reduce_box`, `reduce_optVal`, `lemma33`. |
| s3.degree | `totalDegree_Fp/Gp/Hp/Lp/Qp/Pp` | IDENTICAL | all `≤`, never `=`; proved by genuine `totalDegree_add/mul/pow/finsetSum/...` bookkeeping (`td_*` private helpers); no decide. |
| s3.integer_coeff | by construction (`MvPolynomial _ ℤ`) | IDENTICAL | |
| s3.coeff_bound | not formalized | OPTIONAL, declared | |
| s3.thm32 | not formalized (complexity) | declared | |

Special checks: (1) done above; (2) done, plus `rfl` example; (3) box/`y 0`/`Fin.tail` verified; (4) verified; (5) verified; (6) the degree proofs contain no `decide`/`native_decide` (only `norm_num` on numeral inequalities such as `2*(1+1)... ≤ 4/5`); (7) verified.

Concrete instance (scratch file, compiled): `def I1 : SSI := ⟨1, ![1], 1, 1⟩`; `I1_yes : I1.Yes` with witness `S = 2` (bounds by `simp [I1]`; non-subset-sum by `Finset.sum_le_sum_of_subset` + `omega`, no `decide`); `I1_red : (reduce I1).Yes := (reduce_correct I1).2 I1_yes`; `I1_lt : optVal I1.Pfun I1.Qfun I1.box < 0 := (lemma33 I1).2 I1_yes`. All three depend only on the standard axioms.

## 4. Required fixes
None.

## 5. Optional improvements
- `SSI.subsetSum`/`SSI.Yes` printing `[propext, Quot.sound]` is fine (subset of allowed).
- Blueprint writes `lemma33 : optVal (Pfun I) (Qfun I) (box I.k)`; Lean uses `I.Pfun I.Qfun I.box` (`I.box = cube (k+1)` by `rfl`, `box_eq_cube`). Later waves should use the dot-notation names; no action needed.
- Many auxiliary lemmas (`mem_cube_iff`, `Tset_subset`, ...) lack docstrings; cosmetic.
- Files import all of `Mathlib` (project-wide lint warning only).
