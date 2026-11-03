# AUDIT of R6 — Section 3 (Theorem 3.2, Lemma 3.3, Observations 1–2, Appendix D)

Auditor: Opus. Sources I re-read myself: `paper_html.txt` 98–127 (BP, BP-O), 262–270 (Berge, Cor. 2.9),
1060–1215 (Section 3), 1324–1337 (Appendix D), reference entries [5],[18],[26],[30],[41],[49];
`paper.txt` 1184–1189, 1274, 1283 (the `< 0` symbols lost in the HTML); `research/ew2012/ew.txt` 196–330
(Eggermont–Woeginger STACS'12 text). Mathlib: local checkout, every cited file:line opened.

## A. Summary verdict

The report is reliable. All of its mathematics (L0–L12) re-derives correctly: argmin of L, the value-function
formula (21), the YES/NO analysis, the binary-encoding route, the degree bound and the full coefficient table.
Every Mathlib citation I checked exists at the stated file:line and says what the report needs (one is off by
one line, which does not matter). Changes needed: (i) `BilevelInstance.Yes` writes `(I.c : EReal)` with
`c : ℤ`. EReal has no `IntCast`, so this almost certainly does not elaborate; write `((I.c : ℝ) : EReal)`.
(ii) The report's claim that `Fin.consEquiv` occurs only in MeasureTheory is false. It is at
`Data/Fin/Tuple/Basic.lean:184`, but this does not change the recommended route. (iii) Two of the 15
"paper errors" are overstated: #6 (Corollary 2.9 does state Θ(x) ≠ ∅) and #15 (not an error). (iv) There
are three small paper gaps the report does not list (§E). Option 1 for Theorem 3.2 is the right call.

## B. Lemma-by-lemma verdict

| Lemma | Verdict | Note |
|---|---|---|
| Problem 3.1 encoding (`SSI`, `S < R+2^r`, ℕ data) | CONFIRMED | S ≥ R ≥ 0, so S ∈ ℕ costs no generality. Allowing q_i = 0, R = 0, r = 0 gives a superset of instances, which is harmless for both correctness and hardness (it contains the hard subproblem). |
| L0 separable argmin | CONFIRMED | With (a,b) ∈ A×B: (⇒) take (a',b), resp. (a,b'). This needs b ∈ B, resp. a ∈ A, which the membership hypothesis supplies. (⇐) is `add_le_add`. As sets, argmin_{A×B}(f⊕g) = argmin_A f × argmin_B g holds unconditionally. LHS ⊆ RHS: test (a',b) and (a,b'). RHS ⊆ LHS: add the two inequalities. No nonemptiness is needed, and if one factor's argmin is empty both sides are empty. |
| L1 analysis of L | CONFIRMED | L = z·A with A = (z−1)² + s(x) ≥ 0 and s(x) = Σ((1−x_j)x_j)². On [0,1], L ≥ 0 = L(x,0), so the minimum value is 0. The minimizers are {z : z = 0 ∨ A = 0}. For z ∈ (0,1), (z−1)² > 0 gives A > 0, so L > 0 and z is never a minimizer. z = 1 is a minimizer iff s(x) = 0 iff x is binary. So Z(x) = {0,1} if x is binary, {0} otherwise. |
| L2 analysis of H | CONFIRMED | H ≥ 0 everywhere (sum of squares). H = 0 iff t binary and F = G. A minimizer exists on the compact nonempty box. m ≥ 0, and m = 0 iff ∃t ∈ box with H = 0. |
| L3 separability on `Fin (k+1)` | CONFIRMED | Needs `y ∈ box ↔ y 0 ∈ Icc 0 1 ∧ tail y ∈ box_k` and `Q x y = L x (y 0) + H x (tail y)`. Every pair is hit by `Fin.cons` (`cons_zero`, `tail_cons`). Θ(x) ∋ cons 0 t*, so it is nonempty. |
| L4 binary bijection | CONFIRMED | `finFunctionFinEquiv : (Fin n → Fin m) ≃ Fin (m ^ n)` (Algebra/BigOperators/Fin.lean:577). `finFunctionFinEquiv_apply` (:607) is a `rfl` lemma: `↑(e f) = ∑ i, ↑(f i) * m ^ (i : ℕ)`. The exponent is 0-indexed, `2^j` for `j : Fin r`, which matches the paper's `2^{j−1}` for j = 1..r. With m = 2, `Fin (2^r)` gives every n < 2^r as Σ_j 2^j b_j via `.symm` and `apply_symm_apply`. |
| L5 subset sums ↔ binary t | CONFIRMED | `Finset.sum_ite_mem` (to_additive of `prod_ite_mem`, Piecewise.lean:103) gives `∑ i ∈ s, if i ∈ t then f i else 0 = ∑ i ∈ s ∩ t, f i`. `sum_filter` holds as cited. |
| L6 formula (21) | CONFIRMED | On Θ(x), H(x, tail y) = m(x), so P = 1 − y₀(m+1) ∈ {1, −m}. If x is not binary, every y₀ = 0 and φ = 1. If x is binary, both z = 0 and z = 1 occur, and since m ≥ 0 ⇒ −m ≤ 0 < 1, φ = min(1, −m) = −m. The EReal ⨅ is attained at `cons 1 t*`. Lean pitfall: `biInf_const` needs the integrand to be syntactically constant. Since `P x y` only equals 1 on the set, use `le_antisymm` with `iInf₂_le`/`le_iInf₂` (or `iInf₂_congr` first). |
| L7 YES ⇒ inf < 0 | CONFIRMED | Contradiction chain: m = 0 → t binary with G t = S → S = Σ_I q (`Nat.cast_inj`). Then `iInf_lt_iff` and `EReal.coe_neg'`. |
| L8 NO ⇒ inf = 0 attained | CONFIRMED | φ ≥ 0 everywhere and φ(0) = 0. The inf is a min: φ takes the value 1 off {0,1}^r and finitely many values ≤ 0 on it. |
| L9 Lemma 3.3(c) | CONFIRMED | |
| L10 degree ≤ 5 | CONFIRMED | deg H ≤ 4, deg L ≤ 5, deg P ≤ 1 + 4. Exactly 5 needs r ≥ 1 (z x_j⁴ in Q) and k ≥ 1 (z t_i⁴ in P). For k = 0, deg P = 3 (if r ≥ 1). |
| L11 coefficient bound | CONFIRMED (math); effort estimate plausible | My own table is in §C.6. Every coefficient of H, L, Q, P has absolute value ≤ max(2M², M²+1) ≤ 2(M²+1). The sharp value 2M² needs M ≥ 1, which holds for positive data, and in Lean ℕ always, because `2^(r-1) ≥ 1` even at r = 0 (truncated subtraction). |
| L12 reduction map over ℤ | CONFIRMED with a fix | See C.1 (ℤ → EReal coercion) and E.4 (unify `eval ∘ map` and `aeval`). |
| Theorem 3.2 as Option 1 | CONFIRMED | §F |

## C. Corrections

1. **`BilevelInstance.Yes := I.optVal < (I.c : EReal)` with `c : ℤ`.**
   EReal derives only `AddCommMonoidWithOne` (Data/EReal/Basic.lean:36–39), and grep finds no `IntCast` in
   Data/EReal/. The ℤ→ℝ coercion is the `IntCast` coe (a tail coercion), and ℝ→EReal is `Coe ℝ EReal`
   (Basic.lean:46). Lean does not chain a `Coe` after a tail coercion. Fix: `I.optVal < ((I.c : ℝ) : EReal)`.
   `Set.Icc (I.lo i : ℝ) (I.hi i)` is fine. I have no toolchain, so this verdict is "almost surely", not
   compiled.
2. **"no `Equiv.piFinSucc` found…; `Fin.consEquiv`/`piFinSuccAbove` only appear in MeasureTheory"** is wrong.
   `Fin.consEquiv (α : Fin (n+1) → Type*) : α 0 × (∀ i, α i.succ) ≃ ∀ i, α i` is at
   Data/Fin/Tuple/Basic.lean:184 and is used in Basic/Countable, CategoryTheory and RepresentationTheory.
   `Fin.insertNthEquiv` also exists. Only `MeasurableEquiv.piFinSuccAbove` is measure-theoretic. The
   recommended `Fin.cons`/`Fin.tail` route is still fine, and `Fin.consEquiv` is an equally cheap
   alternative for L0/L3.
3. **Paper error #6** ("the paper never states Θ(x) ≠ ∅") is only partly right. Corollary 2.9 (paper_html
   269) states, for continuous P, Q and compact Y, that Θ(x) ≠ ∅ and that P(x,·) attains its minimum on Θ(x).
   The proof of Lemma 3.3 simply does not invoke it. Reword as "not invoked; follows from Cor. 2.9 or
   directly from L2.d/L3".
4. **Paper error #15** is not an error. The paper only says "this proof cannot be extended" to the
   pessimistic case. That is correct: pessimistic φ_p is usc for continuous P, Q and compact Y, and this
   φ is not usc at binary points. The report's own text agrees. Reclassify as a remark ("pessimistic
   hardness is not addressed").
5. **Paper error #13** is a wording issue only. The preceding sentence defines "the quantified 3-CNF-SAT
   problem" (∀X∃Y φ), so "the 3-CNF-SAT problem" is a sloppy back-reference, not a wrong claim. Keep it as a
   typo. The report's facts about EW are confirmed from ew.txt: the source problem is "2-Quantified
   3-CNF-Sat" with |X| = |Y| = s, there are 4s+3t XYC items, R = U, r = s.
6. **Coefficient table (confirming report §3 item 7, with explicit expansion).** Use 0-based j and
   F − G = R + Σ_j 2^j x_j − Σ_i q_i t_i, with 2^j ≤ 2^{r−1} ≤ M, q_i ≤ M, R ≤ M.
   - (F−G)² terms: R² (≤M²); x_j: 2R·2^j (≤2M²); t_i: −2Rq_i (≤2M²); x_j²: 4^j (≤M²);
     x_jx_{j'} (j<j'): 2^{j+j'+1} (≤2M²); t_i t_{i'} (i<i'): 2q_iq_{i'} (≤2M²); x_j t_i: −2^{j+1}q_i (≤2M²);
     t_i²: q_i².
   - (t_i−t_i²)² terms: t_i² + (−2)t_i³ + t_i⁴. Only t_i² collides, giving q_i²+1 ≤ M²+1.
   - L terms: z³ − 2z² + z + Σ_j(z x_j² − 2z x_j³ + z x_j⁴). Coefficients are in {1,−2}. L and H share no
     monomial (z-degree ≥ 1 vs 0).
   - P = 1 − z − zH: constant 1; z: −(1+R²) (≤M²+1); z·μ for μ ≠ 1 in supp H: −coeff_μ H.
   - Hence every coefficient lies in [−2(M²+1), 2(M²+1)] as the paper claims. Point (5) of the task is
     confirmed: P's bound equals H's bound up to the merged z-term.
7. **§1.3 "decidable in PSPACE/EXP"** is unverified and not needed. Replace it with: "YES ⇔ ∃(x,y) ∀y' ∈ Y
   [y ∈ Y ∧ Q(x,y) ≤ Q(x,y') ∧ P(x,y) < c], an ∃∀ sentence over ℝ (decidable by Tarski; no Σ₂ᵖ upper bound
   is claimed)". This equivalence is exactly `iInf_lt_iff` applied twice to the EReal `optVal`, which is a
   nice sanity check of the encoding.
8. **Paper error #12.** The STACS'12 PDF (ew.txt 305–313) has the relevant results as Lemma 7 and Lemma 8,
   with "will be proved in the full version". The journal version exists: Theory Comput. Syst.
   53(4):569–582, 2013, doi:10.1007/s00224-013-9445-4 (confirmed by web search). The report's guess that
   "Lemma 3.3/3.4" refers to the journal numbering remains unverified, because I did not see the journal
   text. Mark it as such.

Paper-error claims 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 14 are CONFIRMED against the text:
- 1: "z ∈ ℝ^r … y ∈ ℝ^{r+k}".
- 2: Σ_{j=1}^k (t_i(1−t_i))².
- 3: "0" vs "{0,1}".
- 4: "φ(x) ∈ −H(x,t(x))".
- 11: Appendix D's displayed ∀S∃I (R ≤ S ≤ … and S = Σ) is literally false. The correct form is
  ∀S (R ≤ S ≤ R+2^r−1 → ∃I …).
- 14: no coefficient domain is specified.
- 9: "deg = 5" needs r, k ≥ 1.
- 10: positivity of q_i, R, r and r ≤ k is unused in the math; r ≤ k is used only in the size paragraph
  ("at least k ≥ r bits").

The bibliography is confirmed against paper_html: [18] Caprara–Carvalho–Lodi–Woeginger, SIAM J. Optim.
24(2):823–838, 2014; [26] Eggermont–Woeginger, STACS'12, LIPIcs 14, 374–383; [30] Jeroslow, Math. Prog.
32:146–164, 1985 (cited only in Appendix B); [41] Lodi–Ralphs–Woeginger; [49] Stockmeyer, TCS 3(1), 1976;
[5] Arora–Barak 2009.

## D. Mathlib citation check

All paths are relative to `Mathlib/`.

| Declaration | Exists | file:line verified | Adequate | Note |
|---|---|---|---|---|
| `finFunctionFinEquiv`, `finFunctionFinEquiv_apply` | yes | Algebra/BigOperators/Fin.lean:577, 607 | yes | 0-indexed `m ^ (i:ℕ)` |
| `Fin.tail/cons/tail_cons/cons_succ/cons_zero/cons_self_tail` | yes | Data/Fin/Tuple/Basic.lean:107,114,117,121,129,171 | yes | `Fin.consEquiv` :184 also available |
| `mul_eq_one_iff_of_one_le` → `add_eq_zero_iff_of_nonneg` | yes | Algebra/Order/Monoid/Unbundled/Basic.lean:800 | yes | additive name used in NumberTheory/Dioph.lean:222 |
| `Finset.sum_sq_eq_zero_iff` | yes | Algebra/Order/BigOperators/Ring/Finset.lean:92 | yes | `∀ i ∈ s` form |
| `Finset.sum_nonneg` | yes | Algebra/Order/BigOperators/Group/Finset.lean:161 (attr), 162 (theorem `one_le_prod`) | yes | off by one line |
| `prod_eq_one_iff_of_one_le` → `sum_eq_zero_iff_of_nonneg` | yes | same file :239–240 | yes | |
| `MvPolynomial.continuous_eval` | yes | Topology/Algebra/MvPolynomial.lean:31 | yes | |
| `IsCompact.exists_isMinOn` | yes | Topology/Order/Compact.lean:255 | yes | needs `s.Nonempty`, `ContinuousOn` |
| `isCompact_univ_pi` | yes | Topology/Compactness/Compact.lean:1172 | yes | |
| `isCompact_Icc` / export / ℝ instance | yes | Topology/Order/Compact.lean:53, 55, 77 | yes | |
| `Set.mem_pi`, `Set.mem_univ_pi`, `Set.mem_Icc`, `Set.univ_pi_nonempty_iff` | yes | Data/Set/Operations.lean:281,283; Order/Interval/Set/Defs.lean:81; Data/Set/Prod.lean:656 | yes | |
| `IsMinOn`, `isMinOn_iff`, `IsMinOn.add` | yes | Order/Filter/Extr.lean:112,129,447 | yes | |
| `sq_nonneg`, `pow_eq_zero_iff`, `mul_self_eq_zero`, `mul_eq_zero` | yes | Algebra/Order/Ring/Unbundled/Basic.lean:608; Algebra/GroupWithZero/Basic.lean:253; Algebra/GroupWithZero/Defs.lean:315,293 | yes | |
| `Fin.prod_univ_succ`/`sum_univ_succ`, `prod_univ_two` | yes | Algebra/BigOperators/Fin.lean:76,111 | yes | |
| `Finset.prod_ite_mem`/`sum_ite_mem`, `prod_filter`/`sum_filter` | yes | Algebra/BigOperators/Group/Finset/Piecewise.lean:103; Algebra/BigOperators/Group/Finset/Basic.lean:333 | yes | `sum_ite_mem` needs `DecidableEq ι` (Fin k: ok) |
| `Nat.cast_sum`, `Finset.sum_mul_sum` | yes | Algebra/BigOperators/Ring/Finset.lean:344, 65 | yes | |
| `biSup_const` (to_dual → `biInf_const`) | yes | Order/CompleteLattice/Basic.lean:424–425 | yes, see L6 pitfall | |
| `le_iSup`→`iInf_le`, `iSup_le`→`le_iInf`, `le_iSup₂`→`iInf₂_le`, `iSup₂_le`→`le_iInf₂` | yes | Order/CompleteLattice/Basic.lean:210–240 (to_dual attrs) | yes | |
| `lt_sSup_iff`/`lt_iSup_iff` → `sInf_lt_iff`/`iInf_lt_iff` | yes | Order/CompleteLattice/Defs.lean:314, 318–319 | yes | |
| EReal `CompleteLinearOrder` | yes | Data/EReal/Basic.lean:36–39 | yes | no `IntCast` (C.1) |
| `EReal.coe_le_coe_iff/coe_lt_coe_iff/coe_eq_coe_iff/coe_zero/coe_one/coe_nonneg/coe_nonpos/coe_neg'` | yes | Data/EReal/Basic.lean:55,61,67,103,106,342,346,354 | yes | |
| `EReal.coe_neg` | yes | Data/EReal/Operations.lean:220 | yes | |
| `MvPolynomial.totalDegree_C/one/X/add/mul/pow/finsetSum` | yes | Algebra/MvPolynomial/Degrees.lean:457,465,469,474,503,511,545 | yes | `totalDegree_X` needs `Nontrivial` (ℤ ok) |
| `totalDegree_neg/sub`, `eval_sub/neg`, `coeff_neg/sub` | yes | Algebra/MvPolynomial/CommRing.lean:216,219,163,170,68,72 | yes | |
| `eval_C/X/add/mul/pow/sum`, `map_C/X`, `coeff_map`, `eval_map` | yes | Algebra/MvPolynomial/Eval.lean:271,275,286,289,292,295,337,345,384,432 | yes | add `eval₂_eq_eval_map` :352, `aeval_def` :575 |
| `X_pow_eq_monomial`, `monomial_single_add`, `coeff_add/sum/monomial/C_mul/mul`, `as_sum` | yes | Algebra/MvPolynomial/Basic.lean:249,255,537,572,580,644,650,965 | yes | |
| `ManyOneReducible`, `ManyOneEquiv`, `ManyOneDegree` | yes | Computability/Reduce.lean:41,131,306 | as described | |
| `Turing.TM2ComputableInPolyTime`, `idComputableInPolyTime` | yes | Computability/TuringMachine/Computable.lean:174, 216 | as described | |
| `Computability.Encoding`, `encodingNatBool` | yes | Computability/Encoding.lean:38,131 | yes | |
| `Fin.forall_fin_two`, `Nat.lt_two_pow_self` | used in Mathlib | Data/Fin/Tuple/Basic.lean:1351, Data/Nat/BitIndices.lean:135 (uses) | yes | defined upstream |
| P/NP/Σ₂ᵖ, poly-time reductions | NOT IN MATHLIB | grep of `Computability/` finds only Computable.lean | confirmed | |
| Glue lemma (not cited by the report) | `RingHom.eq_intCast'` | Data/Int/Cast/Lemmas.lean:347 | needed to identify `algebraMap ℤ ℝ` with `Int.castRingHom ℝ` | |

Nothing cited was MISSING or MISUSED.

## E. Missed issues

1. **Paper gap, proof of Observation 1.** The paper says z = 0 is always a minimizer and z = 1 is "another
   possibility" when x is binary. It never excludes z ∈ (0,1), which is needed for Z(x) = {0} or {0,1}
   exactly. The fix is trivial ((z−1)² > 0 ⇒ L > 0) and is covered by L1.c, but the report's error list
   does not mention it.
2. **Paper gap, Appendix D completeness.** It concludes that "¬SSI is Π₂ᵖ-complete … SSI Σ₂ᵖ-complete" from
   a hardness reduction alone. Membership (guess S, then check all I) is never argued. The report supplies
   it in §7.2 but does not list it as a gap.
3. **Paper gap, Appendix D use of EW.** In EW, Lemmas 7–8 quantify over item sets J of all items, including
   the dummies D₀, D₁. Restricting to the k = 4s+3t XYC items, which is what the SSI instance contains,
   uses Lemma 6(iii): w(I₀) < w(J) < w(I₁) ⇒ J has no dummy. The paper uses this silently. Appendix D also
   calls the target "an instance of the captive queen problem of the following forms" while displaying a
   subset-sum statement.
4. **Lean: two evaluation encodings.** §5.2 uses `eval (Sum.elim x y) (map (Int.castRingHom ℝ) Pp)` and §5.4
   uses `aeval (Sum.elim x y) I.P`. Pick one (I suggest `aeval`). The glue is `aeval_def` (Eval.lean:575),
   `RingHom.eq_intCast'` (Data/Int/Cast/Lemmas.lean:347) and `eval₂_eq_eval_map` (Eval.lean:352).
5. **Lean: empty box.** `BilevelInstance` allows lo i > hi i. The box is then empty, Θ = ∅, φ ≡ ⊤ and
   optVal = ⊤, so Yes is false. This is harmless for hardness. Optionally add `hlohi : lo ≤ hi` for
   fidelity to "bounded box", but do not require it in the theorem.
6. **Upper-level feasible set.** (BP) minimizes over x ∈ 𝒳. Section 3 implicitly takes 𝒳 = ℝ^n, since
   Lemma 3.3 has x ∈ ℝ^r. The blueprint should say this explicitly, because the baseline `valueFun` has no 𝒳.
7. **Restricting the instance class strengthens hardness.** Choosing ℤ (not ℚ) for c and the box endpoints,
   and positive-free ℕ data for SSI, gives the strongest hardness statement. Hardness on a restricted
   input class implies hardness for any superset format via the identity embedding. This answers the
   report's open question 1: ℤ.

## F. Route assessment and recommendation

The report's route is the cheapest correct one, and I found no materially simpler route:
1. Define P, Q over ℤ. Prove the function-level identities once by `simp`, then do all analysis on explicit
   real functions L, H.
2. Use L0 via `Fin.cons`/`Fin.tail` (or `Fin.consEquiv`) for separability.
3. Use `finFunctionFinEquiv` for the binary encoding.
4. Use the EReal `iInf_lt_iff` / `le_antisymm` style.

Possible lower-degree variants, such as Σ t_i(1−t_i) in place of its square (valid on [0,1]), lower deg P
only. deg Q stays 5 because x is unconstrained and s(x) must have degree 4. Formalize the paper's verbatim
construction and mention the variant at most in a remark.

For Theorem 3.2, Option 1 is correct for a blueprint. Formalize:
- `reduce : SSI → BilevelInstance` (n = r, m = k+1, lo = 0, hi = 1, c = 0);
- `reduce_correct : (reduce I).Yes ↔ I.Yes`;
- `reduce_deg ≤ 5`;
- optionally `reduce_coeff_bound`.

State "polynomial time" and "Σ₂ᵖ-hard" informally, with SSI hardness cited to [26] (journal version) and
[18]. The `BilevelInstance` type is sound with the C.1 fix (`((c:ℝ):EReal)`): ℤ coefficients as
`MvPolynomial (Fin n ⊕ Fin m) ℤ`, degree bound as fields, box `[lo,hi]`, upper level unconstrained.
L11 (coefficient bound) is optional. If it is wanted, the sharp table in C.6 is the specification.

## G. Escalate to orchestrator

1. Make sure all reports use the same `valueFun`/`argminSet` and the same "optimal value" definition
   (`⨅ x, valueFun …` in EReal, with 𝒳 = ℝ^n). R6 relies on exactly the baseline.
2. If another report formalizes Corollary 2.9 (nonempty Θ, attainment, lsc for compact Y), R6's L2.d/L3
   nonemptiness could cite it. The direct proof is also S-effort, so this is optional.
3. Remark (i), the lsc of the explicit φ, links Section 3 to Theorem 2.15. It is optional and should
   follow whichever lsc/EReal conventions R4 uses.
4. Lean coercion hazard for all reports: there is no `IntCast`/`RatCast` into `EReal`. Always go through ℝ.

Sources (web): https://research.tue.nl/en/publications/motion-planning-with-pulley-rope-and-baskets-2/ ,
https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2012.374
