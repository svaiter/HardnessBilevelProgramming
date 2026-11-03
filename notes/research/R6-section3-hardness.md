# R6 — Section 3: computational hardness (Theorem 3.2, Lemma 3.3, Appendix D)

Paper: Bolte, Lê, Pauwels, Vaiter, "Geometric and computational hardness of bilevel programming", arXiv:2407.12372v2.
Sources read: `paper_html.txt` lines 1060–1215 (Section 3 in full), 1286–1296 (Appendix B, last two
paragraphs), 1324–1337 (Appendix D), reference list entries [5], [18], [26], [30], [41], [49];
`paper.txt` lines 1270–1290 (to recover the `< 0` symbols that the HTML extraction swallowed).
Mathlib checkout: `<SCRATCH>/mathlib/mathlib4/Mathlib` (commit 1df8067a). All paths below are relative to that
directory unless stated otherwise.

Notation used throughout: `<SCRATCH> = /tmp/claude-0/-home-user-HardnessBilevelProgramming/418e0315-f899-5121-bf9e-35c4125b9a45/scratchpad`.
Indices are 0-based in Lean (`j : Fin r` carries weight `2^j`), 1-based in the paper (`2^{j-1}`); this
changes nothing.

---

## 1. Scope

### 1.1 Problem 3.1 (subset sum interval, SSI)

Instance: `k : ℕ`, `q : Fin k → ℕ` (paper: positive integers), `R r : ℕ` (paper: positive, `r ≤ k`).
Question (YES iff):
```
∃ S : ℕ, R ≤ S ∧ S < R + 2^r ∧ ∀ I : Finset (Fin k), ∑ i ∈ I, q i ≠ S
```
Lean-style:
```lean
structure SSI where
  k : ℕ
  q : Fin k → ℕ
  R : ℕ
  r : ℕ

def SSI.subsetSum (P : SSI) (S : ℕ) : Prop := ∃ I : Finset (Fin P.k), ∑ i ∈ I, P.q i = S
def SSI.Yes (P : SSI) : Prop := ∃ S, P.R ≤ S ∧ S < P.R + 2 ^ P.r ∧ ¬ P.subsetSum S
```
`S < R + 2^r` replaces `S ≤ R + 2^r − 1` to avoid ℕ-subtraction. None of "q_i > 0", "R > 0", "r > 0",
"r ≤ k" is used by the mathematics of Lemma 3.3; `r ≤ k` is used only in the informal size argument
(coefficient `2^{r-1}` has `r ≤ k ≤ |input|` bits). So the Lean lemma is stated without these hypotheses.

### 1.2 Lemma 3.3 (the construction), precise statement

Given an SSI instance `(k, q, R, r)`, put `M := max (max_i q_i) (2^(r-1)) R` and define, for
`x : Fin r → ℝ`, `z : ℝ`, `t : Fin k → ℝ`:
```
F x     := R + ∑ j, 2^j * x j                                  (paper: R + Σ_{j=1}^r 2^{j-1} x_j)
G t     := ∑ i, t i * q i
H x t   := ∑ i, (t i * (1 - t i))^2 + (F x - G t)^2
L x z   := z * ((z - 1)^2 + ∑ j, ((1 - x j) * x j)^2)
Q x z t := L x z + H x t
P x z t := 1 - z * (H x t + 1)
Y       := [0,1] × [0,1]^k   (as a subset of ℝ^{k+1}: y 0 = z, y i.succ = t i)
```
Claims (all verified below):
(a) `P, Q` are polynomials in `(x, z, t)` with integer coefficients, `totalDegree ≤ 5` (and `= 5` when
    `r ≥ 1` for Q, `k ≥ 1` for P), every coefficient in `[-2(M^2+1), 2(M^2+1)]` (in fact in `[-2M^2, 2M^2]`,
    see §3 item 7).
(b) Let `φ x := valueFun P Q Y x` (optimistic). Then `Θ(x) ≠ ∅` for all `x`, `φ` is real-valued,
    `φ x = 1` if `x ∉ {0,1}^r`, and `φ x = -m x ≤ 0` if `x ∈ {0,1}^r`, where `m x := min_{t ∈ [0,1]^k} H x t`.
(c) `(⨅ x, φ x) < 0 ↔ SSI.Yes`, and `¬ SSI.Yes → (⨅ x, φ x) = 0` (attained).

Lean-style signature (with the baseline `valueFun` of the brief):
```lean
theorem lemma33 (P : SSI) :
    ((⨅ x : Fin P.r → ℝ, valueFun (Pfun P) (Qfun P) (box P.k) x) < (0 : EReal)) ↔ P.Yes
theorem lemma33_no (P : SSI) (h : ¬ P.Yes) :
    (⨅ x : Fin P.r → ℝ, valueFun (Pfun P) (Qfun P) (box P.k) x) = (0 : EReal)
```
where `Pfun P x y := eval (Sum.elim x y) (Ppoly P)` etc. (see §5 for the concrete encoding).

### 1.3 Theorem 3.2 (what the paper states)

"Given two polynomials P and Q of degree at most five, a bounded box lower-level feasible set Y and a
constant c, deciding whether the optimal value of the corresponding bilevel problem of (P,Q,Y) is
strictly smaller than c is Σ₂ᵖ-hard."
Decision problem `BILEVEL₅`: instance = `(n, m, P, Q, lo, hi, c)` with `P Q : MvPolynomial (Fin n ⊕ Fin m) ℤ`
of total degree ≤ 5, `lo hi : Fin m → ℤ`, `c : ℤ`; YES iff `⨅ x, valueFun P Q (Icc-box lo hi) x < c`.
(The paper does not specify the coefficient domain of the inputs; integers are forced by Lemma 3.3 and
by the need for a finite encoding. Rationals would work equally.) The paper claims Σ₂ᵖ-hardness only,
NOT membership in Σ₂ᵖ (correct: membership is not clear — the problem is a sentence of the first-order
theory of the reals with alternating quantifiers, decidable in PSPACE/EXP; no Σ₂ᵖ upper bound is claimed).

### 1.4 What is formalizable vs what must be assumed

- Lemma 3.3 (a)(b)(c): fully formalizable in Mathlib now (no semialgebraic geometry needed). This is
  the entire mathematical content of Section 3.
- Theorem 3.2: the complexity-theoretic wrapper ("Σ₂ᵖ-hard", "polynomial-time reduction") has NO
  Mathlib support beyond a bare `TM2ComputableInPolyTime` structure (see §4). Recommendation (§6/§7):
  do not formalize the wrapper; formalize the reduction map as a computable Lean function
  `SSI → BilevelInstance` plus the correctness equivalence and the size lemmas, and state the
  complexity conclusion informally in the blueprint (Option 1).
- Appendix D (Σ₂ᵖ-hardness of SSI): cited, not proven; outside scope of any formalization without a
  complexity framework. Blueprint cites it.

---

## 2. Proof route (DAG of lemmas)

The DAG, bottom-up. Dependencies in brackets. "x binary" means `∀ j, x j = 0 ∨ x j = 1`.

### L0 — Generic separable-argmin lemma (no dependencies)
Statement. `A : Set α`, `B : Set β`, `f : α → ℝ`, `g : β → ℝ`. For `(a, b) ∈ A ×ˢ B`:
`IsMinOn (fun p => f p.1 + g p.2) (A ×ˢ B) (a, b) ↔ IsMinOn f A a ∧ IsMinOn g B b`.
Proof. (⇒) For `a' ∈ A`: `(a', b) ∈ A ×ˢ B`, so `f a + g b ≤ f a' + g b`, hence `f a ≤ f a'`
(`add_le_add_iff_right`). Symmetric for `b'`. (⇐) `f a ≤ f a'` and `g b ≤ g b'`, add (`add_le_add`).
NOTE: no nonemptiness hypothesis is needed in either direction (the paper's (20) needs none either —
if one argmin is empty both sides are empty).
Lean shape: lower variable is `y : Fin (k+1) → ℝ`, not a product; two options: (i) state L0 directly
for `Q y = f (y 0) + g (Fin.tail y)` on `{y | y 0 ∈ A ∧ Fin.tail y ∈ B}` using `Fin.cons`, `Fin.cons_zero`,
`Fin.tail_cons`, `Fin.cons_self_tail` (Data/Fin/Tuple/Basic.lean:114,129,117,171) — recommended; (ii)
prove on `α × β` and transport along an equivalence `(Fin (k+1) → ℝ) ≃ ℝ × (Fin k → ℝ)` (no
`Equiv.piFinSucc` found by grep in this checkout; `Fin.consEquiv`/`piFinSuccAbove` only appear in
MeasureTheory — NOT worth it). Effort S.

### L1 — Analysis of L (depends: nothing)
Let `A x z := (z-1)^2 + ∑ j, ((1 - x j) * x j)^2 ≥ 0` (`sq_nonneg`, `Finset.sum_nonneg`, `add_nonneg`).
(L1.a) `z ∈ Icc 0 1 → 0 ≤ L x z` (`mul_nonneg`).
(L1.b) `L x 0 = 0`.
(L1.c) `L x z = 0 ↔ z = 0 ∨ (z = 1 ∧ x binary)`:
   `mul_eq_zero`; `A x z = 0 ↔ (z-1)^2 = 0 ∧ ∑ = 0` (`add_eq_zero_iff_of_nonneg`, generated by
   `to_additive` from `mul_eq_one_iff_of_one_le`, Algebra/Order/Monoid/Unbundled/Basic.lean:800);
   `(z-1)^2 = 0 ↔ z = 1` (`pow_eq_zero_iff`, `sub_eq_zero`); `∑ j, ((1-x j) * x j)^2 = 0 ↔ ∀ j, (1 - x j) * x j = 0`
   (`Finset.sum_sq_eq_zero_iff`, Algebra/Order/BigOperators/Ring/Finset.lean:92) `↔ ∀ j, x j = 1 ∨ x j = 0`
   (`mul_eq_zero`, `sub_eq_zero`).
(L1.d) For `z ∈ Icc 0 1`: `IsMinOn (L x) (Icc 0 1) z ↔ L x z = 0`. (⇒) compare with `z' = 0`:
   `L x z ≤ L x 0 = 0` and `L x z ≥ 0`. (⇐) `0 = L x z ≤ L x z'` by (L1.a).
(L1.e) Hence `Z x := {z ∈ Icc 0 1 | IsMinOn (L x) (Icc 0 1) z} = if x binary then {0,1} else {0}`.
Effort S–M (mostly `simp`/`nlinarith`-free algebra, needs care with `Finset.sum` zero lemmas).

### L2 — Analysis of H (depends: nothing)
(L2.a) `0 ≤ H x t` for all `t` (sum of squares; `Finset.sum_nonneg`, `sq_nonneg`, `add_nonneg`).
(L2.b) `H x t = 0 ↔ t binary ∧ F x = G t` (same lemmas as L1.c: `add_eq_zero_iff_of_nonneg`,
   `Finset.sum_sq_eq_zero_iff`, `mul_eq_zero`, `sub_eq_zero`, `pow_eq_zero_iff`).
(L2.c) Continuity of `t ↦ H x t`: via `MvPolynomial.continuous_eval` (Topology/Algebra/MvPolynomial.lean:31)
   if H is defined as an `MvPolynomial` evaluation, else by `fun_prop`/`continuity` on the explicit formula.
(L2.d) Existence of a minimizer: `IsCompact.exists_isMinOn` (Topology/Order/Compact.lean:255) applied to
   `isCompact_univ_pi (fun _ => isCompact_Icc)` (Topology/Compactness/Compact.lean:1172;
   `isCompact_Icc` is the field of class `CompactIccSpace`, Topology/Order/Compact.lean:53, exported at :55)
   and nonemptiness `⟨0, by simp [Set.mem_univ_pi]⟩`. Define `m x := H x t*` for a chosen minimizer
   (`Classical.choose`) or, cleaner, avoid `m` and work with the set `T x := {t ∈ box | IsMinOn (H x) box t}`
   and the fact that H is constant on it (two minimizers have equal values: `le_antisymm`).
(L2.e) `0 ≤ m x`; `m x = 0 ↔ ∃ t ∈ box, H x t = 0` (⇐: `m ≤ H x t = 0` and `m ≥ 0`; ⇒: the minimizer).
Effort S.

### L3 — Separability (20) (depends: L0, L1, L2)
`y ∈ argminSet Q box x ↔ y ∈ box ∧ y 0 ∈ Z x ∧ Fin.tail y ∈ T x`, where
`box = Set.pi univ (fun _ => Icc 0 1)` on `Fin (k+1) → ℝ`; membership unfolds via `Set.mem_univ_pi`
(Data/Set/Operations.lean:283) and `Fin.forall_fin_succ`-style splitting (`y 0 ∈ Icc 0 1 ∧ ∀ i, y i.succ ∈ Icc 0 1`).
Proof: unfold `argminSet` (brief's definition) to `IsMinOn (Q x) box y`, apply L0 with
`f = L x`, `g = H x`, `A = Icc 0 1`, `B = univ.pi (Icc 0 1)`. Effort S (given L0).
Corollary: `argminSet Q box x` is nonempty (`Fin.cons 0 t*`), so `Θ(x) ≠ ∅` and `φ` is never `⊤`.

### L4 — Binary-expansion bijection (5) (depends: nothing)
Mathlib route (cleanest found): `finFunctionFinEquiv : (Fin n → Fin m) ≃ Fin (m ^ n)` with
`finFunctionFinEquiv_apply : (finFunctionFinEquiv f : ℕ) = ∑ i, ↑(f i) * m ^ (i : ℕ)`
(Algebra/BigOperators/Fin.lean:577, 607). Take `m = 2`.
(L4.a) Bridge: `x binary ↔ ∃ f : Fin r → Fin 2, x = fun j => ((f j : ℕ) : ℝ)`.
   (⇒) `f j := if x j = 0 then 0 else 1`; (⇐) `Fin 2` case split (`Fin.forall_fin_two`, used e.g. at
   NumberTheory/Height/Basic.lean:305; or `fin_cases`).
(L4.b) For `x = cast ∘ f`: `F x = ((R + finFunctionFinEquiv f : ℕ) : ℝ)` by `Nat.cast_add`,
   `Nat.cast_sum` (Algebra/BigOperators/Ring/Finset.lean:344, namespace `Nat`), `Nat.cast_mul`, `Nat.cast_pow`, `mul_comm`.
   Hence `F x` is a natural number `S` with `R ≤ S < R + 2^r` (`Fin.isLt`).
(L4.c) Conversely, for `S` with `R ≤ S < R + 2^r`: `n := S - R < 2^r`, `f := finFunctionFinEquiv.symm ⟨n, _⟩`,
   then `F (cast ∘ f) = R + n = S` by `Equiv.apply_symm_apply` and `Nat.add_sub_cancel'`.
Alternatives rejected: `Nat.binaryRec` (Data/Nat/BinaryRec.lean:88), `Nat.digits`/`Nat.ofDigits`
(Data/Nat/Digits/Defs.lean:214,240), `Nat.testBit` — all give lists/recursors, not a fixed-length
`Fin r`-indexed sum; `finFunctionFinEquiv` is exactly the needed statement. Effort S.

### L5 — Subset sums ↔ binary t (depends: nothing)
(L5.a) For `I : Finset (Fin k)`, `tI i := if i ∈ I then 1 else 0` is in the box, is binary, and
   `G tI = ((∑ i ∈ I, q i : ℕ) : ℝ)`: `Finset.sum_ite_mem` (Algebra/BigOperators/Group/Finset/Piecewise.lean:103,
   `∑ i ∈ s, (if i ∈ t then f i else 0) = ∑ i ∈ s ∩ t, f i`, with `univ ∩ I = I`), `Nat.cast_sum`.
(L5.b) For binary `t`, `I := univ.filter (fun i => t i = 1)` satisfies `G t = ((∑ i ∈ I, q i : ℕ) : ℝ)`
   (`Finset.sum_filter`, Algebra/BigOperators/Group/Finset/Basic.lean:333, plus the case split `t i = 0 ∨ 1`).
Effort S.

### L6 — Value function formula (21) (depends: L1.e, L2, L3)
`valueFun P Q box x = ((if x binary then -(m x) else 1 : ℝ) : EReal)`.
Proof. `valueFun = ⨅ y ∈ argminSet, (P x y : EReal)`. By L3, over the argmin set `H x (tail y) = m x`
(constant), so `P x y = 1 - y 0 * (m x + 1)`.
 - `x` not binary: every argmin `y` has `y 0 = 0`, so the integrand is the constant `1`; the set is nonempty
   (L3 corollary) ⇒ `⨅ = 1` by `biInf_const` (generated by `to_dual` from `biSup_const`,
   Order/CompleteLattice/Basic.lean:425; needs `Set.Nonempty`).
 - `x` binary: argmin = `{y ∈ box | y 0 ∈ {0,1} ∧ tail y ∈ T x}`; values are `1` (at `y 0 = 0`) and
   `-(m x)` (at `y 0 = 1`). Show `IsLeast` of the value set is `-(m x)` using `m x ≥ 0 ⇒ -(m x) ≤ 0 < 1`:
   `le_antisymm (iInf₂_le (Fin.cons 1 t*) _) (le_iInf₂ fun y hy => by rcases ... )`
   (`iInf_le`/`le_iInf` are `to_dual` duals of `le_iSup`/`iSup_le`, Order/CompleteLattice/Basic.lean:210–238;
   EReal order: `EReal.coe_le_coe_iff` Data/EReal/Basic.lean:55).
Effort M (EReal bookkeeping; the brief's `valueFun` is a bounded `iInf` in `EReal`).

### L7 — YES ⇒ inf < 0 (depends: L4.c, L2.b, L2.e, L5.b, L6)
Given `S` with `R ≤ S < R + 2^r` and `∀ I, ∑_I q ≠ S`: pick binary `x` with `F x = S` (L4.c). Claim `m x > 0`:
`m x ≥ 0` and `m x ≠ 0`, for if `m x = 0` then by L2.e there is `t ∈ box` with `H x t = 0`, by L2.b `t` is
binary and `G t = F x = S`, by L5.b `S = ∑_I q` for some `I` — contradiction. Then `φ x = -(m x) < 0` (L6),
and `⨅ x, φ x < 0` by `iInf_lt_iff` (`to_dual` of `lt_iSup_iff`, Order/CompleteLattice/Defs.lean:318;
`EReal` is a `CompleteLinearOrder` by `deriving`, Data/EReal/Basic.lean:36–39) and `EReal.coe_neg'`
(Data/EReal/Basic.lean:354: `(x : EReal) < 0 ↔ x < 0`). Effort S.

### L8 — NO ⇒ inf = 0, attained (depends: L4.b, L5.a, L2.b, L2.e, L6)
Assume `∀ S, R ≤ S → S < R + 2^r → ∃ I, ∑_I q = S` (negation of Yes, after `push_neg`).
 - For binary `x`: `S := F x` qualifies (L4.b) ⇒ `I` with `∑_I q = S`; `t := tI` (L5.a) has `H x t = 0`
   (L2.b: binary and `G t = S = F x`), so `m x = 0` (L2.e) and `φ x = 0` (L6).
 - For non-binary `x`: `φ x = 1 ≥ 0`.
 - So `∀ x, 0 ≤ φ x` and `φ 0 = 0` (the zero vector is binary) ⇒ `⨅ x, φ x = 0` by
   `le_antisymm (iInf_le _ 0 ▸ ...) (le_iInf ...)`. Effort S.

### L9 — Lemma 3.3 (c) (depends: L7, L8)
`(⨅ φ) < 0 ↔ Yes`: (⇐) L7; (⇒) contrapositive: `¬Yes ⇒ ⨅ φ = 0 ⇒ ¬ (⨅ φ < 0)` (`lt_irrefl`). Effort S.

### L10 — Polynomial shape: degree (depends: nothing; needs the MvPolynomial definitions of §5)
`totalDegree Ppoly ≤ 5`, `totalDegree Qpoly ≤ 5` by `totalDegree_add` (≤ max), `totalDegree_mul` (≤ sum),
`totalDegree_pow` (≤ n·deg), `totalDegree_finsetSum` (≤ sup), `totalDegree_X` (= 1 over nontrivial ring),
`totalDegree_C` (= 0), `totalDegree_one`, `totalDegree_sub`, `totalDegree_neg`
(Algebra/MvPolynomial/Degrees.lean:474,503,511,545,469,457,465; CommRing.lean:219,216).
Bookkeeping: `deg F ≤ 1`, `deg G ≤ 1`, `deg (t_i(1-t_i))^2 ≤ 4`, `deg H ≤ 4`, `deg L ≤ 1 + 4 = 5`,
`deg Q ≤ 5`, `deg P ≤ 1 + 4 = 5`. Exact equality `= 5` is NOT needed for Theorem 3.2 ("at most five") and
is false when `r = 0` (Q) or `k = 0` (P): do not formalize it. Effort S–M.

### L11 — Polynomial shape: coefficient bound (depends: §5 definitions) — OPTIONAL
Statement: `∀ μ, |coeff μ Ppoly| ≤ 2*(M^2+1)` and same for `Qpoly`, with `M = max (sup q) (max (2^(r-1)) R)`.
Verified by hand (§3 item 7, full monomial table). Lean cost is high because `coeff` of a squared sum of
`r+k+1` terms must be computed monomial by monomial: write `F - G = ∑_{a ∈ A} C (c a) * mono a` with
`A = Option (Fin r ⊕ Fin k)`, expand the square with `Finset.sum_mul_sum`
(Algebra/BigOperators/Ring/Finset.lean:65), use `coeff_sum` (Basic.lean:572), `coeff_C_mul` (:644),
`coeff_monomial` (:580), `X_pow_eq_monomial` (:249), `monomial_single_add` (:255), and the combinatorial
fact that each monomial of degree ≤ 2 is `mono a * mono b` for at most two ordered pairs `(a,b)`.
Cheaper sufficient alternative (if only "coefficients have polynomially many bits" is wanted): bound the
ℓ¹-norm `N p := ∑ μ ∈ p.support, |coeff μ p|` — submultiplicative and subadditive — giving
`|coeff| ≤ N(F−G)^2 + 2 ≤ (R + 2^r + k·max q)^2 + 2 ≤ (k+3)^2 M^2 + 2`, still `O(log k + log M)` bits.
Neither `N` nor its submultiplicativity is in Mathlib for `MvPolynomial` (grep: nothing). Effort L (sharp)
/ M (ℓ¹). Recommendation: state the sharp bound in the blueprint as the paper's claim, formalize only if
the complexity wrapper is pursued; it feeds nothing else.

### L12 — Integer coefficients and the reduction map (depends: §5)
Define `reduce : SSI → BilevelInstance` with `P Q : MvPolynomial (Fin r ⊕ Fin (k+1)) ℤ`, box `lo = 0`,
`hi = 1`, `c = 0`. Integrality is by construction (polynomials over ℤ, mapped to ℝ by
`MvPolynomial.map (Int.castRingHom ℝ)`; `map_C`, `map_X`, `coeff_map` at Algebra/MvPolynomial/Eval.lean:337,345,384;
`eval_map` at :432). The function `reduce` is a plain Lean definition, hence computable in the
informal sense; nothing more is asserted. Effort S.

---

## 3. Errors / gaps / typos in the paper, with fixes

1. **Proof of Lemma 3.3, first sentence**: "y = (z,t), z ∈ ℝ^r, t ∈ ℝ^k (which implies y ∈ ℝ^{r+k})"
   contradicts the statement (`y ∈ ℝ^{k+1}`, `Y = [0,1]^{k+1}`) and the later "z ∈ [0,1]". Fix: `z ∈ ℝ`
   is a scalar, `y ∈ ℝ^{k+1}`.
2. **Definition of H**: `∑_{j=1}^{k} (t_i(1−t_i))^2` — summation index `j`, summand index `i`.
   Fix: `∑_{i=1}^{k}`.
3. **Eq. (21)**: `z(x) := argmin_z L(x,z) = 0 if x ∉ {0,1}^r` mixes an element with a set
   (the other branch is the set `{0,1}`). Fix: `{0}`.
4. **Observation 2 text**: "φ(x) ∈ −H(x,t(x))" should be "φ(x) = −H(x,t(x)) = −min_t H(x,t)".
5. **Eq. (21) justification is incomplete**: the step from `z(x) = {0,1}` to `φ(x) = −H(x,t(x))` silently
   uses (i) that `t(x)` ranges over argmin_t H and H is constant (= its minimum) there, (ii) that the
   minimum over `[0,1]^k` exists (compactness + continuity, never mentioned), and (iii) that
   `min(1, −m) = −m` because `m ≥ 0`. All three are supplied in L2.d, L6.
6. **Observation 1, item 2** ("φ(x) ≤ 0 if x binary") is proved via "H is a sum of squares" — fine, but
   the paper never states `Θ(x) ≠ ∅` (needed for φ to be finite); it follows from L2.d/L3.
7. **Coefficient bound**: the claimed bound `2(M^2+1)` is correct but loose. Full monomial table of H
   (0-based j, so `2^j ≤ 2^{r-1} ≤ M` for `j ≤ r−1`):
   const `R^2 ≤ M^2`; `x_j`: `2R·2^j ≤ 2M^2`; `t_i`: `−2Rq_i`; `x_j^2`: `4^j ≤ M^2`;
   `x_j x_{j'}` (j<j'): `2^{j+j'+1} ≤ 2M^2`; `t_i^2`: `q_i^2 + 1 ≤ M^2 + 1` (the `+1` from `(t_i(1−t_i))^2`);
   `t_i t_{i'}`: `2q_i q_{i'} ≤ 2M^2`; `x_j t_i`: `−2·2^j q_i`, `|·| ≤ 2M^2`; `t_i^3`: `−2`; `t_i^4`: `1`.
   L: `z^3: 1`, `z^2: −2`, `z: 1`, `z x_j^2: 1`, `z x_j^3: −2`, `z x_j^4: 1` — all in `{1,−2}` as claimed.
   P = 1 − z − zH: const `1`, `z: −(R^2+1)` (|·| ≤ M^2+1), `z·(monomials of H)`: negated H-coefficients.
   No monomial of L occurs in H (every L-monomial contains z; H is z-free) — as claimed.
   Since `M ≥ 2^{r−1} ≥ 1`, `max |coeff| ≤ 2M^2 ≤ 2(M^2+1)`. Sharp value: `2M^2`.
8. **"all coefficients can be expressed by log M bits"**: should be `O(log M)` (`2 log₂ M + 2` bits).
   "we have polynomials of r variables": the variables number `r + k + 1`; the number of monomials of
   degree ≤ 5 in `r+k+1` variables is `C(r+k+6, 5)`, polynomial in `r + k`; the actual support has
   `O((r+k)^2)` monomials. The argument is fine, the wording is sloppy.
9. **Degree "exactly five"**: `deg Q = 5` needs `r ≥ 1` (monomial `z x_j^4`), `deg P = 5` needs `k ≥ 1`
   (monomial `z t_i^4`). Both hold under Problem 3.1's "positive r, r ≤ k", but Theorem 3.2 only needs
   "at most five". Formalize `≤ 5`.
10. **Hypotheses not used**: positivity of `q_i, R, r` and `r ≤ k` are never used in the proof of
    Lemma 3.3; `r ≤ k` is used only in the size argument (`2^{r−1}` has `r ≤ k` bits). The blueprint
    should state Lemma 3.3 without them.
11. **Appendix D, displayed formula**: "∀S, ∃I ⊆ {1..k}, R ≤ S ≤ R+2^r−1 and S = ∑_{i∈I} q_i" is false as
    written (it asserts every integer S lies in the interval). The negation of the SSI formula is
    `∀S, (R ≤ S ≤ R+2^r−1 → ∃I, S = ∑_{i∈I} q_i)`. Fix accordingly. (The Section 3.1 formula
    `∃S ∀I, R ≤ S ≤ R+2^r−1 ∧ S ≠ ∑_I q_i` is fine since the range condition does not depend on I.)
12. **Appendix D, citation "[26, Lemma 3.3 and Lemma 3.4]"**: in the STACS'12 version cited in the
    bibliography (Eggermont–Woeginger, LIPIcs 14, pp. 374–383) the relevant statements are **Lemma 7 and
    Lemma 8** (p. 379), and the text says "The following two lemmas will be proved in the full version of
    this paper" — i.e. the STACS version does not contain their proofs. The numbering 3.3/3.4 presumably
    refers to the journal version (Theory of Computing Systems 53 (2013) 569–582), which is not the one
    cited. Fix: cite the journal version, or cite Lemmas 7–8 of the STACS version and note the proofs
    are deferred. Verified from the LIPIcs PDF (saved at `<SCRATCH>/research/ew2012/ew.txt`, lines 196–325).
13. **Appendix D, "Since the 3-CNF-SAT problem is Π₂ᵖ complete"**: should read "2-Quantified 3-CNF-SAT
    (∀X∃Y φ)" — this is the problem Eggermont–Woeginger reduce from (Stockmeyer [49]); plain 3-CNF-SAT is
    NP-complete. Also the reduction in [26] yields `k = 4s + 3t` items (s = #X = #Y variables, t = #clauses),
    `R = U` (their constant U), `r = s`; so `r = s ≤ k` automatically.
14. **Theorem 3.2 statement**: does not say what coefficient domain the input polynomials have, nor how
    the "bounded box" and "constant c" are given. Fix (for the blueprint): integer (or rational)
    coefficients, integer (or rational) box endpoints and c; the reduction produces integer data with
    box `[0,1]^{k+1}` and `c = 0`.
15. **Closing remark on the pessimistic version** ("cannot be extended since ... upper-semicontinuous"):
    correct as a statement about THIS φ (it is lsc, not usc, see §2 D(ii) below), but it does not
    settle whether the pessimistic decision problem is Σ₂ᵖ-hard; the blueprint should say "open / not
    addressed", not "fails".

---

## 4. Mathlib inventory

| Need | Mathlib declaration | File:line | Note |
|---|---|---|---|
| Extreme value theorem (min of continuous on compact) | `IsCompact.exists_isMinOn` | Topology/Order/Compact.lean:255 | needs `s.Nonempty`, `ContinuousOn f s` |
| Compact box | `isCompact_univ_pi` | Topology/Compactness/Compact.lean:1172 | `IsCompact (pi univ s)` from `∀ i, IsCompact (s i)` |
| Compact interval | `isCompact_Icc` (field of `CompactIccSpace`, exported) | Topology/Order/Compact.lean:53,55 | instance for ℝ via `ConditionallyCompleteLinearOrder.toCompactIccSpace` :77 |
| Box membership | `Set.mem_univ_pi`, `Set.mem_pi`, `Set.mem_Icc` | Data/Set/Operations.lean:283,281; Order/Interval/Set/Defs.lean:81 | |
| Box nonempty | `Set.univ_pi_nonempty_iff` | Data/Set/Prod.lean:656 | |
| `IsMinOn` | `IsMinOn`, `isMinOn_iff`, `IsMinOn.add` | Order/Filter/Extr.lean:112,129,447 | |
| Polynomial eval continuous | `MvPolynomial.continuous_eval` | Topology/Algebra/MvPolynomial.lean:31 | |
| Sum ≥ 0 / sum of squares = 0 | `Finset.sum_nonneg` (to_additive of `one_le_prod`), `Finset.sum_sq_eq_zero_iff`, `Finset.sum_eq_zero_iff_of_nonneg` (to_additive of `prod_eq_one_iff_of_one_le`) | Algebra/Order/BigOperators/Group/Finset.lean:161; Algebra/Order/BigOperators/Ring/Finset.lean:92; Group/Finset.lean:239–240 | |
| `a+b=0`, `a,b≥0` | `add_eq_zero_iff_of_nonneg` (to_additive of `mul_eq_one_iff_of_one_le`) | Algebra/Order/Monoid/Unbundled/Basic.lean:800 | |
| squares | `sq_nonneg`, `pow_eq_zero_iff`, `mul_self_eq_zero`, `mul_eq_zero` | Algebra/Order/Ring/Unbundled/Basic.lean:608; Algebra/GroupWithZero/Basic.lean:253; Algebra/GroupWithZero/Defs.lean:315,293 | |
| Binary expansion bijection | `finFunctionFinEquiv`, `finFunctionFinEquiv_apply` | Algebra/BigOperators/Fin.lean:577,607 | `(Fin n → Fin m) ≃ Fin (m^n)`, value `∑ i, f i * m^i` |
| `Fin.cons`/`tail` | `Fin.cons`, `Fin.tail`, `Fin.cons_zero`, `Fin.cons_succ`, `Fin.tail_cons`, `Fin.cons_self_tail` | Data/Fin/Tuple/Basic.lean:114,107,129,121,117,171 | |
| `Fin` sums | `Fin.sum_univ_succ` (to_additive of `prod_univ_succ`), `Fin.sum_univ_two` | Algebra/BigOperators/Fin.lean:76,111 | |
| Subset sum ↔ indicator | `Finset.sum_ite_mem` (to_additive of `prod_ite_mem`), `Finset.sum_filter` (of `prod_filter`) | Algebra/BigOperators/Group/Finset/Piecewise.lean:103; Group/Finset/Basic.lean:333 | |
| Casts | `Nat.cast_sum` | Algebra/BigOperators/Ring/Finset.lean:344 | `Nat.cast_mul`, `Nat.cast_pow` in core/`Data/Nat/Cast` (not pinned, standard simp lemmas) |
| `EReal` complete linear order | `deriving ... CompleteLinearOrder` | Data/EReal/Basic.lean:36–39 | gives `iInf_lt_iff` etc. |
| `EReal` coercion order | `EReal.coe_le_coe_iff`, `coe_lt_coe_iff`, `coe_eq_coe_iff`, `coe_nonneg`, `coe_nonpos`, `coe_neg'`, `coe_neg`, `coe_zero`, `coe_one` | Data/EReal/Basic.lean:55,61,67,342,346,354,103,106; Data/EReal/Operations.lean:220 | |
| inf < c ↔ ∃ | `iInf_lt_iff` (to_dual of `lt_iSup_iff`), `sInf_lt_iff` (of `lt_sSup_iff`) | Order/CompleteLattice/Defs.lean:318,314 | `CompleteLinearOrder` |
| inf bounds | `iInf_le` (dual of `le_iSup`), `le_iInf` (dual of `iSup_le`), `le_iInf₂`, `iInf₂_le` | Order/CompleteLattice/Basic.lean:210–238 | |
| bounded inf of constant | `biInf_const` (dual of `biSup_const`) | Order/CompleteLattice/Basic.lean:424–425 | needs `s.Nonempty` |
| MvPolynomial eval | `eval_add`, `eval_mul`, `eval_pow`, `eval_sum`, `eval_X`, `eval_C`, `eval_sub`, `eval_neg`, `eval_map` | Algebra/MvPolynomial/Eval.lean:286,289,292,295,275,271,432; CommRing.lean:163,170 | |
| MvPolynomial degree | `totalDegree_add/mul/pow/finsetSum/X/C/one`, `totalDegree_sub/neg` | Algebra/MvPolynomial/Degrees.lean:474,503,511,545,469,457,465; CommRing.lean:219,216 | all `≤` bounds |
| MvPolynomial coeff | `coeff_add`, `coeff_sum`, `coeff_monomial`, `coeff_C_mul`, `coeff_mul`, `coeff_sub`, `coeff_neg`, `coeff_map`, `X_pow_eq_monomial`, `monomial_single_add`, `as_sum` | Algebra/MvPolynomial/Basic.lean:537,572,580,644,650,249,255,965; CommRing.lean:72,68; Eval.lean:384 | only for L11 |
| `map ℤ → ℝ` | `MvPolynomial.map`, `map_C`, `map_X` | Algebra/MvPolynomial/Eval.lean:337,345 | |
| Double sum expansion | `Finset.sum_mul_sum` | Algebra/BigOperators/Ring/Finset.lean:65 | only for L11 |
| Many-one reductions (computable) | `ManyOneReducible` (`≤₀`), `ManyOneEquiv`, `ManyOneDegree` | Computability/Reduce.lean:41,131,306 | `∃ f, Computable f ∧ ∀ a, p a ↔ q (f a)`; computable, NOT polynomial-time; requires `Primcodable` |
| Polynomial-time TM computation | `Turing.TM2ComputableInPolyTime` (structure: TM2 + `time : Polynomial ℕ` + output within `time.eval (input.length)` steps) | Computability/TuringMachine/Computable.lean:174 | only `idComputableInPolyTime` (:216) is proven; no composition, no classes P/NP/Σ₂ᵖ, no reductions |
| Encodings | `Computability.Encoding`, `encodingNatBool` | Computability/Encoding.lean:38,131 | |
| Classes P, NP, PH, Σ₂ᵖ, poly-time reductions, NP-hardness | **NOT IN MATHLIB** | grep `Computability/` for "PolyTime|NP|complexity class": only the structure above | see §6 |
| Semialgebraic / Tarski–Seidenberg | **NOT IN MATHLIB** (brief) | — | not needed for Section 3 |

Unpinned but standard (used in Mathlib code; declaration in core/Batteries or generated): `Fin.forall_fin_two`
(used NumberTheory/Height/Basic.lean:305), `Nat.lt_two_pow_self` (used Data/Nat/BitIndices.lean:135),
`Nat.cast_mul`, `Nat.cast_pow`, `sub_eq_zero`, `add_le_add_iff_right`, `mul_nonneg`.

---

## 5. Lean encoding decisions and pitfalls

### 5.1 Types
- Upper variable `x : Fin r → ℝ`; lower variable `y : Fin (k+1) → ℝ` with `z := y 0`, `t := Fin.tail y`
  (`t i = y i.succ`). This keeps the baseline `Fin n ⊕ Fin m` shape and `Sum.elim x y` evaluation.
  `Unit ⊕ Fin k` was considered (more readable `Sum.inl ()` for z) but it breaks the baseline
  `MvPolynomial (Fin n ⊕ Fin m) ℝ` and gains nothing; `Fin (k+1)` with `Fin.cons`/`Fin.tail` is fine.
- Box: `box k : Set (Fin (k+1) → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0:ℝ) 1)`. Membership:
  `Set.mem_univ_pi`. Compactness: `isCompact_univ_pi fun _ => isCompact_Icc`.
- Binary predicate: `IsBinary (x : ι → ℝ) : Prop := ∀ j, x j = 0 ∨ x j = 1` (decidable-free, `Prop`).

### 5.2 Polynomials
Define over ℤ and map to ℝ (gives integrality for free):
```lean
abbrev σ (r k : ℕ) := Fin r ⊕ Fin (k+1)
def xv (j : Fin r) : MvPolynomial (σ r k) ℤ := X (Sum.inl j)
def zv : MvPolynomial (σ r k) ℤ := X (Sum.inr 0)
def tv (i : Fin k) : MvPolynomial (σ r k) ℤ := X (Sum.inr i.succ)
def Fp (R : ℕ) : MvPolynomial (σ r k) ℤ := C (R:ℤ) + ∑ j, C ((2:ℤ)^(j:ℕ)) * xv j
def Gp (q : Fin k → ℕ) : MvPolynomial (σ r k) ℤ := ∑ i, C (q i : ℤ) * tv i
def Hp := (∑ i, (tv i * (1 - tv i))^2) + (Fp R - Gp q)^2
def Lp := zv * ((zv - 1)^2 + ∑ j, ((1 - xv j) * xv j)^2)
def Qp := Lp + Hp
def Pp := 1 - zv * (Hp + 1)
def Pfun (x : Fin r → ℝ) (y : Fin (k+1) → ℝ) : ℝ := eval (Sum.elim x y) (map (Int.castRingHom ℝ) Pp)
```
Pitfalls:
- `MvPolynomial.eval` of `∑`/`^`/`-`: use `eval_sum`, `eval_pow`, `eval_sub`, `map_sum`-style simp set;
  `simp [Pp, Hp, ..., eval_sum, Fin.sum_univ_succ]` should reduce `Pfun x y` to the explicit real formula
  with `y 0` and `y i.succ`. Prove once the "function-level" lemmas `Pfun x y = 1 - y 0 * (Hfun x (Fin.tail y) + 1)`
  etc., then do all analysis on `Hfun, Lfun : ... → ℝ` defined directly as real functions; the polynomial
  side is only used for degree/coefficients/continuity.
- `C ((2:ℤ)^j)` vs `(2:MvPolynomial _ _)^j`: use `C` of the integer so coefficient extraction is literal.
- Degree lemmas are all `≤` (`totalDegree_mul` is `≤ a.deg + b.deg`), so the bound `≤ 5` composes with
  `le_trans`/`max_le`/`Finset.sup_le`; never try to prove `= 5`.
- `MvPolynomial.map` and `eval`: `eval_map : eval g (map f p) = eval₂ f g p` (Eval.lean:432); alternatively
  use `MvPolynomial.aeval (Sum.elim x y) Pp` with `ℤ`-algebra `ℝ`, which also simps well.
- Decidability: `IsBinary`/`SSI.Yes` are `Prop`s; nothing needs `Decidable`; `Finset.filter` in L5.b needs
  `DecidablePred (fun i => t i = 1)` — use `Classical.decPred` or `open Classical`.

### 5.3 Value function and optimal value
- Use the brief's `argminSet Q Y x := {y ∈ Y | ∀ y' ∈ Y, Q x y ≤ Q x y'}` (= `{y ∈ Y | IsMinOn (Q x) Y y}`
  via `isMinOn_iff`), and `valueFun P Q Y x : EReal := ⨅ y ∈ argminSet Q Y x, ((P x y : ℝ) : EReal)`.
- Optimal value: `optVal : EReal := ⨅ x, valueFun P Q Y x`. Decision: `optVal < (c : EReal)`.
  With `EReal` a `CompleteLinearOrder`, `optVal < c ↔ ∃ x, valueFun x < c` is exactly `iInf_lt_iff`.
  This is the cleanest formal meaning of "optimal value strictly smaller than c" (no `BddBelow` side
  conditions, no `sInf ∅` pitfalls — `⨅` over the empty argmin set is `⊤`, consistent with the paper's
  `φ = +∞` convention, and here it never happens).
- EReal arithmetic pitfalls: never compute with `EReal` `+`/`*`; L6 produces a real `ρ x` with
  `valueFun x = (ρ x : EReal)`, and all comparisons go through `EReal.coe_le_coe_iff`/`coe_lt_coe_iff`,
  `EReal.coe_neg'` (`(x:EReal) < 0 ↔ x < 0`), `EReal.coe_zero`.
- `iInf` over `Fin r → ℝ` of an `EReal`-valued function: `iInf_le` (specific point), `le_iInf` (all points).

### 5.4 The decision-problem instance type (for the blueprint's statement of Theorem 3.2)
```lean
structure BilevelInstance where
  n m : ℕ
  P Q : MvPolynomial (Fin n ⊕ Fin m) ℤ
  degP : P.totalDegree ≤ 5
  degQ : Q.totalDegree ≤ 5
  lo hi : Fin m → ℤ          -- bounded box ∏ [lo i, hi i]
  c : ℤ

def BilevelInstance.box (I : BilevelInstance) : Set (Fin I.m → ℝ) :=
  Set.pi Set.univ fun i => Set.Icc (I.lo i : ℝ) (I.hi i)
def BilevelInstance.Pfun (I) (x) (y) : ℝ := MvPolynomial.aeval (Sum.elim x y) I.P
def BilevelInstance.optVal (I : BilevelInstance) : EReal :=
  ⨅ x : Fin I.n → ℝ, valueFun I.Pfun I.Qfun I.box x
def BilevelInstance.Yes (I : BilevelInstance) : Prop := I.optVal < (I.c : EReal)
```
"Coefficients as ℤ-valued finitely supported functions on monomials" is literally what
`MvPolynomial σ ℤ = AddMonoidAlgebra ℤ (σ →₀ ℕ) = ((σ →₀ ℕ) →₀ ℤ)` is, so no separate type is needed; the
degree bound is carried as a field. Rational `c`/box endpoints are an equally good choice; ℤ suffices for
the reduction (`c = 0`, box `[0,1]`).
Reduction: `reduce : SSI → BilevelInstance` with `n = r`, `m = k+1`, `P = Pp`, `Q = Qp`, `lo = 0`, `hi = 1`, `c = 0`.
Correctness: `(reduce I).Yes ↔ I.Yes` (= L9 after unfolding).

---

## 6. Treatment of Theorem 3.2 (the complexity wrapper): options and recommendation

### 6.1 State of the art (verified)
- **Mathlib** (grep of `Mathlib/Computability/`): Turing machines (TM0/TM1/TM2, Post), `Partrec`,
  `Primrec`, `Computable`, `ManyOneReducible` (computable many-one reductions, `Computability/Reduce.lean:41`,
  with degrees `ManyOneDegree` :306 forming a semilattice), `Encoding`, and a single structure
  `Turing.TM2ComputableInPolyTime` (`Computability/TuringMachine/Computable.lean:174`) bundling a TM2, a
  `Polynomial ℕ` time bound and a proof that the machine outputs `f a` within `time.eval |enc a|` steps.
  Only the identity is shown poly-time computable; there is no composition lemma, no class P/NP/Σ₂ᵖ, no
  notion of polynomial-time reduction or hardness. `ManyOneReducible` is the wrong notion (computable,
  not poly-time: every decidable problem is many-one equivalent to every other nontrivial decidable one).
- **External Lean 4 projects** (none in Mathlib; none provide Σ₂ᵖ-hardness infrastructure ready to use):
  - `starpos/lean-np-complete` (Lean/Mathlib v4.35.0): Cook–Levin, SAT/3SAT NP-complete, reusable
    `PolyTimeReduction` over a TM0 cost model with `List Bool` inputs (integers in **unary**, so bit-size
    arguments as in Lemma 3.3 do not transfer). No Σ₂ᵖ. Does not accept PRs/issues. https://github.com/starpos/lean-np-complete
  - `PierreSenellart/descriptive-complexity` (v1.4.0, Mathlib v4.35.0, updated 2026-11-03): machine-free,
    Fagin-style classes via `ModelTheory`; defines Σₖᵖ/Πₖᵖ by alternating second-order quantifier blocks,
    QBF complete at each level, first-order reductions. No cost model; instances are structures, not strings.
    Closest existing Σ₂ᵖ definition, but a bilevel instance would have to be encoded as a finite
    relational structure and the reduction as a first-order interpretation — a research project in itself.
    https://github.com/PierreSenellart/descriptive-complexity, arXiv:2609.18261
  - T. Simas, "Verified polynomial-time reductions in Lean 4" (arXiv:2601.15571, 2026): bundled Karp
    reductions with templates for NP/coNP/Σ₂ᵖ membership and hardness; code on Zenodo
    (doi:10.5281/zenodo.18140965), Lean/Mathlib version and cost model not stated on the abstract page.
  - `DominikPeters/HardnessReductionsLean`: catalogue of reductions, explicitly not connected to a
    machine model ("mathlib does not yet have one"). `lean-dojo/leanmillenniumprizeproblems`
    (`Millennium.PEqualsNP`) and `JoshuaTan42/millennium-cook-levin`: P/NP statements and Cook–Levin
    against those definitions; no PH.
  - Project intention: leanprover-community/project-intentions#52 "Reusable NP-hardness foundations and
    Cook–Levin in Lean 4" (open).
- **Isabelle**: F. Balbach, "The Cook-Levin theorem", AFP 2023 — multi-tape TMs, P, NP, poly-time many-one
  reductions, SAT NP-complete (https://www.isa-afp.org/entries/Cook_Levin.html). No PH.
- **Coq**: Gäher–Kunze, "Mechanising Complexity Theory: The Cook-Levin Theorem in Coq", ITP 2021, LIPIcs 193,
  20:1–20:18 (call-by-value λ-calculus as cost model; https://github.com/uds-psl/cook-levin). No PH.
Conclusion: there is no maintained, Mathlib-compatible library in which "Σ₂ᵖ-hard" can be stated and
Theorem 3.2 proved end-to-end; the nearest (descriptive-complexity) uses a machine-free definition that does
not match the paper's Turing-machine/Stockmeyer definition and would need Fagin's theorem (taken as a
hypothesis there) to connect to it.

### 6.2 Options
**Option 1 (recommended): formalize the reduction's mathematics, state the complexity claim informally.**
Formal content: `reduce : SSI → BilevelInstance` (a plain Lean definition, hence a concrete, evidently
polynomial-size map), `reduce_correct : (reduce I).Yes ↔ I.Yes` (Lemma 3.3), `degree ≤ 5` (L10),
integrality (by construction), optionally `coeff bound` (L11). Blueprint text: "Theorem 3.2 follows from
`reduce_correct` and the Σ₂ᵖ-hardness of SSI [18, 26] by the standard argument; `reduce` is computable in
time polynomial in the bit-size of the instance (it writes `O((r+k)^2)` integer coefficients of magnitude
`≤ 2M^2`, i.e. `O(log M)` bits each, where `r ≤ k`); neither 'polynomial time' nor 'Σ₂ᵖ-hard' is
formalized, as Mathlib has no such notions." Cost: zero beyond Lemma 3.3. Benefit: captures 100% of the
paper's new mathematics; honest about what is not checked.

**Option 2: a minimal machine-free Σ₂ᵖ-style class.** E.g. define `Sigma2 (L : α → Prop)` as "∃ a
polynomial p and a decidable `R : α → β → γ → Prop`, with witnesses of size ≤ p(|a|), such that
`L a ↔ ∃ b, ∀ c, R a b c`", where "size" needs an encoding `α → List Bool` and "decidable in poly time"
is the problem: without a cost model one can only say `Decidable`, which makes the class collapse to
"Σ₂ of decidable relations with bounded witnesses" = all decidable problems with that quantifier shape, and
"hardness" under computable reductions is trivial. Any non-trivial version needs a cost model (TM2 +
`TM2ComputableInPolyTime` + composition lemma + encodings of `MvPolynomial` instances + proof that `reduce`
runs in polynomial time on a TM2 — the last item is a large, unpleasant project; cf. the effort in
Balbach/Gäher–Kunze). Cost: XL, benefit: low (the result would still rest on an unformalized Σ₂ᵖ-hardness
of SSI). Rejected.

**Option 3: axiomatize.** Postulate opaque `PolyTimeReduction : (α → Prop) → (β → Prop) → Prop` with
transitivity, `Sigma2Hard : (α → Prop) → Prop`, `hard_of_reduction`, and `ssi_sigma2_hard : Sigma2Hard SSI.Yes`,
plus an axiom `reduce_polytime : PolyTimeReduction SSI.Yes BilevelInstance.Yes` — but the last axiom is
precisely the content one would want checked, and with it Theorem 3.2 is a two-line consequence. This
produces a `theorem` whose entire force is in axioms; it adds nothing over Option 1 except the risk of an
inconsistent or vacuous axiom set (e.g. `PolyTimeReduction` must be stated for *encoded* instances, so one
must fix encodings anyway). Rejected; at most mention as a possible "interface" if a complexity library
later appears.

**Recommendation: Option 1**, with the blueprint presenting Theorem 3.2 as: (formal) `reduce_correct`,
`reduce_degree`, [`reduce_coeff_bound`]; (informal, cited) SSI is Σ₂ᵖ-hard [18, 26]; (informal) `reduce` is
polynomial-time; hence Theorem 3.2. If the Simas framework or the project-intentions#52 effort matures into
a Mathlib-compatible `PolyTimeReduction`, Option 1's artifacts are exactly what plugs in.

---

## 7. Appendix D and Appendix B: what is claimed, what the blueprint should say

### 7.1 Bibliographic entries (extracted from the paper's reference list, `paper_html.txt` lines 1496–1500, 1567–1573, 1605–1609)
- [18] Alberto Caprara, Margarida Carvalho, Andrea Lodi, and Gerhard J. Woeginger. *A study on the
  computational complexity of the bilevel knapsack problem.* SIAM Journal on Optimization, 24(2):823–838, 2014.
- [26] Christian E.J. Eggermont and Gerhard J. Woeginger. *Motion planning with pulley, rope, and baskets.*
  In STACS'12 (29th Symposium on Theoretical Aspects of Computer Science), LIPIcs vol. 14, pages 374–383,
  Paris, 2012. (DOI 10.4230/LIPIcs.STACS.2012.374; journal version: Theory of Computing Systems 53 (2013) 569–582.)
- [30] R. Jeroslow. *The polynomial hierarchy and a simple model for competitive analysis.* Mathematical
  Programming, 32:146–164, 1985. — cited in Appendix B for Σ₂ᵖ-hardness of (integer) linear bilevel
  programming, NOT for SSI. The task brief's "[26] Jeroslow?" is wrong: [26] is Eggermont–Woeginger.
- [41] Andrea Lodi, Ted Ralphs, and Gerhard Woeginger. *Bilevel programming and the separation problem.*
  Mathematical Programming, 146, 2013. (Appendix B.)
- [49] Larry J. Stockmeyer. *The polynomial-time hierarchy.* Theoretical Computer Science, 3(1):1–22, 1976.
  (definition of Σₖᵖ/Πₖᵖ; Π₂ᵖ-completeness of ∀∃-3-CNF-SAT.)
- [5] Sanjeev Arora and Boaz Barak. *Computational Complexity: A Modern Approach.* CUP, 2009.

### 7.2 What Appendix D claims
1. SSI's Σ₂ᵖ-hardness is "mentioned in [18], credited to [26]"; [26] proves Π₂ᵖ-completeness of
   Captive-Queen, not SSI-hardness directly.
2. [26] reduces 2-Quantified 3-CNF-SAT (∀X∃Y φ; Π₂ᵖ-complete by Stockmeyer) to an instance with items of
   weights `q_1..q_k` (`k = 4s+3t`), `R = U`, `r = s`, such that `∀X∃Yφ ⟺ ∀V ∈ [U, U+2^s−1] ∃J, w(J) = V`
   (Lemmas 7+8 of the STACS version, proofs deferred to the full version; verified in the PDF).
3. Hence the complement of SSI is Π₂ᵖ-hard, so SSI is Σ₂ᵖ-hard; SSI ∈ Σ₂ᵖ (guess `S` — `≤ max(|R|, r)+1
   ≤ poly` bits since `r ≤ k`; check all `I` in coNP) so Σ₂ᵖ-complete.
What the blueprint should say: "Σ₂ᵖ-hardness of SSI is a cited result (Eggermont–Woeginger 2012, Lemmas 7–8
of the STACS version / journal version 2013; see Caprara–Carvalho–Lodi–Woeginger 2014 and Appendix D of the
paper for the derivation). It is not formalized and cannot be stated in Mathlib." Fix the two typos of §3
items 11–13 when restating.

### 7.3 Appendix B, last paragraph
Claims: linear bilevel (P, Q linear, Y polyhedron) is NP-hard [30, 7, 12]; integer linear bilevel is
Σ₂ᵖ-hard [41, 18, 30]; the paper proves the analogue for polynomial bilevel with a bounded box; "natural
since single-level polynomial optimization is NP-hard". All informal context; blueprint: one sentence of
related work, no formal content.

---

## 8. Closing remarks of §3.2 as blueprint remarks (D)

(i) **Relation to Theorem 2.15.** The value function of the constructed problem is
`φ(x) = 1` off `{0,1}^r` and `φ(x) = −m(x) ∈ [−m_max, 0]` on `{0,1}^r`. This φ is semialgebraic (finitely
many isolated points plus a constant), bounded on compact sets, and lsc (binary points are isolated, so at a
binary `x₀` the liminf is `min(φ(x₀), 1) = φ(x₀)`; elsewhere φ is locally constant). Theorem 2.15 says
every such φ is a bounded-box bilevel value function, but gives no degree/size control; Lemma 3.3 is a
bespoke degree-5, integer-coefficient representation of this particular φ. Blueprint remark; optional
formal lemma `lowerSemicontinuous φ_explicit` (S) — not needed for Theorem 3.2.
(ii) **Pessimistic version.** The paper says the proof does not extend because pessimistic value
functions with bounded box are usc. Check: φ above is NOT usc at any binary `x₀` with `φ(x₀) < 1`, i.e. at
every binary point (`φ(x₀) ≤ 0 < 1 = limsup`). So this φ is not the pessimistic value function of any
bounded-box problem — the remark is correct for this construction. It does not show that the pessimistic
decision problem is easy; the paper leaves pessimistic Σ₂ᵖ-hardness unaddressed. Blueprint: state as "not
covered". (Note `φ_p(·;P) = −φ_o(·;−P)` pointwise, but the optimal value is an inf over x in both cases,
so there is no trivial symmetry between the two decision problems.)
(iii) **Convex lower level.** Theorem 2.21 replaces the lower level by a linear objective over
`Conv(M_d(Ω))` (convex hull of the image of the box under the degree-≤d monomial map), a compact convex
semialgebraic set. A semialgebraic description of that set comes from quantifier elimination
(Tarski–Seidenberg + Carathéodory) with no polynomial bound on its size, and the decision problem's input
would need such a description; hence "the reduction is not guaranteed to be polynomial". Blueprint: informal
remark; nothing to formalize (and nothing formalizable: Tarski–Seidenberg is not in Mathlib).

---

## 9. Alternatives considered and rejected

- **Avoid `EReal`, state everything in ℝ**: `φ` here is real-valued, so one could define
  `φ x := sInf ((P x) '' argmin)` in ℝ; but `sInf` in ℝ needs `BddBelow` and nonempty side conditions at
  every use and would diverge from the baseline `valueFun`. Keep `EReal`; L6 converts once.
- **Define P, Q only as real functions** (skip `MvPolynomial`): simplest for the analysis, but then
  "degree ≤ 5 with integer coefficients" must be proven separately for an ad-hoc polynomial witness —
  i.e. one writes the `MvPolynomial` anyway. Define as `MvPolynomial ... ℤ`, prove the function-level
  identities once (`simp`), analyze the functions.
- **Argmin via product types**: considered `(Fin r → ℝ) → ℝ × (Fin k → ℝ)`; rejected (breaks baseline;
  no clean `Equiv.piFinSucc` found in this checkout; `Fin.cons`/`Fin.tail` suffice).
- **Replacing the bijection `{0,1}^r ≅ [0,2^r)`** by `Nat.digits`/`Nat.ofDigits`/`Nat.testBit`: rejected,
  `finFunctionFinEquiv` is the exact statement with a fixed-length `Fin r` index.
- **Simplifying the construction** (fewer variables, lower degree): the `z` gadget is what makes
  `φ = 1` off binary points (so inf is not polluted by non-binary x); H's `(t_i(1−t_i))^2` enforces binary t
  at the minimum. One could lower degrees (e.g. `t_i(1−t_i)` is ≥ 0 on [0,1] already, so `∑ t_i(1−t_i)`
  instead of its square gives degree 2 for that part and degree 3 for P) but the paper states degree 5 and
  the brief says prove as stated; note it as an auditor question (§11.4).
- **Exact `totalDegree = 5`**: rejected (false for r = 0 or k = 0; not needed).

---

## 10. Effort / risk per lemma

| Lemma | Effort | Risk | Assume or prove |
|---|---|---|---|
| L0 separable argmin | S | low | prove |
| L1 analysis of L | S–M | low | prove |
| L2 analysis of H, minimizer | S | low | prove |
| L3 separability on `Fin (k+1)` | S | low (Fin.cons/tail plumbing) | prove |
| L4 binary bijection | S | low | prove (`finFunctionFinEquiv`) |
| L5 subset sums ↔ indicators | S | low | prove |
| L6 value-function formula (EReal) | M | medium (EReal `iInf` bookkeeping) | prove |
| L7 YES ⇒ inf < 0 | S | low | prove |
| L8 NO ⇒ inf = 0 | S | low | prove |
| L9 Lemma 3.3 (c) | S | low | prove |
| L10 degree ≤ 5 | S–M | low | prove |
| L11 coefficient bound 2(M²+1) | L (sharp) / M (ℓ¹) | medium | optional; prove only if the size claim is wanted formally |
| L12 reduction map, integrality | S | low | prove (definition) |
| Theorem 3.2 wrapper (Σ₂ᵖ-hard) | — | — | NOT formalized; informal (Option 1) |
| Appendix D (SSI Σ₂ᵖ-hard) | — | — | cited [26, 18]; not formalizable |
| Remarks (i)–(iii) | S (lsc of φ, optional) | — | informal remarks |
Total for the formal core (L0–L10, L12): roughly 400–700 lines of Lean; one person-week.

---

## 11. Open questions for the auditor

1. Should the blueprint's `BilevelInstance` use `ℤ` or `ℚ` for `c` and the box endpoints? (ℤ suffices for
   the reduction; ℚ matches "arbitrary constant c" more faithfully. Either is Primcodable-friendly.)
2. Should L11 (coefficient bound) be in scope at all, given that it only serves the unformalized size
   argument? If yes, sharp (`2M²`, effort L) or ℓ¹ (`(k+3)²M²+2`, effort M)?
3. Should Lemma 3.3 be stated with the paper's hypotheses (`0 < q_i`, `0 < R`, `0 < r ≤ k`) for fidelity,
   or without them (strictly stronger, as proven)? I recommend without, with a remark.
4. The construction can be simplified to lower degree (e.g. drop the outer square in `∑(t_i(1−t_i))^2`,
   since `t_i(1−t_i) ≥ 0` on `[0,1]`; similarly for `((1−x_j)x_j)^2` — but there `x` is unconstrained, so the
   square is needed). Do we formalize the paper's degree-5 version verbatim (recommended: yes) and mention the
   simplification as a remark?
5. Is a formal lemma that the explicit φ is lower-semicontinuous (remark (i)) wanted, to tie Section 3 to
   Theorem 2.15 in the blueprint's dependency graph?
6. Theorem 3.2 statement in the blueprint: confirm the formulation "the map `reduce` is computable with
   polynomially bounded output size; Σ₂ᵖ-hardness is then a cited/informal consequence" is acceptable, or
   whether an explicit axiom interface (Option 3) is preferred for presentation.
