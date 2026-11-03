# AUDIT of R4 (Theorem 2.15, Theorem 2.21, pessimistic counterparts)

Auditor: Opus (adversarial). Sources read: audit brief, common brief, the full R4 report, paper_html.txt lines 100–340
(Section 2.1: Def 2.1/2.2, Thm 2.3, Props 2.4–2.6, Thm 2.8, Cor 2.9), 527–645 (Thm 2.15 and proof), 904–990 (Sec 2.3.1,
def. (18), Thm 2.21 and proof), 991–1060 (Sec 2.4). Mathlib: local checkout, every cited declaration grepped.

## A. Summary verdict

The report is mathematically RELIABLE. All three deviations from the paper were re-derived and are correct:
(1) the epigraph replaces cl(graph f); (2) the scaling polynomial w(x) goes into the P_ij and into P = t·w(x) instead of
normalizing f to h; (3) Theorem 2.21 is proved through a general two-inequality linearization lemma (L9) instead of the paper's
attainment argument. The counterexample to Prop 2.5 is valid, and the corrected growth statement A3 (under CB) is true; a proof
sketch is given below (C2). What must change is small and mostly on the Lean/Mathlib side:
(i) the "robust" inline proof that the simplex is compact uses `isClosed_stdSimplex` and `stdSimplex_subset_Icc`, and both are
DEPRECATED too, along with the `stdSimplex` definition itself. Use an inline weight set instead (C1).
(ii) `sq_eq_zero'` does not exist (C4).
(iii) The report says A3 is "derived from the paper's Prop 2.5", which is a false statement. A3 must be assumed directly, or derived
from the TRUE one-variable growth lemma plus T–S (C2).
(iv) A few minor statements and line numbers need fixing (C3, C5–C7).
No wrong simplification was found.

## B. Lemma-by-lemma verdict table

| Lemma | Verdict | Note |
|---|---|---|
| A1 (T–S projection) | CONFIRMED (assumption) | standard; needed for L1b, L12, A3 derivation, (⊆) |
| A2 (FT, Prop 2.4) | CONFIRMED (assumption) | Padding rectangular I×J: pad short rows with the constant polynomial 1 (cleaner than repeating). a = 0 represents ∅. b = 0 is harmless (see L5). |
| A3 (growth under CB) | CONFIRMED as a true statement; FIXED justification | Prop 2.5 (n ≥ 2) is false, so A3 cannot be "derived from Prop 2.5". A correct proof sketch is in C2. |
| L1a (E closed) | CONFIRMED | `lowerSemicontinuous_iff_isClosed_epigraph` Basic.lean:353 is stated for total `f : α → γ` with `[TopologicalSpace α]`, `[LinearOrder γ] [TopologicalSpace γ] [ClosedIciTopology γ]` (section variables :305, :335). The set is literally `{p : α × γ \| f p.1 ≤ p.2}`. ℝ qualifies. |
| L1b (E semialgebraic) | CONFIRMED | (x,τ) ∈ E ⇔ ∃ s, (x,s) ∈ graph f ∧ s ≤ τ. Cylinder (coordinate permutation) ∩ polynomial inequality, then one projection. |
| L2 / L2' | CONFIRMED | L2' is the paper's obs. (2): cl(graph f) ⊆ epi f via `closure_minimal`; (x,f x) ∈ graph ⊆ closure. |
| L3 (FT + substitution τ = t·w(x)) | CONFIRMED | P̃_ij(x,t) := P_ij(x, t·w(x)) is a polynomial because w is. `eval` is *definitionally* `eval₂Hom (RingHom.id _) f` (Eval.lean:256), so `eval₂Hom_bind₁` (Monad.lean:250) applies after unfolding `eval`; `aeval_bind₁` (:254) is an alternative. |
| L4 (scalar gadget) | CONFIRMED (one minor slip in (d), C5) | (→): z ≥ 0 and p²+1 > 0 give p = (p²+1)z ≥ 0. (←): z = p/(p²+1) ≥ 0, and z ≤ 1/2 ⇔ 2p ≤ p²+1 ⇔ (p−1)² ≥ 0. Only the zero set is used, not the argmin. No calculus. |
| L5 (box gadget) | CONFIRMED | Only one factor must vanish; z(i,j) for i ≠ i₀ is free in [0,1/2]. Degenerate cases: b = 0 gives R ≡ 0 when a ≥ 1, and the equivalence still holds (both sides ⇔ a ≥ 1); a = 0 gives R ≡ 1 and both sides are false. (★★) holds for all t ∈ ℝ, not only on [−1,1]. |
| L6 (core lemma) | CONFIRMED | Re-derived below (C8). Θ(x) = {(t,z) ∈ Y : R = 0}, nonempty via t₀ = f(x)/w(x) ∈ [−1,1]. Value = w(x)·min{t ∈ [−1,1] : t·w(x) ≥ f(x)} = f(x). Only `le_iInf₂`, `iInf₂_le_of_le` and EReal coe monotonicity are used. No compactness. |
| L7 (assembly) | CONFIRMED | Y = [−1,1] × [0,1/2]^{a×b} is a bounded box. P = t·w(x) and Q = R are polynomials. |
| L8 (splitting identity) | CONFIRMED | `eval_eq'` (needs `[Fintype σ]`, true for Fin n ⊕ ι) + `Fintype.prod_sum_type` + `Finset.sum_subset`. Lean's 0^0 = 1 matches eval, so M_S y d = 1 for d with zero y-part is consistent. |
| L9 (linearization, opt + pess) | CONFIRMED | Re-derived in full (C9). Both inequalities hold without attainment, including the ±∞ cases. Claims 1+2 give A = ∅ ⇔ A' = ∅. Positive weights from `eq_pos_convex_span_of_mem_convexHull` (Caratheodory.lean:123, statement checked). |
| L10 (C_cc data) | CONFIRMED | Q' is linear, hence convex on any convex set (and on univ). P' is a polynomial in (x,λ). |
| L11 (hull of compact is compact) | CONFIRMED math; FIXED Mathlib route (C1) | NOT IN MATHLIB confirmed. The inline simplex proof must not use the deprecated `stdSimplex` API. A padding-free variant is in C1. |
| L12 (Y' semialgebraic) | CONFIRMED | `convexHull_eq_union` has no cardinality bound. The bound comes from `AffineIndependent.card_le_finrank_succ` + `Submodule.finrank_le` + `Module.finrank_fintype_fun_eq_card`. The quantifier count (K+1)(1+\|ι\|) is finite. |
| L13 (pessimistic core) | CONFIRMED | With E = hypograph: Θ(x) t-projection = {t ∈ [−1,1] : t·w(x) ≤ f(x)}, sup·w = f(x) at t₀. |
| L14 (pessimistic linearization) | CONFIRMED | Part of L9 via `ConvexOn.exists_ge_of_mem_convexHull` (Jensen.lean:376). |
| (⊆) of 2.21 | CONFIRMED report's claim (§3.12) | Needs Prop 2.6 for an arbitrary semialgebraic Y; the paper states it for boxes only (line 247–249). Cor 2.9 needs only Y compact and P, Q continuous (line 267–269), so it covers compact Y. |
| Pessimistic (⊆) usc | CONFIRMED | Proof in report §2.4 is correct (outer semicontinuity of Θ + compactness). CB: min_{C×Y} P ≤ φ_p ≤ max_{C×Y} P. |

## C. Corrections

**C1. Compactness of the simplex / L11(b): the "robust option" is not robust.**
Wrong claim: "`isCompact_stdSimplex` … DEPRECATED …; the robust option is to re-prove it inline:
`IsCompact.of_isClosed_subset isCompact_Icc (isClosed_stdSimplex ℝ _) (stdSimplex_subset_Icc ℝ)`".
Fact (grep, Mathlib/Analysis/Convex/StdSimplex.lean): the following are all `@[deprecated … (since := "2026-08-29")]`:
- the definition `stdSimplex` itself (:39–40);
- `stdSimplex_eq_inter` (:43);
- `stdSimplex_subset_Icc` (:85–86, "no replacement");
- `isClosed_stdSimplex` (:208–209);
- `isCompact_stdSimplex` (:217–218);
- the CompactSpace instance (:222);
- `Set.Finite.convexHull_eq_image` (:198).

So the inline proof still uses deprecated API. It compiles with warnings, but it is fragile.
Fix: do not use `stdSimplex`. Define the weight set inline:
`W k := {w : Fin k → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}`.
- Closed: `isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))` ∩ `isClosed_eq (continuous_finset_sum …) continuous_const`.
- Contained in `Set.pi univ (fun _ => Icc 0 1)`: each w i ≤ ∑ w = 1 by `Finset.single_le_sum`.
- Compact: `isCompact_univ_pi (fun _ => isCompact_Icc)` plus `IsCompact.of_isClosed_subset`.

This is about 10 lines and uses no deprecated names. (The new bundled `Convexity.StdSimplex.compactSpace`,
Mathlib/Geometry/Convex/ConvexSpace/CompactSpaceStdSimplex.lean:69, is the alternative. It is a type, not a Set, so it needs
`continuous` coercion plumbing. Not recommended.)

Padding-free variant of L11(a), recommended because it removes the report's "fiddly step (M)":

  convexHull ℝ s = ⋃_{k ∈ Finset.range (K+2)} Φ_k '' (W k ×ˢ Set.pi univ (fun _ : Fin k => s)),  Φ_k(w,z) := ∑ i, w i • z i.

- (⊆): `eq_pos_convex_span_of_mem_convexHull` gives ι₀ with card ι₀ ≤ K+1. Reindex by `Fintype.equivFin ι₀`
  (Mathlib/Data/Fintype/EquivFin.lean:80) with `Fintype.sum_equiv`; no zero weights are needed.
- (⊇): `Convex.sum_mem convex_convexHull`, or `Finset.centerMass_mem_convexHull`.
- Compact: `(Finset.range _).isCompact_biUnion` (finite union) of `IsCompact.image`.

The same union form feeds L12: a finite union of K+2 projections, so R2 needs closure under finite unions.

**C2. A3 must not be "derived from the paper's Prop 2.5".**
The report §2.0 A3 says "Derivation from the paper's Prop 2.5 (with the Euclidean norm): |f| ≤ ‖x‖^N for ‖x‖ ≥ C …". That derivation
starts from a false statement. The counterexample is verified: f(x,y) = 1/(x−y) off the diagonal and 0 on it.
- Graph = {t(x−y) − 1 = 0} ∪ {(x−y)² + t² = 0}, which is a union of two basic sets in Def 2.1 form.
- For any C, N, take (C+ε, C) with ε → 0⁺: the norm is ≥ C and |f| = 1/ε → ∞.

Note: Prop 2.5 is TRUE for n = 1, because singularities cannot escape to infinity on a line. The cited source [51, §4.12] most
likely states this one-variable o-minimal fact. Correct options for the blueprint:
- (a) assume A3 verbatim (the report's final choice; fine); or
- (b) assume only the one-variable growth lemma G1: "g : ℝ → ℝ with semialgebraic graph ⇒ ∃ N R₀, ∀ r ≥ R₀, |g r| ≤ r^N"
  (BCR Prop 2.6.1 / van den Dries), and derive A3 as follows.

Proof of A3 from G1 + T–S + CB:
1. Put g(r) := sup{|f(x)| : ∑ xᵢ² ≤ r} for r ≥ 0 (and g(r) := g(0) for r < 0). The set is compact and nonempty, so g is finite by CB,
   g ≥ 0, and g is nondecreasing.
2. Graph g = {(r,s) : (r ≥ 0 → [(∀x, ∑x² ≤ r → |f x| ≤ s) ∧ (∀ s' < s, ∃ x, ∑x² ≤ r ∧ s' < |f x|)]) ∧ (r < 0 → …same with 0)}.
   Here |f x| ≤ s ⇔ ∀ u, (x,u) ∈ graph f → −s ≤ u ≤ s. This is a first-order formula, so g is semialgebraic by T–S.
3. By G1, g(r) ≤ r^N for r ≥ R₀ (WLOG R₀ ≥ 1). Hence for all x:
   |f x| ≤ g(∑x²) ≤ max(g(R₀), (∑x²)^N) ≤ g(R₀) + (1 + ∑x²)^N.
   So B := g(R₀) ≥ 0 and M := N. ∎

Option (b) is the honest reduction to the classical source. Option (a) is simpler for the blueprint. Either way the blueprint
text must say "Prop 2.5 as stated is false for n ≥ 2" and must not cite it for A3.

**C3. `upperSemicontinuous_iff_IsClosed_hypograph` line.** It is at Basic.lean:897 (the report says :898). The alias at :901 is correct. Cosmetic.

**C4. `sq_eq_zero'` (L4b) does not exist in Mathlib.** Use `sq_eq_zero_iff` (Mathlib/Algebra/GroupWithZero/Basic.lean:262:
`a ^ 2 = 0 ↔ a = 0`) or `pow_eq_zero_iff two_ne_zero` (:253).

**C5. L4(d) slip.** "p/(p²+1) is in (−1/2,1/2] for all p" should read [−1/2,1/2]: the value −1/2 is attained at p = −1. Not used downstream.

**C6. L11(b)/§5.8 deprecation list is incomplete.** See C1. Also, the replacement for `stdSimplex_subset_Icc` is "no replacement".

**C7. Top-level signature hygiene (thm215_supset).** `hgrowth` is a consequence of `hsa`+`hcb` via A3. If it stays as a free
hypothesis, the Lean theorem is weaker than the paper's. The blueprint should state Theorem 2.15 (⊇) with only hsa, hlsc, hcb, and
invoke A1/A2/A3 as named assumed lemmas inside the proof. The report intends this ("assumed lemma"), but the displayed signature
mixes the two. The same applies to `hFT`/`hTS`.

**C8. (Verification record, no change.) L6 re-derived.** Fix x and put t₀ = f x / w x.
- |t₀| ≤ 1.
- (x, t₀ w) = (x, f x) ∈ E, so by (★★) there is z₀ ∈ Z with R(x,t₀,z₀) = 0.
- R ≥ 0 everywhere, so Θ(x) = {(t,z) ∈ Y : R = 0} (⊇ from R ≥ 0; ⊆ since Q ≤ Q(t₀,z₀) = 0 ≤ Q).
- For (t,z) ∈ Θ(x): z ∈ Z and R = 0, so (x, t w) ∈ E by (★★), so f x ≤ t·w x = P. Hence the inf is ≥ f x, and (t₀,z₀) attains it.
- E only needs to satisfy graph ⊆ E ⊆ epi. With E = epi, the argmin t-set is [f(x)/w(x), 1], which is closed and nonempty.

**C9. (Verification record, no change.) L9 re-derived.** Notation: q = Q(x,·), ℓ = Q'(x,·), p = P(x,·), ℓ_P = P'(x,·).
ℓ∘M_S = q and ℓ_P∘M_S = p (L8, needs S ⊇ supp P ∪ supp Q).
- Claim 1: y ∈ A ⇒ M_S y ∈ A'. For λ ∈ Y', `ConcaveOn.exists_le_of_mem_convexHull` (Jensen.lean:386; hypotheses
  `ConcaveOn 𝕜 s f`, `t ⊆ s`, `x ∈ convexHull 𝕜 t`; use s = univ, `LinearMap.concaveOn` Function.lean:392 with `convex_univ`) gives
  y' ∈ Y with ℓ(M y') ≤ ℓ λ, and q y ≤ q y'.
- Claim 2: λ ∈ A' ⇒ λ = ∑ wᵢ M(yᵢ) with wᵢ > 0 and ∑ wᵢ = 1.
  - ℓ(M yᵢ) ≥ ℓ λ =: m, because M yᵢ ∈ Y' (`subset_convexHull`).
  - ∑ wᵢ(q yᵢ − m) = 0 with nonnegative terms, so each wᵢ(q yᵢ − m) = 0 (`Finset.sum_eq_zero_iff_of_nonneg`), so q yᵢ = m.
  - For y' ∈ Y, q y' = ℓ(M y') ≥ m, so yᵢ ∈ A. Hence λ ∈ convexHull(M''A) (`Convex.sum_mem`).
  - Positivity is essential here: with a zero weight, yᵢ is unconstrained.
- Optimistic value:
  - (⨅_{A'} ≤ ⨅_A) by Claim 1, since ℓ_P(M y) = p y.
  - (⨅_A ≤ ⨅_{A'}) by Claim 2 + `ConcaveOn.exists_le_of_mem_convexHull` for ℓ_P on convexHull(M''A): there is y ∈ A with p y ≤ ℓ_P λ.
  - Valid for ⊤ (both argmins empty), ⊥ (unbounded below) and non-attained infima, because only `le_iInf₂`/`iInf₂_le_of_le` are used.
- Pessimistic value: symmetric, with `ConvexOn.exists_ge_of_mem_convexHull`.
- Emptiness: A = ∅ ⇒ A' ⊆ conv ∅ = ∅ (Claim 2), and A' = ∅ ⇒ M''A = ∅ ⇒ A = ∅ (Claim 1).

## D. Mathlib citation check

| Declaration | Exists | file:line verified | Adequate | Note |
|---|---|---|---|---|
| `lowerSemicontinuous_iff_isClosed_epigraph` | yes | Topology/Semicontinuity/Basic.lean:353 ✓ | yes | total f; `[ClosedIciTopology γ]` |
| `LowerSemicontinuous.isClosed_epigraph` (alias) | yes | :357 ✓ | yes | |
| `upperSemicontinuous_iff_IsClosed_hypograph` | yes | :897 (report :898) | yes | `[ClosedIicTopology γ]`; capital `IsClosed` in name |
| `UpperSemicontinuous.IsClosed_hypograph` | yes | :901 ✓ | yes | |
| `LowerSemicontinuous(At)`, `UpperSemicontinuous` abbrevs | yes | Defs.lean:287, :293, :317 ✓ | — | |
| `closure_minimal`, `subset_closure`, `IsClosed.closure_subset_iff` | yes | Topology/Closure.lean:199, :193, :240 ✓ | yes | |
| `ConcaveOn.exists_le_of_mem_convexHull` | yes | Analysis/Convex/Jensen.lean:386 ✓ | yes | conclusion `∃ y ∈ t, f y ≤ f x` |
| `ConvexOn.exists_ge_of_mem_convexHull` | yes | Jensen.lean:376 ✓ | yes | |
| `LinearMap.concaveOn` / `LinearMap.convexOn` | yes | Analysis/Convex/Function.lean:392 / :388 ✓ | yes | need `Convex 𝕜 s`; f bundled as `E →ₗ[𝕜] β` |
| `ConvexOn` def | yes | Function.lean:54 ✓ | — | includes `Convex 𝕜 s` |
| `eq_pos_convex_span_of_mem_convexHull` | yes | Analysis/Convex/Caratheodory.lean:123 ✓ | yes | `∃ (ι : Type u) (_ : Fintype ι) z w, range z ⊆ s ∧ AffineIndependent 𝕜 z ∧ (∀ i, 0 < w i) ∧ ∑ w = 1 ∧ ∑ w • z = x`; ι lives in E's universe |
| `convexHull_eq_union` | yes | Caratheodory.lean:106 ✓ | yes (no card bound in it) | union over affinely independent finsets |
| `AffineIndependent.card_le_finrank_succ` | yes | LinearAlgebra/AffineSpace/FiniteDimensional.lean:348 ✓ | yes | bound is via `vectorSpan` of range |
| `Submodule.finrank_le` | yes | LinearAlgebra/Dimension/Constructions.lean:401 ✓ | yes | `[Module.Finite R M]`, `[StrongRankCondition R]` |
| `Module.finrank_fintype_fun_eq_card` | yes | Constructions.lean:322 ✓ | yes | |
| `Set.Finite.isCompact_convexHull` | yes | Analysis/Convex/Topology.lean:367 ✓ | n/a (finite only) | confirms gap |
| compact hull of compact set | NOT IN MATHLIB ✓ | grep `isCompact_convexHull`, `IsCompact.convexHull`, `IsCompact (convexHull` → only finite versions | — | prove (C1) |
| `isClosed_stdSimplex` | yes | Analysis/Convex/StdSimplex.lean:209 ✓ | DEPRECATED (2026-08-29) | report missed (C1) |
| `stdSimplex_subset_Icc` | yes | StdSimplex.lean:86 ✓ | DEPRECATED, "no replacement" | report missed |
| `isCompact_stdSimplex` | yes | StdSimplex.lean:218 ✓ | DEPRECATED ✓ (report correct) | |
| `stdSimplex` (def) | yes | StdSimplex.lean:40 | DEPRECATED | report missed |
| `Convexity.StdSimplex.compactSpace` | yes | Geometry/Convex/ConvexSpace/CompactSpaceStdSimplex.lean:69 ✓ | yes | type-level API |
| `Set.convexHull_eq_range_iConvexComb` | yes | StdSimplex.lean:181 ✓ | — | correctly rejected |
| `Finset.sum_eq_zero_iff_of_nonneg` | yes (to_additive) | from `Finset.prod_eq_one_iff_of_one_le` Algebra/Order/BigOperators/Group/Finset.lean:240 (attr :239) ✓ | yes | primed version deprecated (:251) ✓ |
| `Finset.prod_nonneg`, `Finset.prod_pos` | yes | Algebra/Order/BigOperators/GroupWithZero/Finset.lean:34, :160 ✓ | yes | |
| `Finset.prod_eq_zero_iff` | yes | Algebra/BigOperators/GroupWithZero/Finset.lean:57 ✓ | yes | needs `[NoZeroDivisors]`, `[Nontrivial]` (ℝ fine) |
| `pow_eq_zero_iff` | yes | Algebra/GroupWithZero/Basic.lean:253 ✓ | yes | |
| `sq_eq_zero'` | NO | — | MISSING | use `sq_eq_zero_iff` :262 (C4) |
| `mul_self_eq_zero` | yes | GroupWithZero/Defs.lean:315 ✓ | yes | |
| `div_le_one`, `abs_div` | yes | Algebra/Order/Field/Basic.lean:43, :673 ✓ | yes | |
| `div_le_iff₀`, `mul_div_cancel₀`, `div_mul_cancel₀` | yes | Order/GroupWithZero/Basic.lean:1149; GroupWithZero/Units/Basic.lean:460, :339 | yes | `mul_div_cancel₀ a hb : b * (a / b) = a` |
| `MvPolynomial.eval_eq/eval_eq'/eval_monomial/eval_C/eval_X/eval_mul/eval_pow/eval_sum/eval_prod` | yes | Algebra/MvPolynomial/Eval.lean:259/263/267/271/275/289/292/295/299 ✓ | yes | |
| `MvPolynomial.as_sum`, `eval_rename` | yes | Basic.lean:965, Rename.lean:244 ✓ | yes | |
| `MvPolynomial.eval₂Hom_bind₁`, `aeval_bind₁`, `bind₁_X_right` | yes | Algebra/MvPolynomial/Monad.lean:250, :254, :136 ✓ | yes | `eval f := eval₂Hom (RingHom.id _) f` (Eval.lean:256) |
| `MvPolynomial.continuous_eval` | yes | Topology/Algebra/MvPolynomial.lean:31 ✓ | yes | |
| `MvPolynomial.sumToIter`, `sumAlgEquiv` | yes | Algebra/MvPolynomial/Equiv.lean:309, :354 ✓ | — | avoided |
| `Fintype.prod_sum_type` | yes | Data/Fintype/BigOperators.lean:268 ✓ | yes | |
| `IsCompact.prod`, `isCompact_univ_pi`, `IsCompact.image` | yes | Topology/Compactness/Compact.lean:1071, :1172, :124 ✓ | yes | |
| `IsCompact.exists_isMinOn` | yes | Topology/Order/Compact.lean:255 ✓ | yes | |
| `CompactIccSpace` pi instance | yes | Topology/Order/Compact.lean:84–86 ✓ | yes | |
| `EReal.coe_le_coe_iff`, `EReal.coe_lt_coe_iff` | yes | Data/EReal/Basic.lean:55, :61 ✓ | yes | |
| `le_iSup₂_of_le`/`iInf₂_le_of_le`, `iSup₂_le`/`le_iInf₂` | yes | Order/CompleteLattice/Basic.lean:229–240 ✓ (`to_dual`) | yes | |
| `subset_convexHull`, `convex_convexHull`, `convexHull_min`, `Convex.convexHull_subset_iff`, `convexHull_mono`, `LinearMap.image_convexHull`, `AffineMap.image_convexHull` | yes | Analysis/Convex/Hull.lean:52, :55, :66, :68, :72, :164, :194 ✓ | yes | |
| `convexHull_eq`, `Finset.convexHull_eq`, `Finset.centerMass_mem_convexHull`, `Finset.centerMass_eq_of_sum_1`, `convexHull_eq_union_convexHull_finite_subsets` | yes | Analysis/Convex/Combination.lean:345, :392, :256, :85, :432 ✓ | yes | |
| `convex_pi`, `convex_Icc` | yes | Analysis/Convex/Basic.lean:108, :257 ✓ | yes | |
| `isClosedMap_fst/snd_of_compactSpace` | yes | Topology/Maps/Proper/Basic.lean:332, :337 ✓ | n/a | remark only |
| `Function.Embedding.nonempty_of_card_le` | yes | Data/Fintype/EquivFin.lean:367 | yes | unnecessary with C1 variant |
| `Fintype.equivFin` | yes | Data/Fintype/EquivFin.lean:80 ✓ | yes | |
| `finProdFinEquiv`, `Fin.consEquiv`, `Fin.snocEquiv` | yes | Logic/Equiv/Fin/Basic.lean:330; Data/Fin/Tuple/Basic.lean:184, :722 ✓ | yes | |
| `Finset.fintypeCoeSort` | yes | Data/Fintype/Sets.lean:226 | yes | |
| `Finset.sum_subset` | yes (to_additive of `prod_subset`) | Algebra/BigOperators/Group/Finset/Basic.lean:203 | yes | |

## E. Missed issues (not raised by the report)

1. **Deprecated simplex API** (C1): `stdSimplex` (def), `isClosed_stdSimplex`, `stdSimplex_subset_Icc` are all deprecated as of 2026-08-29.
2. **Prop 2.5 is true for n = 1** (C2). The blueprint can assume the classical one-variable lemma instead of A3, which keeps the
   assumed surface closer to textbook statements. The report's A3 "derivation from Prop 2.5" must be removed.
3. **Paper, Thm 2.21 proof: the coefficient vector c_Q depends on x.** The paper writes Q'(x,λ) = c_Q^⊤ λ with "c_Q the vector
   containing the coefficients of the monomials of Q". Since Q = Q(x,t,z), the coefficients of the (t,z)-monomials are polynomials
   in x: Q'(x,λ) = c_Q(x)^⊤ λ. The report's c_p d x handles this correctly but does not list it as a paper imprecision.
4. **Paper, Thm 2.21 proof item 3:** "the minimum value of y such that there exists z …" should read "of t".
5. **Paper, Thm 2.21 proof:** "the original polynomial optimization problem can be written equivalently as Minimize c^⊤λ s.t. λ ∈ Conv(M_d(Ω))":
   - the equality of optimal values is asserted without proof (it is Claim 1 + the minimum principle);
   - "Since Ω is compact, so are M_d(Ω) and its convex hull" uses the finite-dimensional Carathéodory compactness fact without
     proof or citation (it is L11).
6. **Paper, Thm 2.15 proof:** (8) gives the P_ij for cl(graph f), but after "we may assume f takes values in [−1,1]" the construction
   (10) needs the P_ij for cl(graph h). Under the WLOG reading this is consistent, but the order of the text is wrong. The report's
   route makes this moot.
7. **Paper, Case 2 of Thm 2.15 (checked, not an error):** "∑_j G_ij(x,t,z*_ij) ≥ P_{ij_i}²" is evaluated at the minimizer z*,
   so it does bound min over z ∈ [0,1/2]^J. The only defect is the product index ∏_{ij} vs ∏_i (the report's item 5).
8. **Cor 2.9 item 3 (R1's scope, simplification):** the lower bound on compacts does not need lsc. φ(x) = P(x,y*) ≥ min_{C×Y} P.
   This gives CB from continuity of P on the compact C×Y alone, for both the optimistic and the pessimistic case.
9. **C_cc definition "Q convex in y":** `ConvexOn ℝ Y (Q x)` and `ConvexOn ℝ univ (Q x)` give the same class equality, since (⊆)
   never uses convexity and the constructed Q' is linear (convex on univ). This is a definitional choice to fix project-wide (G2).
10. **L9 interface:** L9 is stated for `MvPolynomial` P, Q, while the bilevel data are functions with `IsPolyFun`. One must
    `obtain` the witnesses and take S := supp(witness P) ∪ supp(witness Q). Trivial, but the blueprint should state L9 with the
    polynomials as data.
11. **(★) padding:** pad short rows with the constant polynomial `1` (always ≥ 0) instead of repeating polynomials; the equality of
    sets is then immediate.

## F. Route assessment and recommended route

The report's route is the cheapest correct one I can see. Recommended for the blueprint, with C1/C2/C7 applied:

- **Thm 2.15 (⊇):**
  - A3 (assumed, or derived from G1 + A1 as in C2) gives w(x) = B + (1+∑xᵢ²)^M ≥ 1 with |f| ≤ w.
  - L1: E = epi f is closed (`lowerSemicontinuous_iff_isClosed_epigraph`) and semialgebraic (A1, one projection).
  - A2 gives E = ⋃ᵢ⋂ⱼ{P_ij ≥ 0}.
  - L3: P̃_ij(x,t) = P_ij(x, t·w(x)) via `bind₁` + `eval₂Hom_bind₁`.
  - L4/L5: gadget, R = ∏ᵢ∑ⱼ(P̃ − (P̃²+1)z)².
  - L6: core lemma, pure order theory in EReal.
  - L7: P = t·w(x), Y = [−1,1]×[0,1/2]^{a×b}.
- **Thm 2.21 (⊇):**
  - L8 + L9: general linearization with exponent-indexed moments, two-inequality proof, opt + pess.
  - L10.
  - L11 via the padding-free finite-union form with an inline weight set (C1).
  - L12 via the same union + A1.
  - This also yields the stronger corollary "every polynomial bilevel problem with compact semialgebraic Y has an equivalent one
    in C_cc (both value functions)". I recommend recording it (report question 5: yes).
- **Pessimistic:** L13 (hypograph, `upperSemicontinuous_iff_IsClosed_hypograph`) and L9's ⨆ half. No −t trick is needed.
- **(⊆):** Prop 2.6 for an arbitrary semialgebraic Y, and Cor 2.9 (+ its usc twin) for compact Y.

## G. Escalations to the orchestrator

1. **Prop 2.5 is false for n ≥ 2** (verified counterexample). Every report that cites Prop 2.5 must use A3 (with CB) or the
   one-variable G1 instead. Decide project-wide whether the assumed lemma is A3 or G1 (+ derivation).
2. **Definition of C_cc / "Q convex in y":** fix ConvexOn on Y (the report's choice) or on univ. Both work for 2.21. Make it
   consistent with R5 (C_bounded, C_unbound).
3. **Prop 2.6 must be stated for arbitrary semialgebraic Y** (R1/R2), not only boxes. It is needed for C_cc ⊆ SA.
4. **Index-type policy:** lower variables over an arbitrary `[Fintype ι]` (here ι = Unit ⊕ (Fin a × Fin b), κ = ↥S) plus one transport
   lemma, versus `Fin m` everywhere. R2's `IsSemialgebraic` must accept `(Fin n → ℝ) × ℝ` and `κ → ℝ`, or transport lemmas are needed.
   This must be consistent with R1/R2/R5.
5. **Form of assumed inputs:** A1/A2/A3 should be named assumed lemmas (or fields of one `RAGAxioms` structure), not ad-hoc
   hypotheses in the theorem signature (C7). FT padding to `Fin a × Fin b` should be part of A2's statement.
6. **Deprecated `stdSimplex` API:** any other report using `stdSimplex`/`isCompact_stdSimplex`/`isClosed_stdSimplex` (e.g. R5 if
   it uses simplices) should switch to an inline weight set.
7. **Cor 2.9 CB** can be proved without lsc (E.8). Pass this to R1.
