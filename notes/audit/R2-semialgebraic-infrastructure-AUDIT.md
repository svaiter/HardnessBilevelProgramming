# AUDIT of R2 — Semialgebraic-geometry infrastructure

Auditor: Opus (adversarial). Sources I checked myself: paper §2.1 and Appendix C (`paper_html.txt`, and `paper.txt`
where the HTML lost `<` characters), the local Mathlib checkout (commit 1df8067a, `lean-toolchain` v4.36.0-rc2), the
TauCeti repository (raw files at commit `3e061c5f`, 2026-11-03, plus a filename listing from a blobless clone), the
jbaelaw repository (full clone), and Schweighofer's notes (`research/dl/schweighofer.txt`, §6.2–6.3).
Scratch copies: `<SCRATCH>/audit/r2tmp/`.

---

## A. Summary verdict

The report can be relied on for the mathematics. I re-derived every lemma in its DAG: the Boolean/sign-condition
layer, Prop C.1, the Def 2.2 encoding, the corrected Prop 2.5 (thin-set lemma, one-variable growth, sup trick), the
corrected Prop 2.6 descriptions and the closure lemma. All are correct, with one exception: the "slice at t = ½"
step in the Prop 2.4-necessity argument is wrong and must be replaced by the slice at t = 0. Its two main
paper-error findings are confirmed: Prop 2.5 is false as stated, and the Prop 2.6 graph formula assumes the
infimum is attained. Its external claims about TauCeti and jbaelaw are accurate in substance.

Things that must change:
1. The univariate root bound is NOT missing from Mathlib. `Polynomial.IsRoot.norm_lt_cauchyBound` is at
   `Mathlib/Analysis/Polynomial/CauchyBound.lean:78`, so lemma L13 should be dropped.
2. The proposed class is not "TauCeti's exact shape". TauCeti's class takes the ring as a parameter
   (`HasSemialgebraicProjections R`), so the two classes need a short bridge instance.
3. I recommend stating the assumption directly in the "forget finitely many coordinates of `α ⊕ β`" form. That
   form is a theorem in both TauCeti (`image_comp_inl`) and jbaelaw (`image_projInl`), and it removes L9/L10
   (effort M).
4. Do not declare a `sorry` instance.
5. State `HasFinitenessTheorem` over any `[Fintype ι]`, so that it fits R4 (`Fin n ⊕ Unit`).
6. The "unavoidability of FT" argument needs the t = 0 correction and a weaker conclusion (C3).

## B. Lemma-by-lemma verdicts

| Id | Verdict | Note |
|---|---|---|
| Def (B″) `IsSemialgebraic := s ∈ generateSetAlgebra (zero sets ∪ positivity sets)` | CONFIRMED | `generateSetAlgebra` (SetAlgebra.lean:117) is the smallest family containing 𝒜 and closed under ∅, complement and binary union (private inductive, :108–113). So it is closed under finite ∪, finite ∩ (`inter_mem` :72, `biInter_mem` :94, which also covers the empty Finset → univ) and difference. It lives in **namespace `MeasureTheory`**, so the code needs `open MeasureTheory`. The zero-set generators are redundant, because {p=0} = ({0<p} ∪ {0<−p})ᶜ and jbaelaw uses positivity sets only. Keeping them is harmless and gives definitional agreement with TauCeti (`Semialgebraic/Basic.lean:75`, identical body). |
| L1–L3 generators, Boolean API, derived sign sets | CONFIRMED | `{p≠0} = {0<p²}`, `{p≥0} = {0<p} ∪ {p=0}`, and so on; `sign_apply`, `sign_pos`, `sign_neg`, `sign_eq_zero_iff` verified. |
| L4 preimage under polynomial maps (+ reindexing, cylinders, graphs, boxes, singletons, balls) | CONFIRMED | Induction via `generateSetAlgebra_induction` (:134; motive depends on the membership proof, which is harmless). The base case uses eval x (bind₁ F p) = eval (i ↦ eval x (F i)) p, from `eval₂Hom_bind₁` (Monad.lean:250). TauCeti has exactly this as `IsSemialgebraic.preimage_eval`. |
| L5 sign-condition normal form | CONFIRMED | The induction cases are as described. The DNF lemma `mem_generateSetAlgebra_elim` (:196) states exactly "finite union of finite intersections of sets t with t ∈ 𝒜 ∨ tᶜ ∈ 𝒜" (nested `Set.Finite`), so the report's description is accurate. Preferring L5 is right. |
| L6 cells are basic | CONFIRMED (simplify) | Correct. Use `Finset.sum_sq_eq_zero_iff` (`Algebra/Order/BigOperators/Ring/Finset.lean:91`), which the report missed, instead of `sum_eq_zero_iff_of_nonneg` + `sq_nonneg` + `pow_eq_zero_iff`. You can avoid `filter` + `equivFin` entirely with uniform data (C5). |
| L7 (A) ⇒ (B) | CONFIRMED | |
| L8 (B) ⇒ (A), Prop C.1 | CONFIRMED | s = ⋃_{σ ∈ Φ} C σ; the cells are pairwise disjoint (one sign vector per point) and basic. |
| S2 Def 2.2 structure (top, bot, graph), `dom` derived | CONFIRMED | dom = (top ∪ bot)ᶜ by EReal trichotomy. The graph field = graph of f restricted to dom (the paper's "f\|dom(f) semialgebraic"). |
| `isSemialgebraicEReal_iff_extGraph` | CONFIRMED, no projection | (→) extGraph = A ∪ B ∪ C. A = {z(inr 1)=0} ∩ preimage of the graph under z ↦ Sum.elim (z∘inl) (fun _ ↦ z(inr 0)). B and C are coordinate equations ∩ preimages of top/bot under z ↦ z∘inl. All are L4 preimages. (←) top = preimage of extGraph under x ↦ Sum.elim x ![0,1], bot under x ↦ Sum.elim x ![0,−1], graph under w ↦ Sum.elim (w∘inl) ![w(inr()), 0]. These are polynomial maps with constant components, i.e. substitution (L4), not projection. Checked that each preimage meets only the intended disjunct. |
| `isSemialgebraicEReal_coe_iff` | CONFIRMED | top = bot = ∅; the graph field equals `graphSet f` by `EReal.coe_eq_coe_iff`. |
| S3 class `HasSemialgebraicProjections` (one field via `Fin.tail`) | CONFIRMED (mathematically sufficient); FIXED (claims) | It is sufficient for ∃/∀ over finite `α ⊕ β`: reindex by L4 along an equivalence, project one coordinate at a time, and use complement for ∀. It is **not** "exactly TauCeti's class": TauCeti declares `variable (R) in class HasSemialgebraicProjections : Prop` (Basic.lean:405–415), i.e. `TauCeti.HasSemialgebraicProjections ℝ`. A bridge instance is needed (C2). Better field: C3/F. |
| L9 one coordinate, any position | CONFIRMED but awkward | The `{i // i ≠ i₀}` subtype is unnecessary bookkeeping. TauCeti instead proves `image_comp_inr` by `Finite.induction_empty_option` (Image.lean:88). Better still, make the general form the field (F). |
| L10 `exists_sumElim`, L11 `forall_sumElim`, bounded quantifiers | CONFIRMED | Base case β empty: the unique u gives a preimage. ∀ = (∃ ¬)ᶜ. ∀ε>0 φ ≡ ∀ε (ε ≤ 0 ∨ φ). ∃ y ∈ Θ ≡ ∃ y (y ∈ Θ ∧ φ). |
| L_closure, interior | CONFIRMED | `Metric.mem_closure_iff` (Pseudo/Defs.lean:1231, namespace `Metric`): a ∈ closure s ↔ ∀ε>0, ∃b∈s, dist a b < ε. `dist_pi_lt_iff` (Pseudo/Pi.lean:70) needs `0 < r`, which the ε>0 guard provides, and the sup metric on `ι → ℝ` needs `[Fintype ι]`. Then \|y_i − x_i\| < ε ⟺ −ε < y_i − x_i ∧ y_i − x_i < ε, polynomial in (y, ε, x). One ∃-block over x (\|ι\| coordinates) and one ∀ over ε. TauCeti `Semialgebraic/Topology.lean:139` does exactly this. **But no downstream route needs it any more** (G4). |
| L12 thin-set lemma | CONFIRMED | Re-derived. If a nonempty cell C σ ⊆ S had no zero-sign polynomial of positive degree in variable 0, then every σ_i = 0 polynomial is independent of t (`natDegree_finSuccEquiv` = `degreeOf 0`, Equiv.lean:772; `eq_C_of_natDegree_eq_zero`; `eval_eq_eval_mv_eval'`, :669). The σ_i ≠ 0 polynomials keep their sign near t by continuity, so the fibre would contain an open interval, which is a contradiction. This also covers cells with no zero entry at all (they are open in t). Taking the product of one chosen factor per nonempty Φ-cell gives P ≠ 0, S ⊆ {P = 0} and `degreeOf 0 P > 0` (`natDegree_prod`, BigOperators.lean:367, domain coefficients). For S = ∅, use X 0. Same as Schweighofer 6.2.1 (verified). |
| L13 Cauchy root bound "NOT IN MATHLIB" | FIXED | It is in Mathlib: `Polynomial.cauchyBound` (CauchyBound.lean:37) and `Polynomial.IsRoot.norm_lt_cauchyBound (hp : p ≠ 0) (h : p.IsRoot a) : ‖a‖₊ < cauchyBound p` (:78), with cauchyBound = sup_{k<d} ‖a_k‖₊ / ‖a_d‖₊ + 1. Drop L13. |
| L14 univariate asymptotics | CONFIRMED | `eventually_atTop_not_isRoot` (Analysis/Polynomial/Basic.lean:40: `P ≠ 0 → ∀ᶠ x in atTop, ¬P.IsRoot x`); `abs_tendsto_atTop` (:87: `0 < P.degree → Tendsto (fun x ↦ \|eval x P\|) atTop atTop`); `eval_eq_sum_range` (Eval/Degree.lean:63). Adequate. |
| L15 one-variable growth | CONFIRMED (simplify plumbing) | The argument is correct. For MvPolynomial (Fin 1) ℝ ≅ ℝ[X], use `MvPolynomial.uniqueAlgEquiv` (Equiv.lean:63, any `[Unique σ]`) rather than `finSuccEquiv ℝ 0` + `isEmptyAlgEquiv`. Feed the specialised polynomial `P'.map (eval ![ρ])` to `norm_lt_cauchyBound`; its leading coefficient is (a_d)(ρ) ≠ 0 for large ρ. |
| L16 corrected Prop 2.5 | CONFIRMED | The set A_ρ = {\|f x\| : Σx² ≤ ρ} is nonempty (x = 0) and bounded above (hb). So s = sSup A_ρ ⟺ (∀a∈A_ρ, a ≤ s) ∧ ∀ε>0 ∃a∈A_ρ, s−ε < a. This is valid exactly under these two facts (Real.sSup junk values otherwise). G ⊆ ℝ² has subsingleton fibres, so L15 applies. Final constant: c = max c₁ B(ρ₀), using (1+ρ)^M ≥ 1. |
| L17 polynomial bound | CONFIRMED | \|x_i\| ≤ 1 + Σx_j², so a monomial of degree k is ≤ (1+Σx²)^k; summing gives (Σ\|coeff\|)(1+Σx²)^{totalDegree}. |
| §2.E FT-necessity argument | FIXED | The slice t = ½ is wrong; the slice t = 0 works. The conclusion is only "some bounded-quantifier closed polynomial encoding of K is necessary", not "FT is necessary" (C3). |
| (FT′) and its sufficiency for Thm 2.15 | CONFIRMED | FT ⇒ FT′ via the gadget (re-derived, C3). FT′ is exactly R4's core hypothesis (★★) for some closed E with graph f ⊆ E ⊆ epi f (R4 uses E = epi f, not cl graph). FT′ does not suffice for Thm 2.20: the union gadget is a product, which is not convex in z. |
| F1–F4 textbook route (Schweighofer 6.2.1–6.2.4, 6.3.3) | CONFIRMED (summary) | Checked against the local text. F4's U = {C(1+‖x‖²)^k f_i² < (2^m ∏_j g_ij)^N, g_ij > 0} matches 6.3.3 verbatim; the closed ⇔ open reduction is 6.3.3's first chain (uses 1.8.1 distributivity). |
| L18 φ = ⊤ ↔ Θ = ∅ | CONFIRMED | `iInf_eq_top` (to_dual of `iSup_eq_bot`, CompleteLattice/Basic.lean:350–351) twice + `EReal.coe_ne_top` (:270). |
| L19 φ = ⊥ ↔ ∀δ ∃y∈Θ, P < δ | CONFIRMED | `EReal.eq_bot_iff_forall_lt` (Data/EReal/Basic.lean:438, statement `x = ⊥ ↔ ∀ y : ℝ, x < y`), `iInf_lt_iff` (to_dual of `lt_iSup_iff`, CompleteLattice/Defs.lean:318–319; EReal is a `CompleteLinearOrder`). |
| L20 φ = ↑r ↔ lower bound ∧ ε-approximation | CONFIRMED | (⇐) If ↑r < φ, take a real q strictly between them (`EReal.lt_iff_exists_real_btwn`, :863), set ε = q − r, get y with P < q, so φ ≤ ↑P < ↑q < φ, a contradiction. Θ = ∅ is consistent (both sides false). |
| L21 / Prop 2.6 for any semialgebraic Y | CONFIRMED | Θ = {(x,y) \| y ∈ Y ∧ ∀y' (y' ∈ Y → Q(x,y) ≤ Q(x,y'))}, which needs Y semialgebraic. No attainment is used. |
| S8 Carathéodory + T–S | CONFIRMED | Padding to exactly K+1 points with zero weights is fine. The cardinality bound the report left to "locate" exists: `AffineIndependent.card_le_finrank_succ` (`LinearAlgebra/AffineSpace/FiniteDimensional.lean:348`). Simpler: quantify ∃ y_i ∈ Y with a_i = M_d(y_i) directly, so A = M_d(Y) need not be shown semialgebraic first. |

## C. Corrections

**C1 (Cauchy bound is in Mathlib).**
- Wrong claim: "L13 … NOT IN MATHLIB; `grep -ri cauchy Mathlib/Algebra/Polynomial` finds nothing".
- Why: the grep searched the wrong directory.
- Fix: use `Polynomial.IsRoot.norm_lt_cauchyBound` (`Mathlib/Analysis/Polynomial/CauchyBound.lean:78`, any `NormedDivisionRing`, so ℝ). It gives \|s\| < 1 + max_{k<d}\|a_k\|/\|a_d\| ≤ 1 + Σ_{k<d}\|a_k\|/\|a_d\|, which is what L15 needs. Delete L13 from the DAG.

**C2 (TauCeti class shape; "drop-in").**
- Wrong claim: "Exactly TauCeti's class (same name, same field), so a later `instance` is a drop-in".
- Facts: TauCeti's class is `TauCeti.HasSemialgebraicProjections (R)` over `[CommRing R] [LinearOrder R]`, with field `isSemialgebraic_image_tail {n} {s : Set (Fin (n+1) → R)}`. The ℝ instance is `instance : HasSemialgebraicProjections ℝ` in `CAD/Existence.lean`.
- Fix: R2's ℝ-only, parameterless class is a different declaration. Discharging it needs a short bridge, `instance : HasSemialgebraicProjections := ⟨fun hs => TauCeti.HasSemialgebraicProjections.isSemialgebraic_image_tail hs⟩`. This works only after `IsSemialgebraic` and `TauCeti.IsSemialgebraic` are shown to agree on ℝ; they have the same body, so `Iff.rfl` or `unfold` should do it.
- Wording: say "same design; a short bridge", not "drop-in".

**C3 (FT-necessity argument, §2.E).**
- Wrong claim: "the slice T ∩ {t = ½} is forced to be K × {½} whatever sandwiched T is used".
- Why it fails: with h = 0 on K and 1 off K, graph(h) has no point at t = ½. The sandwich graph(h) ⊆ T ⊆ epi(h) therefore gives only T ∩ {t=½} ⊆ K × {½}; it does not force equality.
- Correct slice: t = 0. Graph ∩ {t=0} = K × {0} = epi ∩ {t=0}, so T ∩ {t=0} = K × {0}.
- What the argument then shows: K = {x | ∃ z, (0,z) ∈ Θ(x)}, where Θ(x) = argmin_Y Q(x,·). This is a polynomial **zero** set only if min_Y Q(x,·) ≡ 0, as in the paper's gadgets. In general it is the bounded-quantifier closed formula ∃(t,z) ∈ Y [t = 0 ∧ ∀(t',z') ∈ Y, Q(x,t,z) ≤ Q(x,t',z')].
- Conclusion to state: Thm 2.15 implies that every closed semialgebraic set has a bounded-quantifier encoding by non-strict polynomial conditions. It does not imply FT, and the report should not say FT is "unavoidable". "FT is the natural / only known cheap input" is defensible.
- The example showing that relaxing > to ≥ fails is CONFIRMED. K = {t=0} = {xt=0, x>0} ∪ {xt=0, −x>0} ∪ {x²+t²=0}; the relaxation contains the line {x=0}, which is not inside epi(0) = {t ≥ 0}.
- FT ⇒ FT′ is CONFIRMED. Take Q(x,z) = ∏_i Σ_j (P_ij − (P_ij²+1) z_ij)² with z ∈ [0,½]^{I×J}. Facts used:
  - ∃ z ∈ [0,½], P = (P²+1) z ⟺ P/(P²+1) ∈ [0,½] ⟺ P ≥ 0, since P/(P²+1) ≤ ½ always.
  - A sum of squares vanishes iff each term vanishes.
  - The factors use disjoint blocks of z, so ∃z ∏_i F_i = 0 ⟺ ∃i ∃z_i F_i = 0.
  - I = ∅ gives Q = 1 (K = ∅); J = ∅ gives the factor 0 (K = univ).

**C4 (no `sorry` instance).** The report recommends putting the ℝ-instance in one quarantined file with `sorry`. Problems:
- Any file that imports it gets the instance silently through typeclass inference.
- A corollary stated without the binder then depends on `sorryAx`, and nothing visible in its signature says so.

Recommendation:
- Declare no instance. Every top-level theorem carries `[HasSemialgebraicProjections]` (and `[HasFinitenessTheorem]` where needed) as an explicit binder.
- If an unconditional statement is wanted, add a separate leaf file, not imported by the development: `theorem hasSemialgebraicProjections_real : HasSemialgebraicProjections := sorry`. Later replace it by the TauCeti bridge (C2) or a port of jbaelaw.
- Then `#print axioms` on the main development stays clean, and the assumed-vs-proved labels stay honest.

**C5 (L6/L8 bookkeeping).** Uniform data avoids `Finset.filter`, `equivFin` and dependent `Fin (k i)`. For a sign family p : Fin m → MvPolynomial and σ:
- P_σ := Σ_i (if σ i = 0 then p i ^ 2 else 0);
- Q_σ i := if σ i = 1 then p i else if σ i = −1 then −p i else 1.

The constant 1 always satisfies 0 < 1. Then C σ = {P_σ = 0 ∧ ∀ i : Fin m, 0 < Q_σ i}, and the normal form has uniform κ = Fin m. That is R3's "uniform κ" variant (G1).

**C6 (Def 2.1 item 5 is not an error).** The report says the definition of a semialgebraic function "tacitly needs U semialgebraic". The paper defines semialgebraicity via the graph, and U = π(graph) then follows by T–S, so nothing is tacit. Only the typo "S ∈ ℝⁿ" (also in Prop C.1's statement) is real.

**C7 (minor line numbers).** `le_iSup` is declared at `Order/CompleteLattice/Basic.lean:210`; the report's `:211` is the proof line. The file for `le_iSup :211`, `le_iSup_of_le :222` is `Basic.lean`; the report's table makes it look like `Defs.lean`. `Finset.sum_eq_zero_iff_of_nonneg` is generated by `@[to_additive]` from `Finset.prod_eq_one_iff_of_one_le` (`Algebra/Order/BigOperators/Group/Finset.lean:239–240`); the report left this "not pinned".

**C8 (unverified citation claim).** "The cited source [51] … all carry a hypothesis that excludes this" has not been checked for [51] (van den Dries–Miller §4.12). Neither R2 nor R4 could access it. Record it as unverified. The counterexample alone settles the matter.

## D. Mathlib citation check

All lines were read in the local checkout. ✓ = name exists at the given file:line and the statement is adequate.

| Declaration | Exists | file:line | Adequate | Note |
|---|---|---|---|---|
| `MeasureTheory.generateSetAlgebra` | ✓ | MeasureTheory/SetAlgebra.lean:117 | ✓ | namespace `MeasureTheory` |
| `isSetAlgebra_generateSetAlgebra` | ✓ | :121 | ✓ | |
| `self_subset_generateSetAlgebra` | ✓ | :128 | ✓ | |
| `generateSetAlgebra_induction` | ✓ | :134 | ✓ | cases base/empty/compl/union |
| `IsSetAlgebra.generateSetAlgebra_subset` | ✓ | :149 | ✓ | |
| `mem_generateSetAlgebra_elim` | ✓ | :196 | ✓ | DNF with nested `Set.Finite` |
| `IsSetAlgebra` fields; `univ_mem/inter_mem/sdiff_mem/biUnion_mem/biInter_mem` | ✓ | :60, 68, 72, 78, 90, 94 | ✓ | |
| `SignType`, `deriving Fintype`, `SignType.sign`, `sign_apply`, `sign_pos`, `sign_neg`, `sign_eq_zero_iff` | ✓ | Basic/Sign/Defs.lean:28, 32, 265, 273, 280, 283, 311 | ✓ | |
| `MvPolynomial.eval_sum`, `eval_prod` | ✓ | Algebra/MvPolynomial/Eval.lean:295, 299 | ✓ | |
| `eval₂Hom_bind₁`, `aeval_bind₁`, `bind₁_X_right` | ✓ | Algebra/MvPolynomial/Monad.lean:250, 254, 136 | ✓ | |
| `MvPolynomial.eval_rename` | ✓ | Rename.lean:244 | ✓ | |
| `finSuccEquiv`, `finSuccEquiv_apply`, `eval_eq_eval_mv_eval'`, `degree_finSuccEquiv`, `natDegree_finSuccEquiv` | ✓ | Equiv.lean:606, 619, 669, 762, 772 | ✓ | `natDegree_finSuccEquiv` needs no `f ≠ 0`; `degree_` does |
| `sumAlgEquiv`, `optionEquivLeft`, `isEmptyAlgEquiv` | ✓ | Equiv.lean:354, 424, 222 | ✓ | |
| `MvPolynomial.uniqueAlgEquiv` | ✓ (missed by report) | Equiv.lean:63 | ✓ | better for L15 |
| `MvPolynomial.funext`, `funext_set` | ✓ | Funext.lean:83, 57 | ✓ | |
| `MvPolynomial.continuous_eval` | ✓ | Topology/Algebra/MvPolynomial.lean:31 | ✓ | |
| `finite_setOfPred_isRoot`, `exists_max_root`, `eq_zero_of_infinite_isRoot`, `card_roots'`, deprecated `finite_setOf_isRoot` | ✓ | Algebra/Polynomial/Roots.lean:154, 174, 171, 78, 159 | ✓ | |
| `eventually_atTop_not_isRoot`, `abs_tendsto_atTop`, `isEquivalent_atTop_lead`, `tendsto_atTop_of_leadingCoeff_nonneg` | ✓ | Analysis/Polynomial/Basic.lean:40, 87, 50, 64 | ✓ | ordered normed field |
| Cauchy root bound | **EXISTS** (report: NOT IN MATHLIB) | Analysis/Polynomial/CauchyBound.lean:37, 78 | ✓ | C1 |
| `eval_eq_sum_range` | ✓ | Eval/Degree.lean:63 | ✓ | |
| `eq_C_of_natDegree_eq_zero`, `eq_C_of_degree_le_zero` | ✓ | Degree/Operations.lean:485, 162 | ✓ | |
| `Polynomial.natDegree_prod` | ✓ | Polynomial/BigOperators.lean:367 | ✓ | needs factors ≠ 0, `NoZeroDivisors` |
| `coeff_natDegree`, `leadingCoeff_ne_zero`, `leadingCoeff_map`, `map_ne_zero`, `coeff_map` | ✓ | Degree/Defs.lean:84, 362; FieldDivision.lean:286, 274; Eval/Coeff.lean:81 | ✓ | |
| `Finset.prod_eq_zero_iff`, `prod_pos`, `prod_nonneg` | ✓ | BigOperators/GroupWithZero/Finset.lean:57; Order/…/GroupWithZero/Finset.lean:160, 34 | ✓ | |
| `Finset.sum_eq_zero_iff_of_nonneg` | ✓ (generated) | to_additive of Order/BigOperators/Group/Finset.lean:240 | ✓ | |
| `Finset.sum_sq_eq_zero_iff` | ✓ (missed) | Order/BigOperators/Ring/Finset.lean:91 | ✓ | use in L6 |
| EReal: `coe_le_coe_iff`, `coe_lt_coe_iff`, `coe_eq_coe_iff`, `coe_ne_bot`, `coe_ne_top`, `eq_top_iff_forall_lt`, `eq_bot_iff_forall_lt`, `lt_iff_exists_real_btwn` | ✓ | Data/EReal/Basic.lean:55, 61, 67, 258, 270, 430, 438, 863 | ✓ | |
| `le_iInf_iff`, `iInf_eq_top`, `iInf_lt_iff`, `iInf_le`, `iInf_le_of_le`, `iInf₂_le`, `le_iInf₂_iff`, `iInf_emptyset` | ✓ (to_dual) | sources: Basic.lean:279–280 (`@[to_dual (attr := simp) le_iInf_iff]`), 350–351, Defs.lean:318–319, Basic.lean:209–210, 221–222, 225–226, 283–284, 583–584 | ✓ | names confirmed by uses elsewhere in Mathlib (e.g. Algebra/Module/SpanRank.lean:90, Topology/MetricSpace/Closeds.lean:46) |
| `le_csSup`, `csSup_le`, `lt_csSup_iff`, `Real.sSup_empty`, `Real.sSup_of_not_bddAbove` | ✓ | ConditionallyCompleteLattice/Basic.lean:101, 105, 270; Archimedean/Real/Basic.lean:168, 183 | ✓ | |
| `Metric.mem_closure_iff`, `dist_pi_lt_iff` | ✓ | Pseudo/Defs.lean:1231 (namespace Metric opened at 1211); Pseudo/Pi.lean:70 | ✓ | needs `0 < r` |
| `closure_union`, `closure_iUnion_of_finite`, `IsClosed.closure_eq`, `closure_minimal`, `closure_prod_eq` | ✓ | Topology/Closure.lean:299, 316, 226, 199; Constructions/SumProd.lean:529 | ✓ | |
| `isOpen_lt`, `isClosed_le`, `isClosed_eq`, `ContinuousAt.eventually_lt`, `Filter.Tendsto.eventually_lt` | ✓ | OrderClosed.lean:599, 444; Separation/Hausdorff.lean:492; OrderClosed.lean:702, 695 | ✓ | |
| `lowerSemicontinuous_iff_isClosed_epigraph`, alias `LowerSemicontinuous.isClosed_epigraph` | ✓ | Semicontinuity/Basic.lean:353, 357 | ✓ | |
| `IsCompact.exists_isMinOn`, `exists_isMaxOn`, `IsCompact.bddAbove_image`, `isCompact_univ_pi` | ✓ | Order/Compact.lean:255, 273, 359; Compactness/Compact.lean:1172 | ✓ | |
| `pi_norm_le_iff_of_nonneg'`, `norm_le_pi_norm'`, `pi_norm_lt_iff'` | ✓ | Normed/Group/Constructions.lean:319, 346, 338 | ✓ | |
| `Fin.tail`, `Fin.cons`, `tail_cons`, `cons_self_tail`, `Fin.consEquiv`, `Fin.snocEquiv` | ✓ | Data/Fin/Tuple/Basic.lean:107, 114, 117, 171, 184, 722 | ✓ | |
| `finSumFinEquiv`, `Equiv.sumArrowEquivProdArrow` | ✓ | Logic/Equiv/Fin/Basic.lean:224; Logic/Equiv/Prod.lean:390 | ✓ | |
| `convexHull_eq_union`, `eq_pos_convex_span_of_mem_convexHull` | ✓ | Analysis/Convex/Caratheodory.lean:106, 123 | ✓ | |
| `AffineIndependent.card_le_finrank_succ` | ✓ (report: "locate") | LinearAlgebra/AffineSpace/FiniteDimensional.lean:348 | ✓ | |
| `Set.Definable`, `Definable.preimage_comp`, `image_comp_equiv`, `exists_of_finite`, `forall_of_finite` | ✓ | ModelTheory/Definability.lean:54, 173, 180, 274, 283 | ✓ | |
| `FirstOrder.Ring.mvPolynomial_zeroLocus_definable` | ✓ | ModelTheory/Algebra/Ring/Definability.lean:29 | ✓ | |
| `IsRealClosed` (+ `instance : IsRealClosed ℝ`) | ✓ | FieldTheory/IsRealClosed/Basic.lean:52; Real.lean:15 | — | no QE |
| semialgebraic / Tarski–Seidenberg / o-minimal / CAD | NOT IN MATHLIB ✓ | — | — | grep "semialgebraic\|semi-algebraic": 0 hits. "Tarski" appears only as Sturm–Tarski (Sturm/Sequence.lean) and Tarski–Vaught/fixed point. "quantifier elimination" appears only in a Presburger TODO. |
| finiteness theorem, Łojasiewicz, growth bound | NOT IN MATHLIB ✓ | — | — | also absent from TauCeti (searched filenames and RealAlgebraic sources) |

**External libraries (verified, see §3 of the brief):**
- **TauCeti** — https://github.com/TauCetiProject/TauCeti. Accurate claims:
  - Apache-2.0 (LICENSE fetched); about 24,004 commits (GitHub page).
  - `lean-toolchain` = `leanprover/lean4:v4.36.0-rc2`; Mathlib manifest rev = `1b1ccf4b088b32fa3f23f2de1127433254a81e1e` (fetched at HEAD `3e061c5f`, 2026-11-03). Both match the report. The Mathlib rev moves hourly per the README, so pin a commit if TauCeti is ever used.
  - Files exist as described. `Semialgebraic/Basic.lean:75` has the identical definition and `:381` has `exists_eq_setOf_sign_eval`. `CAD/Existence.lean` has `exists_isCAD_signInvariant` and `instance : HasSemialgebraicProjections ℝ` (proved via `IsCAD.isSemialgebraic_image_tail`). `Topology.lean:139` has `IsSemialgebraic.closure`. `Image.lean:88/137` have `image_comp_inr` / `image_comp_inl`. `QuantifierElimination.lean` has `exists_isQF_realize_iff` and `Set.Definable.isSemialgebraic`.
  - PR #20523 ("semialgebraic sets are the sets definable in the field language") was merged by Bors on 2026-10-24 and added `RingLanguage.lean` (144 lines).
  - Sorry check: I fetched the full TauCeti import closure of `CAD/Existence`, `Topology` and `Image` (118 modules). Grep found **no `sorry`, no `axiom` declaration, no `admit`** (the only hits are the English word "admits" in comments). This is a text check; nothing was compiled. The README says axiom audits run in CI.
  - The library has 23,858 `.lean` files, so depending on it as a whole is a heavy dependency.
- **jbaelaw/tarski-seidenberg-lean-20261011** — confirmed:
  - Single commit 994053f7 (2026-10-11, author "Ji Ho Bae"). The README says it was written by "Claude Fable 5.1 (Claude Code), in one session".
  - Lean v4.34.1, Mathlib `d13f23b7`.
  - **No LICENSE file** (clone listing).
  - 10 files `TS/*.lean`, 2,801 lines, no `sorry`/`axiom`/`admit` by grep. `Verify.lean` has 19 `#print axioms` lines.
  - `IsSemialgebraic := Semialg (Rev (mvEv ι))` (positivity generators). `image_proj` is over `Option ι`; `image_projInl` (TS/Main.lean:246) is `[Fintype β] {s : Set (α ⊕ β → ℝ)}`.

## E. Missed issues

1. Mathlib's Cauchy bound (C1), `Finset.sum_sq_eq_zero_iff`, `MvPolynomial.uniqueAlgEquiv` and `AffineIndependent.card_le_finrank_succ` all exist and simplify L6, L13, L15 and S8.
2. A `sorry` instance can be picked up silently by typeclass search (C4).
3. Namespace: `generateSetAlgebra`, `IsSetAlgebra` and `generateSetAlgebra_induction` are in `MeasureTheory`.
4. The finiteness assumption is stated only for `Fin n → ℝ`, but R4 needs it on `Fin n ⊕ Unit → ℝ`. Moving it there means transporting closedness along a homeomorphism of Pi types; that work disappears if the class quantifies over `[Fintype ι]` (G2).
5. The growth bound has two shapes. R2's A3 is `|f x| ≤ c (1+Σx²)^M`, while D1/R4 use `B + (1+Σx²)^M`. They are equivalent: for Σx² ≤ 1 take B = c·2^M, and for Σx² ≥ 1 take K with 2^K ≥ c, so c(1+s)^M ≤ (1+s)^{M+K}. Pick one project-wide shape (D1's), and keep this as a short conversion lemma.
6. Paper's Prop 2.5 holds for n = 1: any semialgebraic f : ℝ → ℝ is polynomially bounded at infinity (Schweighofer 6.2.1). The failure needs n ≥ 2. The report's example is n = 2, which is correct; the blueprint remark should say "n ≥ 2".
7. Paper, Thm 2.15 obs. 3: "B + ‖x‖^N ≥ B, ∀x ∈ ℝ" should be ℝⁿ (typo; R4's scope).
8. Paper, Thm 2.20 obs. 2: N is reused for both the number of pieces and the exponent in "B + ‖x‖^N" (notation clash; R5's scope).
9. Thm 2.21 cites [52, Theorem 0.0.1] for Carathéodory; [52] is Vershynin's *High-Dimensional Probability*. This is an unusual source but not wrong. Also "Ω ⊆ ℝⁿ" clashes with the upper dimension n, and "M_d(Ω) ⊆ ℝ^{R_d}" clashes with K_d. Typos, R4's scope.
10. Prop C.1's proof never says *why* each cell T_I lies inside or outside each S_i. The reason is that membership in S_i is a Boolean function of the signs of the h's. The report's L8 supplies it implicitly; worth one sentence in the blueprint.

## F. Route assessment and recommended route

The route is correct and close to minimal. Concrete improvements:

1. **Definition.** Keep (B″) exactly as written (identical to TauCeti). Use `open MeasureTheory`. The (A) normal form and Prop C.1 are theorems. Use the uniform-data cell encoding (C5) and `Finset.sum_sq_eq_zero_iff`.

2. **T–S assumption shape.** Use the general "forget finitely many coordinates" field instead of `Fin.tail`:
   ```lean
   class HasSemialgebraicProjections : Prop where
     image_comp_inl {α β : Type} [Fintype α] [Finite β] {S : Set (α ⊕ β → ℝ)} :
       IsSemialgebraic S → IsSemialgebraic ((fun z : α ⊕ β → ℝ => z ∘ Sum.inl) '' S)
   ```
   - It is classically equivalent to the one-coordinate form.
   - It is literally `TauCeti.IsSemialgebraic.image_comp_inl` and `TS.IsSemialgebraic.image_projInl`, so either library discharges it in a few lines.
   - It removes L9/L10 (index transport, effort M). L11 (∀) and bounded quantifiers remain S.
   - If the one-coordinate field is preferred for minimality, then prove L10 by `Finite.induction_empty_option`, as TauCeti does, not with the `{i // i ≠ i₀}` subtype.

3. **FT assumption.** `class HasFinitenessTheorem` quantified over `{ι : Type} [Fintype ι]`. Field: closed and semialgebraic ⇒ `∃ a b (P : Fin a → Fin b → MvPolynomial ι ℝ), s = {x | ∃ i, ∀ j, 0 ≤ eval x (P i j)}`, which matches R4's hFT and R5's A2. Do not add a separate FT′ class: FT′ is derived from FT by the gadget (C3). Mention FT′ in the blueprint as the minimal input for Thm 2.15.

4. **No instances.** Assumptions are explicit binders. Any `sorry` lives only in an unimported leaf file (C4).

5. **Growth bound (D1).** R2's proof of A3 from T–S alone is confirmed, and with C1 it is cheaper:
   - L12 thin-set lemma: M, about 150 lines.
   - L15: M, about 150 lines with `uniqueAlgEquiv` and `norm_lt_cauchyBound`.
   - L16 sup trick: M, about 150 lines.
   - Total M–L, about 400–600 lines, needing only `HasSemialgebraicProjections` (no FT).

   Recommendation:
   - Keep D1 for v1: A3 as a named assumption, `class HasGrowthBound` or a hypothesis.
   - Mark it "derivable from T–S; proof plan L12→L15→L16, effort M–L" as the first phase-2 item, because proving it reduces the trusted base from three assumptions to two.
   - Use D1's `B + (1+Σx²)^M` shape (E5).

6. **Prop 2.6.**
   - State it for any semialgebraic `Y ⊆ ι → ℝ` with `[Fintype ι]`, and for `IsPolyFun` P, Q as in D29, so it applies to the class definitions directly.
   - Use L18–L20. L20 is the same lemma as R1's V3 `valueFun_eq_coe_iff`, so keep one copy, in R1's framework file.
   - Get the pessimistic version by negation (D31). `IsSemialgebraicEReal` is closed under negation without T–S: take the preimage under t ↦ −t and swap the top and bot sets.

7. **Closure lemma.** Optional; nothing in the recommended routes uses it (G4).

## G. Items to escalate to the orchestrator

1. **Normal-form interface for R3.** R2 exports `∃ m (S : Fin m → Set) , (∀ i, IsBasicSemialgebraic (S i)) ∧ …`, with the data hidden inside an existential. R3 wants the data form `exists_basic_family`: (ι : Type) [Fintype ι], κ i, P i, Q i j.
   - Have R2 export the data form directly: `∃ (m k : ℕ) (P : Fin m → MvPolynomial σ ℝ) (Q : Fin m → Fin k → MvPolynomial σ ℝ), S = ⋃ i, {w | eval w (P i) = 0 ∧ ∀ j, 0 < eval w (Q i j)}`.
   - This is uniform κ = Fin k, which falls out of C5. It is R3's stated "uniform κ" variant: R3 uses `ι × κ` and no `Sigma`.
   - Also export the pairwise-disjoint version (Prop C.1) in the same data form.
2. **Ambient types.** R4's hFT and `hsa` use `Set ((Fin n → ℝ) × ℝ)`, which does not typecheck against `IsSemialgebraic : Set (ι → ℝ) → Prop`. R4 must switch to `Fin n ⊕ Unit → ℝ` with `Sum.elim x (fun _ => t)`, the convention R2 and R3 already use. The FT class must therefore be stated over a general `[Fintype ι]` (F3).
3. **Structure field names.** R2 has `IsSemialgebraicEReal` with fields `top`, `bot`, `graph`; R3 has `graph`, `top`, `bot`, `dom` (dom redundant and unused). Standardise on R2's version plus a derived `dom` lemma. R3 only needs `graph` and `bot`.
4. **Closure is no longer needed.**
   - R4 (Thm 2.15) uses E = epi f: semialgebraic by one projection, closed by lsc.
   - R5 (Thm 2.20, D19) uses D_i = {f ≤ P_i}: Boolean operations only.
   - So no route needs "closure of a semialgebraic set is semialgebraic". Keep R2's `IsSemialgebraic.closure` as an optional lemma (S–M), or drop it.
   - Thm 2.15 still needs one T–S use (epigraph). Thm 2.20 needs **no** T–S at all, only FT.
5. **Assumption inventory, final.**
   - (i) `HasSemialgebraicProjections`, general-field form (F2).
   - (ii) `HasFinitenessTheorem` over a Fintype index.
   - (iii) the A3 growth bound (D1), derivable from (i) at effort M–L.
   - None is declared as an instance; all are explicit binders.
   - Record FT′ (implied by (ii) via the gadget) as the minimal input for Thm 2.15.
6. **External dependency decision.** TauCeti is Apache-2.0, on the same toolchain, has a text-level sorry-free T–S via CAD, and its definition matches. But it is a moving, roughly 24k-file AI-written library. jbaelaw has no license.
   - Recommendation: do not depend on either library.
   - Mirror TauCeti's definition and C2-compatible names, and leave the bridge as documented future work.
   - Any later use of TauCeti must pin a commit.
7. **"FT is unavoidable" wording.** Downgrade to "Thm 2.15 implies a bounded-quantifier, closed encoding of every closed semialgebraic set; FT is the standard input, and no cheaper one is known" (C3). The orchestrator's D19 statement "necessary for the gadget route — proven by the auditor" concerns R5's route and is not affected.
8. **Paper-errata tally from R2's list of 13.**
   - Genuine errors: #1 (Prop 2.5 false, n ≥ 2), #2 (Prop 2.6 graph formula needs attainment; unbounded boxes only), #3 (Prop 2.6 needed for general Y; the paper says "using Theorem 2.15"), #4 (Prop C.1 proof garbled, cells not literally basic), #9 (wrong cross-reference "Theorem 2.21" ×2; one-sided display f ≤ B + ‖x‖^N).
   - Typo: #5, only "S ∈ ℝⁿ"; the "tacitly needs U semialgebraic" part is not an error (C6).
   - Clarifications or remarks, not errors: #6, #7, #8, #10, #12, #13.
   - Not a paper error: #11, which is an HTML extraction artefact; the PDF is correct.
