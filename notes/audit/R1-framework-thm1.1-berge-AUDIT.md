# AUDIT of R1 (framework, Theorem 1.1 + Appendix A, Berge / Cor 2.9 / Rem 2.10, pessimistic counterparts)

Auditor: Opus, independent re-derivation. Paper read myself: §1 (BP, BP-O/BP-P, Thm 1.1), §2 intro (box/unbounded
definitions), §2.1 (dom(φ) partition + graph formula, Def 2.7, Thm 2.8, Cor 2.9, Rem 2.10), Def 2.11, Def 2.16, eq. (18),
§2.4, Appendix A (Thm A.1, Prop A.2, proof of Thm 1.1, Discussion) in `paper_html.txt` (cross-checked against `paper.txt`
where the HTML is truncated, e.g. "dom(f) := {x | f(x) < +∞}" in App. A). Mathlib = local checkout commit 1df8067a; every
citation below was grepped (file:line given). No Lean toolchain: "Lean" = proposed text.

---------------------------------------------------------------------------------------------------------------------

## A. Summary verdict

The report is **reliable on the mathematics**: every framework lemma (F1–F8, V1–V9), the strengthened Theorem 1.1
construction (including the explicit ε in T4), and the closed-graph / compact-projection route for Cor 2.9 (B1–B9) re-derive
correctly, and all ~120 Mathlib file:line citations I checked are present and accurate (two usage-level misuses, below).
What must change: (1) **definitional bug** — `C_cc` (eq. (18)) must require `S.Nonempty`, otherwise `∅` is a compact convex
semialgebraic set, φ ≡ ⊤ ∈ C_cc and the claimed `C_cc ⊆ LSC ∩ CB` (R1 §1.5) is false (the paper has the same omission; R4
missed it too); (2) the class layer (`polyFun`, `boxSet`, `valueFunClass`) is hard-wired to `Fin m`, while R3/R4/R5 all
build on `[Fintype ι]`; either generalise the class layer to `ι : Type` with `[Fintype ι]` (recommended) or supply the
missing class-level transport lemmas (box preimage, `eval_rename`, convexity, compact/convex/SA preimages) — F7 alone is
not enough; (3) R1's "𝒫_box = all boxes" deviates from the paper's explicit definition of "unbounded box" (it is *not*
ambiguous — §2 intro defines it), which matters for the strength of Thm 2.18 (`PP ⊆ C_unbound`); (4) two Lean citation
misuses (`mul_le_mul_left`, `contDiff_apply` arity). Missed paper errors: the §2.1 graph formula for φ|dom(φ) presupposes
attainment (wrong as written), eq. (18) lacks nonemptiness, App. A separability display writes `argmin h(x,·)` for
`argmin h(x,·)²`, Thomae's "global minimum at 1/2" is wrong. Two of R1's 20 "paper errors" are overstated (items 6, 14).

---------------------------------------------------------------------------------------------------------------------

## B. Lemma-by-lemma verdict table

| Id | Verdict | Note |
|---|---|---|
| Defs `argminSet`, `valueFun`, `pvalueFun` | CONFIRMED | `⨅ y ∈ Θ, ↑(P x y)` is `⨅ y, ⨅ (_ : y ∈ Θ), …`; empty ⇒ `⊤` by `iInf_emptyset` (to_dual of `iSup_emptyset`, Order/CompleteLattice/Basic.lean:584), `⨆` over empty ⇒ `⊥` (`iSup_emptyset`). Coercion is `Real.toEReal` (`@[coe]`, Data/EReal/Basic.lean:42–46), the one used by `EReal.coe_le_coe_iff` (:55). Generic in `X Y` — fine for `ι → ℝ`. |
| `boxSet lo hi` (EReal bounds) | CONFIRMED w/ remark | membership `∀ i, lo i ≤ ↑(y i) ∧ ↑(y i) ≤ hi i`: Icc = (↑a,↑b), Ici = (↑a,⊤), Iic = (⊥,↑b), univ = (⊥,⊤) ✓. Also admits empty coordinates (`lo i = ⊤`, `hi i = ⊥`, `lo i > hi i`) — harmless for P/C over boxes (φ ≡ ⊤ ∈ SA), but see E9/G4 for the literal "unbounded box". |
| `boundedBox`, `IsBoundedBox` (with `lo ≤ hi`) | CONFIRMED | nonemptiness is needed for `⊆ CB` (Cor 2.9). `m = 0` gives a singleton (bounded, nonempty) — fine. |
| `valueFunClass`, `P_box`, `P_bounded`, `C_box`, `C_bounded` | CONFIRMED (type-correct) | but see G1–G4 (index type, literal unbounded, IsPolyFun). |
| `C_cc` | **FIXED** | must add `S.Nonempty` (Correction 1). |
| `LSC`, `CB` (EReal-valued, two-sided real bounds) | CONFIRMED | `CB` forces real values (K = {x}). |
| F1, F2 | CONFIRMED | `isMinOn_iff` Order/Filter/Extr.lean:129. |
| F3 (argmin = ∅ ↔ every point strictly beaten) | CONFIRMED | classical `not_le`, `Set.eq_empty_iff_forall_notMem` (Data/Set/Basic.lean:460). |
| F4 (Q ≥ 0 on S, zero attained in S ⇒ argmin = zero set) | CONFIRMED | (⊆) `Q y ≤ Q y₀ = 0 ≤ Q y`; (⊇) `Q y = 0 ≤ Q y'`. Both hypotheses are needed (without the witness the argmin can be a positive-level set). |
| F5 (argmin of A(y₁)+B(y₂) over S₁×S₂ = argmin A × argmin B) | CONFIRMED | (⊆) compare with `(y₁',y₂)` / `(y₁,y₂')` (both in S₁×S₂ since y₂∈S₂, y₁∈S₁), cancel with `add_le_add_iff_right`/`_left` (to_additive of `mul_le_mul_iff_right/left`, Algebra/Order/Monoid/Unbundled/Basic.lean:75/80). (⊇) `add_le_add`. No nonemptiness: if one factor is ∅ both sides are ∅. |
| F5' (product of nonneg factors) is false | CONFIRMED | counterexample: S₁=S₂=ℝ, A=y₁², B=y₂²: argmin(A·B) = {y₁=0}∪{y₂=0} ⊋ {(0,0)} = argmin A × argmin B. |
| F6 (positive scaling / additive shift of the lower level) | CONFIRMED, citation FIXED | math ✓; `mul_le_mul_left` is the wrong lemma in current Mathlib (Correction 4). |
| F7 (reindexing by `e : Y' ≃ Y`) | CONFIRMED, made precise | exact statements + proof in Correction 2. |
| F8 (argmin closed / compact) | CONFIRMED | `S ∩ ⋂ y'∈S, {Q x · ≤ Q x y'}`. |
| V1 (`= ⊤ ↔ Θ = ∅`) | CONFIRMED | |
| V2 (attained ⇒ value) | CONFIRMED | |
| V3 (`= ↑r ↔ (∀y∈Θ, r ≤ P) ∧ ∀ε>0 ∃y∈Θ, P < r+ε`) | CONFIRMED | exactly the paper's dom(φ) clause with δ = r; **no attainment needed**; implies Θ ≠ ∅ (ε=1). Proof: (⇒) `iInf₂_le` + `biInf_lt_iff` (to_dual of `lt_biSup_iff`, Order/CompleteLattice/Defs.lean:339) applied to `↑r < ↑(r+ε)`; (⇐) `le_iInf₂` for `≥`; for `≤` by contradiction: if `↑r < φ`, `EReal.exists_between_coe_real` (Data/EReal/Basic.lean:448) gives real `s`, `r < s`, `↑s < φ`; ε := s−r yields y with `φ ≤ ↑(P x y) < ↑s`. Recommend this hand proof over `iInf_eq_of_forall_ge_of_forall_gt_exists_lt` (single-index form; needs `iInf_subtype'` first). Existential form `(∃ δ:ℝ, φ x = ↑δ) ↔ ∃ δ, …` is immediate. |
| V4 (`= ⊥ ↔ ∀ r:ℝ, ∃ y∈Θ, P < r`) | CONFIRMED | `EReal.eq_bot_iff_forall_lt` (:438) + `biInf_lt_iff`. Θ = ∅: LHS is ⊤ ≠ ⊥ and RHS false — consistent. |
| V5, V5' | CONFIRMED | V5' via `iInf_singleton`/`iSup_singleton` (Order/CompleteLattice/Basic.lean:616, to_dual). |
| V6 (`valueFun (c·P) = ↑c * valueFun P`, c>0) | CONFIRMED | trichotomy is right: ⊤: Θ=∅ both sides, `EReal.coe_mul_top_of_pos` (Operations.lean:579); ⊥: V4 with r/c, `coe_mul_bot_of_pos` (:615); ↑v: V3 with ε/c, `EReal.coe_mul` (Basic.lean:155). Note: likely **unused** (R4 avoids it, see G9). |
| V7 (shift by a(x)) | CONFIRMED | ⊤: `EReal.coe_add_top` (Operations.lean:108); ⊥: `EReal.add_bot` (:46); ↑v: V3 + `EReal.coe_add` (Basic.lean:310). Likely unused (R5 uses attained form). |
| V8 (`pvalueFun P = −valueFun(−P)`) | CONFIRMED | Θ unchanged (Q unchanged); `−⨅ ↑(−P) = ⨆ ↑P`; empty: `−⊤ = ⊥` ✓. Most direct tool: `OrderIso.map_iInf₂` (to_dual of `OrderIso.map_iSup₂`, Order/CompleteLattice/Basic.lean:330) with `EReal.negOrderIso` (Operations.lean:295) + `EReal.coe_neg` (:220). R1's `map_iInf` + hom-class route also valid. |
| V9 | CONFIRMED | |
| Box lemmas, `continuous_uncurry_polyFun` | CONFIRMED | `IsBox.convex` needs a 2-line OrdConnected argument (not given; S). |
| W (Whitney wrapper) | CONFIRMED | `IsOpen.exists_contDiff_support_eq {n : ℕ∞}` (BumpFunction/FiniteDimension.lean:83; vars `[NormedAddCommGroup E]` :41, `[NormedSpace ℝ E] [FiniteDimensional ℝ E]` :45). `n := (⊤ : ℕ∞)` coerces to `∞` = C^∞ (FTaylorSeries.lean:120), not `ω` (:118). Applied to `Cᶜ`: `g p = 0 ↔ p ∈ C` via `Function.support_eq_iff` (to_additive, Algebra/Notation/Support.lean:53–54). Empty open set handled inside Mathlib's proof. |
| A2 (real epigraph closed for EReal-valued lsc f) | CONFIRMED | `lowerSemicontinuous_iff_isClosed_epigraph` (Semicontinuity/Basic.lean:353, needs `[LinearOrder γ] [TopologicalSpace γ] [ClosedIciTopology γ]`, section vars :305/:335); EReal: `OrderTopology` (Topology/Order/Real.lean:37) ⇒ `OrderClosedTopology` ⇒ `ClosedIciTopology` (OrderClosed.lean:449, to_dual). Preimage under `Prod.map id Real.toEReal` (continuous: `continuous_coe_real_ereal`, Topology/Instances/EReal/Lemmas.lean:52) is definitionally the real epigraph. |
| T0–T2 | CONFIRMED | T1: `contDiff_apply` needs explicit `𝕜 F'` (Correction 5); `fun_prop` should close it. |
| T3 (f x ≠ ⊤) | CONFIRMED | g x = 0; Θ = {f x ≤ ↑y₀ ∧ y₁y₂ = 1} by F4 with witness `![(f x).toReal,1,1]` (`EReal.le_coe_toReal`, Basic.lean:420, works for f x = ⊥ since `toReal ⊥ = 0`); value: ↑r case attained at `![r,1,1]`; ⊥ case: `![r,1,1] ∈ Θ ∀r` ⇒ `φ ≤ ↑(r−1) < ↑r` ⇒ ⊥ by `eq_bot_iff_forall_lt`. |
| T4 (f x = ⊤ ⇒ Θ = ∅) | CONFIRMED | v := (g y₁)² + (1−y₁y₂)² > 0 (y₁ = 0 ⇒ second term 1; else first > 0). ε := min 1 (v/(2(g²+1))) ∈ (0,1], so ε² ≤ ε and (gε)² = g²ε² ≤ g²ε ≤ (g²+1)ε ≤ v/2 < v; y' := ![y₀, ε, 1/ε] has identical h-term and zero third term, so Q x y' < Q x y. F3 ⇒ Θ = ∅, V1 ⇒ ⊤. (Uses `g x ≠ 0` only through the first summand.) |
| T5, strengthened Thm 1.1 | CONFIRMED | holds for all lsc `f : ℝⁿ → EReal` with `{f ≠ ⊤}` closed; no "proper", ⊥ allowed. f ≡ ⊤: dom = ∅ closed, Whitney's g has support univ (never 0; not literally "g ≡ 1" as R1 says, immaterial). |
| Pessimistic value of the same (P,Q) | CONFIRMED | ⊤ on dom f (y₀ unbounded above in Θ), ⊥ off dom f. |
| Thm 1.1' (usc, `{f ≠ ⊥}` closed, pessimistic) | CONFIRMED | `Continuous.comp_upperSemicontinuous_antitone` (Basic.lean:1033) with `continuous_neg` on EReal (instance Topology/Algebra/Ring/Real.lean:65) and `EReal.neg_strictAnti.antitone` (Operations.lean:253); `{−f ≠ ⊤} = {f ≠ ⊥}` (`EReal.neg_eq_top_iff` :242); P' := −P, V8, `neg_neg`. |
| B1 (closed graph) | CONFIRMED | only needs Q jointly continuous and S closed; `isClosed_le` (OrderClosed.lean:444) with `hQ` and `hQ.comp (continuous_fst.prodMk continuous_const)`; `Function.uncurry Q p` is `Q p.1 p.2` by rfl. |
| B1' (sequence form, Def 2.7) | CONFIRMED | optional. |
| B2 | CONFIRMED | `IsCompact.exists_isMinOn` (Topology/Order/Compact.lean:255; `[ClosedIicTopology α]`, `s.Nonempty`, `ContinuousOn f s`). Needs S ≠ ∅. |
| B3, B4, B5 | CONFIRMED | |
| B6 (sublevel = fst '' C) | CONFIRMED | equality needs attainment (B5) for ⊇ — correct. `C ⊆ X × ↥S` closed; `CompactSpace ↥S` via `isCompact_iff_compactSpace` (Compactness/Compact.lean:1051); `isClosedMap_fst_of_compactSpace [CompactSpace Y] : IsClosedMap (Prod.fst : X × Y → X)` (Topology/Maps/Proper/Basic.lean:332) with second factor `↥S`. No direct "closed ⊆ X × K, K compact" lemma in Mathlib (grepped), so the subtype plumbing is necessary. |
| B7 (lsc) | CONFIRMED, improvable | `lowerSemicontinuous_iff_isClosed_preimage` (Basic.lean:232, only `[LinearOrder γ]`). Cases a=⊥ (∅ by B5), ↑r (B6), ⊤ (univ). Improvement: lsc holds **without** S ≠ ∅ (S = ∅ ⇒ φ ≡ ⊤, all preimages ∅/univ) — state it unconditionally (E7). |
| B7' (ℝ- vs EReal-lsc bridge) | CONFIRMED | (⇐) `Continuous.comp_lowerSemicontinuous` (Basic.lean:391) + `EReal.coe_strictMono.monotone`; (⇒) unfold `lowerSemicontinuousAt_iff` (Defs.lean:328). |
| B8 (bounds on compacts) | CONFIRMED | bounds of `uncurry P` on `K ×ˢ S` (`IsCompact.prod` :1071, `bddBelow_image`/`bddAbove_image` Topology/Order/Compact.lean:354/359) and φ x = P x y₀, y₀ ∈ S. |
| B9 (`P_bounded ⊆ LSC ∩ CB`), Cor 2.9' | CONFIRMED | `C_cc ⊆ LSC ∩ CB` only after Correction 1. |

---------------------------------------------------------------------------------------------------------------------

## C. Corrections

1. **`C_cc` must require a nonempty constraint set.** R1 §1.1: `C_cc := valueFunClass n (fun _ S => IsCompact S ∧ Convex ℝ S ∧
   IsSemialgebraic S) …` and §1.5 "`C_bounded ⊆ C_cc ⊆ LSC ∩ CB`". Counterexample: `S = ∅` is compact, convex and
   semialgebraic; then Θ ≡ ∅, φ ≡ ⊤ ∈ C_cc but ⊤ ∉ CB. Fix: `fun _ S => S.Nonempty ∧ IsCompact S ∧ Convex ℝ S ∧
   IsSemialgebraic S`. (Same omission in the paper's eq. (18) — see E1. `C_bounded ⊆ C_cc` survives because
   `IsBoundedBox` already has `lo ≤ hi`.)

2. **F7 made exact (requested statement + proof).** For arbitrary types `X Y Y'` and `e : Y' ≃ Y`:
   ```lean
   theorem argminSet_comp_equiv (e : Y' ≃ Y) (Q : X → Y → ℝ) (S : Set Y) (x : X) :
       argminSet (fun x y' => Q x (e y')) (e ⁻¹' S) x = e ⁻¹' argminSet Q S x
   theorem valueFun_comp_equiv (e : Y' ≃ Y) (P Q : X → Y → ℝ) (S : Set Y) :
       valueFun (fun x y' => P x (e y')) (fun x y' => Q x (e y')) (e ⁻¹' S) = valueFun P Q S
   theorem pvalueFun_comp_equiv … -- same with ⨆
   ```
   Proof of the first: `ext y'`; (→) given `e y' ∈ S` and `∀ y'', e y'' ∈ S → Q x (e y') ≤ Q x (e y'')`, for `y ∈ S` apply it
   to `y'' := e.symm y` (`e.apply_symm_apply`); (←) instantiate `y := e y''`. Second: `funext x`, rewrite with the first,
   `← Equiv.image_symm_eq_preimage` (Logic/Equiv/Set.lean:67: `e.symm '' s = e ⁻¹' s`), then `Equiv.biInf_comp`
   (to_dual of `Equiv.biSup_comp`, Order/CompleteLattice/Basic.lean:434: `⨅ i ∈ e.symm '' s, g (e i) = ⨅ i ∈ s, g i`) with
   `g := fun y => (P x y : EReal)`. Effort S (R1 rated M). For coordinate relabelling `σ : ι ≃ ι'` take
   `e : (ι' → ℝ) ≃ (ι → ℝ)`, `e y' = y' ∘ σ` (`Equiv.arrowCongr`/`Equiv.piCongrLeft'`, or by hand).
   **But F7 alone does not transport class membership** if classes are stated over `Fin m`: one also needs
   (a) `e ⁻¹' boxSet lo hi = boxSet (lo ∘ σ.symm…) (hi ∘ …)` and the same for `boundedBox` (with `lo ≤ hi` preserved);
   (b) `polyFun p x (y ∘ σ) = polyFun (MvPolynomial.rename (Sum.map id σ) p) x y` by `MvPolynomial.eval_rename`
   (Algebra/MvPolynomial/Rename.lean:244) + `Sum.elim` composition; (c) `convexLower` preserved (`ConvexOn.comp_linearMap`
   or direct); (d) for `C_cc`: compactness/convexity/nonemptiness/semialgebraicity of `e ⁻¹' S` (homeomorphic linear equiv;
   SA needs R2's coordinate-permutation lemma). Recommended instead: G1 (generalise the class layer to `[Fintype ι]`).

3. **Paper-error items 6 and 14 overstated; item 7 is a clarification, not an error.**
   - Item 6 ("case 2 argument incomplete"): the paper's argument *is* complete for `argmin p = ∅`: inf p = 0 (shown by
     y₂ → 0, y₃ = 1/y₂) and p > 0 pointwise (both squares cannot vanish when g(x) ≠ 0), so no point attains the infimum.
     What is unproved is only the separability identity (F5, elementary). T4 is a better *Lean* route, not a repair.
   - Item 14 ("'boxtype = unbound' is ambiguous"): refuted. §2 (paper_html.txt:172) defines: "𝒴 is an unbounded box …
     if there exists an index i such that a_i = −∞ or b_i = +∞. Otherwise, 𝒴 is a bounded box." So 𝒫_unbound is the class over
     *literally unbounded* boxes. R1's `P_box` (all boxes) equals it as a set of functions (add a dummy free coordinate with zero
     Q-term: Θ becomes Θ × ℝ, P ignores it — needs a reindexing step; conversely P_unbound ⊆ P_box trivially), so
     `P_box = SA` is still correct, but for the convex class the literal definition gives the *stronger* Thm 2.18 (see G4).
   - Item 7 ("Thm 1.1 must say optimistic"): §1 (just before Thm 1.1) declares that "bilevel problem"/"value function" means
     (BP-O) for the rest of the paper. So the theorem is correctly scoped by convention; R1's factual claim (pessimistic value
     of that (P,Q) is +∞ on dom f) is correct and worth recording.

4. **F6 citation misused.** "`mul_le_mul_left` with positivity": in current Mathlib `mul_le_mul_left` is
   `[MulRightMono α] (bc : b ≤ c) (a) : b * a ≤ c * a` (Algebra/Order/Monoid/Unbundled/Basic.lean:66) — not an iff, no
   positivity. Use `mul_le_mul_iff_right₀ (a0 : 0 < a) : a * b ≤ a * c ↔ b ≤ c` (Algebra/Order/GroupWithZero/Defs.lean:297)
   or its alias `mul_le_mul_iff_of_pos_left` (:306).

5. **T1 citation arity.** `contDiff_apply` has explicit `𝕜 F'` (`variable (𝕜 F')` at ContDiff/Operations.lean:142, decl :146),
   so `(contDiff_apply 0)` does not elaborate; write `contDiff_apply ℝ (fun _ : Fin 3 => ℝ) 0` or let `fun_prop` (the lemma is
   `@[fun_prop]`) discharge T1.

6. **V3/V4 tooling.** The cited `iInf_eq_of_forall_ge_of_forall_gt_exists_lt` (to_dual at Order/CompleteLattice/Basic.lean:373–378)
   is for single-index `iInf`; for the double `⨅ y ∈ Θ` either `iInf_subtype'` first or (simpler) the hand proof in table B using
   `biInf_lt_iff` (to_dual of `lt_biSup_iff`, Defs.lean:339) and `EReal.exists_between_coe_real`. Not wrong, just costlier.

7. **Small precision fixes.** "Whitney gives g ≡ 1 when dom f = ∅" → "gives some g with support univ (never 0)". Def 2.7 "compact"
   is a harmless restriction, not an error. §1 text "φ_o = +∞ if Θ = ∅" is a convention statement, not an omission.

---------------------------------------------------------------------------------------------------------------------

## D. Mathlib citation check

All entries in R1 §4 were grepped. Unless noted, "file:line verified" means the declaration line itself matches.

| Declaration | Exists | file:line ok | Adequate | Note |
|---|---|---|---|---|
| `IsOpen.exists_contDiff_support_eq` | ✓ | FiniteDimension.lean:83 ✓ | ✓ | `{n : ℕ∞}`; range ⊆ Icc 0 1 |
| `Function.support_eq_iff` (to_additive of `mulSupport_eq_iff`) | ✓ | Algebra/Notation/Support.lean:54 ✓ | ✓ | `mem_mulSupport` :44, `notMem_mulSupport` :38 ✓ |
| `∞`, `ω`, `ℕ∞ω` notations | ✓ | FTaylorSeries.lean:116/118/120 ✓ | ✓ | `∞ = ((⊤:ℕ∞):WithTop ℕ∞)`; `ContDiff` def Defs.lean:1067 (`n : ℕ∞ω`) ✓; `contDiff_infty` :1114 ✓; `ContDiff.continuous` :1150 ✓ |
| `ContDiff.add/mul/pow/sub/neg` | ✓ | Operations.lean:197/462/508/325/264 ✓ | ✓ | |
| `contDiff_fst/snd`, `ContDiff.comp`, `ContDiff.comp₂` | ✓ | Comp.lean:287/344/155/425 ✓ | ✓ | |
| `ContDiff.prodMk`, `contDiff_const`, `contDiff_id` | ✓ | ContDiff/Basic.lean:567/98/173 ✓ | ✓ | |
| `contDiff_apply`, `contDiff_pi` | ✓ | Operations.lean:146/113 ✓ | **MISUSED arity** | explicit `𝕜 F'` (C5) |
| `Module.Finite.prod`, `Module.Finite.pi` | ✓ | Finiteness/Prod.lean:46, Basic.lean:277 ✓ | ✓ | instances |
| `lowerSemicontinuous_iff_isClosed_epigraph`, alias `LowerSemicontinuous.isClosed_epigraph` | ✓ | Semicontinuity/Basic.lean:353/357 (alias decl at 357, R1 says 355 — off by 2) | ✓ | `[ClosedIciTopology γ]` |
| `upperSemicontinuous_iff_IsClosed_hypograph` | ✓ | Basic.lean:897 ✓ | ✓ | |
| `lowerSemicontinuous_iff_isClosed_preimage` | ✓ | Basic.lean:232 ✓ | ✓ | `[LinearOrder γ]` only |
| `upperSemicontinuous_iff_isClosed_preimage` | ✓ | Basic.lean:811 ✓ | ✓ | |
| `lowerSemicontinuous_iff_le_liminf` | ✓ | Basic.lean:289 ✓ | ✓ (unused) | |
| `LowerSemicontinuous` abbrev, `lowerSemicontinuousAt_iff` | ✓ | Semicontinuity/Defs.lean:293/328 ✓ | ✓ | |
| `Continuous.comp_lowerSemicontinuous(_antitone)`, `Continuous.comp_upperSemicontinuous_antitone` | ✓ | Basic.lean:391/409/1033 ✓ | ✓ | need `OrderTopology` on both codomains (section :363–367) — ℝ, EReal ✓ |
| `LowerSemicontinuousOn.exists_isMinOn`, `.bddBelow_of_isCompact` | ✓ | Basic.lean:77/106 ✓ | ✓ (unused) | |
| `IsCompact.exists_isMinOn`/`exists_isMaxOn` | ✓ | Topology/Order/Compact.lean:255/273 ✓ | ✓ | |
| `IsCompact.bddBelow_image/bddAbove_image` | ✓ | :354/:359 ✓ | ✓ | `[Nonempty α]` |
| `CompactIccSpace.isCompact_Icc` (export) | ✓ | :53/:55 ✓ | ✓ | |
| `isCompact_univ_pi`, `IsCompact.prod` | ✓ | Compactness/Compact.lean:1172/1071 ✓ | ✓ | |
| `IsCompact.isClosed`, `IsCompact.inter_right`, `IsCompact.of_isClosed_subset`, `isCompact_iff_compactSpace` | ✓ | Separation/Hausdorff.lean:600; Compact.lean:86/105/1051 ✓ | ✓ | |
| `isClosedMap_fst_of_compactSpace`/`snd` | ✓ | Topology/Maps/Proper/Basic.lean:332/337 ✓ | ✓ | `[CompactSpace Y]`, Y = second factor |
| `IsClosedMap` | ✓ | Topology/Defs/Basic.lean:171 ✓ | ✓ | |
| `isClosed_le`, `isClosed_Icc`, `isClosed_Iic`, `ClosedIciTopology.isClosed_Ici`, instance `ClosedIicTopology` | ✓ | OrderClosed.lean:444/456/116/82/449 ✓ | ✓ | |
| `isClosed_iInter`, `isClosed_biInter`, `IsClosed.inter`, `IsClosed.preimage`, `isClosed_set_pi` | ✓ | Topology/Basic.lean:159/162/176; Continuous.lean:188; Constructions.lean:1127 ✓ | ✓ | |
| `IsClosed.mem_of_tendsto`, `…frequently…`, `Filter.Tendsto.prodMk_nhds` | ✓ | Neighborhoods.lean:357/353; SumProd.lean:339 ✓ | ✓ | |
| `IsCompact.tendsto_subseq` | ✓ | Sequences.lean:298 ✓ | (unused) | |
| `Continuous.prodMap/prodMk/prodMk_left/prodMk_right` | ✓ | SumProd.lean:178/139/147/144 ✓ | ✓ | `prodMk_right x : Continuous fun y => (x, y)` — correct for `Q x` |
| `EReal.coe_le_coe_iff/coe_lt_coe_iff/coe_eq_coe_iff` (protected) | ✓ | Data/EReal/Basic.lean:55/61/67 ✓ | ✓ | |
| `coe_strictMono`, `bot_lt_coe`, `coe_ne_bot`, `coe_lt_top`, `coe_ne_top`, `top_ne_coe`, `bot_ne_coe` | ✓ | Basic.lean:48/254/258/266/270/274/262 ✓ | ✓ | |
| `EReal.rec`, `toReal_coe`, `coe_toReal`, `le_coe_toReal`, `eq_top_iff_forall_lt`, `eq_bot_iff_forall_lt`, `exists_between_coe_real`, `lt_iff_exists_real_btwn` | ✓ | Basic.lean:113/250/416/420/430/438/448/863 ✓ | ✓ | |
| `coe_add`, `coe_mul`, `coe_neg`, `coe_sub` | ✓ | Basic.lean:310/155; Operations.lean:220/222 ✓ | ✓ | |
| `add_bot`, `bot_add`, `top_add_coe`, `coe_add_top`, `top_add_of_ne_bot`, `add_top_of_ne_bot` | ✓ | Operations.lean:46/50/68/108/73/81 ✓ | ✓ | |
| `coe_mul_top_of_pos`, `coe_mul_bot_of_pos`, `mul_top_of_pos`, `mul_bot_of_pos` | ✓ | Operations.lean:579/615/591/627 ✓ | ✓ | |
| `neg_strictAnti`, `neg_le_neg_iff`, `neg_lt_neg_iff`, `neg_top`, `neg_bot`, `neg_eq_top_iff`, `neg_eq_bot_iff`, `negOrderIso` | ✓ | Operations.lean:253/258/260/213/217/242/246/295 ✓ | ✓ | |
| `OrderTopology EReal`, `T2Space EReal` | ✓ | Topology/Order/Real.lean:37/40 ✓ | ✓ | |
| `continuous_coe_real_ereal`, `EReal.continuous_coe_iff`, `EReal.isEmbedding_coe`, `EReal.tendsto_coe` | ✓ | EReal/Lemmas.lean:52/55/41/48 ✓ | ✓ | |
| `ContinuousNeg EReal` | ✓ | Topology/Algebra/Ring/Real.lean:65 ✓ | ✓ | |
| EReal `CompleteLinearOrder` (derived) | ✓ | Data/EReal/Basic.lean:35–39 ✓ | ✓ | |
| `iSup_emptyset`→`iInf_emptyset`, `iSup_univ` | ✓ | Order/CompleteLattice/Basic.lean:584/587 ✓ | ✓ | |
| `le_iSup₂`→`iInf₂_le`, `iSup₂_le`→`le_iInf₂`, `le_iSup`, `iSup_le`, `le_iSup_of_le` | ✓ | Basic.lean:226/239/211/235/222 ✓ | ✓ | |
| `iSup_le_iff`, `iSup₂_le_iff`, `iSup₂_mono`, `iSup_le_iSup_of_subset` | ✓ | Basic.lean:280/284/251/607 ✓ | ✓ | |
| `le_iSup_iff`→`iInf_le_iff`, `iSup_eq_top`, `iSup_eq_bot` | ✓ | Defs.lean:123/335; Basic.lean:351 ✓ | ✓ | |
| `iSup_eq_of_forall_le_of_forall_lt_exists_gt` | ✓ | Basic.lean:378 ✓ | adequate after `iInf_subtype'` | C6 |
| `IsGreatest.csSup_eq`→`IsLeast.csInf_eq` | ✓ | ConditionallyCompletePartialOrder/Basic.lean:71 ✓ | ✓ (unused) | |
| `map_iSup`→`map_iInf`, `OrderIsoClass.toCompleteLatticeHomClass` | ✓ | Order/Hom/CompleteLattice.lean:125/178 ✓ | ✓ | `OrderIso.map_iInf₂` (CompleteLattice/Basic.lean:330, to_dual) is more direct |
| `IsMinOn`, `isMinOn_iff`, `isMinOn_univ_iff`, `IsMinOn.of_subset` | ✓ | Order/Filter/Extr.lean:112/129/135/272 ✓ | ✓ | `on_subset` deprecated 2026-07-17 (:275) ✓ |
| `Set.mem_prod`, `Set.mem_univ_pi`, `Set.univ_pi_nonempty_iff`, `Set.nonempty_Icc` | ✓ | Data/Set/Operations.lean:231/283; Data/Set/Prod.lean:656; Order/Interval/Set/Basic.lean:139 ✓ | ✓ | |
| `ConvexOn`, `convex_pi`, `convex_Icc/Ici/Iic/univ` | ✓ | Convex/Function.lean:54; Convex/Basic.lean:108/257/254/248/89 ✓ | ✓ | |
| `Bornology.isBounded_pi` | ✓ | Topology/Bornology/Constructions.lean:114 ✓ | ✓ (unused) | |
| `MvPolynomial.continuous_eval` | ✓ | Topology/Algebra/MvPolynomial.lean:31 ✓ | ✓ | |
| `finSumFinEquiv`, `Fin.appendEquiv`, `Equiv.sumArrowEquivProdArrow` | ✓ | Logic/Equiv/Fin/Basic.lean:224/401; Logic/Equiv/Prod.lean:390 ✓ | ✓ | |
| `Matrix.cons_val_zero/one/succ`, `head_cons` | ✓ | Data/Fin/VecNotation.lean:128/271/135/224 ✓ | ✓ | |
| `sq_nonneg`, `mul_self_nonneg`, `sq_eq_zero_iff`, `pow_eq_zero_iff`, `pow_pos`, `add_pos_of_pos_of_nonneg` | ✓ | Ring/Unbundled/Basic.lean:608/630; GroupWithZero/Basic.lean:262/253; Order/GroupWithZero/Basic.lean:588; Monoid/Unbundled/Basic.lean:752 ✓ | ✓ | `add_pos_of_nonneg_of_pos` :749 also exists |
| `cantorSet` | ✓ | Topology/Instances/CantorSet.lean:57 ✓ | n/a | |
| `UpperHemicontinuous`, `isClosedMap_iff_upperHemicontinuous` | ✓ | Semicontinuity/Defs.lean:659; Hemicontinuity.lean:117 ✓ | n/a | |
| `mul_le_mul_left` (F6) | ✓ (different statement) | Monoid/Unbundled/Basic.lean:66 | **MISUSED** | use `mul_le_mul_iff_right₀` (C4) |
| `add_le_add_iff_right/left` (F5, F6) | ✓ (to_additive) | Monoid/Unbundled/Basic.lean:75/80 | ✓ | not cited with line by R1 |
| `add_eq_zero_iff_of_nonneg` (T3) | ✓ (to_additive of `mul_eq_one_iff_of_one_le`) | Monoid/Unbundled/Basic.lean:800 | ✓ | |
| `mul_one_div_cancel` (T4) | ✓ | Algebra/GroupWithZero/Units/Basic.lean:341 | ✓ | |
| NOT-IN-MATHLIB claims: Berge maximum theorem; outer semicontinuity as such; Thomae/Weierstrass/SVC/Cantor-function | confirmed absent | — | — | grepped `Berge`, `[Ll]owerSemicontinuous.*iInf` with compact, `Thomae`: nothing usable. Also no lemma "projection of a closed subset of X × K, K compact, is closed" except via `isClosedMap_fst_of_compactSpace`. |

Additional useful declarations (not cited by R1): `Equiv.biInf_comp` (to_dual, Order/CompleteLattice/Basic.lean:434),
`Equiv.image_symm_eq_preimage` (Logic/Equiv/Set.lean:67), `biInf_lt_iff`/`iInf_lt_iff` (to_dual, Order/CompleteLattice/Defs.lean:339/319),
`OrderIso.map_iInf₂` (to_dual, Basic.lean:330), `MvPolynomial.eval_rename` (Algebra/MvPolynomial/Rename.lean:244),
`mul_le_mul_iff_right₀` (Algebra/Order/GroupWithZero/Defs.lean:297).

---------------------------------------------------------------------------------------------------------------------

## E. Missed issues (math or Lean)

E1. **Paper eq. (18) (C_cc) omits "nonempty"** — with 𝒴 = ∅, φ ≡ +∞ ∈ C_cc, contradicting "C_cc ⊆ SA ∩ LSC ∩ CB" and Thm 2.21.
    Same for Def 2.11 (bounded) only implicitly (a box [a_i,b_i] tacitly has a_i ≤ b_i). R1 flagged nonemptiness for Thm 2.8,
    Cor 2.9 and bounded boxes but not for (18), and its own `C_cc` definition inherits the bug (Correction 1).
    Also: "Using Theorem 2.15, we get … C_cc ⊆ SA ∩ LSC ∩ CB" (paper_html.txt:914) — the inclusion comes from Prop 2.6 + Cor 2.9,
    and Prop 2.6 is stated only for boxes; C_cc ⊆ SA needs Prop 2.6 for an arbitrary semialgebraic 𝒴 (same Tarski–Seidenberg
    argument). R4 noticed the Prop 2.6 point; escalate to R2.

E2. **§2.1 graph formula for φ|dom(φ) is wrong as written** (paper_html.txt:241ff; paper.txt:248–250):
    `{(x, P(x,y)) | x ∈ dom φ, y ∈ Θ(x), ∀y' ∈ Θ(x), P(x,y) ≤ P(x,y')}` only contains points where the inner infimum is
    *attained*. Counterexample: n arbitrary, 𝒴 = ℝ², Q = (1 − y₁y₂)², P = y₁²: Θ(x) = {y₁y₂ = 1}, φ ≡ 0 (not attained), and the
    displayed set is ∅. Fix (still first-order, hence semialgebraic): graph(φ|dom) = {(x,δ) | ∀y∈Θ(x), δ ≤ P(x,y) ∧ ∀ε>0 ∃y∈Θ(x),
    P(x,y) < δ+ε} — exactly R1's V3. R1 item 16 called the dom(φ) part correct (true) but did not check the next display. This
    matters for R2's Prop 2.6.

E3. **App. A separability display**: "arg min_y Q = arg min_{y₁} h(x,·) × arg min p" should be `h(x,·)²`. With a general
    Whitney function (any sign) argmin h ≠ argmin h²; Mathlib's version has range ⊆ [0,1], making them coincide, but the paper's
    Thm A.1 gives no sign.

E4. **App. A Discussion, Thomae**: "−t … with global minimum at 1/2" is false: −t(p/q) = −1/q, so on ℝ (Thm 1.1 is on ℝⁿ) the
    minimum −1 is attained at the integers; even on [0,1] (Bartle–Sherbert's setting, t(0) = 1) the minimum is at 0 and 1. Only on
    (0,1) is 1/2 the minimiser.

E5. **Nuance on R1 item 18 (SVC)**: R1 is right that 1_S (S closed, nowhere dense) is usc and not lsc, hence not covered by
    Thm 1.1. But the Discussion's claim "admits a representation as a bilevel program with smooth data" is nonetheless *true*:
    with g smooth, g⁻¹(0) = S (Whitney), P = y₁, Q = (y₁(1−y₁))² + ((y₁−1)(g(x)y₂ − 1))² on 𝒴 = ℝ²: Q ≥ 0; x ∈ S ⇒ zero set
    = {y₁ = 1} (y₁ = 0 gives second term 1) ⇒ φ = 1; x ∉ S ⇒ zero set ∋ (0, 1/g(x)) and (1, ·) ⇒ φ = 0. So the paper's error is
    only attributing it to Theorem 1.1. (Not a formalisation target.)

E6. **Literal "unbounded box"** — see Correction 3/G4. If the blueprint uses all-boxes classes for the convex results, Thm 2.18
    (`PP ⊆ C_unbound`) is formalised in a *weaker* form than the paper's (a class over more boxes is larger).

E7. **lsc does not need 𝒴 ≠ ∅.** If S = ∅, φ ≡ ⊤ is lsc. So `lowerSemicontinuous_valueFun` can be stated with only
    `IsCompact S` (case split `S.eq_empty_or_nonempty`), and Remark 2.10 needs no nonemptiness; only real-valuedness/CB does.

E8. **EReal-valued Thm 1.1 hypothesis.** For f allowed to take −∞, the paper's "dom f := {f ∈ ℝ}" is no longer {f < +∞}; R1's
    choice `IsClosed {x | f x ≠ ⊤}` is the right hypothesis (g must vanish exactly where Θ(x) should be nonempty, i.e. on
    {f < +∞}). Worth a one-line remark in the blueprint so nobody "restores" `{f ∈ ℝ}`.

E9. **`boxSet` admits degenerate data** (`lo i = ⊤`, `hi i = ⊥`, `lo i > hi i`) giving ∅, and admits `m = 0`. Harmless for
    the "all boxes" P/C classes (φ ≡ ⊤ ∈ SA; ⊇-directions unaffected). For a literal `IsUnboundedBox` define it on data with
    `lo i ≠ ⊤ ∧ hi i ≠ ⊥ ∧ lo i ≤ hi i` for all i and `∃ i, lo i = ⊥ ∨ hi i = ⊤`.

E10. **Lean: `Function.uncurry` of curried `polyFun`** — `continuous_uncurry_polyFun` route (`MvPolynomial.continuous_eval`
    composed with `p ↦ Sum.elim p.1 p.2`) needs `continuous_pi` + `Sum.rec`/`Sum.forall`; fine, but `Sum.elim p.1 p.2` is also
    `Homeomorph.sumArrowHomeomorphProdArrow.symm p` (Topology/Homeomorph/Lemmas.lean:279) gives continuity in one step;
    not needed.

---------------------------------------------------------------------------------------------------------------------

## F. Route assessment and recommended route

- **Framework**: keep R1's definitions (curried `P Q : X → Y → ℝ`, `argminSet`, EReal `valueFun`/`pvalueFun` generic in X, Y).
  Add helper **F0**: `IsLeast ((P x) '' argminSet Q S x) r → valueFun P Q S x = ↑r` (and `IsGreatest … → pvalueFun = ↑r`) —
  a 3-line corollary of V2, wanted by R5. Add `mem_argminSet_univ` simp lemma (R3). F7 as in Correction 2.
- **Order of priority**: F1–F5, F7, V1–V5, V5', V8, F0 are needed by consumers; V6/V7 are optional (no consumer found: R4's
  route R-b avoids the multiplicative scaling, R5 avoids the shift via the attained form). Defer them.
- **Theorem 1.1**: R1's route (Whitney via `IsOpen.exists_contDiff_support_eq` on complements, real epigraph by preimage,
  F4 in the finite case, explicit ε "beat every candidate" in the +∞ case, no separability) is the cheapest correct route. State
  the strengthened EReal version with `ContDiff ℝ ∞ (Function.uncurry P)`; the paper's version is a corollary. T1 by `fun_prop`.
- **Cor 2.9**: R1's closed-graph (B1) + `isClosedMap_fst_of_compactSpace` on `X × ↥S` sublevel route (B6–B7) is shorter than
  the sequential proof; no simpler Mathlib shortcut exists (no "inf over compact of lsc is lsc" lemma). Use E7 to drop
  nonemptiness from the lsc lemma. B8 as given.
- **Pessimistic**: V8 is a uniform transfer for every row of Table 4 provided the target class is closed under negation
  (PP, LSC↔USC, CB trivially; SA needs "graph of −h is SA", a polynomial-substitution lemma from R2). Thm 1.1' as given.

---------------------------------------------------------------------------------------------------------------------

## G. Items to escalate to the orchestrator

G1. **Lower index type** (R3 §5.1, R4 §5.1, R5 §5.1 all want arbitrary `[Fintype ι]`; R6 uses `Fin (k+1)`). Recommendation:
    generalise `polyFun` (= R3's `evalXY`) to `MvPolynomial (Fin n ⊕ ι) ℝ`, `boxSet`/`boundedBox` to `ι → ℝ`, and define every
    class with `∃ (ι : Type) (_ : Fintype ι) …`. Then no class-level transport is needed; F7 remains for in-proof relabelling.
    If `Fin m` is kept, the extra transport lemmas (a)–(d) of Correction 2 become mandatory (M effort, plus an SA-permutation lemma from R2).

G2. **Class codomain**: R1 = sets of EReal-valued functions; R4/R5 state memberships for real `f` as
    `∀ x, valueFun … x = (f x : EReal)`. Compatible (real f ↦ `fun x => (f x : EReal)`), but fix one convention: EReal classes,
    with B7' (lsc bridge) and a `CB`↔`|f x| ≤ B` bridge in the shared API.

G3. **Polynomiality encoding**: R1/R3 put `MvPolynomial` terms in the class (`polyFun p`); R4/R5 use a predicate
    `IsPolyFun F := ∃ p, ∀ x y, F x y = eval (Sum.elim x y) p`. Recommend defining classes with `IsPolyFun` on functions
    (equivalent; lets R4/R5 discharge polynomiality by closure lemmas) and keeping `polyFun` as the constructor.

G4. **Box notion and literal unboundedness**: R1 `boxSet` (EReal bounds, all boxes), R5 interval-predicate `IsBox` with literal
    `IsUnboundedBox` (and a dummy free coordinate to witness unboundedness), R4/R6 `Set.pi univ Icc`. Recommend: one `boxSet`
    (EReal bounds) + `boundedBox` (real bounds, `lo ≤ hi`) + literal `IsUnboundedBox` (E9); define 𝒫_unbound/𝒞_unbound
    literally as in the paper (paper_html.txt:172); optional lemma `P_unbound = P_box` via dummy coordinate.

G5. **C_cc nonemptiness** (Correction 1, E1) — affects R4's Thm 2.21 statement; also R4/R2: Prop 2.6 for semialgebraic 𝒴.

G6. **Convexity reading of "Q convex w.r.t. y"**: R1/R5 `∀ x, ConvexOn ℝ Set.univ (Q x)`; R4 `∀ x, ConvexOn ℝ Y (Q x)`.
    R4's linearised Q' is linear in λ, so it satisfies the `univ` reading; R5's constructions too. Recommend `univ` (smallest
    class ⇒ strongest ⊇-theorems; ⊆-directions insensitive). R4 must restate.

G7. **Pessimistic naming and route**: `pvalueFun` (R1) / `valueFunP` (R5) / `pessFun` (R4) — pick one. Route: R1 negation (V8),
    R3 swapped construction (avoids SA-negation lemma), R4 same construction with hypograph (L13). All correct; V8 is the most
    uniform if R2 provides "h ∈ SA ⇒ −h ∈ SA". R1 item 20 (§2.4 "unique minimisers" false for Thm 2.12) independently agrees with R3.

G8. **Helper lemmas to add to R1's API** for consumers: F0 (attained form, R5), `mem_argminSet_univ` (R3), `pvalueFun` twins of
    V1/V2/V4 (R3's A3'–A5'), `valueFun_comp_equiv` in the exact form of Correction 2 (R3's "R1 lemma", R4's `valueFun_comp_equiv`).

G9. **V6/V7** have no consumer in R3–R6 (R4 explicitly avoids EReal multiplication). Mark optional.

G10. R6's `optVal := ⨅ x, valueFun …` and box `Set.pi univ (Icc 0 1)` are consistent with R1's `valueFun`/`boundedBox` (lo = 0, hi = 1).
