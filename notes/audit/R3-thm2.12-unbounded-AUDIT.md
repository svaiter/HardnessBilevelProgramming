# AUDIT of R3 — Theorem 2.12 (unbounded / unconstrained lower level), pessimistic counterpart

Auditor: Opus (adversarial, independent). Sources checked: `paper/paper_html.txt` lines 120–130 (BP-O/BP-P conventions),
185–210 (Def 2.1, 2.2, Thm 2.3), 240–252 (Prop 2.6), 316–525 (Def 2.11 – Remark 2.14), 991–1047 (Section 2.4);
`paper/paper.txt` lines 368–369 (padding remark, truncated in the HTML) and 429–450 (eq. (7), to rule out an HTML artifact);
Mathlib tree at commit 1df8067a (every citation grepped; see D).

## A. Summary verdict

The report is **reliable**. I re-derived every gadget lemma (G1–G5), every argmin/value lemma (A1–A5, A3'–A5'), the three
cases of the simplified construction (M1–M3) and the pessimistic swap. The simplified construction
`Q = W_Γ(x,t,z)·W₋(x,ν)·u² + (1−uv)²`, `P = t`, is **correct** and proves Theorem 2.12 (⊇) under hypotheses strictly weaker
(formally) than the paper's. All paper-error claims check out against the text; one (the "dummy 0 = 0" padding) should be
reworded from "error" to "gap/ambiguity". The only defects I found are Lean-level: the explicit variable indices `uX`, `vX`
in E1 are mis-nested (type errors, trivially fixed), one line-number slip, and a deprecated lemma name. Adopt the
simplified route for the blueprint; keep the paper's `Q` only as a prose remark (V1–V8), not as a formal corollary.

## B. Lemma-by-lemma verdict table

| Id | Verdict | Note |
|---|---|---|
| G1 scalar gadget `(1−pz²)²` | CONFIRMED | `p>0`: `z=√(p⁻¹)` gives `p z² = 1`, value 0. `p≤0`: `p z² ≤ 0` ⇒ `1−pz² ≥ 1 ≥ 0` ⇒ square ≥ 1, equality at `z=0`. G1.4 by contradiction `1 ≤ 0`. |
| G2 basic-set gadget `P² + Σ_j (1−Q_j ξ_j²)²` | CONFIRMED | `w∈S`: `P=0`, each summand 0 at `ξ_j=√(Q_j⁻¹)`. `w∉S`: either `P≠0` ⇒ value ≥ `P²>0`, or some `Q_{j0}≤0` ⇒ value ≥ summand `j0` ≥ 1. Empty `κ` gives `P²`, `S={P=0}` — consistent. |
| G3 union gadget (product over blocks, Σ-indexed variables) | CONFIRMED | Factors nonneg ⇒ product nonneg (`Finset.prod_nonneg`); over ℝ product = 0 iff some factor = 0 (`Finset.prod_eq_zero_iff`, `NoZeroDivisors`); all factors >0 ⇒ product >0 (`Finset.prod_pos`). Blocks use disjoint variables `⟨i,j⟩`, so the selector can set block `i0` to its witness without constraining the others (the others are merely ≥ 0, which is all that is needed once one factor is 0). Empty `ι`: product 1 > 0, union ∅ ✓. |
| G4 semialgebraic ⇒ gadget | CONFIRMED | Given `W ≥ 0`, "`w∉S ⇒ ∀ξ, W>0`" ⇔ "`w∉S ⇒ ∀ξ, W≠0`" ⇔ "`(∃ξ, W=0) ⇒ w∈S`". So with `W≥0` the pair of conditions is equivalent to the single "`w∈S ⇔ ∃ξ, W(w,ξ)=0`". The structure `ZeroGadget` (nonneg + selector-zero + positivity off S) encodes exactly this, plus an explicit witness map (harmless: exists by choice; here it is even explicit). The proof uses both halves: `sel_zero` (attainment) and `pos_of_notMem` (strict positivity, needed in M2). |
| G5 escape gadget `N = a u² + (1−uv)²` | CONFIRMED | `a>0`: `u=0` ⇒ N=1; `u≠0` ⇒ `a u² > 0`. `a≥0`: `u=√c, v=1/√c` with `a c < ε` ⇒ N = `a c < ε` (so inf 0). `a≥0 ∧ N=0` ⇒ `uv=1` ⇒ `u≠0` ⇒ `a=0`; converse trivial. `exists_pos_mul_lt` has exactly the needed shape. |
| A1 zero set = argmin | CONFIRMED | |
| A2 empty argmin | CONFIRMED | uses `ε := Q x y > 0` |
| A3 / A3' | CONFIRMED | `iInf_emptyset` / `iSup_emptyset` after rewriting Θ = ∅ |
| A4 / A4' | CONFIRMED | nonempty argmin with constant value `c` ⇒ ⨅ = ⨆ = ↑c |
| A5 / A5' | CONFIRMED | `EReal.eq_bot_iff_forall_lt` / `eq_top_iff_forall_lt` |
| E1 eval formula | FIXED (Lean only) | Math fine; `uX`, `vX` index terms are ill-typed — see C1. |
| E2 a-lemma | CONFIRMED | |
| M1 `h x = r` | CONFIRMED | `x∉D₋` ⇒ `W₋>0` ∀ν. `Q≥0`, `Q(y₀)=N(0,1,1)=0` ⇒ Θ = {Q=0}. `Q=0` ⇒ `uv=1` ⇒ `u≠0` ⇒ `a=0` ⇒ `W_Γ=0` (since `W₋>0`) ⇒ `(x,t)∈Γ` ⇒ `t=r`. No spurious argmin points. Θ ≠ ∅, all values `r` ⇒ ⨅ = ↑r. |
| M2 `h x = ⊤` | CONFIRMED | `(x,t)∉Γ` ∀t (⊤ ≠ ↑t) and `x∉D₋` (⊤ ≠ ⊥) ⇒ `a>0` everywhere ⇒ `Q>0` everywhere, inf 0 ⇒ Θ = ∅ ⇒ ⊤. |
| M3 `h x = ⊥` | CONFIRMED | `W₋(x,sel₋ x)=0` ⇒ `a=0` for that ν and every t ⇒ `(t,0,sel₋x,1,1)` has Q=0 ∈ Θ for every t ⇒ ⊥. |
| MAIN | CONFIRMED | Case split on `h x` — see C3 for a robust tactic pattern. |
| R1 reindexing invariance | CONFIRMED | `y' ↦ y'∘e` is a bijection of function spaces; Θ' = preimage of Θ; `Equiv.iInf_comp`. |
| R2 polynomial reindexing | CONFIRMED | `eval_rename` + `Sum.elim_comp_map`. |
| V1–V3 (paper's F) | CONFIRMED | identical to G1–G3 with uniform `J`. |
| V4 (paper's H, H⁺, H⁻) | CONFIRMED | requires `S⁺_ij`, `S⁻_ij` in (7) (typo confirmed in both HTML and PDF text). |
| V5 | CONFIRMED | = G5. |
| V6 (paper Case 1) | CONFIRMED | `Q=0` ⇒ `Q₁=0 ∧ Q₂=0` (both ≥ 0); `H⁺>0` (x∉dom⁺), `H⁻>0` (x∉dom⁻) ⇒ `F=0` ⇒ `t=h(x)`. `Q₁` cannot vanish via `H⁻=0` because `x∉dom(h)⁻`. Role of `H` in `Q₂ = H H⁻ u² + (1−uv)²`: in Case 1 the coefficient `H H⁻` must vanish for `Q₂=0` to be attainable (H⁻>0 there, so `H(x,ν*)=0` is essential); in Case 2 `H>0` (x∉dom h) makes the coefficient > 0, so Q₂ > 0 everywhere. |
| V7 (paper Case 2) | CONFIRMED | `H⁺=0` is needed in the paper's architecture: without it `Q₁ = H⁻F > 0` and `inf_{t,z} F` could be positive, so `inf Q` could be > 0 and attained. The simplified Q removes this need by putting `W_Γ` into the coefficient of `u²` (inf over (u,v) is 0 for every fixed coefficient). |
| V8 (paper Case 3) | CONFIRMED | `H⁻=0` kills both `Q₁` and the `u²` term. |
| Pessimistic swap `Q_p = W_Γ W₊ u² + (1−uv)²` | CONFIRMED | `h x=r`: `x∉D₊` ⇒ as M1, ⨆ = r. `h x=⊥`: `(x,t)∉Γ` ∀t and `x∉D₊` ⇒ `a>0` ⇒ Θ = ∅ ⇒ ⨆∅ = ⊥ (matches paper's convention φ_p = −∞ on Θ = ∅, line 127). `h x=⊤`: `x∈D₊` ⇒ every t occurs ⇒ ⨆ = ⊤. Uses only Γ, D₊ semialgebraic. |
| Real-valued corollary `Q = W_Γ` alone | CONFIRMED | For total real `h`: Θ(x) = {(h(x), z) : W_Γ = 0} ≠ ∅; any selection gives h(x). |

## C. Corrections

**C1 (Lean, E1: ill-typed variable indices).** Report: `uX := X (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))`,
`vX := X (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))` with `ι := Unit ⊕ (τ_Γ ⊕ (τ₋ ⊕ (Unit ⊕ Unit)))`.
In `Fin n ⊕ ι`, after the outer `Sum.inr` the remaining path `.inr (.inr (.inl ()))` lands in `τ₋` (needs `() : τ₋`), and
`.inr (.inr (.inr ()))` needs `() : Unit ⊕ Unit`. Both fail to elaborate. Correct (one more `Sum.inr` each), consistent with
`uc`/`vc`: `uX := X (Sum.inr (.inr (.inr (.inr (.inl ())))))`, `vX := X (Sum.inr (.inr (.inr (.inr (.inr ())))))`.
Recommendation: define named indices once, `iT iU iV : ι` and `iZ : τ_Γ → ι`, `iN : τ₋ → ι`, and write `tc y := y iT`,
`uX := X (Sum.inr iU)`, `ρ₋ := Sum.map id iN`, etc., so the nesting is written exactly once. (`ρΓ`, `ρ₋`, `Ppoly`, `mk`,
`tc/zc/νc/uc/vc` are correct as written.) Alternatively use a `structure`-free record by `Option`/`Fin 3 ⊕ ...`; not needed.

**C2 (paper error 3, padding remark — reword).** Report: "'dummy 0 = 0' cannot be used to pad the outer index set I".
The paper (PDF text l. 368–369) says: "with the same index sets I, J as in (3) (otherwise, one can add 'dummy' polynomial
equalities/inequalities, e.g., 0 = 0, 0 < 1 to match the index sets)". Read literally, "0 < 1" pads `J` (harmless) and
"0 = 0" is a dummy *equality* (a basic set in Def 2.1 has exactly one equation, so it is relevant only if one starts from a
description with no equation). The paper never says to add whole basic sets `{0 = 0 ∧ 0 < 1}`, so it does not literally
commit the error; it is *silent* on padding `I`, for which dummy equalities/inequalities do not work at all. Fair statement:
"gap: padding the outer index `I` requires adding empty basic sets, e.g. `{1 = 0}` (or duplicating an existing `𝒮_i` when
`I ≠ ∅`); the dummy-constraint remark only covers `J`; the natural misreading (add `{0=0, 0<1}` = ℝⁿ) would be wrong."
Irrelevant to the Lean route (per-block index types, no padding).

**C3 (Lean, MAIN case split).** Report recommends `cases hx : h x` / `induction h x using EReal.rec`. `induction (h x)` loses the
equation; whether `cases hx : h x` picks up the custom `cases_eliminator` with the `hx :` binder is not something I can
verify without a toolchain. Robust pattern: `generalize hx : h x = e; induction e using EReal.rec` (or prove a 3-line
trichotomy `∀ e : EReal, e = ⊥ ∨ (∃ r : ℝ, e = r) ∨ e = ⊤` by `induction e <;> simp` — not in Mathlib — and `rcases`).

**C4 (citation slips).** `MvPolynomial.rename` is at `Mathlib/Algebra/MvPolynomial/Rename.lean:54` (the report's 62/80/244 are
`rename_X`, `rename_rename`, `eval_rename`). `Set.mem_setOf_eq` exists only as a **deprecated** alias (since 2026‑07‑09) of
`Set.mem_ofPred_eq`, `Mathlib/Data/Set/Operations.lean:73,76` — use `Set.mem_ofPred_eq` or `Iff.rfl`. The deprecated alias
`Finset.prod_eq_one_iff_of_one_le'` (l. 251) is not the `to_additive` source; the source is the unprimed
`Finset.prod_eq_one_iff_of_one_le` (l. 239–240), as the report correctly says.

**C5 (minor wording, report §3 item 8).** "dom(f) … automatically semialgebraic (under either definition (A) or (B))": under
(A) closure under complement is a (elementary, sign-condition) theorem, not definitional. True, but it is R2's lemma, not free.

**C6 (minor, report §6).** "Non-attainment via a single variable: impossible … two variables (u,v) are necessary" — the
univariate argument does not cover interaction with the other lower variables, so "necessary" is unproved. Not load-bearing;
drop the word "necessary".

No mathematical correction is needed to G1–G5, A1–A5, E2, M1–M3, R1–R2, V1–V8 or the pessimistic construction.

## D. Mathlib citation check

All paths relative to `<SCRATCH>/mathlib/mathlib4/`. "gen" = generated by `to_additive`/`to_dual` from the cited source; I
verified the generated name is used elsewhere in Mathlib (so it really exists under that name).

| Declaration | Exists | file:line ok | Adequate | Note |
|---|---|---|---|---|
| `MvPolynomial.eval_C/eval_X/eval_add/eval_mul/eval_pow` | yes | Eval.lean:271,275,286,289,292 ✓ | yes | |
| `MvPolynomial.eval_sub` | yes | CommRing.lean:163 ✓ | yes | |
| `MvPolynomial.eval_sum`, `eval_prod` | yes | Eval.lean:295,299 ✓ | yes | over `Finset`, `map_sum`/`map_prod` |
| `MvPolynomial.rename` | yes | **Rename.lean:54** (report: 62) | yes | C4 |
| `rename_X`, `rename_rename`, `eval_rename` | yes | Rename.lean:62,80,244 ✓ | yes | `eval g (rename k p) = eval (g ∘ k) p` |
| `Finset.prod_nonneg` | yes | Order/BigOperators/GroupWithZero/Finset.lean:34 ✓ | yes | `[Preorder][ZeroLEOneClass][PosMulMono]` |
| `Finset.prod_pos` | yes | same file:160 ✓ | yes | `[PartialOrder][ZeroLEOneClass][PosMulStrictMono][Nontrivial]` — ℝ ok |
| `Finset.prod_eq_zero`, `prod_eq_zero_iff`, `prod_ne_zero_iff` | yes | BigOperators/GroupWithZero/Finset.lean:33,57,63 ✓ | yes | iff versions need `[Nontrivial][NoZeroDivisors]` |
| `Finset.sum_nonneg` | gen ✓ | from `one_le_prod`, Order/BigOperators/Group/Finset.lean:161–162 ✓ | yes | `@[to_additive sum_nonneg]` |
| `Finset.sum_eq_zero_iff_of_nonneg` | gen ✓ | from `prod_eq_one_iff_of_one_le` l.239–240 ✓ | yes | primed name at l.251 is a deprecated alias |
| `Finset.single_le_sum` | gen ✓ | from `single_le_prod` l.275–276 ✓ | yes | |
| `Fintype.sum_sum_type` | gen ✓ | Data/Fintype/BigOperators.lean:267–268 ✓ | yes | optional |
| `Fintype.prod_sigma` | yes | :151 ✓ | n/a | not needed |
| `sq_nonneg` | yes | Order/Ring/Unbundled/Basic.lean:608 ✓ | yes | |
| `sq_eq_zero_iff`, `pow_eq_zero_iff` | yes | GroupWithZero/Basic.lean:262,253 ✓ | yes | |
| `sq_pos_of_ne_zero` | yes (alias) | Order/Ring/Basic.lean:225 (of `sq_pos_iff` :223) ✓ | yes | |
| `one_le_sq_iff₀` | yes | Order/GroupWithZero/Basic.lean:749 ✓ | yes | `(ha : 0 ≤ a) : 1 ≤ a^2 ↔ 1 ≤ a` |
| `mul_nonpos_of_nonpos_of_nonneg` | yes | :79 ✓ | yes | |
| `mul_pos`, `mul_nonneg` | yes (aliases) | :46, :70 ✓ | yes | |
| `add_nonneg`, `add_pos_of_nonneg_of_pos`, `add_pos_of_pos_of_nonneg` | gen ✓ | Order/Monoid/Unbundled/Basic.lean:746,749,752 ✓ | yes | |
| `add_eq_zero_iff_of_nonneg` | gen ✓ | from `mul_eq_one_iff_of_one_le` :799–800 ✓ | yes | |
| `mul_eq_zero`, `mul_inv_cancel₀` | yes | GroupWithZero/Defs.lean:293,228 ✓ | yes | |
| `left_ne_zero_of_mul`, `mul_ne_zero` | yes | GroupWithZero/Basic.lean:54,84 ✓ | yes | |
| `sub_eq_zero` | gen ✓ | from `div_eq_one`, Group/Basic.lean:754–755 ✓ | yes | |
| `inv_nonneg`, `inv_pos` | yes | Order/GroupWithZero/Basic.lean:862,853 ✓ | yes | |
| `Real.sq_sqrt`, `sqrt_pos`, `sqrt_nonneg`, `sqrt_inv` | yes | Analysis/Real/Sqrt.lean:177,285,143,373 ✓ | yes | `√x⁻¹` parses as `√(x⁻¹)` (cf. `sqrt_inv`) |
| `exists_pos_mul_lt` | yes | Order/Field/Basic.lean:290 ✓ | yes | `(h : 0 < a) (b) : ∃ c, 0 < c ∧ b * c < a` |
| `EReal` (`CompleteLinearOrder` derived) | yes | Data/EReal/Basic.lean:34–38 ✓ | yes | |
| `EReal.rec` (`induction_eliminator`, `cases_eliminator`) | yes | :113 ✓ | yes | see C3 |
| `EReal.coe_le_coe_iff/coe_lt_coe_iff/coe_eq_coe_iff/coe_strictMono/coe_injective` | yes | :55,61,67,48,51 ✓ | yes | protected |
| `EReal.coe_ne_top/coe_ne_bot/bot_lt_coe/coe_lt_top` | yes | :270,258,254,266 ✓ | yes | |
| `EReal.eq_bot_iff_forall_lt`, `eq_top_iff_forall_lt` | yes | :438,430 ✓ | yes | `x = ⊥ ↔ ∀ y : ℝ, x < y` |
| `EReal.coe_sub/coe_add/coe_one/coe_zero` | yes | Operations.lean:222; Basic.lean:310,106,103 ✓ | yes | |
| `iInf_emptyset` | gen ✓ | from `iSup_emptyset` (`@[to_dual]`) Order/CompleteLattice/Basic.lean:583–584 ✓ | yes | `⨅ x ∈ (∅ : Set β), f x = ⊤` |
| `iInf_le`, `le_iInf` | gen ✓ | from `le_iSup`, `iSup_le` :210–211, 234–235 ✓ | yes | |
| `iInf₂_le`, `le_iInf₂` | gen ✓ | from `le_iSup₂`, `iSup₂_le` :225–226, 238–239 ✓ | yes | |
| `le_iInf_iff` | gen ✓ | :279–280 ✓ | yes | |
| `iInf_lt_iff` | gen ✓ | CompleteLattice/Defs.lean:318–319 ✓ | yes | |
| `iInf_eq_bot` | gen ✓ | from `iSup_eq_top` Defs.lean:334–335 ✓ | yes | |
| `iInf_eq_of_forall_ge_of_forall_gt_exists_lt` | gen ✓ | Basic.lean:373 ✓ | yes | |
| `Equiv.iInf_comp` | gen ✓ | from `Equiv.iSup_comp` :166–167 ✓ | yes | `⨅ x, g (e x) = ⨅ y, g y` |
| `iInf_congr`, `iInf_subtype'` | gen ✓ | :140–141, 415–416 ✓ | yes | |
| `Fintype.equivFin` | yes | Data/Fintype/EquivFin.lean:80 ✓ | yes | |
| `Equiv.arrowCongr`, `Equiv.piCongrLeft` | yes | Logic/Equiv/Defs.lean:453; Basic.lean:846 ✓ | yes | |
| `Equiv.sumCongr`, `sumAssoc`, `finSumFinEquiv` | yes | Logic/Equiv/Sum.lean:60,147; Fin/Basic.lean:224 ✓ | n/a | optional |
| `Function.update_self` | yes | Logic/Function/Basic.lean:644 ✓ | n/a | not needed |
| `Set.mem_iUnion`, `Set.mem_univ`, `Set.eq_empty_iff_forall_notMem` | yes | SetNotation.lean:224; Set/Operations.lean:105; Set/Basic.lean:460 ✓ | yes | |
| `Set.mem_setOf_eq` | deprecated alias | Set/Operations.lean:76 → `Set.mem_ofPred_eq` :73 | yes | C4 |
| `Sum.elim_inl/inr`, `Sum.elim_comp_inl/inr`, `Sum.elim_comp_map` | yes (core/Batteries; not defined in Mathlib) | — | yes | existence confirmed by use: Algebra/Category/ModuleCat/Free.lean:146,148; FieldTheory/AxGrothendieck.lean:163; ModelTheory/Semantics.lean:400. All needed instances are also `rfl` after `funext; rintro (_|_)`. |
| `lt_of_le_of_ne`, `ne_of_lt`, `le_min`, `lt_min`, `min_le_left/right`, `zero_lt_one`, `zero_lt_two` | yes | Order/Defs/PartialOrder.lean:201,100; LinearOrder.lean:168,204,162,165; ZeroLEOne.lean:52; Monoid/NatCast.lean:63 ✓ | yes | |
| Semialgebraic / Tarski–Seidenberg | NOT IN MATHLIB | — | — | agreed |

No MISUSED citation found. Universe/typeclass hypotheses of every lemma used are satisfied by ℝ / `EReal`.

## E. Missed issues

1. **Paper, proof of Thm 2.12, eq. (3) preamble:** "By definition, graph h = {(x,h(x))} is a semi-algebraic set" — for
   extended-real `h` this must be `graph(h|dom h)`; Def 2.2 assumes only that. The report's `Γ h` encodes the correct set but
   does not list the misstatement. Minor.
2. **Paper, Section 2.4 also covers Theorem 2.18** ("Both representation results involving unbounded boxes … unique
   minimizers"). The report correctly refutes it for Thm 2.12; whether it holds for the convex unbounded construction
   (Thm 2.18) is out of R3's scope and must be checked by that report (escalate, G2).
3. **"Any selection" claim is false for every construction, not just the paper's**, whenever `h` takes the value −∞ (a
   selection yields a real number `P(x,s(x))` when Θ(x) ≠ ∅) — the report says this ("no selection can produce ±∞");
   worth stating as a theorem-level remark in the blueprint: the "any selection" version holds exactly for real-valued `h`
   (via `Q = W_Γ`).
4. **Lean:** C1 (index nesting) and C3 (case split) above.
5. **Lean:** `valueFun` generalised to arbitrary `ι` changes the shared definition used by other reports; if the blueprint
   keeps `Fin m` as the primary definition, R1 must be proved once in a shared file. (Escalate, G3.)

## F. Route assessment and recommendation

The simplified construction is the cheapest correct route I can see: two gadgets (Γ, D₋), one escape term, lower variables
`(t, z, ν, u, v)`, hypotheses only `IsSemialgebraic (Γ h)` and `IsSemialgebraic (D₋ h)`. Compared with the paper: the paper
needs four gadgets (F, H, H⁺, H⁻), two more evaluation identities, uniform index padding, and its proof uses all four set
hypotheses; the simplified one saves roughly 30–40% of the Lean for this theorem with zero new mathematics. The theorem
proved implies the paper's (same conclusion; Def 2.2's graph and dom⁻ hypotheses are a subset of its assumptions) and is
consistent with Prop 2.6 (under Tarski–Seidenberg, `dom h = π(Γ)` and `{h=+∞} = ℝⁿ \ (dom h ∪ D₋)` are semialgebraic, so
the hypothesis sets are actually equivalent modulo TS; without TS in Lean the simplified statement is formally stronger).

Recommended blueprint route:
1. Shared gadget file: G1, G2, G3, G4 (`ZeroGadget` with selector), G5; generic A1–A5 and duals.
2. `exists_bilevel_valueFun_eq` (hyps: Γ, D₋) with `Q = W_Γ·W₋·u² + (1−uv)²`, `P = t`; then `thm_2_12_sup` from
   `IsSemialgebraicEReal` as a one-line corollary; `Fin m` form via R1/R2 only if `valueFun` is fixed to `Fin m`.
3. Pessimistic theorem via the swap (hyps Γ, D₊) — nearly free, and it corrects Section 2.4.
4. Real-valued corollary `Q = W_Γ` (optimistic = pessimistic = any selection) as Remark 2.14 / Section 2.4 fix.
5. Paper's `Q`: prose remark with V1–V8 and the (7) typo fix. Do **not** formalize it as an optional corollary: it has the
   same conclusion as step 2, so a formal version would only certify the paper's specific polynomial; it costs two extra
   gadget instantiations, the uniform-index padding (or a non-uniform rewrite), and the three-case argument again (≈ M–L).
   If fidelity is ever wanted, it can be added later on top of the same G1–G5 without touching anything else.

## G. Escalations to the orchestrator

1. **Ambient type for graphs** (`Fin n ⊕ Unit` vs `Fin (n+1)`) and whether R2's `IsSemialgebraic` is stated for an arbitrary
   `Fintype σ`. R3 needs `σ = Fin n ⊕ Unit` (or a `rename`-along-`Equiv` transfer lemma). Must be consistent with R2.
2. **Section 2.4 uniqueness claim** must be checked for Theorem 2.18 (convex, unbounded box) by its report; for Thm 2.12 it
   is false (confirmed).
3. **`valueFun` over a general `ι`** vs `Fin m`: a definitional choice affecting every report; recommend general `ι` with a
   single shared reindexing lemma R1.
4. **Definition 2.11 must be extended-real valued** for `P_unbound = SA` (confirmed: paper writes `h : ℝⁿ → ℝ`, paper_html.txt l. 324); this
   affects the statement of the class definitions used by all reports (for bounded boxes nothing changes by Cor. 2.9).
5. **Gadget sharing:** G1–G5 and the `ZeroGadget` interface should be one shared module also used by Thm 1.1 / Thm 2.15
   reports (they need an additional `≥ 0` gadget on bounded boxes); align names.
6. **Interface lemma `IsSemialgebraic.exists_basic_family`** (with per-block index types `κ i`) must be provided by R2 in
   exactly this shape (or the uniform `ι × κ` variant).
