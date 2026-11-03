# R3 — Theorem 2.12 (unconstrained lower level): every extended-real semialgebraic function is an optimistic value function

Paper: Bolte–Lê–Pauwels–Vaiter, arXiv:2407.12372v2, Section 2.2 (Def 2.11, Thm 2.12, eqs (3)–(7), Table 1, Remarks 2.13–2.14) and Section 2.4 (pessimistic counterpart). Mathlib checkout: `<SCRATCH>/mathlib/mathlib4` (commit 1df8067a); every declaration cited below was located by grep in that tree (file:line given in §4). No Lean toolchain is available, so all Lean text here is a *sketch* and has not been compiled.

## 0. TL;DR

* The paper's construction (eqs (5)–(7), `Q = H⁺H⁻F + HH⁻u² + (1−uv)²`) is **correct** after fixing one typo in (7) (`S_ij` must be `S⁺_ij`, `S⁻_ij`) and one padding remark ("dummy `0 = 0`" cannot be used to pad the *outer* index set `I`; empty basic sets such as `{1 = 0}` must be used). All six verification points (b)(i)–(vi) of my brief check out and are recorded as lemmas V1–V8 in §2.1.
* The construction can be **simplified substantially while proving the same (indeed a stronger) theorem**: neither the `dom(h)` gadget `H` (variables `ν`) nor the `dom(h)⁺` gadget `H⁺` (variables `ν⁺`) is needed. The minimal lower-level objective is

  `Q(x; t, z, ν, u, v) = W_Γ(x, t, z) · W₋(x, ν) · u² + (1 − u·v)²,   P(x; y) = t`

  where `W_Γ` is a "zero-locus gadget" for `Γ := graph(h|dom h) ⊆ ℝⁿ⁺¹` and `W₋` one for `D₋ := {h = −∞} ⊆ ℝⁿ`. Full proofs in §2.2–2.4. Only semialgebraicity of `Γ` and `D₋` is used; semialgebraicity of `{h = +∞}` and of `dom h` is **not needed** (it follows from the other two via Tarski–Seidenberg, so the statement is a genuine strengthening of Theorem 2.12's hypotheses, consistent with Prop 2.6).
* Variable count: `m = 3 + |τ_Γ| + |τ₋|` where `τ_Γ`, `τ₋` are the numbers of strict inequalities appearing in the descriptions of `Γ` and `D₋` (paper: `m = 3 + 4|I||J|` after padding all four sets to common index sets).
* Everything is built from five reusable gadget lemmas (G1–G5, §2.2) plus five generic argmin/`valueFun` lemmas (A1–A5, §2.3). G1–G4 give, as a by-product, Remark 2.14: every semialgebraic set is the projection of the zero locus of a nonnegative polynomial. G5 is the "non-attained infimum" gadget. These are the same bricks Theorem 1.1 / Theorem 2.15 need (with a different scalar gadget for `≥ 0` constraints on a bounded box).
* Section 2.4's claim that the unbounded-box constructions "involve unique minimizers in the lower level", hence transfer verbatim to the pessimistic/any-selection setting, is **false** for Theorem 2.12 (minimizers are highly non-unique; on `{h = −∞}` the whole `t`-line is in `Θ(x)`, so the pessimistic value there is `+∞`, not `−∞`). The correct pessimistic statement (swap the roles of `{h=+∞}` and `{h=−∞}`; or negate) is given in §2.7 with proof.

---

## 1. Scope: exact statements

### 1.1 The paper's statement and the fix of Definition 2.11

Definition 2.11 defines `P_boxtype := {h : ℝⁿ → ℝ | ∃ P, Q polynomials, 𝒴 box of type boxtype, φ = h}` with **real-valued** `h`, but `φ` (eq. (BP-O)) is extended-real-valued (`+∞` if `Θ(x) = ∅`, `−∞` if `P(x,·)` is unbounded below on `Θ(x)`) and Theorem 2.12 asserts `P_unbound = SA` where `SA` (Def 2.2) consists of extended-real-valued functions. As written, `P_unbound ⊆ SA` would only be the real-valued part. **Fix:** read Definition 2.11 with `h : ℝⁿ → ℝ ∪ {±∞}` (for `P_bounded` the value function is automatically real-valued by Corollary 2.9, so nothing changes there).

**Theorem 2.12 (⊇, the content of this report).** Let `h : ℝⁿ → ℝ ∪ {±∞}` be an extended-real-valued semialgebraic function (Def 2.2). Then there exist `m ∈ ℕ` and polynomials `P, Q ∈ ℝ[x₁..xₙ, y₁..yₘ]` such that for every `x ∈ ℝⁿ`,
`φ(x) := inf { P(x,y) | y ∈ Θ(x) } = h(x)`, where `Θ(x) = argmin_{y ∈ ℝᵐ} Q(x,y)` (conventions `inf ∅ = +∞`, unbounded below `= −∞`).

**Theorem 2.12 (⊆).** `P_unbound ⊆ SA` is Proposition 2.6 (Tarski–Seidenberg applied to the first-order descriptions of `dom φ`, `dom φ⁺`, `dom φ⁻`, `graph φ|dom φ`); handled by agent R2; in the blueprint it rests on the projection-stability assumption. Nothing in this report depends on it.

### 1.2 Semialgebraic data as consumed here (interface with R2)

I only *consume* semialgebraic sets through the following normal form, which is literally definition (A) of the brief (finite union of basic sets, each basic set with its own finite family of strict inequalities and one equation); if R2 chooses (B), R2's (A)⇔(B) lemma supplies it:

```lean
-- Interface lemma expected from R2 (any Fintype index σ for the ambient space).
theorem IsSemialgebraic.exists_basic_family {σ : Type*} [Fintype σ] {S : Set (σ → ℝ)}
    (hS : IsSemialgebraic S) :
    ∃ (ι : Type) (_ : Fintype ι) (κ : ι → Type) (_ : ∀ i, Fintype (κ i))
      (P : ι → MvPolynomial σ ℝ) (Q : (i : ι) → κ i → MvPolynomial σ ℝ),
      S = ⋃ i, {w | MvPolynomial.eval w (P i) = 0 ∧ ∀ j, 0 < MvPolynomial.eval w (Q i j)}
```
Variants (all fine, see §2.2 G2/G3 remarks): uniform `κ` (`Fin k × Fin l` data) — then use the product type `ι × κ` instead of `Σ i, κ i`; several equations per basic set — replace `P²` by `∑ₑ Pₑ²` in G2; `Fin k`, `Fin (l i)` instead of `Type`.

Extended-real-valued semialgebraic function (Def 2.2), encoded as in the brief. For `h : (Fin n → ℝ) → EReal` write
* `D₊ h := {x | h x = ⊤}`, `D₋ h := {x | h x = ⊥}`, `dom h := {x | h x ≠ ⊤ ∧ h x ≠ ⊥}`,
* `Γ h : Set (Fin n ⊕ Unit → ℝ) := {p | h (p ∘ Sum.inl) = ((p (Sum.inr ())) : EReal)}` — this is exactly `graph (h|dom h)` (no `t` satisfies `⊤ = ↑t` or `⊥ = ↑t`).

```lean
structure IsSemialgebraicEReal {n : ℕ} (h : (Fin n → ℝ) → EReal) : Prop where
  graph : IsSemialgebraic (Γ h)          -- graph of the real-valued restriction
  top   : IsSemialgebraic (D₊ h)
  bot   : IsSemialgebraic (D₋ h)
  dom   : IsSemialgebraic (dom h)        -- paper's Def 2.2; redundant, NOT used below
```
(`Fin n ⊕ Unit` rather than `Fin (n+1)` avoids `Fin.snoc`/`Fin.init` bookkeeping; if R2 standardises on `Fin (n+1)`, one needs a reindexing lemma `IsSemialgebraic.comp_equiv` for `MvPolynomial.rename` along an `Equiv` — see §8.)

### 1.3 Lean-style signatures

Baseline encoding from the brief, generalised to an arbitrary finite index type `ι` for the lower variable (the `Fin m` form is a corollary via reindexing, lemma R1 in §2.5):

```lean
def argminSet {n : ℕ} {ι : Type*} (Q : (Fin n → ℝ) → (ι → ℝ) → ℝ) (Y : Set (ι → ℝ)) (x : Fin n → ℝ) :
    Set (ι → ℝ) := {y ∈ Y | ∀ y' ∈ Y, Q x y ≤ Q x y'}

noncomputable def valueFun {n : ℕ} {ι : Type*} (P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ) (Y : Set (ι → ℝ))
    (x : Fin n → ℝ) : EReal := ⨅ y ∈ argminSet Q Y x, ((P x y : ℝ) : EReal)

/-- Evaluation of a polynomial in (x,y). -/
noncomputable def evalXY {n : ℕ} {ι : Type*} (p : MvPolynomial (Fin n ⊕ ι) ℝ) :
    (Fin n → ℝ) → (ι → ℝ) → ℝ := fun x y => MvPolynomial.eval (Sum.elim x y) p
```

**Main theorem (strengthened hypotheses; recommended blueprint statement).**
```lean
theorem exists_bilevel_valueFun_eq {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hΓ : IsSemialgebraic (Γ h)) (hbot : IsSemialgebraic (D₋ h)) :
    ∃ (ι : Type) (_ : Fintype ι) (P Q : MvPolynomial (Fin n ⊕ ι) ℝ),
      ∀ x, valueFun (evalXY P) (evalXY Q) Set.univ x = h x
```
**Theorem 2.12 (⊇) as stated in the paper, `Fin m` form.**
```lean
theorem thm_2_12_sup {n : ℕ} (h : (Fin n → ℝ) → EReal) (hh : IsSemialgebraicEReal h) :
    ∃ (m : ℕ) (P Q : MvPolynomial (Fin n ⊕ Fin m) ℝ),
      ∀ x, valueFun (evalXY P) (evalXY Q) Set.univ x = h x
```
(`Set.univ` is the unconstrained box `𝒴 = ℝᵐ`, an unbounded box in the sense of Def 2.11.) `P_unbound = SA` is then the conjunction of `thm_2_12_sup` with R2's `Prop 2.6`.

---

## 2. Proof route (DAG of lemmas)

### 2.0 Overview

Paper's lower-level objective (Table 1 variables `y = (t, z, ν, ν⁺, ν⁻, u, v)`):
```
F(x,t,z)  = ∏_i ( P_i(x,t)² + ∑_j (1 − Q_ij(x,t) z_ij²)² )          -- graph gadget (5)
H, H⁺, H⁻ = same shape for dom h, dom h⁺, dom h⁻ in variables ν, ν⁺, ν⁻   -- (7)
Q = H⁺(x,ν⁺) H⁻(x,ν⁻) F(x,t,z) + H(x,ν) H⁻(x,ν⁻) u² + (1 − uv)²,   P = t
```
Minimal objective proved here (§2.4): `Q = N( W_Γ(x,t,z) · W₋(x,ν), u, v )` with `N(a,u,v) := a u² + (1 − uv)²`, i.e.
```
Q = W_Γ(x,t,z) · W₋(x,ν) · u² + (1 − uv)²,   P = t,   y = (t, z, ν, u, v).
```
Mechanism, for fixed `x`:
| case | `a(t,z,ν) := W_Γ·W₋` | `Q = N(a,u,v)` | `Θ(x)` | `φ(x)` |
|---|---|---|---|---|
| `h x = r ∈ ℝ` | `a = 0 ⇔ t = r` (attainable) | min `0` attained iff `a = 0 ∧ uv = 1` | `{t = r, W_Γ = 0, uv = 1}` ≠ ∅ | `r` |
| `h x = +∞` | `a > 0` for all `(t,z,ν)` | `Q > 0` everywhere, `inf Q = 0` | `∅` | `+∞` |
| `h x = −∞` | `a = 0` attainable for every `t` | `Q = 0` at `(t, 0, s₋ x, 1, 1)` ∀ t | contains every `t` | `−∞` |

### 2.1 Line-by-line verification of the paper's construction (task (b))

Throughout, `(x,t)` fixed, all functions real-valued. Each item is a lemma usable as is if the blueprint wants a "faithful" version; the minimal route of §2.4 only needs G1–G5 (which subsume V1–V3 and V5).

**V1 (eq. (6), scalar gadget).** `G(q, z) := (1 − q z²)²`. (a) `G ≥ 0`. (b) If `q > 0` then `min_z G = 0`, attained exactly at `z = ±1/√q` (two minimizers). (c) If `q ≤ 0` then `G(q,z) ≥ 1` for all `z` (since `q z² ≤ 0 ⇒ 1 − q z² ≥ 1`), with equality at `z = 0`; if `q = 0` every `z` is a minimizer. So the "`G* = 1` otherwise" in (6) is correct, but the minimizer is never unique (relevant for §2.7). *Proof:* G1 below.

**V2 (basic factor).** `B_i(x,t,z_i) := P_i(x,t)² + ∑_j G(Q_ij(x,t), z_ij) ≥ 0`, and `∃ z_i, B_i = 0 ⇔ (P_i(x,t) = 0 ∧ ∀ j, Q_ij(x,t) > 0) ⇔ (x,t) ∈ 𝒮_i`; if `(x,t) ∉ 𝒮_i` then `B_i > 0` for all `z_i` (indeed `B_i ≥ P_i² > 0` if `P_i ≠ 0`, and `B_i ≥ 1` if some `Q_ij ≤ 0`). *Proof:* G2.

**V3 (eq. (5), case analysis of F).** `F = ∏_i B_i ≥ 0`. `F(x,t,z) = 0` for some `z` iff some `B_i` vanishes for some `z_i` iff `(x,t) ∈ ⋃_i 𝒮_i = graph h` (for `x ∈ dom h`: iff `t = h(x)`). If `(x,t) ∉ graph h` then every factor is `> 0` for every `z`, so `F(x,t,z) > 0` for all `z` (product of positives). The paper's "`F ≥ 0` and the product can be `0` only if one factor is `0`" is exactly `Finset.prod_eq_zero_iff` over ℝ (no zero divisors). *Proof:* G3.

**V4 (eq. (7), H, H⁺, H⁻).** Same statements with `(x,t)` replaced by `x` and `𝒮_i` by `𝒟_i, 𝒟⁺_i, 𝒟⁻_i`, **provided** `K⁺_ij` and `K⁻_ij` are defined with `S⁺_ij` and `S⁻_ij` (the paper writes `S_ij` in all three lines of (7) — typo, see §3 item 2). With the typo as printed, `H⁺` and `H⁻` would encode `{R⁺_i = 0 ∧ S_ij > 0}`, which is unrelated to `dom(h)⁺`, and Case 2 would fail.

**V5 (escape gadget, used in Case 2).** For `a > 0`: `a u² + (1 − uv)² > 0` for all `(u,v)` (if `u = 0` the value is `1`; else `a u² > 0`). For `a ≥ 0`: `inf_{u,v} (a u² + (1−uv)²) = 0` (take `v = 1/u`, `u → 0`). For `a = 0`: minimum `0` attained on the hyperbola `uv = 1` (non-unique). *Proof:* G5.

**V6 (Case 1, `x ∈ dom h`).** `H⁺(x,ν⁺) > 0`, `H⁻(x,ν⁻) > 0` for all `ν±` (V4, since `x ∉ dom h⁺ ∪ dom h⁻`). `Q ≥ 0` as a sum of products of nonnegative terms. Attainment: `t = h(x)`, `z = z*` (V3), `ν = ν*` with `H(x,ν*) = 0` (V4, `x ∈ dom h`), `u = v = 1`: all three summands vanish, `Q = 0`. Hence `Θ(x) = {y | Q(x,y) = 0}` (A1). If `Q(x,y) = 0`: each summand is `0`; from `H⁺H⁻ > 0` and `H⁺H⁻F = 0` we get `F(x,t,z) = 0`, so `(x,t) ∈ graph h`, i.e. `t = h(x)` (V3). (The paper's objection "could `Q₁` vanish because `H⁻ = 0`?" — no: `x ∉ dom h⁻`.) So `P = t = h(x)` on all of `Θ(x) ≠ ∅` and `φ(x) = h(x)` (A4). ✔

**V7 (Case 2, `x ∈ dom h⁺`).** For all `ν, ν⁻`: `H(x,ν) > 0`, `H⁻(x,ν⁻) > 0` (V4, `x ∉ dom h`, `x ∉ dom h⁻`), so `a := H H⁻ > 0` and the second-plus-third summand `a u² + (1−uv)² > 0` (V5) while the first is `≥ 0`: `Q(x,y) > 0` for every `y`. Infimum `0`: fix `ν⁺*` with `H⁺(x,ν⁺*) = 0` (V4, `x ∈ dom h⁺`), fix any `t, z, ν, ν⁻`; then `Q = a u² + (1−uv)²` with `a > 0` fixed, which is `< ε` for suitable `(u,v)` (V5). Hence no `y` attains the infimum: `Θ(x) = ∅` (A2) and `φ(x) = +∞` (A3). ✔ (The paper's "`u → 0, v = 1/u → +∞`" is this.)

**V8 (Case 3, `x ∈ dom h⁻`).** Choose `ν⁻*` with `H⁻(x,ν⁻*) = 0` (V4). Then for **every** `t ∈ ℝ` and any `z, ν, ν⁺`, with `u = v = 1`: `Q = H⁺·0·F + H·0·1 + 0 = 0`, so (as `Q ≥ 0`) this `y` is in `Θ(x)` with `P = t`. Hence `{P(x,y) | y ∈ Θ(x)} = ℝ`, `φ(x) = −∞` (A5). ✔ The first term vanishes identically regardless of `F`, as noted in the brief.

Conclusion: the paper's proof is correct modulo §3 items 2–3, and `H`/`H⁺` are never needed for correctness (V6 uses `H = 0` only for attainment, which `W_Γ = 0` already gives if the `u²` term is multiplied by `W_Γ W₋` instead of `H H⁻`; V7 uses `H⁺ = 0` only to kill the first summand, which is unnecessary once the first summand is merged into the `u²` term). This is the simplification of §2.4.

### 2.2 Reusable gadget lemmas (task (d)(3)), with full proofs

All lemmas are over ℝ; `σ`, `κ`, `ι`, `τ` are finite index types.

**Definition (zero-locus gadget with selector).**
```lean
structure ZeroGadget {σ : Type*} (S : Set (σ → ℝ)) (τ : Type*) where
  W : MvPolynomial (σ ⊕ τ) ℝ
  sel : (σ → ℝ) → (τ → ℝ)                                   -- explicit witness map
  nonneg : ∀ w ξ, 0 ≤ MvPolynomial.eval (Sum.elim w ξ) W
  sel_zero : ∀ w ∈ S, MvPolynomial.eval (Sum.elim w (sel w)) W = 0
  pos_of_notMem : ∀ w ∉ S, ∀ ξ, 0 < MvPolynomial.eval (Sum.elim w ξ) W
```
Derived facts (one-liners): `mem_of_eval_eq_zero : eval (Sum.elim w ξ) W = 0 → w ∈ S` (contrapositive of `pos_of_notMem` with `ne_of_gt`); `mem_iff : w ∈ S ↔ ∃ ξ, eval (Sum.elim w ξ) W = 0`. The selector avoids any `Classical.choose`/cast when assembling unions (G3) and witnesses (M1, M3). (Statement in words: `∀ w, (w ∈ S ↔ ∃ ξ, W(w,ξ) = 0) ∧ (w ∉ S → ∀ ξ, W(w,ξ) > 0)`, exactly the gadget statement proposed in the brief, plus `W ≥ 0`.)

**G1 (scalar strict-inequality gadget).** `g (p z : ℝ) : ℝ := (1 - p * z ^ 2) ^ 2`.
1. `0 ≤ g p z` — `sq_nonneg _`.
2. `0 < p → g p (Real.sqrt p⁻¹) = 0` — `(√p⁻¹)^2 = p⁻¹` by `Real.sq_sqrt (inv_nonneg.2 hp.le)`; `p * p⁻¹ = 1` by `mul_inv_cancel₀ hp.ne'`; so `1 - 1 = 0` and `0^2 = 0`.
3. `p ≤ 0 → 1 ≤ g p z` — `p * z^2 ≤ 0` by `mul_nonpos_of_nonpos_of_nonneg hp (sq_nonneg z)`, hence `1 ≤ 1 - p z^2`, hence `1 ≤ (1 - p z^2)^2` by `one_le_sq_iff₀ (by linarith)` (or `nlinarith`).
4. `g p z = 0 → 0 < p` — by contradiction from 3 (`1 ≤ 0`). (`lt_of_not_ge`.)
Size S.

**G2 (basic set gadget).** Data `P : MvPolynomial σ ℝ`, `Q : κ → MvPolynomial σ ℝ`, `S := {w | eval w P = 0 ∧ ∀ j, 0 < eval w (Q j)}`.
```lean
W_B := (rename Sum.inl P) ^ 2 + ∑ j, (1 - rename Sum.inl (Q j) * X (Sum.inr j) ^ 2) ^ 2   -- in MvPolynomial (σ ⊕ κ) ℝ
sel_B w := fun j => Real.sqrt (eval w (Q j))⁻¹
```
* **Eval identity** `eval (Sum.elim w ξ) W_B = (eval w P)^2 + ∑ j, g (eval w (Q j)) (ξ j)`: `simp [MvPolynomial.eval_add, eval_pow, eval_sum, eval_sub, eval_mul, eval_one, eval_X, eval_rename]` plus `Sum.elim w ξ ∘ Sum.inl = w` (core `Sum.elim_comp_inl`, or `rfl` after `funext`).
* `nonneg`: `add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => G1.1)`.
* `sel_zero`: for `w ∈ S`, `eval w P = 0` so the square is `0`; each summand is `g (eval w (Q j)) (√(eval w (Q j))⁻¹) = 0` by G1.2; `Finset.sum_eq_zero`-style (`Finset.sum_const_zero` after `Finset.sum_congr`) gives `0`.
* `pos_of_notMem`: `w ∉ S` means `eval w P ≠ 0 ∨ ∃ j, eval w (Q j) ≤ 0` (`not_and_or`, `not_forall`, `not_lt`). First case: value `≥ (eval w P)^2 > 0` (`sq_pos_of_ne_zero`, `le_add_of_nonneg_right`-type step with the sum `≥ 0`). Second case: value `≥ g (eval w (Q j₀)) (ξ j₀) ≥ 1 > 0` (`Finset.single_le_sum` with nonneg terms, G1.3). Alternatively prove `W_B = 0 → w ∈ S` via `add_eq_zero_iff_of_nonneg`, `sq_eq_zero_iff`, `Finset.sum_eq_zero_iff_of_nonneg`, G1.4, then positivity by `lt_of_le_of_ne` — either way S/M.
* *Variant, several equations* `P : ε → MvPolynomial σ ℝ`: use `∑ e, (rename Sum.inl (P e))^2`; `(∑ e, a_e^2 = 0) ↔ ∀ e, a_e = 0` by `Finset.sum_eq_zero_iff_of_nonneg` + `sq_eq_zero_iff`. Same proofs.
Size M.

**G3 (finite union gadget).** Data: `ι` finite, `τ : ι → Type` finite, `𝒢 i : ZeroGadget (S i) (τ i)`. Put `τ' := Σ i, τ i` and
```lean
W_U := ∏ i, rename (Sum.map id (Sigma.mk i)) (𝒢 i).W        -- in MvPolynomial (σ ⊕ Σ i, τ i) ℝ
sel_U w := fun p => (𝒢 p.1).sel w p.2
```
* **Eval identity** `eval (Sum.elim w ξ) W_U = ∏ i, eval (Sum.elim w (fun j => ξ ⟨i, j⟩)) (𝒢 i).W`: `MvPolynomial.eval_prod`, `eval_rename`, and `Sum.elim w ξ ∘ Sum.map id (Sigma.mk i) = Sum.elim w (fun j => ξ ⟨i,j⟩)` (`funext; rintro (a|b) <;> rfl`).
* `nonneg`: `Finset.prod_nonneg fun i _ => (𝒢 i).nonneg _ _`.
* `sel_zero`: `w ∈ ⋃ i, S i` gives `i₀` with `w ∈ S i₀` (`Set.mem_iUnion`). The factor `i₀` evaluates at `fun j => sel_U w ⟨i₀, j⟩ = (𝒢 i₀).sel w j` (definitional), so it is `0` by `(𝒢 i₀).sel_zero`; conclude with `Finset.prod_eq_zero (Finset.mem_univ i₀)`.
* `pos_of_notMem`: `w ∉ ⋃ i, S i` gives `∀ i, w ∉ S i`; each factor `> 0` by `(𝒢 i).pos_of_notMem`; `Finset.prod_pos`.
* Empty `ι`: product is `1 > 0` and the union is `∅` — the lemma covers it without a special case.
* If R2's normal form has a uniform `κ`, use `τ' := ι × κ`, `Sum.map id (Prod.mk i)`, `fun j => ξ (i, j)` — identical proof, no `Sigma`.
Size M (bookkeeping of `rename`/`Sum.elim`, no mathematics).

**G4 (semialgebraic ⇒ gadget).** `IsSemialgebraic S → ∃ (τ : Type) (_ : Fintype τ), Nonempty (ZeroGadget S τ)`. Proof: `IsSemialgebraic.exists_basic_family` (R2) gives `ι, κ, P, Q` with `S = ⋃ i, basic i`; apply G2 to each `i` (gadget for `basic i` on `κ i`), then G3; rewrite with `S = ⋃ ...`. Size S given G2, G3. (This is Remark 2.14's "representation of semialgebraic sets as the projection of a polynomial zero locus": `S = {w | ∃ ξ, W(w,ξ) = 0}` with `W ≥ 0`.)

**G5 (escape / non-attainment gadget).** `N (a u v : ℝ) : ℝ := a * u ^ 2 + (1 - u * v) ^ 2`.
1. `0 ≤ a → 0 ≤ N a u v` — `add_nonneg (mul_nonneg ha (sq_nonneg u)) (sq_nonneg _)`.
2. `N a 1 1 = a` — `ring`/`simp`; hence `a = 0 → N a 1 1 = 0`.
3. `0 < a → ∀ u v, 0 < N a u v` — `by_cases hu : u = 0`: if `u = 0`, `N = 0 + (1 - 0)^2 = 1 > 0`; else `0 < a * u^2` (`mul_pos ha (sq_pos_of_ne_zero hu)`) and `add_pos_of_pos_of_nonneg _ (sq_nonneg _)`.
4. `0 ≤ a → ∀ ε > 0, ∃ u v, N a u v < ε` — `obtain ⟨c, hc, hac⟩ := exists_pos_mul_lt hε a` (gives `0 < c`, `a * c < ε`); take `u := √c`, `v := (√c)⁻¹`: `u^2 = c` (`Real.sq_sqrt hc.le`), `u * v = 1` (`mul_inv_cancel₀ (Real.sqrt_pos.2 hc).ne'`), so `N = a * c + 0 < ε`.
5. `0 ≤ a → N a u v = 0 → a = 0 ∧ u * v = 1` — `add_eq_zero_iff_of_nonneg (mul_nonneg ha (sq_nonneg u)) (sq_nonneg _)` gives `a u² = 0` and `(1 - uv)² = 0`; the latter gives `uv = 1` (`sq_eq_zero_iff`, `sub_eq_zero`), so `u ≠ 0` (`left_ne_zero_of_mul` applied to `uv = 1 ≠ 0`), so `u² ≠ 0`, so `a = 0` (`mul_eq_zero`).
6. Converse: `a = 0 → u * v = 1 → N a u v = 0` — `simp`.
Size S.

### 2.3 Generic argmin / value-function lemmas (unconstrained box `Y = Set.univ`)

Let `Q : (Fin n → ℝ) → (ι → ℝ) → ℝ`, `x` fixed. Write `Θ := argminSet Q Set.univ x`; after `simp [argminSet, Set.mem_univ]`, `y ∈ Θ ↔ ∀ y', Q x y ≤ Q x y'`.

**A1 (zero set = argmin).** `(∀ y, 0 ≤ Q x y) → Q x y₀ = 0 → Θ = {y | Q x y = 0}`. ⊆: `y ∈ Θ ⇒ Q x y ≤ Q x y₀ = 0`, with `0 ≤ Q x y` gives `= 0` (`le_antisymm`). ⊇: `Q x y = 0 ≤ Q x y'`. Also the one-directional `Q x y = 0 → y ∈ Θ` (needs only nonnegativity). S.

**A2 (empty argmin).** `(∀ y, 0 < Q x y) → (∀ ε > 0, ∃ y, Q x y < ε) → Θ = ∅`. If `y ∈ Θ`, apply the second hypothesis with `ε := Q x y > 0` to get `y'` with `Q x y' < Q x y ≤ Q x y'`, contradiction (`lt_irrefl`). Use `Set.eq_empty_iff_forall_notMem`. S.

**A3 (value over empty argmin).** `Θ = ∅ → valueFun P Q Set.univ x = ⊤`: `unfold valueFun; rw [hΘ]; exact iInf_emptyset`. S.

**A4 (constant value on argmin).** `y₀ ∈ Θ → P x y₀ = c → (∀ y ∈ Θ, P x y = c) → valueFun P Q Set.univ x = (c : EReal)`. `le_antisymm`: `≤` by `iInf₂_le y₀ hy₀` and rewriting `P x y₀ = c`; `≥` by `le_iInf₂ fun y hy => by rw [hc y hy]`. S.

**A5 (unbounded below).** `(∀ r : ℝ, ∃ y ∈ Θ, P x y ≤ r) → valueFun P Q Set.univ x = ⊥`. Use `(EReal.eq_bot_iff_forall_lt _).2`: for `r : ℝ`, get `y ∈ Θ` with `P x y ≤ r - 1`; then `valueFun ≤ ↑(P x y) ≤ ↑(r-1) < ↑r` (`iInf₂_le`, `EReal.coe_le_coe_iff`, `EReal.coe_lt_coe_iff`, `linarith`). S. (Alternative: `iInf_eq_bot` from `to_dual` of `iSup_eq_top`, then `EReal.rec` on the bound.)

Pessimistic duals (§2.7): A3' `Θ = ∅ → ⨆ ... = ⊥` (`iSup_emptyset`), A4' identical with `le_iSup₂`/`iSup₂_le`, A5' `(∀ r, ∃ y ∈ Θ, r ≤ P x y) → ⨆ = ⊤` (`EReal.eq_top_iff_forall_lt`).

### 2.4 Main assembly (minimal construction)

Fix `h`, gadgets `𝒢_Γ : ZeroGadget (Γ h) τ_Γ` (from G4 applied to `hΓ`, ambient `σ = Fin n ⊕ Unit`) and `𝒢₋ : ZeroGadget (D₋ h) τ₋` (from G4 applied to `hbot`, ambient `Fin n`). Lower index type and coordinate projections:
```lean
abbrev ι := Unit ⊕ (τ_Γ ⊕ (τ₋ ⊕ (Unit ⊕ Unit)))           -- (t, z, ν, u, v)
def tc (y : ι → ℝ) : ℝ := y (.inl ())
def zc (y : ι → ℝ) : τ_Γ → ℝ := fun j => y (.inr (.inl j))
def νc (y : ι → ℝ) : τ₋ → ℝ := fun j => y (.inr (.inr (.inl j)))
def uc (y : ι → ℝ) : ℝ := y (.inr (.inr (.inr (.inl ()))))
def vc (y : ι → ℝ) : ℝ := y (.inr (.inr (.inr (.inr ()))))
def mk (t : ℝ) (z : τ_Γ → ℝ) (ν : τ₋ → ℝ) (u v : ℝ) : ι → ℝ :=
  Sum.elim (fun _ => t) (Sum.elim z (Sum.elim ν (Sum.elim (fun _ => u) (fun _ => v))))
```
Real-valued abbreviations (`x : Fin n → ℝ`):
`WΓ x t z := eval (Sum.elim (Sum.elim x (fun _ => t)) z) 𝒢_Γ.W`, `W₋ x ν := eval (Sum.elim x ν) 𝒢₋.W`, `a x t z ν := WΓ x t z * W₋ x ν`.

**E2 (the `a`-lemma).** For all `x t z ν`:
1. `0 ≤ a x t z ν` (`mul_nonneg` of the two `nonneg`).
2. `a x t z ν = 0 → h x = ↑t ∨ h x = ⊥`: `mul_eq_zero`, then `𝒢_Γ.mem_of_eval_eq_zero` (unfold `Γ h`: `(Sum.elim x (fun _ => t)) ∘ Sum.inl = x` and `(…) (Sum.inr ()) = t`, both `rfl`/`funext`) or `𝒢₋.mem_of_eval_eq_zero`.
3. `h x = ↑t → a x t (𝒢_Γ.sel (Sum.elim x fun _ => t)) ν = 0` (first factor `0` by `sel_zero`; `mul_eq_zero.2 (Or.inl _)`).
4. `h x = ⊥ → a x t z (𝒢₋.sel x) = 0` (second factor `0`).
5. `h x ≠ ⊥ → (∀ t, h x ≠ ↑t) → 0 < a x t z ν` (`mul_pos` of the two `pos_of_notMem`).
Size S.

**E1 (`Q` is a polynomial; evaluation formula).**
```lean
def ρΓ : (Fin n ⊕ Unit) ⊕ τ_Γ → Fin n ⊕ ι :=
  Sum.elim (Sum.elim Sum.inl (fun _ => Sum.inr (Sum.inl ()))) (fun j => Sum.inr (Sum.inr (Sum.inl j)))
def ρ₋ : Fin n ⊕ τ₋ → Fin n ⊕ ι := Sum.map id (fun j => Sum.inr (Sum.inr (Sum.inl j)))
def uX : MvPolynomial (Fin n ⊕ ι) ℝ := X (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))
def vX : MvPolynomial (Fin n ⊕ ι) ℝ := X (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))
def Qpoly : MvPolynomial (Fin n ⊕ ι) ℝ :=
  rename ρΓ 𝒢_Γ.W * rename ρ₋ 𝒢₋.W * uX ^ 2 + (1 - uX * vX) ^ 2
def Ppoly : MvPolynomial (Fin n ⊕ ι) ℝ := X (Sum.inr (Sum.inl ()))

lemma eval_Qpoly (x : Fin n → ℝ) (y : ι → ℝ) :
    evalXY Qpoly x y = N (a x (tc y) (zc y) (νc y)) (uc y) (vc y)
lemma eval_Ppoly : evalXY Ppoly x y = tc y
```
Proof of `eval_Qpoly`: `simp only [evalXY, Qpoly, map_add, map_mul, map_pow, map_sub, map_one, eval_X, eval_rename]` (or the `MvPolynomial.eval_*` names) and the two composition identities `Sum.elim x y ∘ ρΓ = Sum.elim (Sum.elim x fun _ => tc y) (zc y)` and `Sum.elim x y ∘ ρ₋ = Sum.elim x (νc y)`, each by `funext; rintro ((i | ⟨⟩) | j) <;> rfl` resp. `rintro (i | j) <;> rfl`. Also `tc (mk t z ν u v) = t` etc. are `rfl`. Size M (pure bookkeeping; the risk is only `simp` normal forms).

**M1 (case `h x = ↑r`).** Let `y₀ := mk r (𝒢_Γ.sel (Sum.elim x fun _ => r)) 0 1 1`. Then `Q x y₀ = N 0 1 1 = 0` (E2.3, G5.2). `Q x y ≥ 0` for all `y` (E2.1, G5.1). By A1, `Θ = {y | Q x y = 0}`. For `y ∈ Θ`: `N (a …) (uc y) (vc y) = 0 ⇒ a x (tc y) (zc y) (νc y) = 0` (G5.5) `⇒ h x = ↑(tc y) ∨ h x = ⊥` (E2.2); the second is impossible (`EReal.coe_ne_bot r`), so `↑(tc y) = ↑r`, `tc y = r` (`EReal.coe_eq_coe_iff`). By A4 with `c := r`: `valueFun … x = ↑r = h x`. ✔

**M2 (case `h x = ⊤`).** `∀ t, h x ≠ ↑t` (`EReal.coe_ne_top t` symm) and `h x ≠ ⊥` (`top_ne_bot`-type lemma), so `0 < a x t z ν` for all `t z ν` (E2.5), hence `0 < Q x y` for all `y` (G5.3, after `eval_Qpoly`). For `ε > 0`: with `t := 0, z := 0, ν := 0` and `a₀ := a x 0 0 0 ≥ 0`, G5.4 gives `u v` with `N a₀ u v < ε`; `y := mk 0 0 0 u v` has `Q x y = N a₀ u v < ε`. By A2, `Θ = ∅`; by A3, `valueFun … x = ⊤ = h x`. ✔

**M3 (case `h x = ⊥`).** For every `r : ℝ`, `y_r := mk r 0 (𝒢₋.sel x) 1 1` has `Q x y_r = N 0 1 1 = 0` (E2.4, G5.2), so `y_r ∈ Θ` (A1, one-directional part) and `P x y_r = r ≤ r`. By A5, `valueFun … x = ⊥ = h x`. ✔

**MAIN.** `rcases h x` via `EReal.rec` (`induction h x using EReal.rec`, or `cases hx : h x`) into M3 / M1 / M2. Then `exact ⟨ι, inferInstance, Ppoly, Qpoly, fun x => …⟩`.

### 2.5 Reindexing to `Fin m` (task (e))

**R1 (value function is invariant under relabeling lower variables).** For `e : ι ≃ ι'` and `P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ`, define `P' x y' := P x (y' ∘ e)`, `Q'` likewise. Then `valueFun P' Q' Set.univ x = valueFun P Q Set.univ x`. Proof: the map `E : (ι' → ℝ) ≃ (ι → ℝ)`, `E y' := y' ∘ e` (either `Equiv.arrowCongr e.symm (Equiv.refl ℝ)` up to `Equiv.symm_symm`, or built by hand with inverse `y ↦ y ∘ e.symm`), satisfies `y' ∈ argminSet Q' univ x ↔ E y' ∈ argminSet Q univ x` (quantifier over `y''` transported by `E`'s surjectivity). Then `⨅ y' ∈ Θ', ↑(P' x y') = ⨅ y', ⨅ (_ : E y' ∈ Θ), ↑(P x (E y')) = ⨅ y ∈ Θ, ↑(P x y)` by `Equiv.iInf_comp E` (the `to_dual` twin of `Equiv.iSup_comp`). Size M.

**R2 (polynomial relabeling).** `rename (Sum.map id e) Qpoly : MvPolynomial (Fin n ⊕ Fin m) ℝ` with `m := Fintype.card ι`, `e := Fintype.equivFin ι`; `evalXY (rename (Sum.map id e) Qpoly) x y' = evalXY Qpoly x (y' ∘ e)` by `eval_rename` and `Sum.elim x y' ∘ Sum.map id e = Sum.elim x (y' ∘ e)`. Size S.

**thm_2_12_sup** = MAIN + R1 + R2. Alternatively state `valueFun` for arbitrary `ι` and skip `Fin m` entirely (recommended; see §5).

### 2.6 Dependency DAG

```
R2: IsSemialgebraic.exists_basic_family ─┐
G1 ─► G2 ─► G3 ─► G4 ◄───────────────────┘
G5
A1 A2 A3 A4 A5                       (generic, Y = univ; A3'/A4'/A5' pessimistic twins)
G4 ─► 𝒢_Γ, 𝒢₋ ─► E2 (a-lemma) ─┐
E1 (eval_Qpoly, eval_Ppoly) ────┼─► M1 (A1,A4,G5.2,G5.5)  M2 (A2,A3,G5.3,G5.4)  M3 (A1,A5,G5.2) ─► MAIN
R1, R2 ─────────────────────────┴─► thm_2_12_sup (Fin m form)
Prop 2.6 (R2) + thm_2_12_sup ─► P_unbound = SA
PESS: same with 𝒢₊ in place of 𝒢₋, A3',A4',A5' ─► pessimistic theorem (§2.7)
```

### 2.7 Pessimistic counterpart (task (f))

Facts about the optimistic construction (both the paper's and the minimal one):
* Minimizers are **not unique**: `z_ij = ±1/√Q_ij` (two values), coordinates of inactive blocks are free (e.g. all `z` when `W₋ = 0`, all `ν` in Case 1), `(u,v)` ranges over the hyperbola `uv = 1`, and in Case 3 every `t ∈ ℝ` occurs. So the sentence in Section 2.4, "all these constructions involve unique minimizers in the lower level", is false for Theorem 2.12.
* What *is* true: the set of upper-level values `T(x) := {P(x,y) | y ∈ Θ(x)}` is `{h(x)}` if `x ∈ dom h`, `∅` if `h(x) = +∞`, `ℝ` if `h(x) = −∞` (M1–M3 prove exactly this). Hence
  `φ_o(x) = h(x)` everywhere, but `φ_p(x) = sup T(x) = h(x)` on `dom h`, `= −∞` on `{h = +∞}` (sup ∅), `= +∞` on `{h = −∞}`.
  So the optimistic construction has pessimistic value `h` only on `dom h`; "for any specification of the selection process" holds only on `dom h` (any selection `s(x) ∈ Θ(x)` yields `P(x,s(x)) = h(x)` there; on `{h = ±∞}` no selection can produce `±∞`).

**Correct pessimistic statement.** For every extended-real semialgebraic `h` there are `P, Q` with `φ_p = h` on all of `ℝⁿ`. Proof: swap the roles of `D₊` and `D₋`:
`Q_p(x; t, z, ν, u, v) := W_Γ(x,t,z) · W₊(x,ν) · u² + (1 − uv)²`, `P = t`, with `𝒢₊ : ZeroGadget (D₊ h) τ₊`.
Case `h x = r`: `x ∉ D₊`, same as M1, `T(x) = {r}`, `⨆ = r` (A4'). Case `h x = ⊤`: `x ∈ D₊`, every `t` is attained with `Q_p = 0` (as M3), `T(x) = ℝ`, `⨆ = ⊤` (A5'). Case `h x = ⊥`: `x ∉ D₊` and `(x,t) ∉ Γ` for all `t`, so `a > 0`, `Q_p > 0`, `inf = 0` (as M2), `Θ = ∅`, `⨆ = ⊥` (A3'). Hypotheses used: `Γ` and `D₊` semialgebraic. Equivalent route: `φ_p(P,Q) = −φ_o(−P,Q)` (as `sup = −inf(−·)` including the `∅` convention) applied to `−h`; this needs `IsSemialgebraicEReal (−h)`, i.e. closure of semialgebraic sets under the reflection `t ↦ −t` (a `rename`/substitution lemma from R2), so the swap route is cheaper.

**Real-valued corollary (Remark 2.14, "semialgebraic functions as polynomial argmin").** If `h : ℝⁿ → ℝ` is semialgebraic, then with `Q := W_Γ(x,t,z)` alone (no `u, v, ν`) and `P = t`, `Θ(x) = {(t,z) | t = h(x), W_Γ(x,h(x),z) = 0} ≠ ∅` and *every* selection gives `h(x)`; optimistic = pessimistic = any selection. This is the correct form of the Section 2.4 remark for Theorem 2.12.

---

## 3. Errors, gaps and typos in the paper (with fixes)

1. **Def 2.11 vs Thm 2.12 (type of `h`).** `P_boxtype` is defined with `h : ℝⁿ → ℝ` but `φ` and `SA` are extended-real-valued; `P_unbound = SA` only makes sense with `h : ℝⁿ → ℝ ∪ {±∞}` in (2). Fix as in §1.1.
2. **Eq. (7) typo.** `K⁺_ij` and `K⁻_ij` are written with `S_ij`; they must use `S⁺_ij` and `S⁻_ij` (the polynomials of `𝒟⁺_i`, `𝒟⁻_i` in (4)). Also the arguments of `H⁺`, `H⁻` are printed as `(x,ν)` but are `(x,ν⁺)`, `(x,ν⁻)`. With the typo, `H⁺`/`H⁻` do not encode `dom(h)^±` and Cases 2–3 fail.
3. **"WLOG the same index sets `I, J` … add dummy `0 = 0`, `0 < 1`."** Padding `J` with `0 < 1` (constant polynomial `1`) is harmless. Padding `I` (adding basic sets to a union) is **not** harmless: a dummy basic set `{0 = 0 ∧ 0 < 1} = ℝⁿ` would change the union to `ℝⁿ`. One must pad with an *empty* basic set, e.g. `{1 = 0}`. (Padding is not needed at all in the Lean route: each set carries its own index types, G3 takes a `Σ`-type.)
4. **Def 2.1 allows only one equation per basic set**, so an "obvious" basic set `{P₁ = P₂ = 0, Q_j > 0}` must be rewritten with `P₁² + P₂² = 0`; the paper never says so. Harmless (G2 variant handles several equations directly).
5. **Case 1 of the proof** silently uses that minimizers have `Q = 0` (true because `min Q = 0` is attained) and that `Q₁ = 0 ∧ H⁺H⁻ > 0 ⇒ F = 0`; fine, but the sentence "then `t = h(x)` due to our analysis of `F`" also needs `x ∉ dom(h)⁻` (so that `H⁻ > 0`), which the text asserts ("for any `ν⁺,ν⁻`") without saying why. Fix: cite the partition.
6. **Case 2** asserts "`H(x,ν)H⁻(x,ν⁻) > 0` for any `ν, ν⁻`"; this uses `x ∉ dom(h)` and `x ∉ dom(h)⁻`, again not spelled out. Correct.
7. **Section 2.4, first bullet ("unique minimizers … any selection").** False for Theorem 2.12, see §2.7: minimizers are non-unique, and the pessimistic value of the paper's construction is `+∞` on `dom(h)⁻`. Fix: the pessimistic theorem holds with the swapped construction `Q_p` of §2.7; "any selection" is correct only on `dom h` (and everywhere for real-valued `h`).
8. **Redundant hypothesis.** Def 2.2 lists `dom(f)` among the three sets; it is the complement of `dom(f)⁺ ∪ dom(f)⁻`, hence automatically semialgebraic (under either definition (A) or (B)). More importantly, the construction (both the paper's and the minimal one) never needs `dom(h)` semialgebraic; the minimal one does not even need `dom(h)⁺`. The theorem holds under the weaker hypothesis "`graph(h|dom h)` and `{h = −∞}` semialgebraic" (then `{h = +∞}` is semialgebraic a posteriori by Tarski–Seidenberg via Prop 2.6, so this is not in conflict with `P_unbound ⊆ SA`).
9. **Eq. (6).** "`z*_ij = 0` otherwise" is a minimizer but not the only one when `Q_ij = 0` (every `z` is); harmless for the optimistic proof, relevant for item 7.
10. **Variable count.** Table 1 gives `|y| = 3 + 4|I||J|` *after* padding all four descriptions to common `I, J`, which can be far larger than the natural `3 + Σ(#strict inequalities)`; with the minimal construction `m = 3 + |τ_Γ| + |τ₋|`.
11. **Statement "lower-level problem is unconstrained" vs `P_unbound`.** `𝒴 = ℝᵐ` is an unbounded box, so `⊇` holds for `P_unbound`; fine, but note `P_unbound ⊆ SA` must be proved for *every* unbounded box (R2/Prop 2.6), not just `ℝᵐ`.

---

## 4. Mathlib inventory

All paths relative to `<SCRATCH>/mathlib/mathlib4/`. "via `to_dual`"/"via `to_additive`" means the name is generated by an attribute on the listed declaration and does **not** appear textually in the source (grep for the generated name finds nothing; this is a pitfall for the auditor).

| Need | Declaration | File:line | Note |
|---|---|---|---|
| MvPolynomial evaluation of `+ * ^ − 1 X C` | `MvPolynomial.eval_add`, `eval_mul`, `eval_pow`, `eval_X`, `eval_C` | `Mathlib/Algebra/MvPolynomial/Eval.lean:286,289,292,275,271` | `eval` is a `RingHom`, so `map_add`/`map_mul`/`map_pow`/`map_sub`/`map_one` also work |
| `eval` of subtraction | `MvPolynomial.eval_sub` | `Mathlib/Algebra/MvPolynomial/CommRing.lean:163` | needs `CommRing` (ℝ ok) |
| `eval` of finite sums / products | `MvPolynomial.eval_sum`, `MvPolynomial.eval_prod` | `Mathlib/Algebra/MvPolynomial/Eval.lean:295,299` | over a `Finset`; use `Finset.univ` |
| variable relabeling | `MvPolynomial.rename`, `rename_X`, `rename_rename`, `eval_rename` | `Mathlib/Algebra/MvPolynomial/Rename.lean:62,80,244` | `eval g (rename k p) = eval (g ∘ k) p` |
| product of nonnegatives / positives | `Finset.prod_nonneg`, `Finset.prod_pos` | `Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean:34,160` | |
| product zero iff a factor zero | `Finset.prod_eq_zero_iff`, `Finset.prod_ne_zero_iff`, `Finset.prod_eq_zero` | `Mathlib/Algebra/BigOperators/GroupWithZero/Finset.lean:57,63,33` | needs `NoZeroDivisors`, `Nontrivial` (ℝ ok) |
| sum of nonnegatives | `Finset.sum_nonneg` | via `to_additive` on `Finset.one_le_prod`, `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:161-162` | |
| sum zero iff all zero (nonneg terms) | `Finset.sum_eq_zero_iff_of_nonneg` | via `to_additive` on `Finset.prod_eq_one_iff_of_one_le`, same file `:239-240` | |
| a term bounds a nonneg sum | `Finset.single_le_sum` | via `to_additive` on `Finset.single_le_prod`, same file `:275-276` | |
| sum over a `Sum` type | `Fintype.sum_sum_type` | via `to_additive` on `Fintype.prod_sum_type`, `Mathlib/Data/Fintype/BigOperators.lean:267-268` | only if one prefers `Sum`-indexed blocks |
| product over a `Sigma` type | `Fintype.prod_sigma` | `Mathlib/Data/Fintype/BigOperators.lean:151` | not needed by G3 as written (product over `ι` only) |
| `0 ≤ a²` | `sq_nonneg` | `Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean:608` | |
| `a² = 0 ↔ a = 0` | `sq_eq_zero_iff`, `pow_eq_zero_iff` | `Mathlib/Algebra/GroupWithZero/Basic.lean:262,253` | |
| `0 < a²` for `a ≠ 0` | `sq_pos_of_ne_zero` (alias of `sq_pos_iff`) | `Mathlib/Algebra/Order/Ring/Basic.lean:223-225` | |
| `1 ≤ a² ↔ 1 ≤ a` (a ≥ 0) | `one_le_sq_iff₀` | `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:749` | or `nlinarith` |
| `a ≤ 0 → 0 ≤ b → a*b ≤ 0` | `mul_nonpos_of_nonpos_of_nonneg` | `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:79` | |
| `mul_pos`, `mul_nonneg` | aliases of `Left.mul_pos`, `Left.mul_nonneg` | `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:43-46,70` | |
| `add_nonneg`, `add_pos_of_pos_of_nonneg`, `add_pos_of_nonneg_of_pos` | via `to_additive` | `Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:746,752,749` | |
| `a + b = 0 ↔ a = 0 ∧ b = 0` (a,b ≥ 0) | `add_eq_zero_iff_of_nonneg` | via `to_additive` on `mul_eq_one_iff_of_one_le`, `Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:799-800` | |
| `a * b = 0 ↔ …`, `a*b ≠ 0 → a ≠ 0` | `mul_eq_zero`, `left_ne_zero_of_mul`, `mul_ne_zero` | `Mathlib/Algebra/GroupWithZero/Defs.lean:293`; `…/Basic.lean:54,84` | |
| `a - b = 0 ↔ a = b` | `sub_eq_zero` | via `to_additive` on `div_eq_one`, `Mathlib/Algebra/Group/Basic.lean:754-755` | |
| `a * a⁻¹ = 1` | `mul_inv_cancel₀` | `Mathlib/Algebra/GroupWithZero/Defs.lean:228` | |
| `0 ≤ a⁻¹ ↔ 0 ≤ a`, `0 < a⁻¹ ↔ 0 < a` | `inv_nonneg`, `inv_pos` | `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:862,853` | |
| square roots | `Real.sqrt` (`√`), `Real.sq_sqrt`, `Real.sqrt_pos`, `Real.sqrt_nonneg`, `Real.sqrt_inv` | `Mathlib/Analysis/Real/Sqrt.lean:177,285,143,373` | `Real.sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x` |
| small positive multiple | `exists_pos_mul_lt` | `Mathlib/Algebra/Order/Field/Basic.lean:290` | `0 < a → ∀ b, ∃ c, 0 < c ∧ b * c < a` |
| `EReal` structure | `EReal := WithBot (WithTop ℝ)`, `CompleteLinearOrder` by `deriving` | `Mathlib/Data/EReal/Basic.lean:33-38` | gives `iInf`, `⊤`, `⊥` |
| case split on `EReal` | `EReal.rec` (`induction_eliminator`, `cases_eliminator`) | `Mathlib/Data/EReal/Basic.lean:113` | |
| coercion order facts | `EReal.coe_le_coe_iff`, `EReal.coe_lt_coe_iff`, `EReal.coe_eq_coe_iff`, `EReal.coe_strictMono`, `EReal.coe_injective` | `Mathlib/Data/EReal/Basic.lean:55,61,67,48,51` | all `protected` (write `EReal.`) |
| `↑r ≠ ⊤`, `↑r ≠ ⊥`, `⊥ < ↑r`, `↑r < ⊤` | `EReal.coe_ne_top`, `EReal.coe_ne_bot`, `EReal.bot_lt_coe`, `EReal.coe_lt_top` | `Mathlib/Data/EReal/Basic.lean:270,258,254,266` | |
| `x = ⊥ ↔ ∀ r:ℝ, x < ↑r`; `x = ⊤ ↔ ∀ r, ↑r < x` | `EReal.eq_bot_iff_forall_lt`, `EReal.eq_top_iff_forall_lt` | `Mathlib/Data/EReal/Basic.lean:438,430` | A5 / A5' |
| `EReal.coe_sub`, `coe_add`, `coe_one`, `coe_zero` | | `Mathlib/Data/EReal/Operations.lean:222`, `Basic.lean:310,106,103` | norm_cast |
| `⨅ x ∈ ∅, f x = ⊤` | `iInf_emptyset` | via `to_dual` on `iSup_emptyset`, `Mathlib/Order/CompleteLattice/Basic.lean:583-584` | A3; `iSup_emptyset` for A3' |
| `iInf ≤ f i`, `(∀ i, a ≤ f i) → a ≤ iInf` | `iInf_le`, `le_iInf` | via `to_dual` on `le_iSup`, `iSup_le`, `Mathlib/Order/CompleteLattice/Basic.lean:210-211,234-235` | |
| binary-index versions | `iInf₂_le`, `le_iInf₂` | via `to_dual` on `le_iSup₂`, `iSup₂_le`, same file `:225-226,238-239` | for `⨅ y ∈ A` |
| `le_iInf_iff`, `iInf_lt_iff` | | via `to_dual`, `Mathlib/Order/CompleteLattice/Basic.lean:279-280`, `…/Defs.lean:318-319` | |
| `iInf f = ⊥ ↔ ∀ b > ⊥, ∃ i, f i < b` | `iInf_eq_bot` | via `to_dual` on `iSup_eq_top`, `Mathlib/Order/CompleteLattice/Defs.lean:334-335` | alternative for A5 |
| `iInf` characterisation | `iInf_eq_of_forall_ge_of_forall_gt_exists_lt` | via `to_dual` on `iSup_eq_of_forall_le_of_forall_lt_exists_gt`, `Mathlib/Order/CompleteLattice/Basic.lean:373-378` | alternative for A4/A5 |
| reindex an `iInf` by an `Equiv` | `Equiv.iInf_comp` | via `to_dual` on `Equiv.iSup_comp`, `Mathlib/Order/CompleteLattice/Basic.lean:166-167` | R1 |
| `iInf_congr`, `iInf_subtype'` | | via `to_dual`, same file `:140-141, 415-416` | |
| `Fintype.equivFin` | `noncomputable def equivFin (α) [Fintype α] : α ≃ Fin (card α)` | `Mathlib/Data/Fintype/EquivFin.lean:80` (namespace `Fintype`) | R2 |
| function-space `Equiv` | `Equiv.arrowCongr`, `Equiv.piCongrLeft` | `Mathlib/Logic/Equiv/Defs.lean:453`, `Mathlib/Logic/Equiv/Basic.lean:846` | R1 (or hand-built) |
| `Equiv.sumCongr`, `Equiv.sumAssoc`, `finSumFinEquiv` | | `Mathlib/Logic/Equiv/Sum.lean:60,147`, `Mathlib/Logic/Equiv/Fin/Basic.lean:224` | only if `Fin`-arithmetic indexing is chosen (not recommended) |
| dependent `Function.update` | `Function.update_self` | `Mathlib/Logic/Function/Basic.lean:644` | only for the `Pi`-indexed union variant (not needed with selectors) |
| `Set.mem_iUnion`, `Set.mem_univ`, `Set.eq_empty_iff_forall_notMem` | | `Mathlib/Order/SetNotation.lean:224`, `Mathlib/Data/Set/Operations.lean:105`, `Mathlib/Data/Set/Basic.lean:460` | |
| `Sum.elim_inl`, `Sum.elim_inr`, `Sum.elim_comp_inl/inr`, `Sum.elim_comp_map` | Lean core (`Init`), not in the Mathlib tree; toolchain not installed, so unverified | — | every use is closed by `funext; rintro (_|_) <;> rfl` |
| `lt_of_le_of_ne`, `le_min`, `lt_min`, `min_le_left/right`, `ne_of_lt` | | `Mathlib/Order/Defs/PartialOrder.lean:201,100`, `Mathlib/Order/Defs/LinearOrder.lean:168,204,162,165` | |
| `zero_lt_one`, `zero_lt_two` | | `Mathlib/Algebra/Order/ZeroLEOne.lean:52`, `Mathlib/Algebra/Order/Monoid/NatCast.lean:63` | |
| Semialgebraic sets, Tarski–Seidenberg, Prop 2.6 | **NOT IN MATHLIB** (grep `semialgebraic`/`semi-algebraic`: no hits) | — | definitions by R2; projection stability assumed; this report does not need it |
| `Set.mem_setOf_eq` | not located by my grep (likely `Mathlib/Data/Set/Defs.lean`) | — | replaceable by `Iff.rfl`/`show` |

---

## 5. Lean encoding decisions and pitfalls

1. **Generic lower index type.** Define `argminSet`/`valueFun` for an arbitrary `ι : Type*` (lower variable `ι → ℝ`); `Fin m` is the special case. The construction naturally produces `ι = Unit ⊕ (τ_Γ ⊕ (τ₋ ⊕ (Unit ⊕ Unit)))`; converting to `Fin m` needs R1/R2 (one-off, M). Do **not** use `Fin (1 + k₁ + k₂ + 2)` with `Fin.natAdd`/`castAdd`: casts everywhere.
2. **Existentials over types.** `∃ (ι : Type) (_ : Fintype ι), …` — the instance is an anonymous existential witness; consumers do `obtain ⟨ι, _, P, Q, hPQ⟩ := …; letI : Fintype ι := ‹_›` (or state with `Fin m` and reindex at the end). Keep universes at `Type` (`Fin n ⊕ ι` must live in `Type` for `MvPolynomial`; everything is `Type 0` anyway).
3. **Gadget interface.** Use the `ZeroGadget` *structure with selector* (§2.2) rather than a `∃ ξ` statement: the selector gives the union witness in G3 and the minimizers in M1/M3 with no `Classical.choose`, no `dite` and no `Sigma` casts. The selector may be defined everywhere (G2's `√(q⁻¹)` is defined for all `q`, `Real.sqrt` of a negative is `0`).
4. **`Σ`-indexed blocks** (G3): the only dependent-type content is `fun j => ξ ⟨i, j⟩`; products are over `ι`, not over `Σ`. If R2's normal form uses uniform `κ`, replace by `ι × κ` and `fun j => ξ (i, j)`.
5. **Polynomial-ness is by construction**: `Qpoly` is a term of `MvPolynomial (Fin n ⊕ ι) ℝ`; the only lemma needed is the evaluation formula `eval_Qpoly` (E1), proved by `simp` with `eval_rename` and two `Sum.elim ∘ …` identities. Never prove "the function is polynomial" after the fact.
6. **`EReal` pitfalls.** `valueFun` is a `⨅ y ∈ A, (↑(P x y) : EReal)`, i.e. `⨅ y, ⨅ (_ : y ∈ A), …`; use `iInf₂_le`/`le_iInf₂` (names generated by `to_dual`; grep for `le_iSup₂`/`iSup₂_le`). `iInf_emptyset` needs the set to be literally `∅`: `rw` the argmin equality first. Never do arithmetic in `EReal` here; all comparisons go through `EReal.coe_le_coe_iff`/`coe_lt_coe_iff`/`coe_eq_coe_iff` and the two `eq_bot_iff_forall_lt`/`eq_top_iff_forall_lt` characterisations. Case split on `h x` with `EReal.rec` (`cases hx : h x`), *not* with `by_cases h x = ⊤`.
7. **Name generation by attributes.** Many lemmas used (`iInf_le`, `le_iInf`, `iInf₂_le`, `le_iInf₂`, `iInf_emptyset`, `iInf_eq_bot`, `Equiv.iInf_comp`, `add_nonneg`, `add_pos_of_pos_of_nonneg`, `add_eq_zero_iff_of_nonneg`, `Finset.sum_nonneg`, `Finset.sum_eq_zero_iff_of_nonneg`, `Finset.single_le_sum`, `sub_eq_zero`) exist only through `to_dual`/`to_additive`; the blueprint should warn that grepping for them fails and give the source declaration (§4).
8. **`Finset.prod_eq_zero_iff`** needs `[CommMonoidWithZero] [NoZeroDivisors] [Nontrivial]` — fine for ℝ; `Finset.prod_pos` needs `PosMulStrictMono`; both instances exist for ℝ.
9. **Decidability.** Products/sums are over `Finset.univ` of a `Fintype`; no `DecidableEq` is needed anywhere in the minimal route (G3 with selectors avoids `Function.update`/`dite`). If `Function.update` is used instead, add `[DecidableEq ι]` or `classical`.
10. **`argminSet` with `Y = Set.univ`.** Provide a `simp` lemma `mem_argminSet_univ : y ∈ argminSet Q Set.univ x ↔ ∀ y', Q x y ≤ Q x y'` once; A1/A2 become trivial.
11. **Graph encoding.** `Γ h ⊆ (Fin n ⊕ Unit → ℝ)`; the point `(x,t)` is `Sum.elim x (fun _ => t)`; `(Sum.elim x f) ∘ Sum.inl = x` and `(Sum.elim x f) (Sum.inr ()) = f ()` are `rfl`. If R2 insists on `Fin (n+1)`, add `IsSemialgebraic.comp_equiv` (preimage under `MvPolynomial.rename` of an `Equiv`) and use `finSumFinEquiv`/`Fin.snoc`; cost M, pure bookkeeping.
12. **Universe of `IsSemialgebraic`.** Should be stated for `Set (σ → ℝ)` with `σ` an arbitrary `Fintype` (used here with `σ = Fin n` and `σ = Fin n ⊕ Unit`).
13. **`Real.sqrt` notation** is `√` (prefix); lemma statements use `√x ^ 2 = x`, not `Real.sqrt x ^ 2`.

---

## 6. Alternatives considered and why rejected

| Alternative | Verdict |
|---|---|
| Paper's `Q` verbatim (`H⁺H⁻F + HH⁻u² + (1−uv)²`, 7 blocks of variables, 4 gadgets) | Correct (V1–V8) but strictly more work: two extra gadgets (`H`, `H⁺`), two extra evaluation identities, and extra hypotheses. Keep only as a remark in the blueprint ("faithful version"). |
| Drop `H` but keep `H⁺`: `Q = H⁻ F (H⁺ + u²) + (1−uv)²` | Correct (same proof as §2.4 with `a := W_Γ W₋`, replacing `u²` by `(W₊ + u²)`); strictly dominated by the minimal `Q`. |
| Minimal `Q = W_Γ W₋ u² + (1−uv)²` | **Chosen.** Two gadgets, one escape term, hypotheses only on `Γ` and `D₋`. |
| Single gadget for `Γ ∪ (D₋ × ℝ)` instead of the product `W_Γ·W₋` | Identical content (the product *is* the union gadget of G3 for two blocks); building `D₋ × ℝ` as a semialgebraic set of `ℝⁿ⁺¹` would need an extra cylinder lemma. Rejected. |
| Non-attainment via a single variable | Impossible: a univariate real polynomial bounded below attains its infimum (even degree or constant); two variables `(u,v)` are necessary. `(1−uv)² + a u²` is the cheapest. |
| Definition (B) (Boolean algebra) consumed directly | No gadget for complements (`{∀ ξ, W > 0}` is not a zero locus); must convert to (A) first — that is R2's (A)⇔(B) lemma anyway. |
| Binary-union gadget + induction on `Fin k` | Avoids `Σ` types but needs a `⋃ over Fin (k+1)` decomposition lemma and nested `Sum` types; the `Σ`/selector version is one lemma with no casts. Rejected. |
| `Pi`-indexed lower variables `(i : ι) → τ i → ℝ` with `Function.update` | Needs `DecidableEq` and an `Equiv` to `(Σ i, τ i) → ℝ` for the final statement; selectors make it unnecessary. |
| Witness `z = 1/√q` via `Real.sqrt (1/q)` or `(√q)⁻¹` | Equivalent; `√(q⁻¹)` with `Real.sq_sqrt` + `mul_inv_cancel₀` is the shortest. |
| Gadget `(q z² − 1)²` or `(1 − q z)² + (z − w²)²` | Same cost as `(1 − q z²)²`; no gain. |
| Pessimistic theorem via `−h` and `φ_p = −φ_o(−P,·)` | Needs closure of semialgebraicity under `t ↦ −t` (substitution lemma); the swapped construction (§2.7) reuses everything with zero new lemmas. |

---

## 7. Effort / risk per lemma

| Lemma | Size | Assume or prove | Risk |
|---|---|---|---|
| R2 interface `IsSemialgebraic.exists_basic_family` | S (if def (A)) / M (if def (B)) | prove (R2) | depends on R2's definition |
| G1 scalar gadget | S | prove | none |
| G2 basic gadget (+ eval identity) | M | prove | `simp` normal form of `eval_rename` |
| G3 union gadget (`Σ`) | M | prove | `rename`/`Sum.map` bookkeeping |
| G4 semialgebraic ⇒ gadget | S | prove | none |
| G5 escape gadget | S | prove | none |
| A1–A5 (+ A3'–A5') | S each | prove | `iInf₂` lemma names (`to_dual`) |
| E1 eval_Qpoly / eval_Ppoly | M | prove | `simp` bookkeeping only |
| E2 a-lemma | S | prove | none |
| M1, M2, M3 | M, M, S | prove | none mathematically |
| MAIN (`ι` form) | S | prove | none |
| R1 reindexing of `valueFun` | M | prove | `Equiv.iInf_comp` form of the goal; `arrowCongr` direction |
| R2 polynomial reindexing | S | prove | none |
| thm_2_12_sup (`Fin m`) | S | prove | none |
| Pessimistic theorem | S (given the above) | prove | none |
| `P_unbound ⊆ SA` (Prop 2.6) | XL | **assume** (Tarski–Seidenberg) | R2 |
Total for the `⊇` direction: roughly 15 lemmas, ~500–700 lines of Lean, no real-algebraic-geometry input beyond R2's normal form. Nothing needs to be assumed.

---

## 8. Open questions for the auditor

1. Which definition of `IsSemialgebraic` does R2 fix, and in which ambient index type (`Fin n` only, or any `Fintype σ`)? This report needs `σ = Fin n ⊕ Unit` for graphs (or a `Fin (n+1)` ↔ `Fin n ⊕ Unit` transfer lemma).
2. Should the blueprint state Theorem 2.12 with the paper's hypotheses (`IsSemialgebraicEReal h`, four sets) or with the strengthened ones (only `Γ h` and `D₋ h` semialgebraic)? I recommend the strengthened statement plus a one-line corollary for the paper's form.
3. Should `valueFun` be defined for a general lower index type `ι` (recommended) or fixed to `Fin m` (then R1/R2 are mandatory)?
4. Is a "faithful" formalisation of the paper's `Q` (with `H`, `H⁺`) wanted in addition to the minimal one? It costs two more gadgets and adds nothing mathematically; V1–V8 document its correctness.
5. Should the pessimistic counterpart (§2.7) be in the blueprint? It is nearly free once the optimistic one is done, and it corrects the paper's Section 2.4 claim.
6. `Sum.elim_*` simp lemmas are in Lean core and could not be grepped (no toolchain); all uses are `rfl`-closable, so no risk, but the auditor may want to confirm the names.
7. Variable-count statement (Remark 2.13): do we want an explicit bound `m = 3 + |τ_Γ| + |τ₋|` and a degree bound `deg Q ≤ 2 + 2·max(deg of inputs)·(#blocks)` in the blueprint? Easy to add as a remark, no formal content needed.
