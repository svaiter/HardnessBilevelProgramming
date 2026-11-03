# AUDIT of R5 — Convex lower level (Lemma 2.19, Thm 2.18, Thm 2.20, §2.3.1 remark, §2.4 pessimistic, Prop C.1 usage)

Auditor: Opus (adversarial, independent). Sources checked: `paper/paper_html.txt` lines 644–1058 and 1295–1320,
`paper/paper.txt` (PDF text, pp. 14–17, 28), Mathlib checkout `mathlib/mathlib4/Mathlib` (every citation grepped).

---

## A. Summary verdict

The report is **mathematically reliable**. I re-derived every construction from scratch: the simplified Lemma 2.19 gadget,
the separable-argmin lemma F2, the Prop-C.1-free proof of Thm 2.18, the normalisation `g = 1/4 + Σ P_i²`, the
`D_i = {f ≤ P_i}` route, and the lower-bound-plus-explicit-minimiser proof of the Thm 2.20 gadget. All are correct, and
none of the proposed simplifications is wrong. Corrections are needed on these points. (i) Three Mathlib facts reported as
missing do exist: `Finset.indicator_biUnion`, `lowerSemiContinuous_neg_iff`, and `MvPolynomial.funext_set`. The last one
makes the §2.3.1 remark much cheaper. (ii) `stdSimplex` is deprecated in this checkout. (iii) Two of the 17 claimed paper
errors are refuted (#4 and #17), and #1 and #9 are overstated. (iv) The report missed a real gap in the paper's proof of
Thm 2.18: it uses Lemma 2.19 only through its *statement*, and the statement alone is not enough. (v) The claim that
"A2 cannot be dodged" was only heuristic; I give a rigorous version for the gadget route. Recommended change to the route:
index the Thm 2.20 core by a single flat finite family of (closed basic set, polynomial) pairs. This removes all the
`J`/`K` padding.

---

## B. Lemma-by-lemma verdicts

| Id | Verdict | Note |
|---|---|---|
| F0 `valueFun_eq_of_isLeast` | CONFIRMED | `le_antisymm (iInf₂_le_of_le y₀ hy₀ (le_of_eq _)) (le_iInf₂ fun y hy => EReal.coe_le_coe_iff.2 (h.2 ⟨y,hy,rfl⟩))`. `iInf₂_le`, `le_iInf₂` are `to_dual` of `le_iSup₂` / `iSup₂_le` (Order/CompleteLattice/Basic.lean:225–239). See C7 for the converse. |
| F1 constant on nonempty argmin | CONFIRMED | `biInf_const` (to_dual of `biSup_const`, CompleteLattice/Basic.lean:425, needs `s.Nonempty`). |
| F2 separable argmin = product of argmins | CONFIRMED | Both inclusions re-proved (C2). No nonemptiness hypothesis needed. Cleaner Lean route: `Finset.sum_lt_sum` (C2). |
| F3 one-variable argmins | CONFIRMED | All three case splits checked, including `c<0` on `Ici 0`: `1−cu ≥ 1`, with equality iff `u=0`. |
| F4 convexity toolkit | CONFIRMED | Route B identity: `a u²+b v²−(au+bv)² = ab(u−v)²` when `a+b=1`. Checked. |
| F5 transport | CONFIRMED (not checked in detail) | Standard. I endorse quantifying over `∃ (ι : Type) [Fintype ι]` (G1). |
| F6 shift by `g(x)` | CONFIRMED | The EReal version also holds, including `⊤`/`⊥`, since `⊤+c=⊤` and `⊥+c=⊥` for real `c`. It is not needed. |
| L1 simplified Lemma 2.19 | CONFIRMED | Full re-derivation in C1. |
| L2 Thm 2.18 ⊆ (no C.1) | CONFIRMED | C3. It proves a strictly stronger statement (arbitrary finite families). |
| L3 eq. (13) | CONFIRMED | Filter proof checked. Covering is needed for `I(x) ≠ ∅`. Disjointness is needed for `f = P_i` on `S_i`. |
| L4 normalisation `g = 1/4+ΣP_i²` | CONFIRMED | `P_i − g ≤ P_i − P_i² − 1/4 = −(P_i−1/2)² ≤ 0`. |
| L5 z-gadget facts Z1–Z3 | CONFIRMED | |
| L6 simplex facts | CONFIRMED, but avoid `stdSimplex` (deprecated) | Use the explicit set `{s | (∀ c, 0 ≤ s c) ∧ ∑ c, s c = 1}`. |
| L7 Thm 2.20 core | CONFIRMED | Lower bound and attainment re-derived (C4d). Recommend the flat-index restatement (F). |
| L8 Thm 2.20 as stated (+ D_i route) | CONFIRMED with a sharpening | The `D_i` route is correct and drops A1 and L3. "A2 unavoidable" is now proved for the gadget route (C5). |
| L9 pessimistic via negation | CONFIRMED | EReal identity holds in all cases. The Mathlib path exists (C6). |
| L10 ‖·‖₂ ∈ C_cc \ PP, n ≥ 2 | CONFIRMED, much cheaper than stated | `MvPolynomial.funext_set` replaces the analytic identity theorem. A univariate restriction replaces coefficient comparison (C8). |

---

## C. Corrections and verifications (numbered)

### C1. Simplified Lemma 2.19 — verified in full
Data: `S = {P = 0 ∧ ∀ j∈J, Q_j > 0}`, with `J` finite and possibly empty. Lower variable `(t,u) ∈ ℝ × [0,∞)^J`.
`G(x,t,u) = (1 − tP(x))² + Σ_j (1 − Q_j(x)u_j)²` and `F(x,t,u) = (1 − tP(x)) ∏_j Q_j(x)u_j`.
Fix `x` and write `p = P(x)`, `q_j = Q_j(x)`. `G` is a sum of one-variable functions, so by F2 the argmin is the product of
the coordinate argmins:
* `t` over ℝ, function `(1−tp)²`. If `p ≠ 0`, the minimum value is 0, reached only at `t = 1/p`, so `1−tp = 0`. If `p = 0`, the function is ≡ 1, the argmin is ℝ, and `1−tp = 1` for every `t`.
* `u_j` over `[0,∞)`, function `(1−q_j u)²`.
  * `q_j > 0`: the minimum value is 0, reached only at `u = 1/q_j ≥ 0`, so `q_j u_j = 1`.
  * `q_j = 0`: the function is ≡ 1, the argmin is `[0,∞)`, and `q_j u_j = 0` for every `u_j`.
  * `q_j < 0`: for `u ≥ 0`, `1−q_j u ≥ 1 > 0`, so `(1−q_j u)² ≥ 1`, with equality iff `q_j u = 0` iff `u = 0`. The argmin is `{0}` and `q_j u_j = 0`.
* Every factor is nonempty, so the argmin is nonempty. A witness is `t = if p=0 then 0 else 1/p`, `u_j = if q_j>0 then 1/q_j else 0`.
* On the whole argmin, `F = [p=0]·∏_j [q_j>0] = 1_S(x)`. For `J = ∅` the empty product is 1 and `S = {P=0}`, which is consistent. So `F(x,·)` is **constant** on `Θ(x)`, and the optimistic value, the pessimistic value and every selection equal `1_S`.
* Convexity: `G(x,·)` is a sum of squares of affine functions of `(t,u)`, so it is `ConvexOn ℝ univ`. The box `Set.pi univ (Sum.elim (fun _ => univ) (fun _ => Ici 0))` is convex by `convex_pi` with `convex_univ` / `convex_Ici`, so `ConvexOn.subset` gives the version on the box. No coordinate causes trouble.
* Box type: the paper's definition (line 172) says "unbounded if ∃ i, a_i = −∞ or b_i = +∞". The `t` coordinate has `a = −∞`, so the box is unbounded even when `J = ∅`. Each `u_j` coordinate `[0,+∞]` would also qualify. Mixed boxes are allowed; the paper's own gadget `[0,1]^J × ℝ^J × ℝ` is mixed.

Verdict: correct. It is strictly simpler than the paper's version: `|J|+1` variables instead of `2|J|+1`, and no linear term.

### C2. F2 (separable argmin) — both inclusions
Setting: `Y = Set.pi univ Y_c` and `Φ(y) = Σ_c g_c(y_c)`, with `c` ranging over a Fintype.
* `⊇`: let `y ∈ Y` with each `y_c` a minimiser of `g_c` over `Y_c`. For any `y' ∈ Y`, `g_c(y_c) ≤ g_c(y'_c)` for every `c`, so `Φ(y) ≤ Φ(y')` (`Finset.sum_le_sum`).
* `⊆`: let `y ∈ Y` minimise `Φ`, and fix `k`. We have `y_k ∈ Y_k` because `y ∈ Y`. Suppose some `v ∈ Y_k` has `g_k(v) < g_k(y_k)`. Put `y' = Function.update y k v`; then `y' ∈ Y` by `mem_univ_pi`, with `update_self` and `update_of_ne`. Termwise `g_c(y'_c) ≤ g_c(y_c)`, with equality for `c ≠ k` and strict inequality at `k`. So `Φ(y') < Φ(y)` by **`Finset.sum_lt_sum`** (to_additive of `Finset.prod_lt_prod`, Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:579). This contradicts minimality.
* Empty factor: if some `Y_c = ∅` then `Y = ∅`. The left side is empty, and the right side is empty because its `c` factor is empty. The proof needs no case split.

Lean note: the report's `Finset.sum_update_of_mem` route (Piecewise.lean:247, statement `∑ x∈s, update f i b x = b + ∑ x∈s\{i}, f x`) also needs **`Function.apply_update`** (Logic/Function/Basic.lean:765). That lemma turns `fun c => g c (update y k v c)` into `update (fun c => g c (y c)) k (g k v)`. The `sum_lt_sum` route needs neither lemma nor any sum splitting, so it is the one to use. The `Prod` version, `argmin (A∘fst + B∘snd) (Y₁ ×ˢ Y₂) = argmin A Y₁ ×ˢ argmin B Y₂`, has a non-strict proof (compare `(a,b)` with `(a',b)`) and is CONFIRMED.

### C3. Theorem 2.18 without Prop C.1
* Identity: for any finite family `(T_j)`, `1_{⋃_j T_j} = 1 − ∏_j (1 − 1_{T_j})`. If `x ∈ T_{j₀}`, that factor is 0, so the right side is 1. Otherwise every factor is 1 and the right side is 0. For an empty family both sides are 0. CONFIRMED; disjointness is not used.
* `P(x,y) = Σ_i P_i(x)·(1 − ∏_j (1 − F_ij(x,y_ij)))` is a polynomial, built from `rename inl`, `X`, `+`, `−`, `*`, `∏`, `∑`.
* `Q = Σ_ij G_ij(x,y_ij)`. Each `G_ij` is a sum of squares of affine maps of the scalar coordinates of block `ij`, so `Q(x,·)` is a sum of squares of affine maps of `y`. It is convex on `univ`, and hence on the product box.
* Argmin: `Q` is coordinate-separable, so scalar F2 applies once. The argmin is the product of the C1 coordinate argmins, which is nonempty. On it, `F_ij(x,y_ij) = 1_{T_ij}(x)` by C1 applied blockwise; this needs the *constancy* from C1, not only the value. So `P = Σ_i P_i 1_{S_i} = f` on the whole argmin. Optimistic = pessimistic = every selection = `f`.
* Disjointness of the `S_i` is never used, and neither is covering. The construction represents `x ↦ Σ_i 1_{S_i}(x) P_i(x)` for **any** finite family of semialgebraic `S_i` and polynomials `P_i`. **The blueprint should state this stronger lemma** (`indicatorSum_mem_C_unbound`) and derive `PP ⊆ C_unbound` from it as a corollary. The theorem as stated in the paper is recovered exactly.
* Unboundedness: with the paper's partition, `ℝ^n ≠ ∅`, so some `S_i` is nonempty. Its presentation then has a basic piece, and that piece contributes a `t`-coordinate. For the stronger lemma, where the family may be empty or have only empty presentations, the dummy coordinate (`univ`, `Q`-term 0) of report §5.5 is required. CONFIRMED.

### C4. Theorem 2.20 core
(a) **Eq. (13)** (L3): re-derived.
* `i₀` with `x ∈ S_{i₀}` exists by covering. Then `i₀ ∈ I(x)` and `f(x) = P_{i₀}(x)`.
* For `i ∈ I(x)`, assume `P_i(x) < m < f(x)`. Then
  * lsc gives `∀ᶠ x', m < f x'`;
  * continuity gives `∀ᶠ x', P_i x' < m`;
  * closure gives `∃ᶠ x', x' ∈ S_i`, where `f x' = P_i x'`.
  Combining these gives a contradiction.
* Both covering (for `I(x) ≠ ∅`) and `f = P_i` on `S_i` (from disjointness, or from the "equivalently" form of Def 2.17) are used. CONFIRMED.

(b) **Normalisation**:
* `P_i − g = P_i − 1/4 − Σ_k P_k² ≤ P_i − 1/4 − P_i² = −(P_i − 1/2)² ≤ 0`. CONFIRMED.
* `f − g` is lsc: `f` is lsc, `−g` is continuous, so the sum is lsc by `LowerSemicontinuous.add` (Semicontinuity/Basic.lean:540). The section variables are `[AddCommMonoid γ] [LinearOrder γ] [IsOrderedAddMonoid γ] [TopologicalSpace γ] [OrderTopology γ]` plus `[ContinuousAdd γ]` (line 513). The report listed only three of these, but all of them hold for ℝ.
* `f − g` is piecewise polynomial with the same `S_i` and pieces `P_i − g`.
* The hypothesis `IsLeast {P_i(x) | x ∈ C_i} (f x)` is invariant under subtracting `g(x)` from every value.
* Adding `g(x)` back to the upper objective leaves `Q` and `Θ` unchanged and shifts `IsLeast` by `g(x)`, using `add_le_add_right`. The EReal version also holds, as noted in table B.

(c) **`D_i` route**:
* `D_i := {f ≤ P_i}` equals `(f − P_i)⁻¹' Iic 0`, which is closed by `LowerSemicontinuous.isClosed_preimage` (Basic.lean:237). Here `f − P_i` is lsc by (b).
* `D_i = ⋃_k (S_k ∩ {P_k ≤ P_i})`, using covering and `f = P_k` on `S_k`.
* Under definition (A), the set `{P_k ≤ P_i}` is `{P_i−P_k > 0} ∪ {P_i−P_k = 0}`. The intersection of two finite unions of basic sets is a finite union of pairwise intersections, and `{P=0,Q_j>0} ∩ {P'=0,Q'_l>0} = {P²+P'²=0, Q_j>0, Q'_l>0}`. So `D_i` is semialgebraic using only `∩` and `∪`: no complement and no Tarski–Seidenberg.
* `f(x) = min_{i : x∈D_i} P_i(x)`. Every `i` with `x ∈ D_i` has `P_i(x) ≥ f(x)` by the definition of `D_i`. The `i₀` with `x ∈ S_{i₀}` lies in that set and has `P_{i₀}(x) = f(x)`.
* This step needs **no lsc**; lsc is used only for the closedness of `D_i`. CONFIRMED.

(d) **Gadget**, after normalisation, so `P_i ≤ 0` and hence `f ≤ 0`, because `f(x) = P_{i₀}(x)`:
* For `(s,z) ∈ Θ(x)`, the separable structure gives `s_c ≥ 0` and `Σ s = 1` (the s-part; the vertex shows the minimum value is 0 when `I×J ≠ ∅`), and `R_ijk(x) < 0 ⇒ z_ijk = 0`.
* Put `a_ij = P_i(x) ∏_k z_ijk`.
  * If `x ∈ C_ij`: `∏ z ∈ [0,1]`, and `P_i ≤ 0`, so `a_ij − P_i = (−P_i)(1 − ∏z) ≥ 0`, which gives `a_ij ≥ P_i(x) ≥ f(x)`.
  * If `x ∉ C_ij`: some `z_ijk = 0`, so `a_ij = 0 ≥ f(x)`.
  * Hence `P = Σ s_ij a_ij ≥ f(x)`.
* Attainment: take `(i*,j*)` with `x ∈ C_{i*j*}` and `P_{i*}(x) = f(x)`. Let `s*` be the vertex at `(i*,j*)` and set `z*_ijk = [R_ijk(x) ≥ 0]`. Each coordinate is a one-variable minimiser (when `R = 0` every value is a minimiser), so `(s*,z*) ∈ Θ(x)` and `P = f(x)`.
* The report is right that the exact set (15) is never needed: only `Θ ⊆ {...}` and `(s*,z*) ∈ Θ` are used.
* Convexity: `(1−Σs)²` is the square of an affine map, and `−Σ R z` is linear in `(s,z)`. So `Q` is convex on `univ`, and `[0,1]^{…}` is a bounded box.
* `Nonempty (I×J)` is needed (otherwise `Q`'s s-part ≡ 1 and `P ≡ 0`). It follows from the `IsLeast` hypothesis at any point, because `Fin n → ℝ` is nonempty.

CONFIRMED.

(e) **Paper's final chain**: `min_i P_i(x)1_{cl S_i}(x) = f(x)` needs `0 ≥ f(x)` for the `i ∉ I(x)` terms, and that follows from the normalisation `P_i ≤ 0`. It also needs `I(x) ≠ ∅`. The paper is correct but leaves both points implicit, as the report says (#11). The report's L7 handles them explicitly.

### C5. "A2 (Prop 2.4) is unavoidable; A1 is avoidable" — sharpened
The report's example is right. With `Q = x²(x−1)`, `{Q>0} = (1,∞)` and `{Q≥0} = {0} ∪ [1,∞) ⊋ [1,∞) = cl{Q>0}`.
A complete counterexample to the naive relaxation:
* Take `f = 1` on `S₂ = {1−x>0}` with `P₂ = 1`, and `f = 0` on `S₁ = {Q>0} ∪ {x−1=0} = [1,∞)` with `P₁ = 0`.
* `f` is lsc, because its sublevel sets are `∅`, `[1,∞)` and `ℝ`. Also `D₁ = [1,∞)`.
* The naive relaxation is `C₁ = {Q≥0} ∪ {x−1=0} ∋ 0`. The gadget would then output `min(P₁(0), P₂(0)) = 0 ≠ f(0) = 1`.

**Rigorous necessity for the gadget route.** Suppose the L7 hypothesis can be met for every lsc PP function. That means: for some PP representation `(S'_l, P'_l)`, there are finitely many closed basic sets `C'_l = ⋂_k{R_lk ≥ 0}` with `IsLeast {P'_l(x) | x∈C'_l} (f x)`. Then Prop 2.4 follows:
* Let `D` be closed semialgebraic and `f = 1_{D^c}`. This is PP, using that the complement of a semialgebraic set is semialgebraic, which is elementary. It is lsc, since its sublevel sets are `∅`, `D` and `ℝⁿ`.
* `IsLeast` gives `f(x) ≤ 0 ⇔ ∃ l, x ∈ C'_l ∧ P'_l(x) ≤ 0`.
* So `D = ⋃_l (C'_l ∩ {−P'_l ≥ 0})`, a finite union of closed basic sets.

So, on the L7 route, A2 is *equivalent* to what is needed. A2 applied to `D_i` gives the hypothesis, and the hypothesis gives A2. Whether Thm 2.20 itself, by any route, implies Prop 2.4 is unclear: the value function only gives `D = {x | ∃ y∈Θ(x), P ≤ 0}`, which is a projection. The blueprint should say "assumed; necessary for this route". The claim that A1 (closure of a semialgebraic set is semialgebraic) is avoidable is CONFIRMED by C4(c).

### C6. Pessimistic reduction
* `φ_p(−P,Q,Y)(x) = ⨆_{y∈Θ} ↑(−P x y) = ⨆_{y∈Θ} −↑(P x y)` (by `EReal.coe_neg`, Data/EReal/Operations.lean:220), and this equals `−⨅_{y∈Θ} ↑(P x y)`.
* Empty `Θ`: `⨆∅ = ⊥ = −⊤ = −⨅∅`, matching the paper's convention `φ_p = −∞` (line 127).
* Unbounded cases: `−⊥ = ⊤`. The identity holds because negation is an order anti-isomorphism.
* Mathlib: there is no `EReal.neg_iInf`, as the report says. But **`EReal.negOrderIso : EReal ≃o ERealᵒᵈ`** (Operations.lean:295) exists, and so does `OrderIso.map_iInf₂` (to_dual of `OrderIso.map_iSup₂`, Order/CompleteLattice/Basic.lean:330). Then `ofDual_iInf` gives the identity in a few lines. The alternative is `le_antisymm` with `EReal.neg_le` / `EReal.le_neg` (Operations.lean:263/270).
* Consequences:
  * `f ∈ C^p_box ⇔ −f ∈ C_box`, since `Q` and `Y` are unchanged (so convexity and box type are preserved) and `−P` is still a polynomial.
  * `PP ⊆ C^p_unbound`.
  * `PP ∩ USC = −(PP ∩ LSC) ⊆ C^p_bounded ⊆ −(SA∩LSC∩CB) = SA∩USC∩CB`.
  * `C^p_cc = SA∩USC∩CB`.
  * These use that `PP`, `SA` and `CB` are closed under negation, plus **`lowerSemiContinuous_neg_iff`** (to_additive of `lowerSemiContinuous_inv_iff`, Topology/Semicontinuity/Basic.lean:978; note the capital C in `SemiContinuous`) and its aliases `UpperSemicontinuous.neg` / `LowerSemicontinuous.neg`. The report said this may need a 3-line proof; it already exists.
* The negation trick does **not** give the paper's stronger "any selection" claim for the nonconvex unbounded result (Thm 2.12; the report miswrites it as "Thm 2.14"). For Thm 2.18 the "any selection" claim does follow, from constancy (C3).

### C7. Attained form
* `IsLeast (P x '' Θ x) r ⇔ (valueFun P Q Y x = ↑r ∧ ∃ y ∈ Θ x, P x y = r)`. The forward direction is F0. The converse comes from `iInf₂_le` at the witness plus `EReal.coe_le_coe_iff`.
* The conversion lemma is `valueFun_eq_of_isLeast : IsLeast ((fun y => P x y) '' argminSet Q Y x) r → valueFun P Q Y x = (r : EReal)`, with its twin `valueFunP_eq_of_isGreatest`.
* It suffices for every *construction* (⊆ direction) in 2.15, 2.18, 2.20, 2.21 and Lemma 3.3: all of them produce real-valued `f` with an attained minimum. On a compact `Y` attainment is automatic anyway.
* The class definitions must stay `valueFun`-based. Defining the classes by attainment would shrink `C_unbound` / `P_unbound`, and it is unusable for the reverse inclusions (`C ⊆ SA`, Prop 2.6) and for Thm 2.12's `±∞` values.

### C8. Euclidean-norm remark (§2.3.1)
* `n ≥ 2` is needed: `|x| ∈ PP` on ℝ (pieces `{x>0}∪{x=0}` with `x`, and `{−x>0}` with `−x`), and on ℝ⁰ every function is constant. CONFIRMED.
* `‖·‖ ∈ C_cc`: take `Y = {Σy²≤1}`, `Q = −⟨x,y⟩`, `P = ⟨x,y⟩`. For `x ≠ 0` the argmin is `{x/‖x‖}`; for `x = 0` it is `Y` and `P ≡ 0`. CONFIRMED.
  * It can stay in `Fin n → ℝ`, using Cauchy–Schwarz `Finset.sum_mul_sq_le_sq_mul_sq` (Algebra/Order/BigOperators/Ring/Finset.lean:171) and its equality case. `EuclideanSpace` is not needed.
* `‖·‖ ∉ PP`: the report says "a polynomial vanishing on a nonempty open set is 0" is NOT IN MATHLIB and proposes the analytic identity theorem. That is **unnecessary**. Use **`MvPolynomial.funext_set`** (Mathlib/Algebra/MvPolynomial/Funext.lean:57): polynomials that agree on a box `Set.pi univ s` with infinite sides are equal. A nonempty open set in `Fin n → ℝ` contains `pi univ (fun i => Ioo …)`, and `Set.Ioo_infinite` is at Order/Interval/Set/Infinite.lean:47. The density/complement argument of L10 goes through unchanged.
* For the final contradiction, avoid `MvPolynomial.coeff` of a square:
  1. Pick `x₀ ∈ U` with `x₀ ≠ 0` and a unit `v ⊥ x₀`, which exists because `n ≥ 2`.
  2. Then `r(t) := p(x₀+tv)` is a univariate polynomial with `r(t)² = ‖x₀‖² + t²` on an interval, hence everywhere (`Polynomial.eq_of_infinite_eval_eq`).
  3. `deg r = 1`, so `r` has a real root; but `r² ≥ ‖x₀‖² > 0`. Contradiction.
* Effort is M, not M–L. Keep it OPTIONAL: it is not needed for any table-4 inclusion, only for the strictness remark.

### C9. The 17 claimed paper errors

| # | Verdict | Evidence / comment |
|---|---|---|
| 1 | PARTLY CONFIRMED | Construction correct, and the argmins are sets written as points. But the paper *does* state the constancy explicitly ("although there are multiple minimizers … they all yield the same value F", html l.710), so "implicitly uses" is overstated. Missed by the report: the display of `G` lacks parentheses (`Σ_j (1−Q_j z_j)² − Q_j w_j`; the `−Q_j w_j` must be inside the sum). |
| 2 | CONFIRMED | `⋃_{j∈J}^M` (PDF p.15 shows the superscript `M`). "the S_ij are pairwise disjoint" should be T_ij. `i ∈ I` is undefined. Also a uniform `J` across `i` is assumed implicitly. |
| 3 | CONFIRMED (cosmetic) | |
| 4 | REFUTED as a paper error | With a partition of `ℝⁿ ≠ ∅`, some `T_ij` exists, so the combined box is unbounded. This is only a Lean pitfall for the stronger lemma. (The report's sentence for #4 is also garbled.) |
| 5 | CONFIRMED | PDF p.28: "H := {P_i, i = 1 ∈ I}", "either disjoint and included in". The cells use `<` and multiple `=`. Fix as stated. |
| 6 | CONFIRMED | `\mathcal I` is undefined (html l.796). The proof of (13) is omitted. |
| 7 | CONFIRMED | "pair integer N" (= even), clash with `N` pieces, "element of 𝒮", "equal to h" (html l.804). The growth bound is replaceable by `g`. |
| 8 | CONFIRMED | Uniform `J,K`. "Closure of semialgebraic is semialgebraic" is asserted without citation (html l.806). |
| 9 | HALF CONFIRMED | "(z^i)^⋆" should be "(z^i_j)^⋆". The lost `<` case is an HTML extraction artifact (the PDF is correct), not a paper error. |
| 10 | PARTLY CONFIRMED | The paper says "Due to the optimistic nature…". Iterating the minimisation over `Θ_s × Θ_z` is legitimate (for fixed `s ≥ 0` the z-minimisation splits blockwise) but not justified. Minor. |
| 11 | CONFIRMED | Implicit `0 ≥ f` and `I(x) ≠ ∅`. Typo `\overline{s_i}` (html l.897). |
| 12 | NOT A PAPER ERROR | The degenerate cases cannot occur under the paper's hypotheses. This is a Lean-level remark only. |
| 13 | CONFIRMED | (C8) |
| 14 | CONFIRMED | Contradicted by the paper's own proof of Lemma 2.19 (multiple minimisers when `P(x)=0` or `Q_j(x)=0`). |
| 15 | NOT AN ERROR | A valid simplification, not a mistake. |
| 16 | CONFIRMED | "Q convex w.r.t. y" (html l.174) does not say on ℝ^m or on 𝒴. |
| 17 | REFUTED | The proof of Theorem 2.15 opens with `P_bounded ⊆ SA∩LSC∩CB` (by Prop 2.6 + Cor 2.9; html l.535–539), and `C_bounded ⊆ P_bounded` is stated after Def 2.16. So "justified in Theorem 2.15" is accurate. (The report's "paragraph before Thm 2.15" is wrong. The real typo nearby is "To prove the equalities in Theorem 2.21" inside the proof of 2.15.) |

---

## D. Mathlib citation check

| Declaration | Exists | file:line verified | Adequate | Note |
|---|---|---|---|---|
| `ConvexOn.add` | yes | Analysis/Convex/Function.lean:228 | yes | result `f + g` (Pi add) |
| `convexOn_const` | yes | Function.lean:245 | yes | |
| `LinearMap.convexOn` | yes | Function.lean:388 | yes | |
| `ConvexOn.comp_linearMap` | yes | Function.lean:491 | yes | on `g ⁻¹' s` |
| `ConvexOn.comp_affineMap` | yes | Function.lean:974 | yes | `(g : E →ᵃ[𝕜] F) (hf : ConvexOn 𝕜 s f) : ConvexOn 𝕜 (g ⁻¹' s) (f ∘ g)` |
| `ConvexOn.subset` | yes | Function.lean:121 | yes | needs `Convex 𝕜 s` |
| `convexOn_id`, `ConvexOn.smul` | yes | Function.lean:85, :944 | yes | |
| `Even.convexOn_pow` | yes | Analysis/Convex/Mul.lean:159 | yes | `ConvexOn 𝕜 univ fun x ↦ x ^ n`, comm-ring section |
| `convexOn_pow`, `ConvexOn.pow` | yes | Mul.lean:155, :146 | n/a | |
| finite-sum `ConvexOn` | NOT IN MATHLIB (confirmed) | — | — | grep found only Jensen `ConvexOn.map_sum_le` (Jensen.lean:66). Prove via `Finset.sum_induction` |
| `Finset.prod_induction` / `sum_induction` | yes | Algebra/BigOperators/Group/Finset/Defs.lean:619 | yes | |
| `convex_pi` | yes | Analysis/Convex/Basic.lean:108 | yes | `(ht : ∀ ⦃i⦄, i ∈ s → Convex 𝕜 (t i)) : Convex 𝕜 (s.pi t)` |
| `convex_univ`, `convex_Iic`, `convex_Ici`, `convex_Icc` | yes | Basic.lean:89, :248, :254, :257 | yes | |
| `stdSimplex`, `convex_stdSimplex` | yes, **DEPRECATED** | Analysis/Convex/StdSimplex.lean:40 (`@[deprecated StdSimplex +typeChanged (since := "2026-08-29")]`), :49 | avoid | use an explicit set |
| `LinearMap.proj`, `AffineMap.proj` | yes | Algebra/Module/Pi.lean:115; LinearAlgebra/AffineSpace/AffineMap.lean:661 | yes | |
| `Function.update_self`, `update_of_ne` | yes | Logic/Function/Basic.lean:644, :648 | yes | |
| `Function.apply_update` | yes (not cited by report) | Logic/Function/Basic.lean:765 | needed for the update route | |
| `Finset.sum_update_of_mem` | yes | Algebra/BigOperators/Group/Finset/Piecewise.lean:247 (`prod_update_of_mem`) | yes, with `apply_update` | |
| `Finset.sum_lt_sum` | yes (recommended) | Algebra/Order/BigOperators/Group/Finset.lean:579 (`prod_lt_prod`; `prod_lt_prod'` deprecated alias) | yes | F2 |
| `Finset.add_sum_erase`, `sum_eq_single` | yes | Finset/Basic.lean:773, :355 | yes | |
| `Finset.sum_le_sum`, `sum_nonneg`, `single_le_sum` | yes | Order/BigOperators/Group/Finset.lean:121, :162, :276 | yes | |
| `Finset.prod_nonneg`, `prod_le_one₀` | yes | Order/BigOperators/GroupWithZero/Finset.lean:34, :81 | yes | |
| `Finset.prod_eq_one`, `prod_eq_zero`, `prod_eq_zero_iff`, `prod_const_one` | yes | Finset/Basic.lean:108; GroupWithZero/Finset.lean:33, :57; Finset/Defs.lean:391 | yes | |
| `Finset.sum_ite_eq'` | yes | Piecewise.lean:153 (also the Fintype form at :319) | yes | |
| `Fintype.sum_sum_type`, `Finset.sum_sigma` | yes | Data/Fintype/BigOperators.lean:268; Finset/Sigma.lean:38 | yes | |
| `Set.indicator_union_of_disjoint` | yes | Algebra/Group/Indicator.lean:69 | yes | |
| indicator of a finite disjoint biUnion | **EXISTS** (the report says NOT FOUND) | `Finset.indicator_biUnion` = to_additive of `Finset.mulIndicator_biUnion`, Algebra/BigOperators/Group/Finset/Indicator.lean:70 | yes | only for the paper's route |
| `mem_closure_iff_frequently` | yes | Topology/Neighborhoods.lean:278 | yes | |
| `Filter.Frequently.and_eventually`, `.exists`, `Eventually.and_frequently` | yes | Order/Filter/Basic.lean:800, :809, :805 | yes | |
| `ContinuousAt.eventually_lt` | yes | Topology/Order/OrderClosed.lean:702 | yes | `g := const` |
| `Filter.Tendsto.eventually_const_lt` / `eventually_lt_const` | yes | OrderClosed.lean:237 (`@[to_dual eventually_lt_const]`) | yes | |
| `LowerSemicontinuous` (abbrev), `lowerSemicontinuousAt_iff` | yes | Topology/Semicontinuity/Defs.lean:293, :328 | yes | |
| `lowerSemicontinuous_iff_isClosed_preimage`, `LowerSemicontinuous.isClosed_preimage` | yes | Semicontinuity/Basic.lean:232, :237 | yes | `IsClosed (f ⁻¹' Iic y)`; needs only `[LinearOrder γ]` |
| `LowerSemicontinuous.add` | yes | Basic.lean:540 | yes for ℝ | needs `[AddCommMonoid γ] [LinearOrder γ] [IsOrderedAddMonoid γ] [TopologicalSpace γ] [OrderTopology γ] [ContinuousAdd γ]` |
| `Continuous.lowerSemicontinuous` | yes | Basic.lean:258 | yes | |
| `lowerSemicontinuous_sum` | yes | Basic.lean:567 | yes | |
| `lowerSemiContinuous_neg_iff` (+ `.neg` aliases) | **EXISTS** (the report says it may need proof) | Basic.lean:978 (to_additive of `lowerSemiContinuous_inv_iff`) | yes | spelling `SemiContinuous` |
| `LowerSemicontinuousOn.exists_isMinOn`, `IsCompact.exists_isMinOn` | yes | Basic.lean:77; Topology/Order/Compact.lean:255 | n/a | |
| `MvPolynomial.continuous_eval` | yes | Topology/Algebra/MvPolynomial.lean:31 (`theorem MvPolynomial.continuous_eval`) | yes | |
| `MvPolynomial.eval_C/X/add/mul/pow/sum/prod` | yes | Algebra/MvPolynomial/Eval.lean:271, 275, 286, 289, 292, 295, 299 | yes | |
| `MvPolynomial.eval_sub`, `eval_rename` | yes | MvPolynomial/CommRing.lean:163; Rename.lean:244 | yes | |
| `MvPolynomial.funext` | yes | Funext.lean:83 | yes | |
| `MvPolynomial.funext_set` | **EXISTS, not used by the report** | Funext.lean:57 | yes; key for L10 | |
| `AnalyticAt.aeval_mvPolynomial` | yes | Analysis/Analytic/Polynomial.lean:60 | yes, but unnecessary | |
| identity theorem | yes | `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` Analysis/Analytic/Uniqueness.lean:205; `eqOn_of_preconnected_of_eventuallyEq` (used at DirichletContinuation.lean:132) | unnecessary | |
| `EReal.coe_neg` | yes | Data/EReal/Operations.lean:220 | yes | |
| `EReal.neg_iInf` | NOT IN MATHLIB (confirmed) | — | — | use `EReal.negOrderIso` (Operations.lean:295) + `OrderIso.map_iInf₂` (to_dual, CompleteLattice/Basic.lean:330) |
| `EReal.coe_le_coe_iff` etc. | yes | Data/EReal/Basic.lean:55, 61, 67 | yes | |
| `biInf_const`, `iSup_const`, `iSup_congr` | yes | CompleteLattice/Basic.lean:425; Order/Bounds/Basic.lean:931; CompleteLattice/Basic.lean:141 | yes | |
| `IsGreatest.csSup_eq`, `IsLUB.iSup_eq` | yes | ConditionallyCompletePartialOrder/Basic.lean:71; Order/Bounds/Basic.lean:900 | yes | |
| `Equiv.piCongrLeft_preimage_univ_pi`, `Fintype.equivFin`, `Equiv.piCurry`, `Equiv.piCongrLeft` | yes | Data/Set/Prod.lean:919; Data/Fintype/EquivFin.lean:80; Logic/Equiv/Basic.lean:169, :846 | yes | |
| `Equiv.sumArrowEquivProdArrow` | yes | Logic/Equiv/Prod.lean:390 (ring version at Algebra/Ring/Equiv.lean:962) | yes | the report gave only "Logic/Equiv" |
| `Set.mem_pi`, `Set.mem_univ_pi` | yes | Data/Set/Operations.lean:281, :283 | yes | |
| `IsMinOn`, `isMinOn_iff` | yes | Order/Filter/Extr.lean:112, :129 | n/a | |
| `mem_closure_iff_nhds`, `mem_closure_iff_seq_limit` | yes | Topology/ClusterPt.lean:301; Topology/Sequences.lean:108 | n/a | |
| `sq_nonneg`, `mul_le_of_le_one_right'` | yes | Algebra/Order/Ring/Unbundled/Basic.lean:608; Monoid/Unbundled/Basic.lean:373 | yes (the report correctly says the latter has the wrong sign) | |
| `Finset.exists_max_image`, `le_sup'`, `exists_mem_eq_sup'` | yes | Data/Finset/Max.lean:386; Lattice/Fold.lean:561, :758 | n/a | |

Every line number the report gives is correct. There are no MISUSED citations. There are three wrong "not found" claims
(`Finset.indicator_biUnion`, the lsc negation lemma, and the polynomial-vanishing lemma via `funext_set`), one deprecated
declaration (`stdSimplex`), and one missing helper (`Function.apply_update`).

---

## E. Missed issues

1. **Paper gap in the proof of Thm 2.18 (math).** The proof uses Lemma 2.19 as a black box ("has value function equal to `1_{T_ij}`") and then concludes `Σ_j F_ij(x, y_ij(x)) = Σ_j 1_{T_ij}`. That conclusion does not follow from the lemma's *statement*. In `P = Σ_i P_i(x) Σ_j F_ij`, the coefficients `P_i(x)` have arbitrary sign, so the optimistic minimum over the product argmin is not determined by the block value functions unless `F_ij(x,·)` is constant on `Θ_ij(x)`. Fix: strengthen Lemma 2.19 to "`F(x,·)` is constant (= `1_S(x)`) on a nonempty `Θ(x)`". The paper's proof gives this; the report's S1 states it, but the report never flags the gap.
2. **Typo in Lemma 2.19:** the parentheses in `G` are missing (`… (1−Q_j z_j)² − Q_j w_j` should have the linear term inside `Σ_j`).
3. **Typo in the proof of Thm 2.15**: "To prove the equalities in Theorem 2.21" should be "Theorem 2.15" (html l.535). This is R4's scope; noted for consistency.
4. **The report's misreference:** "(For Thm 2.14, other agent)" in L9(c) and #14 should be Thm 2.12 (2.14 is a Remark).
5. **`stdSimplex` is deprecated** in the pinned checkout (`StdSimplex` structure in Geometry/Convex/ConvexSpace/Defs.lean:61). Do not build on it.
6. **Simplification of L8 missed:** L7 only ever uses the pairs `(i,j)`. State L7 for a flat Fintype `L` of pairs `(B_l, p_l)`, with `B_l = ⋂_{k : K l} {R_lk ≥ 0}` and `K : L → Type` dependent. The hypothesis becomes `IsLeast {p_l(x) | x ∈ B_l} (f x)`. Then the uniform-`J`/`K` padding of eq. (14) and of L8 disappears (`L := Σ i, J_i`, `p_⟨i,j⟩ := p_i`). The `z` variables are then indexed by `Σ l, K l`.
7. **L7 hypotheses `Nonempty I`, `Nonempty J` are derivable.** Each follows from the `IsLeast` hypothesis at any point of the nonempty space `Fin n → ℝ`. Drop them, or prove them inside.
8. **The `D_i` semialgebraicity proof needs only `∩` and `∪` under definition (A)**, via the `P²+P'²` trick (C4c). It does not need the complement, so R2's Boolean-algebra result is not even required here.
9. **L10 can stay in `Fin n → ℝ`**, using `Finset.sum_mul_sq_le_sq_mul_sq`. `EuclideanSpace` is unnecessary.

---

## F. Route assessment and recommended route

The report's route is the cheapest correct one I can find. Recommended blueprint route:
1. **Framework:**
   * F0 (attained ⇒ `valueFun`) and its pessimistic twin.
   * F1.
   * F2: prove the pi version via `Finset.sum_lt_sum`, and the Prod version directly.
   * F3.
   * F4, including `convexOn_finset_sum` by `Finset.sum_induction`, and the square of an affine map via the Route B `nlinarith`.
   * Classes quantified over `∃ (ι : Type) [Fintype ι]` for the lower variable, or F5 once.
   * Convexity on `univ`.
2. **Lemma 2.19′** (C1 gadget, conclusion "nonempty argmin and `F` constant = `1_S`").
3. **Lemma 2.18′** (stronger): `x ↦ Σ_i 1_{S_i}(x)P_i(x) ∈ C_unbound` for *any* finite family, via `1 − ∏(1 − F_ij)`, with a dummy `univ` coordinate. Corollary: `PP ⊆ C_unbound`. No Prop C.1. The second inclusion is Prop 2.6 (R2, T–S assumed).
4. **Theorem 2.20 core (flat form, E6):** given finitely many `(B_l, p_l)` with `B_l` closed basic and `IsLeast {p_l x | x ∈ B_l} (f x)` for all `x`, conclude `f ∈ C_bounded` (attained). Proof: normalise with `g = 1/4 + Σ p_l²`, then the s/z gadget with lower bound plus explicit minimiser (C4d), then add `g` back.
5. **Theorem 2.20 as stated:** `D_i = {f ≤ P_i}` is closed (lsc) and semialgebraic (elementary). A2 (Prop 2.4, shared with Thm 2.15, assumed) gives the `B_l`. The `IsLeast` hypothesis is immediate. Drop A1, and drop eq. (13) from the critical path (keep it as an optional remark L3). The second inclusion is `C_bounded ⊆ P_bounded` plus the first lines of the proof of Thm 2.15.
6. **Pessimistic counterparts:** a single EReal lemma `valueFunP (−P) Q Y = −valueFun P Q Y` (via `EReal.negOrderIso`), plus `lowerSemiContinuous_neg_iff`, plus closure of PP/SA/CB under negation. Every Table-4 pessimistic statement is then a corollary.
7. **§2.3.1 remark:** optional, effort M, with `MvPolynomial.funext_set` and the univariate-restriction contradiction (C8).

---

## G. Escalations to the orchestrator

1. **Lower-variable index type in the class definitions.** `Fin m` vs `∃ ι Fintype` affects every construction (R3, R4, R6 too). I recommend `∃ (ι : Type) [Fintype ι]`. Note the universe: fix `ι : Type`.
2. **Convexity convention (Def 2.16):** `ConvexOn ℝ univ (Q x)` vs `ConvexOn ℝ Y (Q x)`. R5's constructions satisfy the stronger `univ` reading. Check that the Thm 2.21 construction (Carathéodory/moment lifting; linear objective) also does; it does, being linear. Then fix `univ` globally. Inclusions `C ⊆ SA` hold under either reading.
3. **Prop 2.4 (A2)** should be ONE named assumption shared by Thm 2.15 (closure of the graph) and Thm 2.20 (the sets `D_i`). Its necessity for the Thm 2.20 gadget route is now rigorous (C5). Under the `D_i` route, the Thm 2.20 side does not need "closure of a semialgebraic set is semialgebraic". Ask R4 whether Thm 2.15 still needs it (for `cl(graph f)`).
4. **Definition of semialgebraic (R2):** the `D_i` route needs only finite `∪`/`∩` of basic sets. PP for `1_{D^c}` in C5 needs complements, but C5 is a meta-argument, not part of the blueprint.
5. **EReal shift/negation lemmas:** if the framework wants EReal statements (not only the attained forms), it needs `valueFunP (−P) = −valueFun P` (via `negOrderIso`) and `valueFun (P + g) = valueFun P + g` (true in all cases; the proof needs `x ↦ x + ↑c` as an order iso of EReal — no such lemma found; prove it by `le_antisymm`).
6. **Paper-error list consistency:** R4 should record the "Theorem 2.21" typo in the proof of Thm 2.15. Claimed error #17 should be dropped.
7. **"Any selection" claim in §2.4 bullet 1:** it holds for Thm 2.18 (constancy). For Thm 2.12 (R3) it must be checked separately; the negation trick does not provide it.
