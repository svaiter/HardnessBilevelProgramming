# R5 — Convex lower level: Lemma 2.19, Theorem 2.18, Theorem 2.20, Section 2.3.1 remark, Section 2.4 (pessimistic)

Paper: Bolte–Lê–Pauwels–Vaiter, arXiv:2407.12372v2, Section 2.3 (lines 644–990 of paper_html.txt), Section 2.4, Appendix C.
Mathlib checkout: `<SCRATCH>/mathlib/mathlib4` (master 1df8067a). Every declaration below was located by grep; "NOT IN MATHLIB" means I searched and found nothing.

Semialgebraic-set definition assumed: paper's (A) = finite union of basic sets `{P = 0 ∧ ∀ j, Q_j > 0}`; I only ever
use the *data* of such a presentation, so (A)⇔(B) (R2) is irrelevant to this report except for Prop. 2.4.

Executive summary (details below):

* **Lemma 2.19** is correct, but can be simplified to half the variables and no linear term:
  `G(x,u,t) = (1 − tP(x))² + Σ_j (1 − Q_j(x) u_j)²` over `t ∈ ℝ, u ∈ [0,∞)^J`, `F = (1 − tP(x)) ∏_j Q_j(x) u_j`.
  The value function is `1_S`, and `F` is *constant* on the (non-unique) argmin ⇒ optimistic = pessimistic = any selection.
* **Theorem 2.18** does **not** need Prop. C.1 (disjoint decomposition): write `1_{S_i} = 1 − ∏_j (1 − 1_{T_ij})` for any
  (non-disjoint) union `S_i = ∪_j T_ij`; the upper objective stays polynomial. The S_i need not even be disjoint for the
  construction (only the formula `f = Σ_i 1_{S_i} P_i` is used). Convexity is just "sum of squares of affine maps".
* **Theorem 2.20**: eq. (13) is right and provable with filters in a few lines; the growth step (`B + ‖x‖^N`, Prop 2.5) is
  unnecessary — use the identity `P ≤ P² + 1/4` and subtract the single polynomial `g = 1/4 + Σ_i P_i²`; the
  gadget argument is right but the paper's final chain silently uses `f ≤ 0`. The only heavy input is the closed-basic
  representation (14) of `cl(S_i)` (needs "closure of semialgebraic is semialgebraic" AND the finiteness theorem Prop 2.4);
  it cannot be avoided by choosing other closed sets. Blueprint: prove a *core theorem* whose hypothesis is a given
  closed-basic presentation, and derive the paper's Thm 2.20 from it + two assumed real-algebraic-geometry facts.
* **Section 2.4 (pessimistic)**: the paper's justification "unique minimizers" is false for Lemma 2.19/Thm 2.18, but the
  conclusion holds (P constant on argmin). More importantly: for *every* result, `φ_p(−P,Q,Y) = −φ_o(P,Q,Y)` (sup of −P =
  −inf of P), so the pessimistic classes are exactly the negatives of the optimistic ones and all pessimistic
  counterparts are one-line corollaries; no adapted constructions are needed.
* **Section 2.3.1 remark** (Euclidean norm ∈ C_cc \ PP): correct for n ≥ 2 only (|x| is PP on ℝ); formalizable but
  optional (M–L); recommend leaving it out of the blueprint or marking it optional.

---

## 1. Scope — exact statements covered

Notation (baseline encoding of the brief): `x : Fin n → ℝ`, lower variable `y : Fin m → ℝ` (but see §5.1: I recommend
allowing `y : ι → ℝ` for a `Fintype ι` in the construction lemmas and transporting to `Fin m` once),
`P Q : (Fin n → ℝ) → (Fin m → ℝ) → ℝ`, `Y : Set (Fin m → ℝ)`,
`argminSet Q Y x = {y ∈ Y | ∀ y' ∈ Y, Q x y ≤ Q x y'}` (= Θ(x)),
`valueFun P Q Y x : EReal = ⨅ y ∈ argminSet Q Y x, ((P x y : ℝ) : EReal)`, `valueFunP` the `⨆` version.

**Polynomiality**: `IsPolyFun P := ∃ p : MvPolynomial (Fin n ⊕ Fin m) ℝ, ∀ x y, P x y = MvPolynomial.eval (Sum.elim x y) p`.
**Box**: `IsBox Y := ∃ (I : Fin m → Set ℝ), (∀ i, I i is one of Icc a b / Ici a / Iic b / univ) ∧ Y = Set.pi Set.univ I`;
`IsBoundedBox` = all `Icc`; `IsUnboundedBox` = box with at least one coordinate not `Icc`
(paper, line 184: "unbounded box if some a_i = −∞ or b_i = +∞"; a mixed box such as `[0,1]^J × ℝ^J × ℝ` IS an unbounded box).
**Convexity** of the lower level (Def. 2.16 "Q convex w.r.t. y"): `∀ x, ConvexOn ℝ Set.univ (fun y => Q x y)`
(decision discussed in §5.3; all constructions satisfy it on `univ`, and `ConvexOn.subset` gives the `Y`-version).

Classes (as predicates on `f : (Fin n → ℝ) → ℝ`):
* `f ∈ C_unbound  ↔ ∃ m P Q Y, IsPolyFun P ∧ IsPolyFun Q ∧ (∀ x, ConvexOn ℝ univ (Q x)) ∧ IsUnboundedBox Y ∧ ∀ x, valueFun P Q Y x = (f x : EReal)`
* `f ∈ C_bounded  ↔` same with `IsBoundedBox Y`.
* `f ∈ PP ↔ ∃ (N : ℕ) (S : Fin N → Set (Fin n → ℝ)) (p : Fin N → MvPolynomial (Fin n) ℝ), (∀ i, IsSemialgebraic (S i)) ∧ Pairwise (Disjoint on S) ∧ (⋃ i, S i) = univ ∧ ∀ x, f x = Σ i, (S i).indicator 1 x * eval x (p i)`
  (Def. 2.17; equivalently `∀ i, ∀ x ∈ S i, f x = eval x (p i)`).
* `LSC f ↔ LowerSemicontinuous f` (Mathlib abbrev; Defs.lean:293).

### Statement S1 (Lemma 2.19, strengthened)
For a basic set `S = {x | eval x P = 0 ∧ ∀ j : J, 0 < eval x (Q j)}` (`J` a Fintype, possibly empty) there exist
`m, P', Q', Y` with `P', Q'` polynomial, `Q'` convex in `y` on `univ`, `Y` an unbounded box, such that for every `x`:
`argminSet Q' Y x` is nonempty and `P' x` is constant on it with value `S.indicator 1 x`.
Consequently `valueFun = valueFunP = (1_S : EReal)` and the infimum is attained.

### Statement S2 (Theorem 2.18, first inclusion, strengthened)
If `f x = Σ_i 1_{S_i}(x) p_i(x)` with `S_i` semialgebraic (given as finite unions of basic sets; disjointness NOT needed
for this direction) then `f ∈ C_unbound`, with `P` constant on the argmin (hence also pessimistic, and the inf is attained).
Second inclusion `C_unbound ⊆ SA` is Prop 2.6 (agent R2; Tarski–Seidenberg-dependent).

### Statement S3 (eq. (13))
`f ∈ PP` with representation `(S_i, p_i)_{i<N}`, `f` lower semicontinuous. For all `x`, with `I(x) = {i | x ∈ closure (S i)}`:
`IsLeast {eval x (p i) | i ∈ I(x)} (f x)`, i.e. `(∃ i ∈ I(x), f x = p_i(x)) ∧ ∀ i ∈ I(x), f x ≤ p_i(x)`. (`I(x) ≠ ∅` follows.)

### Statement S4 (Theorem 2.20 core — the formalizable heart)
Data: Fintypes `I, J, K` with `Nonempty I`, `Nonempty J`; polynomials `p : I → MvPolynomial (Fin n) ℝ` and
`R : I → J → K → MvPolynomial (Fin n) ℝ`; closed sets `C_ij := {x | ∀ k, 0 ≤ eval x (R i j k)}`, `C_i := ⋃ j, C_ij`;
`f : (Fin n → ℝ) → ℝ` with `∀ x, IsLeast {eval x (p i) | i, x ∈ C_i} (f x)`.
Conclusion: `f ∈ C_bounded`, with the minimum over the argmin attained (`IsLeast ((P x) '' Θ(x)) (f x)`).
(No lsc hypothesis needed — it is implied; no sign hypothesis on `p` — handled inside.)

### Statement S5 (Theorem 2.20 as in the paper)
`PP ∩ LSC ⊆ C_bounded ⊆ SA ∩ LSC ∩ CB`. First inclusion = S3 + S4 + [Assumption A1: `closure` of a semialgebraic set is
semialgebraic] + [Assumption A2 = Prop 2.4: every closed semialgebraic set is a finite union of sets `∩_k {R_k ≥ 0}`].
Second inclusion: Prop 2.6 + Cor 2.9 (other agents).

### Statement S6 (pessimistic counterparts, Section 2.4)
(a) General: `valueFunP (fun x y => −P x y) Q Y x = − valueFun P Q Y x` (EReal), for all `P Q Y x` (including `Θ(x)=∅`: `−⊤ = ⊥`).
Hence `f ∈ C^p_boxtype ↔ −f ∈ C_boxtype` (same for `P_boxtype`, `C_cc`).
(b) Corollaries: `PP ⊆ C^p_unbound`; `PP ∩ USC ⊆ C^p_bounded ⊆ SA ∩ USC ∩ CB`; and `C^p_cc = SA ∩ USC ∩ CB`.
(c) For S1/S2 additionally `valueFun = valueFunP` directly (P constant on argmin).

### Statement S7 (Section 2.3.1 remark; optional)
For `n ≥ 2`, `x ↦ ‖x‖₂ ∈ C_cc \ PP`. (For `n = 1`, `|x| ∈ PP`.)

---

## 2. Proof route — DAG of lemmas

Dependencies: `F0–F6` framework lemmas (coordinate with the framework agent; some may already be planned), then
`L1` (S1) → `L2` (S2); `L3` (S3), `L4`, `L5`, `L6` → `L7` (S4) → `L8` (S5); `L9` (S6); `L10` (S7, optional).

### F0 — value function from an attained minimum (framework)
`valueFun_eq_of_isLeast : IsLeast ((fun y => P x y) '' argminSet Q Y x) r → valueFun P Q Y x = (r : EReal)`.
Proof: `le_antisymm`; `≤`: `iInf₂_le` at the witness `y₀`; `≥`: `le_iInf₂` + `EReal.coe_le_coe_iff`.
Also the `⨆` twin `valueFunP_eq_of_isGreatest`. (S)
*Why*: every construction in this report attains its minimum, so we never need GLB-transfer between ℝ and EReal.

### F1 — "constant on argmin" principle (framework)
`(argminSet Q Y x).Nonempty → (∀ y ∈ argminSet Q Y x, P x y = c) → valueFun P Q Y x = c ∧ valueFunP P Q Y x = c`.
Proof: `IsLeast`/`IsGreatest` of a singleton image, then F0; or directly `iInf_congr` twice + `biInf_const` (CompleteLattice/Basic.lean:425, `to_dual` of `biSup_const`). (S)

### F2 — separable sums have product argmins (framework; the lemma Lemma 2.19/2.18/2.20 all need)
Setting: `ι` a type (Fintype for sums), `E : ι → Type*`, `Y : ∀ i, Set (E i)`, `g : ∀ i, E i → ℝ`.
```
theorem argmin_pi_sum [Fintype ι] :
  {y ∈ Set.pi univ Y | ∀ y' ∈ Set.pi univ Y, ∑ i, g i (y i) ≤ ∑ i, g i (y' i)}
    = Set.pi univ (fun i => {v ∈ Y i | ∀ v' ∈ Y i, g i v ≤ g i v'})
```
No nonemptiness hypothesis is needed (if some factor is empty both sides are empty).
Proof. `⊇`: `Finset.sum_le_sum` (to_additive of `Finset.prod_le_prod'`, Algebra/Order/BigOperators/Group/Finset.lean) termwise.
`⊆`: let `y` be a minimizer of the sum and suppose coordinate `k` is not a minimizer of `g k`: pick `v' ∈ Y k` with
`g k v' < g k (y k)`; set `y' := Function.update y k v'` (`Function.update_self` Logic/Function/Basic.lean:644,
`Function.update_of_ne` :648); `y' ∈ Set.pi univ Y` (`Set.mem_univ_pi` Data/Set/Operations.lean:283); the sums differ only
in term `k` (`Finset.sum_eq_single`-free route: `Finset.sum_update_of_mem` or split `∑ = term k + ∑_{i≠k}` via `Finset.add_sum_erase`), so
`∑ g i (y' i) < ∑ g i (y i)`, contradicting minimality. (S–M; `DecidableEq ι` needed for `update`.)
Instantiations: (i) scalar coordinates `E i = ℝ` (L1, L2, z-part of L7); (ii) two blocks `ι = Bool`/`Fin 2` with
`E = (s-space, z-space)` (L7), or a direct `Prod` version `argmin_prod_add`:
`{p ∈ Y₁ ×ˢ Y₂ | …A p.1 + B p.2…} = argmin A Y₁ ×ˢ argmin B Y₂` (same proof, no `update`). I recommend proving the `Prod`
version separately (simpler) and the pi version once.

### F3 — one-variable argmins (framework, trivial calculus-free facts)
For `c ∈ ℝ`:
* `argmin_sq_affine : {t ∈ univ | ∀ t', (1 − c t)^2 ≤ (1 − c t')^2} = if c = 0 then univ else {1/c}`;
  proof: `c ≠ 0`: `(1 − c t)² ≥ 0 = (1 − c (1/c))²` and equality iff `1 − ct = 0` iff `t = 1/c` (`mul_inv_cancel₀`, `sq_eq_zero_iff`/`pow_eq_zero_iff`); `c = 0`: function constant 1.
* `argmin_sq_affine_Ici : {u ∈ Ici 0 | ∀ u' ∈ Ici 0, (1 − c u)^2 ≤ (1 − c u')^2} = if 0 < c then {1/c} else if c = 0 then Ici 0 else {0}`;
  for `c < 0`: on `u ≥ 0`, `1 − c u ≥ 1 > 0` and `u ↦ 1 − cu` is strictly increasing, so `(1 − cu)²` is strictly increasing; min at `0`.
  (Only the *facts* needed later: membership of the chosen point and the value of `c·u` on the argmin: `c u = 1` if `c > 0`,
  `c u = 0` if `c ≤ 0`. For `c = 0` trivially `c u = 0`; for `c < 0` the argmin is `{0}`.)
* `argmin_linear_Icc : {z ∈ Icc 0 1 | ∀ z' ∈ Icc 0 1, −c z ≤ −c z'} = if 0 < c then {1} else if c = 0 then Icc 0 1 else {0}`.
  Again only needed: `1 ∈ argmin ↔ 0 ≤ c`; `z ∈ argmin ∧ c < 0 → z = 0`.
(S each.)

### F4 — convexity toolkit (framework)
* `convexOn_sq_affine (ℓ : E →ₗ[ℝ] ℝ) (c : ℝ) : ConvexOn ℝ univ (fun v => (c − ℓ v)^2)`.
  Route A: `(Even.convexOn_pow even_two)` (Analysis/Convex/Mul.lean:159, `ConvexOn 𝕜 univ fun x => x ^ n`) composed with the
  affine map `v ↦ c − ℓ v` via `ConvexOn.comp_affineMap` (Analysis/Convex/Function.lean:974; gives `ConvexOn 𝕜 (g ⁻¹' univ) (f ∘ g)`, and `g ⁻¹' univ = univ`).
  Building the `AffineMap`: `⟨fun v => c − ℓ v, −ℓ, by simp [sub_sub, ...]⟩` (`AffineMap.mk`), or `AffineMap.const` + `LinearMap.toAffineMap`.
  Route B (if affine-map plumbing is annoying): unfold `ConvexOn` (`convex_univ` Analysis/Convex/Basic.lean:89) and prove
  `(a(c−ℓv)+b(c−ℓv'))² ≤ a(c−ℓv)² + b(c−ℓv')²` from `a+b=1, a,b ≥ 0` by `nlinarith [mul_nonneg ha hb, sq_nonneg ((c−ℓv)−(c−ℓv'))]`
  (the difference is `ab((c−ℓv)−(c−ℓv'))²`). Route B is probably faster.
* Linear functions: `LinearMap.convexOn (f : E →ₗ[𝕜] β) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s f` (Function.lean:388);
  coordinate `v ↦ v j` is `LinearMap.proj j` (Algebra/Module/Pi.lean:115); scalar multiples/sums of linear maps are linear maps.
* Sums: `ConvexOn.add` (Function.lean:228) is binary; a Finset version is NOT IN MATHLIB (no `ConvexOn.sum`/`convexOn_sum` found).
  Prove `convexOn_finset_sum : (∀ i ∈ s, ConvexOn 𝕜 t (g i)) → ConvexOn 𝕜 t (fun v => ∑ i ∈ s, g i v)` by
  `Finset.sum_induction` (to_additive of `Finset.prod_induction`, Algebra/BigOperators/Group/Finset/Defs.lean:619) with
  `p := ConvexOn 𝕜 t`, `hom := ConvexOn.add`, `unit := convexOn_const 0 ht` (Function.lean:245). Mind the `f + g` vs `fun v => f v + g v` shape (`Pi.add_apply`, `funext`).
* Boxes are convex: `convex_pi` (Basic.lean:108, for `s.pi t` with each `t i` convex), `convex_Icc` (:257), `convex_Ici` (:254), `convex_Iic` (:248), `convex_univ` (:89).
* Restriction: `ConvexOn.subset` (Function.lean:121).
* Composition with the coordinate projection to make a one-variable convex function a convex function of `y`: `ConvexOn.comp_linearMap` (Function.lean:491) with `LinearMap.proj j`, or just use `convexOn_sq_affine` with `ℓ = c • LinearMap.proj j` directly.
(S each; the whole convexity side of 2.18/2.20 is ≈ 60 lines.)

### F5 — reindexing / transport (framework)
* `valueFun_equiv (e : E ≃ E') : valueFun P Q Y x = valueFun (fun x y' => P x (e.symm y')) (fun x y' => Q x (e.symm y')) (e '' Y) x`
  (argmin sets correspond under `e`; `Set.image` + `iInf` reindex). Same for `valueFunP`. (S–M)
* Boxes transport: `Equiv.piCongrLeft_preimage_univ_pi` (Data/Set/Prod.lean:919) and `Fintype.equivFin` (Data/Fintype/EquivFin.lean:80):
  a `Set.pi univ I` over `ι → ℝ` becomes a `Set.pi univ (I ∘ e.symm)` over `Fin (card ι) → ℝ`. (S)
* Polynomials transport: `MvPolynomial.rename` along `Sum.map id e` with `MvPolynomial.eval_rename` (Algebra/MvPolynomial/Rename.lean:244). (S)
*Recommendation* (§5.1): define the classes with `∃ (ι : Type) [Fintype ι], y : ι → ℝ, …` OR prove constructions for
general `ι` and apply F5 once; do NOT fight with `Fin (a + b + c)` arithmetic.

### F6 — value-function shift by a function of `x` (only the attained form is needed)
`IsLeast ((fun y => P x y) '' Θ) r → IsLeast ((fun y => P x y + g x) '' Θ) (r + g x)` (`add_le_add_right`). (S)
(An EReal `valueFun (P + g) = valueFun P + g` is NOT needed on my route; if the framework wants it, mind `⊤ + r = ⊤`, `⊥ + r = ⊥` in EReal.)

---

### L1 — Lemma 2.19 (simplified construction)  [depends: F1, F2(scalar), F3, F4]
Data: `P : MvPolynomial (Fin n) ℝ`, `Q : J → MvPolynomial (Fin n) ℝ`, `J` Fintype.
Lower variable: `y : (Unit ⊕ J) → ℝ`, write `t = y (inl ())`, `u j = y (inr j)`.
Box: `Y = Set.pi univ (Sum.elim (fun _ => univ) (fun _ => Ici 0))` — unbounded (coordinate `t`), so `IsUnboundedBox` holds even if `J = ∅`.
```
Q'(x, y) = (1 − t·P(x))² + ∑ j, (1 − Q_j(x)·u_j)²           -- polynomial in (x,y), convex in y on univ
P'(x, y) = (1 − t·P(x)) · ∏ j, (Q_j(x) · u_j)              -- polynomial in (x,y)
```
Claims, for fixed `x` (write `p = P(x)`, `q_j = Q_j(x)`):
1. `Q' x` is coordinate-separable: `Q' x y = ∑_{c : Unit ⊕ J} g_c (y c)` with `g_{inl} t = (1 − tp)²`, `g_{inr j} u = (1 − q_j u)²`.
   (In Lean: `Fintype.sum_sum_type` to split the sum over `Unit ⊕ J`, `Finset.sum_const`/`Fintype.sum_unique` for the `Unit` part.)
2. By F2: `argminSet Q' Y x = Set.pi univ A` with `A (inl) = argmin_sq_affine p` (= `univ` if `p = 0`, `{1/p}` otherwise)
   and `A (inr j) = argmin_sq_affine_Ici q_j` (`{1/q_j}` if `q_j > 0`, `Ici 0` if `q_j = 0`, `{0}` if `q_j < 0`). All factors nonempty ⇒ argmin nonempty.
   Witness: `y₀ (inl) = if p = 0 then 0 else 1/p`, `y₀ (inr j) = if 0 < q_j then 1/q_j else 0`.
3. On the argmin, `1 − t p = if p = 0 then 1 else 0` (if `p = 0` trivially `1`; else `t = 1/p`, `1 − p/p = 0` by `mul_inv_cancel₀`).
4. On the argmin, `q_j u_j = if 0 < q_j then 1 else 0` (`q_j > 0`: `u_j = 1/q_j`; `q_j = 0`: product is `0·u = 0`; `q_j < 0`: `u_j = 0`).
5. Hence `P' x y = (if p = 0 then 1 else 0) * ∏ j, (if 0 < q_j then 1 else 0) = if (p = 0 ∧ ∀ j, 0 < q_j) then 1 else 0 = S.indicator 1 x`
   (`Finset.prod_eq_one` BigOperators/Group/Finset/Basic.lean:108; `Finset.prod_eq_zero` BigOperators/GroupWithZero/Finset.lean:33; `Finset.prod_eq_zero_iff` :57; `Set.indicator_apply` = to_additive of `mulIndicator_apply`, Algebra/Notation/Indicator.lean:61).
6. Constant on nonempty argmin ⇒ F1 gives `valueFun = valueFunP = 1_S`.
7. Convexity: `convexOn_finset_sum` of `convexOn_sq_affine` with `ℓ = p • LinearMap.proj (inl ())` and `ℓ = q_j • LinearMap.proj (inr j)`.
8. Polynomiality: `Q' = (1 − X(inr t)·rename inl P)^2 + ∑ j (1 − rename inl (Q j) · X (inr (inr j)))^2` in `MvPolynomial (Fin n ⊕ (Unit ⊕ J)) ℝ`; evaluation via `eval_add/mul/pow/sum/prod/X/C` (Algebra/MvPolynomial/Eval.lean:271–299) and `eval_rename` + `Sum.elim_inl` (core).
Effort: M (mostly bookkeeping). The paper's original gadget (`w ∈ [0,1]^J, z ∈ ℝ^J, t ∈ ℝ`, with linear term `−Q_j w_j`) is also correct — verified line by line in §3 — but has `2|J|+1` variables instead of `|J|+1` and needs `argmin_linear_Icc` in addition.

### L2 — Theorem 2.18, first inclusion  [depends: L1 (as a lemma about the *data*), F1, F2, F4, F5]
Input: `f x = ∑ i, 1_{S_i}(x) p_i(x)` with `S_i = ⋃_{j : J_i} T_ij`, `T_ij` basic with data `(P_ij, Q_ijk)_{k : K_ij}`.
(Disjointness of the `T_ij` within `S_i`, and of the `S_i`, is **not** used.)
Lower variable: one L1-block per pair `(i,j)`: index type `ι := Σ (i : I) (j : J_i), (Unit ⊕ K_ij)`, `y : ι → ℝ`; box = `Set.pi univ` of the L1 intervals (unbounded as soon as some `J_i ≠ ∅`; add a dummy block `Unit` with interval `univ` and `Q`-term `0` to make this unconditional — see §5.5).
```
Q(x,y) = ∑_{(i,j)} Q'_{ij}(x, y|_{block ij})          -- still coordinate-separable: Q(x,y) = ∑_{c : ι} g_c(y c)
P(x,y) = ∑_i p_i(x) · (1 − ∏_{j : J_i} (1 − P'_{ij}(x, y|_{block ij})))
```
Proof: F2 (scalar) ⇒ argmin = product of the 1-D argmins ⇒ on the argmin each `P'_{ij}(x, ·) = 1_{T_ij}(x)` (L1 steps 3–5 applied blockwise; the block restriction `y|_{block ij}` is `fun c => y ⟨i, j, c⟩`), so
`1 − ∏_j (1 − 1_{T_ij}(x)) = 1_{⋃_j T_ij}(x) = 1_{S_i}(x)` (product of `(1 − 1_T)` is `0` iff some `x ∈ T_ij`, else `1`: `Finset.prod_eq_zero_iff`),
hence `P(x,y) = f(x)` on the (nonempty) argmin; F1. Convexity by `convexOn_finset_sum`. Polynomiality by `eval_sum/prod/sub`.
Effort: M–L (the Sigma-indexed bookkeeping is the cost; mathematically trivial).
If the blueprint keeps the paper's route instead: it needs Prop C.1 (disjoint basic pieces within each `S_i`, R2) and `Finset.sum` of disjoint indicators (`Set.indicator_union_of_disjoint` = to_additive of `mulIndicator_union_of_disjoint`, Algebra/Group/Indicator.lean:69, iterated; a Finset-biUnion version `Set.indicator_finset_biUnion` was not found in this checkout — grep found no declaration, only possible uses — so it would be an extra lemma). My route avoids all of that.

### L3 — eq. (13)  [depends: nothing beyond topology]
Hypotheses: `S : Fin N → Set X` with `⋃ i, S i = univ`, `f` with `∀ i, ∀ x ∈ S i, f x = P i x`, each `P i` continuous, `f` lower semicontinuous. Let `I(x) = {i | x ∈ closure (S i)}`.
(a) `∃ i ∈ I(x), f x = P i x`: take `i₀` with `x ∈ S i₀` (covering), `subset_closure`.
(b) `∀ i ∈ I(x), f x ≤ P i x`. By contradiction, assume `P i x < f x`. Pick `m := (P i x + f x)/2`, so `P i x < m < f x`.
   * lsc: `LowerSemicontinuousAt` unfolds (Defs.lean:287/329) to `∀ y < f x, ∀ᶠ x' in 𝓝 x, y < f x'`; apply with `y := m`: `∀ᶠ x' in 𝓝 x, m < f x'`.
   * continuity: `∀ᶠ x' in 𝓝 x, P i x' < m` via `ContinuousAt.eventually_lt` (Topology/Order/OrderClosed.lean:702, with `g := const m`) or `Filter.Tendsto.eventually_const_lt`-style lemma (OrderClosed.lean:237 is `eventually_const_lt`; the `lt_const` twin exists by duality).
   * closure: `mem_closure_iff_frequently` (Topology/Neighborhoods.lean:278): `∃ᶠ x' in 𝓝 x, x' ∈ S i`.
   * combine: `Filter.Frequently.and_eventually` (Order/Filter/Basic.lean:800) twice, then `Filter.Frequently.exists` (:809): get `x' ∈ S i` with `P i x' < m < f x' = P i x'`, contradiction (`lt_irrefl`).
No sequences, no first countability, no `Fin n → ℝ` specifics; works in any topological space with `P i` continuous into ℝ.
Effort: S. (Needs: `MvPolynomial.continuous_eval` Topology/Algebra/MvPolynomial.lean:31 for `P i = eval · (p i)`.)
Remark: lsc is genuinely needed (`f = 1_{x ≤ 0}` on ℝ: `I(0) = {both}`, `min = 0 ≠ f(0) = 1`).

### L4 — sign normalisation without growth bounds  [depends: nothing]
For polynomials `p_i`, define `g := C (1/4) + ∑ i, (p i)^2` (a polynomial). Then `∀ i x, eval x (p i) − eval x g ≤ 0`,
because `a ≤ a² + 1/4` (`nlinarith [sq_nonneg (a − 1/2)]`) and `a² ≤ ∑_k (p_k x)²` (`Finset.single_le_sum` with `sq_nonneg`).
`g` is continuous (`MvPolynomial.continuous_eval`), so `f − g` is lsc when `f` is (`LowerSemicontinuous.add` Topology/Semicontinuity/Basic.lean:540 with `Continuous.lowerSemicontinuous` :258 applied to `−g`; the file's `add` needs `[LinearOrder γ] [OrderTopology γ] [ContinuousAdd γ]`, fine for ℝ).
This replaces the paper's `B + ‖x‖^N` (Prop 2.5 / "similar to Thm 2.15"), which is unnecessary here because the pieces are polynomials. The same trick works in Thm 2.15's proof wherever a polynomial upper bound of finitely many polynomials is needed — but there the bound is for a general semialgebraic `f`, which is Prop 2.5 territory (other agent).
Effort: S.

### L5 — the z-gadget facts  [depends: F3]
For `c : K → ℝ` (values `c k = eval x (R i j k)`), the problem `min_{z ∈ Icc 0 1 ^ K} −∑ k, c k * z k` has argmin `Set.pi univ (fun k => argmin_linear_Icc (c k))` (F2 scalar). Facts used (and only these):
(Z1) `∀ z ∈ argmin, 0 ≤ ∏ k, z k ≤ 1` (`Finset.prod_nonneg` Algebra/Order/BigOperators/GroupWithZero/Finset.lean:34; `Finset.prod_le_one₀` :81);
(Z2) if `∃ k, c k < 0` then `∀ z ∈ argmin, ∏ k, z k = 0` (`Finset.prod_eq_zero` with the forced coordinate `z k = 0`);
(Z3) if `∀ k, 0 ≤ c k` then `(fun _ => 1) ∈ argmin` and `∏ k, 1 = 1` (`Finset.prod_const_one`/`Finset.prod_eq_one`).
The exact description (15) of the *set* of products (`{0}` / `[0,1]` / `{1}`) is never needed. Effort: S.

### L6 — simplex facts  [depends: F3-style one-liners]
Selector problem: `min_{s ∈ Icc 0 1 ^ (I×J)} (1 − ∑ s)²`. With `Nonempty (I × J)`:
(S1') argmin `= {s | (∀ ij, 0 ≤ s ij ≤ 1) ∧ ∑ s = 1} = stdSimplex ℝ (I × J)` (`stdSimplex` Analysis/Convex/StdSimplex.lean:40: `{f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}`; the `≤ 1` part is implied by nonnegativity and the sum; proof: `(1 − ∑ s)² ≥ 0` with equality iff `∑ s = 1`, and `∑ s = 1` is attainable at a vertex `Pi.single ij₀ 1`/`fun ij => if ij = ij₀ then 1 else 0` (`Finset.sum_ite_eq'`, to_additive of `prod_ite_eq'`, BigOperators/Group/Finset/Piecewise.lean:153)).
(S2') convex combination bound: for `s ∈ stdSimplex` and `a : I × J → ℝ` with `∀ ij, m ≤ a ij`: `m ≤ ∑ ij, s ij * a ij`
   (`∑ s ij * a ij ≥ ∑ s ij * m = m * ∑ s ij = m`; `Finset.sum_le_sum`, `mul_le_mul_of_nonneg_left`, `Finset.mul_sum`).
(S3') vertex evaluation: `∑ ij, (if ij = ij₀ then 1 else 0) * a ij = a ij₀` (`Finset.sum_ite_eq'`).
Effort: S.

### L7 — Theorem 2.20 core (S4)  [depends: F0, F2(Prod + scalar), F4, F6, L4, L5, L6]
Step 0 (normalise). Put `g` from L4, `p'_i := p_i − g`, `f' := f − g`. The hypothesis `IsLeast {p_i(x) | x ∈ C_i} (f x)` is invariant under subtracting `g(x)` from everything, so WLOG `∀ i x, p_i(x) ≤ 0` and then also `f(x) ≤ 0` (as `f(x) = p_{i*}(x)` for some `i*`). At the end add `g(x)` back to `P` (F6).
Step 1 (variables). `s : I × J → ℝ` in `Icc 0 1`, `z : I × J × K → ℝ` in `Icc 0 1` (Table 3). Box bounded.
```
Q(x,(s,z)) = (1 − ∑_{ij} s_ij)² + ∑_{ij} ( −∑_k R_ijk(x) · z_ijk )
P(x,(s,z)) = ∑_{ij} p_i(x) · s_ij · ∏_k z_ijk
```
Step 2 (argmin). F2 (Prod version) splits `Θ(x) = Θ_s × Θ_z`; L6 gives `Θ_s = stdSimplex`; F2 (scalar) + L5 describe `Θ_z` coordinatewise. `Θ(x) ≠ ∅`.
Step 3 (lower bound). For `(s,z) ∈ Θ(x)` set `a_ij := p_i(x) ∏_k z_ijk`. Claim `f(x) ≤ a_ij` for every `ij`:
   * if `x ∈ C_ij` (all `R_ijk(x) ≥ 0`): `∏ z ∈ [0,1]` (Z1) and `p_i(x) ≤ 0` ⇒ `a_ij ≥ p_i(x)` (`mul_le_of_le_one_right`-type: `p ≤ p·t` for `p ≤ 0, t ≤ 1`), and `p_i(x) ≥ f(x)` by hypothesis (`x ∈ C_ij ⊆ C_i`);
   * if `x ∉ C_ij` (some `R_ijk(x) < 0`): `∏ z = 0` (Z2) ⇒ `a_ij = 0 ≥ f(x)` (since `f(x) ≤ 0`).
   Then `P(x,(s,z)) = ∑ s_ij a_ij ≥ f(x)` by (S2').
Step 4 (attained). From the hypothesis pick `i*` and `j*` with `x ∈ C_{i*j*}` and `p_{i*}(x) = f(x)`. Take `s* := vertex at (i*,j*)`, `z*_ijk := if 0 ≤ R_ijk(x) then 1 else 0`. Then `(s*,z*) ∈ Θ(x)` (`s*` in simplex; each `z*` coordinate is a 1-D minimizer by F3) and `P(x,(s*,z*)) = p_{i*}(x) · 1 · ∏_k 1 = f(x)` ((S3'), (Z3)).
Step 5. Steps 3–4 give `IsLeast ((P x) '' Θ(x)) (f(x))` for the normalised data; F6 adds `g(x)` back; F0 converts to `valueFun = f`.
Step 6 (convexity). `Q x = (sq-affine in s) + ∑_{ij} (linear in z)`: `convexOn_sq_affine` with `ℓ = ∑_{ij} LinearMap.proj ij` (as a map on the product space, compose with `LinearMap.fst`) and `LinearMap.convexOn` for each linear term (compose with `LinearMap.snd`), summed with `convexOn_finset_sum`, all on `univ`.
   If the lower variable space is a single `ι → ℝ` with `ι = (I × J) ⊕ (I × J × K)` instead of a `Prod`, use `LinearMap.proj` on `ι` directly and F2 with blocks via `Equiv.sumArrowEquivProdArrow` (Algebra/Ring/Equiv.lean:962 is the ring-equiv version; the plain `Equiv.sumArrowEquivProdArrow` lives in Logic/Equiv — use whichever the framework fixes).
Step 7 (polynomiality). `P, Q` are built from `X`, `C`, `rename inl (p i)`, `rename inl (R i j k)` by `+, *, ^2, ∑, ∏`; evaluation lemmas as in L1.
Effort: L (the longest single item; every step is elementary).

### L8 — Theorem 2.20 as stated (S5)  [depends: L3, L7, A1, A2]
Given `f ∈ PP ∩ LSC` with partition `(S_i, p_i)`:
* A1 (assumed; T–S-dependent): `IsSemialgebraic (closure (S i))`.
* A2 (assumed; Prop 2.4 = BCR Thm 2.7.2 "finiteness theorem"): a closed semialgebraic set is `⋃_{j : J} ⋂_{k : K} {x | 0 ≤ eval x (R j k)}` for some finite `J, K` and polynomials `R`.
* Uniformise indices: the paper uses one `J, K` for all `i` (eq. (14)); in Lean either use dependent `J i`, `K i j` (Sigma types in L7 — more bookkeeping) or pad: duplicate a `j` to enlarge `J_i`, append the constant polynomial `1` to enlarge `K_ij`; if `closure (S i) = ∅` (i.e. `S i = ∅`) take `J` arbitrary nonempty and `K`-condition `−1 ≥ 0`. `Nonempty I` and `Nonempty J` hold because `⋃ S_i = univ ≠ ∅` (`n` arbitrary, `Fin n → ℝ` nonempty). I recommend stating L7 with uniform `I J K` and doing the padding in L8 (S effort).
* With `C_i := closure (S i)`, L3 gives exactly the `IsLeast` hypothesis of L7 (`C_i = ⋃_j C_ij` by A2's presentation). Apply L7.
Effort: S (given L3, L7, A1, A2).
**Why A2 cannot be dodged** (task item C(3)): L7 needs, for each `i`, a set `C_i ⊇ S_i`, *presented* as a finite union of basic closed sets, with `f ≤ p_i` on `C_i`. Candidates: `cl(S_i)` (paper) or the larger `D_i := {f ≤ p_i} = ⋃_k (S_k ∩ {p_k ≤ p_i})`. `D_i` is closed (`f − p_i` lsc ⇒ `{f − p_i ≤ 0}` closed, `lowerSemicontinuous_iff_isClosed_preimage` Basic.lean:232) and semialgebraic *without* T–S (finite Boolean combination of the given basic sets and `{p_k − p_i ≤ 0}`), so `D_i` avoids A1 — but to present `D_i` (or any closed set between `S_i` and `D_i`) as a union of basic *closed* sets one still needs A2 in general: the naive "closed relaxation" of a basic set `{P=0, Q_j>0} ↦ {P=0, Q_j≥0}` can be strictly larger than the closure (`Q = x²(x−1)`: `{Q>0} = (1,∞)`, `{Q≥0} = {0} ∪ [1,∞)`) and need not lie inside `D_i`. So: **A2 is essential; A1 can be traded for the Boolean-algebra argument if one uses `D_i` instead of `cl(S_i)`** — this removes one T–S dependence from Thm 2.20. Recommended blueprint phrasing: Thm 2.20 = L7 + L3′ where L3′ says `IsLeast {p_i(x) | x ∈ D_i} (f x)` (trivial: `x ∈ D_i ↔ f x ≤ p_i x`, and `x ∈ D_{i*}` for the piece containing `x`) + A2 applied to `D_i` (closed by lsc, semialgebraic by Boolean closure (R2)). With `D_i`, even L3 is not needed! (`D_i` is closed *because* `f` is lsc — this is where lsc enters.) Both routes are recorded; the `D_i` route is strictly cheaper (drops A1 and L3). Keep L3 only if the blueprint wants eq. (13) as a stated result.

### L9 — pessimistic counterparts (S6)  [depends: framework EReal lemma]
(a) `valueFunP (−P) Q Y x = − valueFun P Q Y x`: `⨆ y ∈ Θ, ((−P x y : ℝ) : EReal) = ⨆ y ∈ Θ, −((P x y : ℝ) : EReal) = −⨅ y ∈ Θ, (P x y : EReal)`
   using `EReal.coe_neg` (Data/EReal/Operations.lean:220) and an order-anti-isomorphism lemma `−⨅ = ⨆ −` for EReal: NOT FOUND by name (`EReal.neg_iInf`/`neg_iSup` do not exist in Data/EReal or Topology/Instances/EReal; prove via `OrderIso.map_iInf` with `EReal.negOrderIso` if present, or directly by `le_antisymm` with `EReal.neg_le`/`EReal.le_neg`). (S–M for the framework.)
   For the attained forms used in this report, the statement is trivial: `IsLeast (P '' Θ) r ↔ IsGreatest ((−P) '' Θ) (−r)`.
(b) Corollaries are immediate: `f ∈ C^p_box ↔ −f ∈ C_box`; `PP`, `SA`, `CB` are closed under negation; `LSC f ↔ USC (−f)` (Mathlib: `UpperSemicontinuous` abbrev Defs.lean:317; negation lemma may need a 3-line proof: `lowerSemicontinuous_iff`/`upperSemicontinuous_iff` with `neg_lt_neg_iff`).
(c) Paper's bullet 1 ("unique minimizers") is false but harmless: for L1/L2, F1 gives `valueFun = valueFunP` directly and indeed for *any* selection `y(x) ∈ Θ(x)`.
Effort: S.

### L10 — Euclidean norm remark (S7; optional)  [depends: nothing in the main DAG]
(i) `‖·‖₂ ∈ C_cc`: `Y = closedBall 0 1` in `EuclideanSpace ℝ (Fin n)` (compact, convex, semialgebraic: `{y | ∑ y_i² ≤ 1}`), `Q(x,y) = −⟪x,y⟫` (linear ⇒ convex), `P(x,y) = ⟪x,y⟫`. Argmin: `x ≠ 0 ⇒ {x/‖x‖}` (Cauchy–Schwarz equality case: `real_inner_le_norm`, `abs_real_inner_div_norm_mul_norm_eq_one_iff`), `x = 0 ⇒ Y`; `P` constant on it with value `‖x‖` ⇒ F1. (M)
(ii) `‖·‖₂ ∉ PP` for `n ≥ 2`. Proof sketch avoiding dimension theory: let the pieces be basic sets `T = {P_T = 0 ∧ Q_j > 0}`. If `P_T ≠ 0` as a polynomial, `T ⊆ Z(P_T)` which has empty interior (a polynomial vanishing on a nonempty open set is `0`: NOT IN MATHLIB as such; obtain from analyticity — `AnalyticAt.aeval_mvPolynomial` Analysis/Analytic/Polynomial.lean:60 + identity theorem `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` (Analysis/Analytic/Uniqueness.lean; used at NumberTheory/LSeries/DirichletContinuation.lean:132) + `MvPolynomial.funext` Algebra/MvPolynomial/Funext.lean:83). The finite union of these `Z(P_T)` is `Z(∏ P_T)`, closed with empty interior, so its complement `W` is open dense; a point of `W` lies in a piece with `P_T = 0`, i.e. in the *open* set `{Q_j > 0}`; so on a nonempty open `V`, `‖x‖ = p(x)` for a polynomial `p`; hence `∑ x_i² = p²` on `V` ⇒ as polynomials (identity theorem again). Compare coefficients: `p` has degree 1, `p = ∑ a_i x_i + b`; `b = 0`; coefficient of `x_1 x_2` in `p²` is `2a_1a_2 = 0` but `a_1² = a_2² = 1`: contradiction. (M–L; needs `MvPolynomial.coeff` of a square — fiddly.) For `n = 1`, `|x| = (x ≥ 0 ? x : −x)` IS piecewise polynomial, so the paper's example needs `n ≥ 2` (not stated).
Recommendation: mention in the blueprint as an *optional remark*, not a target. Strictness of `PP ∩ LSC ⊆ C_cc` also follows from Thm 2.21 (`C_cc = SA ∩ LSC ∩ CB`) plus (ii), so (i) is not even needed for the strictness claim.

---

## 3. Errors / gaps / typos in the paper (with fixes)

1. **Lemma 2.19 (verified correct).** The construction, convexity, argmin description, and the two displayed identities are all right. Minor: the argmin is written as if `w*, z*, t*` were points but they are sets; the final "result follows" implicitly uses that `F` is constant on the product set (true: when `Q_j(x) = 0` the factor `w_j z_j Q_j(x)` is `0` for *all* free `w_j, z_j`; when `P(x) = 0` the factor `1 − tP(x)` is `1` for all `t`). Fix: state "`F(x,·)` is constant on `Θ(x)`" explicitly (F1). Simplification: drop `w` (see L1).
2. **Thm 2.18 proof, notation.** "`S_i = ∪_{j∈J}^{M} T_ij`" (garbled superscript `M`), "the `S_ij` are pairwise disjoint" should read "the `T_ij` (for fixed `i`) are pairwise disjoint", "for all `i ∈ I`" uses an undefined `I` (= `{1,…,N}`). The disjointness of the `S_i` is invoked to make the `T_ij` disjoint *across* `i` — unnecessary: only disjointness within each `S_i` is used (for `∑_j 1_{T_ij} = 1_{S_i}`), and that comes from Prop C.1 applied to `S_i` alone. With the product formula `1_{S_i} = 1 − ∏_j(1 − 1_{T_ij})` no disjointness is needed at all (L2).
3. **Thm 2.18 proof, convexity.** "`Q` is convex since it is the sum of convex functions": each `G_ij` is convex in its *own* block; as a function of the whole `y` it is convex because it is `G_ij ∘ (linear projection)`. Trivial but implicit (F4, `ConvexOn.comp_linearMap`).
4. **Thm 2.18 statement, boundary case.** If every `S_i` with `J_i ≠ ∅` … the box of the combined problem is unbounded only because some block has a `t ∈ ℝ`; since `⋃ S_i = ℝ^n ≠ ∅` some block exists. In Lean add a dummy unconstrained coordinate to avoid the case analysis (§5.5).
5. **Prop C.1 (Appendix C) proof is garbled** in the HTML (and partly in the PDF: "`H := {P_i, i = 1 ∈ I}`", "for each `T_I` is either disjoint and included in `S_i`" should be "each `T_I` is either disjoint from or included in each `S_i`"). Also the cells `T_I` use conditions `h < 0` and several equalities, which are not literally of the basic form `{P = 0, Q_j > 0}`; fix: `h < 0 ⇔ −h > 0` and `h_1 = 0 ∧ … ∧ h_r = 0 ⇔ ∑ h_l² = 0`. (R2's scope; my route for 2.18 does not use C.1.)
6. **Thm 2.20, observation 1 / eq. (13).** Correct, but the proof is omitted ("since `f` is lsc"); `I(x) ≠ ∅` must be noted (holds since the `S_i` cover). Proof supplied in L3. Also the paper's notation `\mathcal I` for `{1,…,N}` is never defined; Table 3 uses `|I|`.
7. **Thm 2.20, observation 2.** "pair integer `N`" → "even integer `N`"; the symbol `N` clashes with the number of pieces; "`r … is also an element of `𝒮`" → "of `𝒫𝒫`"; "value function equal to `h`" → "equal to `f`". The bound `max_i P_i ≤ B + ‖x‖^N` is attributed to "similar to the proof of Theorem 2.15" (which uses Prop 2.5 for semialgebraic functions) — overkill for polynomials, and in fact no growth bound is needed: subtract `g = 1/4 + ∑_i P_i²` (L4). The lsc of `r = f − B − ‖x‖^N` (needs continuity of the subtracted polynomial) is asserted without comment — fine.
8. **Thm 2.20, eq. (14).** Uses the same `J, K` for all `i`; needs padding (L8). Requires two unstated heavy facts: closure of a semialgebraic set is semialgebraic (cited nowhere in this proof; BCR Prop 2.2.2) and Prop 2.4 (cited). Both are T–S/finiteness-theorem dependent; see L8 for how to isolate them (and how to drop the closure fact by using `D_i = {f ≤ P_i}`).
9. **Thm 2.20, display after Table 3.** "the optimal value of `(z^i)^*`" should be "`(z^i_j)^*`"; and `z^i_{jk}` cases `0 / [0,1] / 1` are sets (the HTML lost the `<` case; PDF has it right).
10. **Thm 2.20, eq. (15)/(17).** (15) describes the *set* of attainable products correctly, but (17) "`P_i ∏ z = 0` if `x ∉ ∩_k{…}`, `= P_i(x)` if `x ∈ ∩_k{…}`" is only true *after* the optimistic selection and *because* `P_i(x) ≤ 0` (in the `[0,1]` case the optimistic choice takes the product `= 1`); the sentence "Due to the optimistic nature … and (15)" says this, but (17) is used inside a further minimisation over `s`, so the order of the two minimisations (over `s` and over `z`) should be justified (they commute because `Θ = Θ_s × Θ_z` and `min` over a product is iterated `min`). L7 avoids this by proving a lower bound + attainment directly.
11. **Thm 2.20, final chain.** The step `min_{i} P_i(x) 1_{x ∈ cl S_i} = f(x)` silently uses: (a) terms with `x ∉ cl S_i` contribute `0`, and `0 ≥ f(x)` because all `P_i ≤ 0` after normalisation; (b) `I(x) ≠ ∅`. Also the display "`min_{(i,j)} P_i(x) 1_{∩_k…} = min_i P_i(x) 1_{x ∈ \overline{s_i}}`" has a typo `\overline{s_i}` → `\overline{S_i}`, and this equality needs `cl S_i = ∪_j C_ij` (eq. 14) — fine. Fixed in L7 Steps 3–4.
12. **Thm 2.20, degenerate index sets.** The simplex argument needs `I × J ≠ ∅` (else `(1 − 0)² = 1` is the min and `P ≡ 0`); `K = ∅` is harmless (`∏_∅ = 1`, `∩_∅ = ℝ^n`). Covered in L8.
13. **Section 2.3.1 remark.** "the Euclidean norm … is not piecewise polynomial" holds only for `n ≥ 2` (for `n = 1`, `|x|` is PP). No proof is given; see L10.
14. **Section 2.4, bullet 1.** "all these constructions involve unique minimizers in the lower level" is **false** for Lemma 2.19/Thm 2.18 (argmin is a whole interval/line when `Q_j(x) = 0` or `P(x) = 0`); the conclusion (pessimistic and any selection give the same value function) is nevertheless true because `P(x,·)` is constant on `Θ(x)` (F1). (For Thm 2.14, other agent.)
15. **Section 2.4, bullet 2.** "constructions can be adapted" — no adaptation is needed: `φ_p(−P,Q,Y) = −φ_o(P,Q,Y)` identically, so every pessimistic counterpart is a formal corollary (L9). The paper's claim that pessimistic value functions with compact lower level are usc is the mirror of Cor 2.9 (also a corollary of L9 + Cor 2.9 applied to `−P`).
16. **Def 2.16 / eq. (11).** The display defines `𝒞_boxtype` with "`φ = h`" but the inner braces are typeset as `\begin{array}{c}…\end{array}` with a stray "`\text{ \texttt{boxtype}}`"; harmless. Whether "convex w.r.t. `y`" means on `ℝ^m` or on `𝒴` is not specified (§5.3).
17. **Theorem 2.20, second inclusion** "was already justified in Theorem 2.15" — actually in the paragraph before Thm 2.15 (Prop 2.6 + Cor 2.9). Cosmetic.

---

## 4. Mathlib inventory

| Need | Declaration | File:line | Note |
|---|---|---|---|
| sum of two convex functions | `ConvexOn.add` | Mathlib/Analysis/Convex/Function.lean:228 | shape `f + g` (Pi add) |
| finite sum of convex functions | NOT IN MATHLIB | — | prove via `Finset.sum_induction` (to_additive of `Finset.prod_induction`, Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:619) + `ConvexOn.add` + `convexOn_const` |
| constant function convex | `convexOn_const` | Function.lean:245 | |
| linear map convex | `LinearMap.convexOn` | Function.lean:388 | needs `Convex 𝕜 s` |
| composition with affine map | `ConvexOn.comp_affineMap` | Function.lean:974 | result on `g ⁻¹' s` |
| composition with linear map | `ConvexOn.comp_linearMap` | Function.lean:491 | |
| restrict convexity to subset | `ConvexOn.subset` | Function.lean:121 | |
| `x ↦ x^2` convex on `univ` | `Even.convexOn_pow` | Mathlib/Analysis/Convex/Mul.lean:159 | `ConvexOn 𝕜 univ fun x => x ^ n`, `hn : Even n` |
| `x ↦ x^n` convex on `Ici 0` | `convexOn_pow` | Mul.lean:155 | not needed on my route |
| `ConvexOn.pow` | `ConvexOn.pow` | Mul.lean:146 | needs nonneg values; not needed |
| identity convex | `convexOn_id` | Function.lean:85 | |
| scalar multiple | `ConvexOn.smul` | Function.lean:944 | `0 ≤ c` |
| products of convex sets | `convex_pi` | Mathlib/Analysis/Convex/Basic.lean:108 | `s.pi t` |
| intervals convex | `convex_Icc`, `convex_Ici`, `convex_Iic`, `convex_univ` | Basic.lean:257, :254, :248, :89 | |
| coordinate projection as linear map | `LinearMap.proj` | Mathlib/Algebra/Module/Pi.lean:115 | |
| coordinate projection as affine map | `AffineMap.proj` | Mathlib/LinearAlgebra/AffineSpace/AffineMap.lean:661 | |
| standard simplex | `stdSimplex`, `convex_stdSimplex` | Mathlib/Analysis/Convex/StdSimplex.lean:40, :49 | `{f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}` |
| argmin notion | `IsMinOn`, `isMinOn_iff` | Mathlib/Order/Filter/Extr.lean:112, :129 | optional; baseline uses explicit set |
| argmin of separable sum = product | NOT IN MATHLIB | — | F2 (also no `IsMinOn` pi lemma found) |
| lower semicontinuity (abbrev) | `LowerSemicontinuous`, `LowerSemicontinuousAt` | Mathlib/Topology/Semicontinuity/Defs.lean:293, :287 | now `abbrev` over `Semicontinuous (· < ·)`-style relation; unfold lemmas at :329/:333 |
| upper semicontinuity | `UpperSemicontinuous` | Defs.lean:317 | |
| lsc ⇔ sublevel sets closed | `lowerSemicontinuous_iff_isClosed_preimage` | Mathlib/Topology/Semicontinuity/Basic.lean:232 | for `D_i` route |
| lsc + lsc | `LowerSemicontinuous.add` | Basic.lean:540 | `[LinearOrder γ] [OrderTopology γ] [ContinuousAdd γ]` |
| finite sum lsc | `lowerSemicontinuous_sum` | Basic.lean:567 | |
| continuous ⇒ lsc | `Continuous.lowerSemicontinuous` | Basic.lean:258 | |
| lsc attains min on compact | `LowerSemicontinuousOn.exists_isMinOn` | Basic.lean:77 | not needed on my route (min is explicit) |
| closure via frequently | `mem_closure_iff_frequently` | Mathlib/Topology/Neighborhoods.lean:278 | |
| closure via nhds | `mem_closure_iff_nhds` | Mathlib/Topology/ClusterPt.lean:301 | alternative |
| sequences (not needed) | `mem_closure_iff_seq_limit` | Mathlib/Topology/Sequences.lean:108 | needs `FrechetUrysohnSpace` |
| frequently ∧ eventually | `Filter.Frequently.and_eventually`, `Filter.Eventually.and_frequently`, `Filter.Frequently.exists`, `Filter.Frequently.mono`, `Filter.Eventually.and` | Mathlib/Order/Filter/Basic.lean:800, :805, :809, :796, :657 | |
| continuous ⇒ eventually below a constant | `ContinuousAt.eventually_lt` | Mathlib/Topology/Order/OrderClosed.lean:702 | use `g := fun _ => m` |
| tendsto ⇒ eventually above a constant | `Filter.Tendsto.eventually_const_lt` | OrderClosed.lean:237 | the `lt_const` twin by duality |
| eventually above a constant in nhds | `eventually_gt_nhds` | OrderClosed.lean:227 | |
| polynomial evaluation continuous | `MvPolynomial.continuous_eval` | Mathlib/Topology/Algebra/MvPolynomial.lean:31 | `Continuous fun x => eval x p` |
| eval lemmas | `MvPolynomial.eval_C/eval_X/eval_add/eval_mul/eval_pow/eval_sum/eval_prod` | Mathlib/Algebra/MvPolynomial/Eval.lean:271, 275, 286, 289, 292, 295, 299 | |
| eval of rename | `MvPolynomial.eval_rename` | Mathlib/Algebra/MvPolynomial/Rename.lean:244 | `eval g (rename k p) = eval (g ∘ k) p` |
| polynomial extensionality (all points) | `MvPolynomial.funext` | Mathlib/Algebra/MvPolynomial/Funext.lean:83 | only for L10 |
| polynomial analytic | `AnalyticAt.aeval_mvPolynomial` | Mathlib/Analysis/Analytic/Polynomial.lean:60 | only for L10 |
| identity theorem | `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` | Mathlib/Analysis/Analytic/Uniqueness.lean (used at NumberTheory/LSeries/DirichletContinuation.lean:132) | only for L10 |
| `Sum.elim` on `inl` | `Sum.elim_inl` | Lean core (used e.g. Mathlib/FieldTheory/AxGrothendieck.lean:163) | not greppable in Mathlib source |
| indicator | `Set.indicator_apply`, `Set.indicator_of_mem`, `Set.indicator_of_notMem` | to_additive of `Set.mulIndicator_apply` (Mathlib/Algebra/Notation/Indicator.lean:61), `mulIndicator_of_mem` (:67), `mulIndicator_of_notMem` | |
| indicator of disjoint union | `Set.indicator_union_of_disjoint` | to_additive of `mulIndicator_union_of_disjoint`, Mathlib/Algebra/Group/Indicator.lean:69 | only on paper's route |
| indicator of finite disjoint union | `Set.indicator_finset_biUnion` | NOT FOUND (no declaration line in this checkout) | only on paper's route |
| product = 1 / = 0 | `Finset.prod_eq_one`, `Finset.prod_eq_zero`, `Finset.prod_eq_zero_iff` | Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:108; Mathlib/Algebra/BigOperators/GroupWithZero/Finset.lean:33, :57 | |
| product bounds | `Finset.prod_nonneg`, `Finset.prod_le_one₀` | Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean:34, :81 | |
| sum monotone / nonneg | `Finset.sum_le_sum`, `Finset.sum_nonneg` | to_additive of `Finset.prod_le_prod` (Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:121, `@[to_additive (attr := gcongr)]`), `Finset.one_le_prod` (:162, `@[to_additive sum_nonneg]`) | unprimed names in this checkout |
| single term ≤ sum | `Finset.single_le_sum` | to_additive of `Finset.single_le_prod` (same file :276; `single_le_prod'` is a deprecated alias :283) | for L4; needs `∀ i ∈ s, 0 ≤ f i` |
| sum after updating one coordinate | `Finset.sum_update_of_mem` | to_additive of `prod_update_of_mem`, Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:247 | F2 |
| split term off a sum | `Finset.add_sum_erase` | to_additive of `mul_prod_erase`, Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:773 | F2 alternative |
| sums over `α ⊕ β`, `Σ` | `Fintype.sum_sum_type`, `Finset.sum_sigma` | to_additive of `Fintype.prod_sum_type` (Mathlib/Data/Fintype/BigOperators.lean:268), `Finset.prod_sigma` (Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean:38) | L1/L2 bookkeeping |
| `∏ 1 = 1` | `Finset.prod_const_one` | Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:391 | (Z3) |
| `p ≤ p·t` for `p ≤ 0 ≤ t ≤ 1` | — | `nlinarith [mul_nonneg (neg_nonneg.2 hp) (sub_nonneg.2 ht)]` (`mul_le_of_le_one_right'` Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:373 is the monoid version for `0 ≤ a`, wrong sign here) | L7 Step 3 |
| eval of subtraction | `MvPolynomial.eval_sub` | Mathlib/Algebra/MvPolynomial/CommRing.lean:163 | |
| `Sum.elim x y ∘ Sum.inl = x` | `Sum.elim_comp_inl` | Lean core (`Init`), not present in Mathlib source; use `simp` or `rfl` | F5/5.8 |
| EReal coercion of negation | `EReal.coe_neg` | Mathlib/Data/EReal/Operations.lean:220 | L9(a) |
| sum with `ite` | `Finset.sum_ite_eq'` | to_additive of `prod_ite_eq'`, Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:153 | vertex evaluation |
| single-point sum | `Finset.sum_eq_single` | to_additive of `prod_eq_single`, Finset/Basic.lean:355 | |
| finite min attained | `Finset.exists_min_image` | to_dual of `Finset.exists_max_image`, Mathlib/Data/Finset/Max.lean:386 | if a `Finset.inf'` formulation is used |
| `inf'` bounds | `Finset.inf'_le`, `Finset.exists_mem_eq_inf'` | to_dual of `le_sup'` (Mathlib/Data/Finset/Lattice/Fold.lean:561, attr `@[to_dual inf'_le]`), `exists_mem_eq_sup'` (:758) | ditto |
| `Set.pi` membership | `Set.mem_pi`, `Set.mem_univ_pi` | Mathlib/Data/Set/Operations.lean:281, :283 | |
| update a coordinate | `Function.update_self`, `Function.update_of_ne` | Mathlib/Logic/Function/Basic.lean:644, :648 | F2 |
| reindex pi sets | `Equiv.piCongrLeft_preimage_univ_pi`, `Equiv.piCongrLeft` | Mathlib/Data/Set/Prod.lean:919; Mathlib/Logic/Equiv/Basic.lean:846 | F5 |
| finite type ≃ `Fin` | `Fintype.equivFin` | Mathlib/Data/Fintype/EquivFin.lean:80 | F5 |
| curry a Sigma-indexed pi | `Equiv.piCurry` | Mathlib/Logic/Equiv/Basic.lean:169 | F5 (blocks) |
| `biInf` of a constant | `biInf_const` | to_dual of `biSup_const`, Mathlib/Order/CompleteLattice/Basic.lean:425 | F1 |
| `iInf_const`, `iInf_congr` | to_dual of `iSup_const` (Mathlib/Order/Bounds/Basic.lean:931), `iSup_congr` (CompleteLattice/Basic.lean:141) | | |
| `IsLeast` ⇒ `sInf` | `IsLeast.csInf_eq` | to_dual of `IsGreatest.csSup_eq`, Mathlib/Order/ConditionallyCompletePartialOrder/Basic.lean:71 | alternative to F0's `le_antisymm` |
| `IsLUB.iSup_eq` | `IsLUB.iSup_eq` | Mathlib/Order/Bounds/Basic.lean:900 | dual `IsGLB.iInf_eq` |
| EReal coercion order | `EReal.coe_le_coe_iff`, `EReal.coe_lt_coe_iff`, `EReal.coe_eq_coe_iff` | Mathlib/Data/EReal/Basic.lean:55, :61, :67 | |
| EReal `−⨅ = ⨆ −` | NOT FOUND (`EReal.neg_iInf`/`neg_iSup` absent) | — | L9(a); prove via order anti-iso or `le_antisymm` |
| `a ≤ a² + 1/4` | — | `nlinarith [sq_nonneg (a - 1/2)]`; `sq_nonneg` Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean:608 | L4 |
| `IsCompact.exists_isMinOn` | | Mathlib/Topology/Order/Compact.lean:255 (brief) | not needed on my route |
| semialgebraic sets, closure semialgebraic, finiteness theorem | NOT IN MATHLIB | — | A1, A2 assumed (A1 avoidable via `D_i`) |

---

## 5. Lean encoding decisions and pitfalls

5.1 **Lower-variable index type.** The constructions index coordinates by `Unit ⊕ J`, `Σ i j, (Unit ⊕ K_ij)`, `(I×J) ⊕ (I×J×K)`. Forcing `Fin m` from the start means `Fin (1 + |J|)` casts everywhere. Recommendation: state the classes with `y : Fin m → ℝ` (baseline) but prove the constructions for `y : ι → ℝ`, `[Fintype ι] [DecidableEq ι]`, and transport once with F5 (`Fintype.equivFin`, `Equiv.piCongrLeft_preimage_univ_pi`, `MvPolynomial.rename`). Alternatively define the classes with an existentially quantified `Fintype ι` — then F5 is unnecessary, and nothing in the paper distinguishes the two (I prefer this).
5.2 **Value functions**: use the attained form `IsLeast ((fun y => P x y) '' argminSet Q Y x) (f x)` as the *conclusion* of every construction lemma, then F0 to get the EReal `valueFun` statement. This sidesteps all EReal arithmetic in Section 2.3, including the shift lemma (F6) and `−⨅ = ⨆ −` (L9 attained form).
5.3 **Convexity hypothesis in Def. 2.16**: use `∀ x, ConvexOn ℝ Set.univ (fun y => Q x y)` (the strongest reading ⇒ smallest class ⇒ strongest inclusion theorems 2.18/2.20; `C ⊆ SA` is insensitive). Note Mathlib's `ConvexOn 𝕜 s f` bundles `Convex 𝕜 s`.
5.4 **Boxes**: for the constructions, `Set.pi Set.univ I` with `I : ι → Set ℝ` and a predicate `IsIntervalLike (I c)` (one of `Icc/Ici/Iic/univ`); bounded = all `Icc`. `[0,1]^J × ℝ^J × ℝ` or `ℝ × [0,∞)^J` are legal unbounded boxes (paper line 184). If the framework models boxes with `a b : ι → EReal`, map `Ici 0 ↦ (0, ⊤)`, `univ ↦ (⊥, ⊤)`.
5.5 **Unboundedness must be witnessed**: L2's box is unbounded only via some `t`-coordinate; add a dummy coordinate `d : Unit` with `I d = univ` and `Q`-term `0` (argmin of the constant `0` on `univ` is `univ`, nonempty; `P` ignores `d`). With that, `IsUnboundedBox` is immediate and `C_bounded ⊆ C_unbound` also follows (dummy coordinate with `Q`-term `d²`, argmin `{0}`); the paper never states the latter but Table 4 implicitly orders the classes.
5.6 **Decidability**: `Set.indicator`, `if 0 < q then … else …`, `Function.update` need `Classical` / `DecidableEq ι`; open `Classical` in the construction files.
5.7 **`Finset.sum` over `Unit ⊕ J`**: `Fintype.sum_sum_type`, `Fintype.sum_unique`; over `Σ`-types: `Fintype.sum_sigma`. Products likewise. These are routine but verbose; keep coordinates scalar so F2 is applied once.
5.8 **`MvPolynomial` evaluation of the constructed polynomials**: build `P, Q` with `MvPolynomial.rename Sum.inl` for upper-level polynomials and `X (Sum.inr c)` for lower variables; `eval (Sum.elim x y) (rename inl p) = eval x p` by `eval_rename` + `Sum.elim_comp_inl` (core/Mathlib `Sum.elim_comp_inl`); keep a `simp` set `[eval_add, eval_mul, eval_pow, eval_sum, eval_prod, eval_X, eval_C, eval_rename, Sum.elim_inl, Sum.elim_inr]`.
5.9 **Semicontinuity API changed**: `LowerSemicontinuous` is now an `abbrev` (Defs.lean:293) over a generic relation; use the `_iff` unfolding lemmas (`lowerSemicontinuousAt_iff` Defs.lean:329: `∀ y < f x, ∀ᶠ x' in 𝓝 x, y < f x'`). Do not rely on `LowerSemicontinuous` being a `def` you can `intro` through without `rw`.
5.10 **`IsLeast` with `Finset`-indexed families**: express `min_{i ∈ I(x)} p_i(x)` as `IsLeast {r | ∃ i, x ∈ C i ∧ r = eval x (p i)} (f x)`; avoid `Finset.inf'` (needs a nonemptiness proof term threaded everywhere).
5.11 **`f ≤ 0` after normalisation** is a consequence, not a hypothesis: derive it from the `IsLeast` witness.
5.12 **EReal pitfalls** (only if the framework insists on EReal statements): `⊤ + r = ⊤`, `⊥ + r = ⊥`, `−⊤ = ⊥`; `iInf` over an empty `Θ` is `⊤`, matching the paper's `φ_o = +∞`, and `⨆ = ⊥` matching `φ_p = −∞` — consistent with L9(a).

---

## 6. Alternatives considered

* **Paper's Lemma 2.19 gadget** (`w, z, t`): correct; rejected in favour of the `u ∈ [0,∞)` gadget (half the variables, no linear term, one fewer 1-D argmin lemma). Both are fine if the framework prefers to match the paper literally — the proof structure is identical.
* **Prop C.1 route for Thm 2.18**: rejected; `1 − ∏(1 − 1_T)` removes the need for disjoint decompositions and for any indicator-of-disjoint-union lemma, and makes the theorem hold for arbitrary (overlapping) families `(S_i)`. Prop C.1 is still cheap if R2 wants it for the semialgebraic-set theory.
* **Growth bound `B + ‖x‖^N`** (paper) vs `g = 1/4 + ∑ P_i²`: the latter needs zero analysis; rejected the former.
* **Computing the exact argmin sets** of the `z`-gadget (eq. (15)) and of the product: unnecessary; lower bound + explicit minimiser suffice.
* **Choice of closed sets in Thm 2.20**: `cl(S_i)` (paper; needs A1 + A2 + L3) vs `D_i = {f ≤ P_i}` (needs only A2 + lsc ⇒ closed + Boolean closure of semialgebraic sets). `D_i` is cheaper and recommended; keep `cl(S_i)` only if eq. (13) is wanted as a stated result. No choice avoids A2 (argument in L8).
* **Using `IsMinOn`/`IsCompact.exists_isMinOn`** to get attainment: unnecessary, the minimisers are explicit.
* **Sequential proof of (13)**: replaced by the filter proof (no `FrechetUrysohnSpace`, shorter).
* **Pessimistic constructions adapted by hand** (task item E): unnecessary thanks to `φ_p(−P) = −φ_o(P)`.

---

## 7. Effort / risk per lemma

| Item | Effort | Assume or prove | Risk |
|---|---|---|---|
| F0, F1 | S | prove | none |
| F2 (Prod and pi versions) | S–M | prove | `Function.update` + sum splitting bookkeeping |
| F3 (three 1-D argmins) | S | prove | none |
| F4 (convexity toolkit incl. `convexOn_finset_sum`, `convexOn_sq_affine`) | S–M | prove | affine-map plumbing (use Route B) |
| F5 (transport along equivs) | M | prove | only if classes are fixed to `Fin m`; avoid by quantifying over `Fintype ι` |
| F6 | S | prove | none |
| L1 (Lemma 2.19) | M | prove | polynomial-encoding boilerplate |
| L2 (Thm 2.18 ⊆) | M–L | prove | Sigma-indexed coordinates; mitigated by scalar F2 |
| Prop 2.6 (`C_unbound ⊆ SA`) | — | R2 (T–S assumed) | — |
| L3 (eq. 13) | S | prove | none |
| L4 | S | prove | none |
| L5, L6 | S | prove | none |
| L7 (Thm 2.20 core) | L | prove | longest; all elementary |
| A1 (closure semialgebraic) | — | assume (or avoid via `D_i`) | T–S |
| A2 (Prop 2.4 finiteness theorem) | XL if proved | **assume** | real algebraic geometry (BCR 2.7.2, Łojasiewicz) |
| L8 (Thm 2.20 as stated) | S | prove from L7 + A2 (+A1 or `D_i`) | padding of index sets |
| L9 (pessimistic) | S (attained form) / M (EReal form) | prove | missing `EReal` `neg_iInf` lemma |
| L10 (norm ∉ PP) | M–L | optional | `MvPolynomial.coeff` of squares; polynomial-vanishing-on-open-set lemma NOT IN MATHLIB |

---

## 8. Open questions for the auditor

1. Does the framework fix lower variables to `Fin m → ℝ` in the *class definitions*? If so F5 is mandatory; I recommend `∃ (ι : Type) [Fintype ι]` instead (equivalent classes, far less friction).
2. Convexity in Def 2.16: on `univ` (my recommendation) or on `Y`? Any theorem in the paper that needs the weaker reading?
3. Should eq. (13) (L3) be a stated blueprint result, or do we take the `D_i = {f ≤ P_i}` route for Thm 2.20 (which drops A1 and L3)? I recommend the `D_i` route and keeping L3 as an optional remark.
4. How is A2 to be stated in the blueprint — as a Lean `axiom`-like hypothesis of Thm 2.20 ("given a closed-basic presentation of each closed semialgebraic set") or as an assumed lemma about `IsSemialgebraic ∧ IsClosed`? I propose: Theorem 2.20 core (L7) is unconditional; the paper's Thm 2.20 is `L7 + A2 + (closedness of D_i from lsc)`, with A2 an explicit named assumption shared with Thm 2.15 (which also uses Prop 2.4, for `cl(graph f)`).
5. Confirm with R2 that `IsSemialgebraic` is closed under finite ∩, ∪ and complement without T–S (needed for `D_i`), and whether R2 proves Prop C.1 (not needed by my route).
6. EReal: does the framework want `valueFunP (−P) Q Y = −valueFun P Q Y` in EReal (needs a `−⨅ = ⨆ −` lemma for EReal, not found by name), or is the attained form enough? For all results in my scope the attained form suffices.
7. Is `C_bounded ⊆ C_unbound` (dummy-variable trick, §5.5) wanted in the blueprint? The paper does not state it.
8. The `Section 2.3.1` strictness remark: include L10 as optional, or omit?
