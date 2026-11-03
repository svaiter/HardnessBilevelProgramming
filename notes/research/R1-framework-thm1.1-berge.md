# R1 report: core framework, Theorem 1.1 (Whitney/smooth bilevel), Berge-type results (Thm 2.8, Cor 2.9, Rem 2.10), pessimistic counterparts

Paper: Bolte–Lê–Pauwels–Vaiter, arXiv:2407.12372v2. Sections read line by line: §1 ((BP), (BP-O), (BP-P), Thm 1.1),
§2.1 (Def 2.7, Thm 2.8, Cor 2.9, Rem 2.10 and the dom(φ) discussion before Prop 2.6), Def 2.11, Def 2.16, eq. (18),
§2.4, Appendix A (Thm A.1, Prop A.2, proof of Thm 1.1, Discussion). Mathlib = local checkout at
`<SCRATCH>/mathlib/mathlib4/Mathlib` (commit 1df8067a); every declaration cited below was located by grep, file:line given.
All Lean below is *proposed* (no toolchain available); names are suggestions for the blueprint.

Conventions used throughout this report:
- `X := Fin n → ℝ` (upper variable), `Y := Fin m → ℝ` (lower variable); most lemmas are stated for arbitrary types `X Y` and
  specialised later — this is free generality and makes the lemmas reusable by R2–R5.
- `open scoped ContDiff` so that `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)` (C^∞) and `ω = (⊤ : WithTop ℕ∞)` (analytic).
  **Pitfall:** `ContDiff ℝ ⊤ f` now means *analytic*; C^∞ must be written `ContDiff ℝ ∞ f`
  (`Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:118-120`).

---------------------------------------------------------------------------------------------------------------------

## 1. Scope: statements covered

### 1.1 Framework definitions (used by every other agent)

```lean
namespace Bilevel
variable {X Y : Type*}

/-- Θ(x): minimisers of `Q x` over `S`. -/
def argminSet (Q : X → Y → ℝ) (S : Set Y) (x : X) : Set Y :=
  {y | y ∈ S ∧ ∀ y' ∈ S, Q x y ≤ Q x y'}

/-- optimistic value function (BP-O); `⊤` if Θ(x)=∅, `⊥` if `P x` unbounded below on Θ(x). -/
noncomputable def valueFun (P Q : X → Y → ℝ) (S : Set Y) (x : X) : EReal :=
  ⨅ y ∈ argminSet Q S x, ((P x y : ℝ) : EReal)

/-- pessimistic value function (BP-P); `⊥` if Θ(x)=∅. -/
noncomputable def pvalueFun (P Q : X → Y → ℝ) (S : Set Y) (x : X) : EReal :=
  ⨆ y ∈ argminSet Q S x, ((P x y : ℝ) : EReal)

/-- polynomial data, baseline encoding of the brief -/
noncomputable def polyFun {n m : ℕ} (p : MvPolynomial (Fin n ⊕ Fin m) ℝ) :
    (Fin n → ℝ) → (Fin m → ℝ) → ℝ :=
  fun x y => MvPolynomial.eval (Sum.elim x y) p

/-- boxes: `lo i ≤ y i ≤ hi i` with extended-real bounds; covers Icc, Ici, Iic, univ (and ∅ when lo>hi or lo=⊤…). -/
def boxSet {m : ℕ} (lo hi : Fin m → EReal) : Set (Fin m → ℝ) :=
  {y | ∀ i, lo i ≤ (y i : EReal) ∧ (y i : EReal) ≤ hi i}
def IsBox {m : ℕ} (S : Set (Fin m → ℝ)) : Prop := ∃ lo hi : Fin m → EReal, S = boxSet lo hi

def boundedBox {m : ℕ} (lo hi : Fin m → ℝ) : Set (Fin m → ℝ) := Set.pi Set.univ fun i => Set.Icc (lo i) (hi i)
def IsBoundedBox {m : ℕ} (S : Set (Fin m → ℝ)) : Prop :=
  ∃ lo hi : Fin m → ℝ, (∀ i, lo i ≤ hi i) ∧ S = boundedBox lo hi      -- `lo ≤ hi` ⇒ nonempty (needed by Cor 2.9)

/-- generic value-function class (Def 2.11 / 2.16 / eq. (18)): all are sets of EReal-valued functions. -/
def valueFunClass (n : ℕ) (boxOK : ∀ m, Set (Fin m → ℝ) → Prop)
    (lowerOK : ∀ m, MvPolynomial (Fin n ⊕ Fin m) ℝ → Prop) : Set ((Fin n → ℝ) → EReal) :=
  {h | ∃ (m : ℕ) (P Q : MvPolynomial (Fin n ⊕ Fin m) ℝ) (S : Set (Fin m → ℝ)),
        boxOK m S ∧ lowerOK m Q ∧ h = valueFun (polyFun P) (polyFun Q) S}

def convexLower {n m : ℕ} (Q : MvPolynomial (Fin n ⊕ Fin m) ℝ) : Prop :=
  ∀ x, ConvexOn ℝ Set.univ (polyFun Q x)                      -- "Q convex w.r.t. y" (Def 2.16)

def P_box     (n) := valueFunClass n (fun _ S => IsBox S)        (fun _ _ => True)   -- paper's 𝒫_unbound (see §3 item 12)
def P_bounded (n) := valueFunClass n (fun _ S => IsBoundedBox S) (fun _ _ => True)   -- 𝒫_bounded
def C_box     (n) := valueFunClass n (fun _ S => IsBox S)        (fun _ Q => convexLower Q)  -- 𝒞_unbound
def C_bounded (n) := valueFunClass n (fun _ S => IsBoundedBox S) (fun _ Q => convexLower Q)  -- 𝒞_bounded
def C_cc      (n) := valueFunClass n (fun _ S => IsCompact S ∧ Convex ℝ S ∧ IsSemialgebraic S)  -- eq. (18); `IsSemialgebraic` from R2
                                   (fun _ Q => convexLower Q)

/-- target classes (all EReal-valued) -/
def LSC (n) : Set ((Fin n → ℝ) → EReal) := {h | LowerSemicontinuous h}
def CB  (n) : Set ((Fin n → ℝ) → EReal) :=
  {h | ∀ K : Set (Fin n → ℝ), IsCompact K → ∃ M : ℝ, ∀ x ∈ K, ((-M : ℝ) : EReal) ≤ h x ∧ h x ≤ (M : EReal)}
-- `CB` forces real values (take K = {x}): lemma `CB.ne_top_ne_bot`.
-- `SA n` (extended-real semialgebraic, Def 2.2) is defined by R2.
end Bilevel
```
Pessimistic variants of the classes: same with `pvalueFun`.

### 1.2 Theorem 1.1 (as I propose to state it — a strengthening; paper's version is a corollary)

Math. Let `f : ℝⁿ → ℝ ∪ {±∞}` be lower semicontinuous with `{x | f(x) < +∞}` closed. Then there are C^∞ functions
`P, Q : ℝⁿ × ℝ³ → ℝ` such that the optimistic value function of `(P, Q, 𝒴 = ℝ³)` equals `f` everywhere.
(Paper: additionally "proper" and `f > −∞`; both are unnecessary, see §3.)

```lean
open scoped ContDiff in
theorem Bilevel.exists_smooth_of_lowerSemicontinuous {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : LowerSemicontinuous f) (hdom : IsClosed {x | f x ≠ ⊤}) :
    ∃ P Q : (Fin n → ℝ) → (Fin 3 → ℝ) → ℝ,
      ContDiff ℝ ∞ (Function.uncurry P) ∧ ContDiff ℝ ∞ (Function.uncurry Q) ∧
      valueFun P Q Set.univ = f

/-- paper's statement -/
theorem Bilevel.exists_smooth_of_lowerSemicontinuous' {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hbot : ∀ x, f x ≠ ⊥) (hproper : ∃ x, f x ≠ ⊤)     -- both unused in the proof
    (hf : LowerSemicontinuous f) (hdom : IsClosed {x | f x ≠ ⊤}) : (same conclusion)
```
Typing decision: `f : (Fin n → ℝ) → EReal` (not `WithTop ℝ`), because `valueFun` is `EReal`-valued, `EReal` has the
complete-lattice/topology/semicontinuity API we need, and the proof extends to `⊥` values for free.
Smoothness: `ContDiff ℝ ∞ (Function.uncurry P)` on the product normed space `(Fin n → ℝ) × (Fin 3 → ℝ)` (sup norms;
`ContDiff` in finite dimension does not depend on the norm choice).

Pessimistic counterpart (new, follows by negation): `f` upper semicontinuous with `{x | f x ≠ ⊥}` closed ⇒ ∃ smooth `P Q`,
`pvalueFun P Q Set.univ = f`.

### 1.3 Proposition A.2 (lsc ⇔ closed epigraph)
Mathlib: `lowerSemicontinuous_iff_isClosed_epigraph` (`Mathlib/Topology/Semicontinuity/Basic.lean:353`):
`LowerSemicontinuous f ↔ IsClosed {p : α × γ | f p.1 ≤ p.2}` for `[TopologicalSpace α] [LinearOrder γ] [TopologicalSpace γ]
[ClosedIciTopology γ]`. Applies to `γ = ℝ` and to `γ = EReal` (both have `OrderTopology`, hence `ClosedIciTopology`:
`Mathlib/Topology/Order/Real.lean:37`, `Mathlib/Topology/Order/OrderClosed.lean:449` + `@[to_dual]`). For an EReal-valued
`f` the epigraph lives in `α × EReal`; the *real* epigraph `{(x,r) : α × ℝ | f x ≤ ↑r}` is its preimage under the continuous
map `Prod.map id Real.toEReal`, hence closed (lemma A2 below). Only the direction lsc ⇒ closed is needed.

### 1.4 Theorem 2.8 (simplified Berge) and Corollary 2.9
Math (clarified). `X, Y` topological spaces, `Y` Hausdorff, `P Q : X → Y → ℝ` jointly continuous, `S ⊆ Y` compact **and
nonempty**. Then (i) the graph `{(x,y) | y ∈ Θ(x)}` is closed (⇒ outer semicontinuity, Def 2.7); (ii) `Θ(x)` is nonempty
and compact; (iii) `P(x,·)` attains its min on `Θ(x)`, so `φ(x) = P(x,y*) ∈ ℝ`; (iv) `φ` is lsc; (v) `φ` is bounded on
every compact `K`: `min_{K×S} P ≤ φ ≤ max_{K×S} P`.

```lean
variable [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {P Q : X → Y → ℝ} {S : Set Y}
  (hP : Continuous (Function.uncurry P)) (hQ : Continuous (Function.uncurry Q)) (hS : IsCompact S) (hne : S.Nonempty)

theorem isClosed_graph_argminSet : IsClosed {p : X × Y | p.2 ∈ argminSet Q S p.1}
theorem argminSet_nonempty (x) : (argminSet Q S x).Nonempty
theorem argminSet_isCompact (x) : IsCompact (argminSet Q S x)
theorem exists_isMinOn_argminSet (x) : ∃ y₀ ∈ argminSet Q S x, IsMinOn (P x) (argminSet Q S x) y₀
theorem valueFun_ne_top (x) : valueFun P Q S x ≠ ⊤ ;  theorem valueFun_ne_bot (x) : valueFun P Q S x ≠ ⊥
theorem lowerSemicontinuous_valueFun : LowerSemicontinuous (valueFun P Q S)
theorem valueFun_bddOn_compact {K : Set X} (hK : IsCompact K) :
    ∃ M : ℝ, ∀ x ∈ K, ((-M : ℝ) : EReal) ≤ valueFun P Q S x ∧ valueFun P Q S x ≤ (M : EReal)
```

### 1.5 Remark 2.10 (and the "⊆" half of Theorem 2.15)
`P_bounded n ⊆ LSC n ∩ CB n` (plus `⊆ SA n` from R2's Prop 2.6). Contrapositive = Remark 2.10. Also `C_bounded ⊆ C_cc ⊆ LSC ∩ CB`
(a bounded box is compact, convex, semialgebraic — the last needs R2's `IsSemialgebraic` for `Set.pi univ Icc`).

### 1.6 Section 2.4 pessimistic counterparts (what changes)
`pvalueFun P Q S = -(valueFun (fun x y => -P x y) Q S)` pointwise (lemma V8). Hence every optimistic statement transfers:
usc replaces lsc (`Continuous.comp_lowerSemicontinuous_antitone` with `g = Neg.neg : EReal → EReal`, continuous by
`Mathlib/Topology/Algebra/Ring/Real.lean:65` `instance : ContinuousNeg EReal`, antitone by `EReal.neg_strictAnti`
`Mathlib/Data/EReal/Operations.lean:253`), hypograph replaces epigraph (`upperSemicontinuous_iff_IsClosed_hypograph`,
`Basic.lean:897`), `⊥` replaces `⊤` for `Θ(x)=∅`. For the unbounded-box results the paper's remark "constructions have unique
lower-level minimisers" is a property of R3/R4's constructions, which they should record as a lemma `argminSet = {y*}`
so that `valueFun = pvalueFun` there (lemma V5').

---------------------------------------------------------------------------------------------------------------------

## 2. Proof route: DAG of lemmas (granularity for a Lean implementer)

### 2.A Basic API (file `Bilevel/Basic.lean`), all elementary

**F1 `mem_argminSet_iff`** `y ∈ argminSet Q S x ↔ y ∈ S ∧ IsMinOn (Q x) S y`. Proof: `Iff.rfl` after `isMinOn_iff`
(`Mathlib/Order/Filter/Extr.lean:129`). **F2 `argminSet_subset`**: `argminSet Q S x ⊆ S`.

**F3 `argminSet_eq_empty_iff`** `argminSet Q S x = ∅ ↔ ∀ y ∈ S, ∃ y' ∈ S, Q x y' < Q x y`. Proof: unfold, `not_le`, `Set.eq_empty_iff_forall_notMem`.
(This is the only tool needed for "no minimiser" arguments: exhibit, for each candidate, a strictly better point.)

**F4 `argminSet_eq_zeroSet`** (the "Q ≥ 0 and Q(x,y)=0 ⇒ y ∈ argmin" lemma, with its converse)
  `(∀ y ∈ S, 0 ≤ Q x y) → (∃ y₀ ∈ S, Q x y₀ = 0) → argminSet Q S x = {y ∈ S | Q x y = 0}`.
  Proof: (⊆) y minimiser ⇒ `Q x y ≤ Q x y₀ = 0` and `0 ≤ Q x y`, `le_antisymm`. (⊇) `Q x y = 0 ≤ Q x y'`.
  Half-version **F4'** `mem_argminSet_of_nonneg_of_eq_zero`: nonneg ∧ `y ∈ S` ∧ `Q x y = 0` ⇒ `y ∈ argminSet`. Used by Thms 2.12, 2.15, 2.18, 3.2.

**F5 `argminSet_prod_add`** (separability; unconditional — no boundedness/attainment needed)
  `argminSet (fun x (y : Y₁ × Y₂) => A x y.1 + B x y.2) (S₁ ×ˢ S₂) x = argminSet A S₁ x ×ˢ argminSet B S₂ x`.
  Proof: (⊆) given `(y₁,y₂)` minimiser and `y₁' ∈ S₁`: `A x y₁ + B x y₂ ≤ A x y₁' + B x y₂` (`Set.mem_prod`, `Mathlib/Data/Set/Operations.lean:231`),
  cancel (`add_le_add_iff_right`) ⇒ `y₁ ∈ argmin A`; symmetric for `B`. (⊇) `add_le_add`.
  Generalises to finite sums over blocks by induction (`Fin (k+1)` blocks), but the binary version + reindexing (F7) suffices.
  Variant **F5'** for products of nonnegative factors is *false* in general (0·anything) — do not state it; the paper's product
  constructions (Thm 2.15) go through F4 instead.

**F6 `argminSet_mul_pos` / `argminSet_add_left`**: for `c : X → ℝ`, `0 < c x` ⇒ `argminSet (fun x y => c x * Q x y) S x = argminSet Q S x`
  (`mul_le_mul_left` with positivity); `argminSet (fun x y => a x + Q x y) S x = argminSet Q S x` (`add_le_add_iff_left`).
  These are about the *lower* level; the upper-level analogues are V6/V7.

**F7 `argminSet_reindex` / `valueFun_reindex`** (block/variable reindexing; needed to apply F5 to `Fin m → ℝ`):
  for `e : Y' ≃ Y`: `argminSet (fun x y' => Q x (e y')) (e ⁻¹' S) x = e ⁻¹' argminSet Q S x` and
  `valueFun (fun x y' => P x (e y')) (fun x y' => Q x (e y')) (e ⁻¹' S) x = valueFun P Q S x`
  (proof: `Equiv.forall_congr`, `Equiv.preimage`, and `iInf` reindexing via `e.surjective`/`Equiv.iInf_comp`-style rewriting).
  Concrete equivalences for the baseline encoding: `finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)`
  (`Mathlib/Logic/Equiv/Fin/Basic.lean:224`), `Equiv.sumArrowEquivProdArrow : (α ⊕ β → γ) ≃ (α → γ) × (β → γ)`
  (`Mathlib/Logic/Equiv/Prod.lean:390`), `Fin.appendEquiv` (`Mathlib/Logic/Equiv/Fin/Basic.lean:401`).
  Recommendation to all agents: *state constructions on product types* `(Fin m₁ → ℝ) × (Fin m₂ → ℝ) × …` with `S = S₁ ×ˢ S₂ ×ˢ …`,
  prove everything there, and transport once to `Fin m → ℝ` with F7 at the very end (when the class definition demands `Fin m → ℝ`).

**F8 `argminSet_isClosed`** (`Continuous (Q x)`, `IsClosed S`) and **`argminSet_isCompact`** (`IsCompact S`):
  `argminSet Q S x = S ∩ ⋂ y' ∈ S, {y | Q x y ≤ Q x y'}`; `isClosed_biInter` (`Mathlib/Topology/Basic.lean:162`) of
  `isClosed_le (hQx) continuous_const` (`Mathlib/Topology/Order/OrderClosed.lean:444`); `IsClosed.inter`; `IsCompact.inter_right`
  (`Mathlib/Topology/Compactness/Compact.lean:86`). (For `S` compact in a T2 space `IsClosed S` is `IsCompact.isClosed`,
  `Mathlib/Topology/Separation/Hausdorff.lean:600`.)

**V1 `valueFun_eq_top_iff`** `valueFun P Q S x = ⊤ ↔ argminSet Q S x = ∅`.
  (⇐) `iInf_emptyset` (to_dual of `iSup_emptyset`, `Mathlib/Order/CompleteLattice/Basic.lean:584`).
  (⇒) if `y ∈ Θ` then `valueFun ≤ ↑(P x y) < ⊤` by `iInf₂_le` (to_dual of `le_iSup₂`, `Basic.lean:226`) and `EReal.coe_lt_top` (`Mathlib/Data/EReal/Basic.lean:266`).

**V2 `valueFun_eq_of_isMinOn`** `y₀ ∈ Θ → IsMinOn (P x) Θ y₀ → valueFun P Q S x = ↑(P x y₀)`.
  `le_antisymm (iInf₂_le y₀ hy₀) (le_iInf₂ fun y hy => EReal.coe_le_coe_iff.2 (hmin hy))` (`le_iInf₂` = to_dual of `iSup₂_le`, `Basic.lean:239`;
  `EReal.coe_le_coe_iff` `Mathlib/Data/EReal/Basic.lean:55`, protected).

**V3 `valueFun_eq_coe_iff`** (paper's dom(φ) description, §2.1 item 1; needed by R2 for Prop 2.6)
  `valueFun P Q S x = (r : EReal) ↔ (∀ y ∈ Θ, r ≤ P x y) ∧ ∀ ε > 0, ∃ y ∈ Θ, P x y < r + ε`.
  Proof: `iInf_eq_of_forall_ge_of_forall_gt_exists_lt` (to_dual of `iSup_eq_of_forall_le_of_forall_lt_exists_gt`,
  `Mathlib/Order/CompleteLattice/Basic.lean:378`, applied to the `iInf₂` seen as an `iInf` over the subtype `↥Θ` or via `iInf_subtype`-style rewriting),
  with `EReal.lt_iff_exists_real_btwn` (`Data/EReal/Basic.lean:863`) / `EReal.exists_between_coe_real` (`:448`) to pass from `w > ↑r` in EReal to a real `r + ε`.
  Note it forces `Θ ≠ ∅` (second conjunct).

**V4 `valueFun_eq_bot_iff`** `valueFun = ⊥ ↔ ∀ r : ℝ, ∃ y ∈ Θ, P x y < r`. Via `EReal.eq_bot_iff_forall_lt` (`Data/EReal/Basic.lean:438`) and
  `iInf_lt_iff`-style reasoning (`iInf_le_iff`, to_dual of `le_iSup_iff` `Order/CompleteLattice/Defs.lean:123`) + `EReal.coe_lt_coe_iff` (`:61`).

**V5 `valueFun_eq_of_const_on_argmin`** `Θ.Nonempty → (∀ y ∈ Θ, P x y = v) → valueFun = ↑v` (special case of V2). Used by Lemma 2.19 ("all minimisers yield the same value").
  **V5'** `argminSet = {y₀} → valueFun = ↑(P x y₀) ∧ pvalueFun = ↑(P x y₀)` (unique minimiser ⇒ optimistic = pessimistic; §2.4 bullet 1).

**V6 `valueFun_mul_pos`** `0 < c x → valueFun (fun x y => c x * P x y) Q S x = (c x : EReal) * valueFun P Q S x`.
  Proof by trichotomy on `valueFun P Q S x` (`EReal.rec`, `Data/EReal/Basic.lean:113`):
  `⊤`: both sides `⊤` (V1 both ways, `EReal.coe_mul_top_of_pos` `Data/EReal/Operations.lean:579`);
  `⊥`: V4 both ways (given `r`, take `r / c x`), `EReal.coe_mul_bot_of_pos` (`:615`);
  `↑r`: V3 both ways (`ε ↦ ε / c x`), `EReal.coe_mul` (`Data/EReal/Basic.lean:155`). Rated M because of EReal case bookkeeping.
  Used by Thm 2.15 (`P·(B+‖x‖^N)`) — note the paper *multiplies* the upper level, so the scaling factor must be positive, not just nonnegative.

**V7 `valueFun_add_left`** `valueFun (fun x y => a x + P x y) Q S x = (a x : EReal) + valueFun P Q S x`. Same trichotomy; `EReal.coe_add_top` (`Operations.lean:108`),
  `EReal.add_bot` (`:46`), `EReal.coe_add` (`Data/EReal/Basic.lean:310`).

**V8 `pvalueFun_eq_neg_valueFun_neg`** `pvalueFun P Q S x = -(valueFun (fun x y => -P x y) Q S x)`.
  Proof: `EReal.negOrderIso : EReal ≃o ERealᵒᵈ` (`Data/EReal/Operations.lean:295`) is an `sInfHomClass` by
  `OrderIsoClass.toCompleteLatticeHomClass` (`Mathlib/Order/Hom/CompleteLattice.lean:178`), so `map_iInf`
  (to_dual of `map_iSup`, `Order/Hom/CompleteLattice.lean:125`) turns `-(⨅ …)` into `⨆ …` in `ERealᵒᵈ`; then `EReal.coe_neg`
  (`Operations.lean:220`), `neg_neg`. Alternative hand proof: `le_antisymm` with `EReal.neg_le_neg_iff` (`:258`). S/M.

**V9 `valueFun_real_iff`** `valueFun ≠ ⊤ ∧ valueFun ≠ ⊥ ↔ Θ.Nonempty ∧ BddBelow ((P x) '' Θ)` (from V1, V4). Optional.

**Box lemmas** (`Bilevel/Box.lean`): `boundedBox_eq_boxSet : boundedBox lo hi = boxSet (fun i => ↑(lo i)) (fun i => ↑(hi i))`
  (ext; `Set.mem_univ_pi` `Mathlib/Data/Set/Operations.lean:283`, `Set.mem_Icc`, `EReal.coe_le_coe_iff`);
  `IsBoundedBox.isBox`; `IsBoundedBox.isCompact` (`isCompact_univ_pi` `Mathlib/Topology/Compactness/Compact.lean:1172` + `isCompact_Icc`
  from class `CompactIccSpace`, `Mathlib/Topology/Order/Compact.lean:53/55`); `IsBoundedBox.nonempty` (`Set.univ_pi_nonempty_iff`
  `Mathlib/Data/Set/Prod.lean:656`, `Set.nonempty_Icc` `Mathlib/Order/Interval/Set/Basic.lean:139`); `IsBoundedBox.convex`
  (`convex_pi` `Mathlib/Analysis/Convex/Basic.lean:108`, `convex_Icc` `:257`); `IsBox.isClosed` (`isClosed_le`/`isClosed_set_pi`
  `Mathlib/Topology/Constructions.lean:1127`, or directly: `boxSet lo hi = ⋂ i, (coe ∘ eval i)⁻¹' Icc (lo i) (hi i)`, closed by
  `isClosed_Icc` in EReal and `continuous_coe_real_ereal` `Mathlib/Topology/Instances/EReal/Lemmas.lean:52`); `IsBox.convex`;
  `boxSet_bot_top : boxSet ⊥ ⊤ = Set.univ`; `P_bounded ⊆ P_box`, `C_bounded ⊆ C_box`, `C_box ⊆ P_box`, `C_bounded ⊆ P_bounded` (trivial).

**Polynomial continuity** `continuous_uncurry_polyFun : Continuous (Function.uncurry (polyFun p))`:
  `MvPolynomial.continuous_eval` (`Mathlib/Topology/Algebra/MvPolynomial.lean:31`) composed with
  `(x,y) ↦ Sum.elim x y`, continuous by `continuous_pi` + `Sum.rec` on the index: `(continuous_apply i).comp continuous_fst` /
  `… continuous_snd` (or `Equiv.sumArrowEquivProdArrow` symm). S.

### 2.B Theorem 1.1

**W `exists_contDiff_zeroSet_eq`** (Whitney, Mathlib form). `E` real normed space, `[FiniteDimensional ℝ E]`, `C : Set E` closed ⇒
  `∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ ∀ p, g p = 0 ↔ p ∈ C`.
  Proof: `hC.isOpen_compl.exists_contDiff_support_eq (n := ⊤)` — `IsOpen.exists_contDiff_support_eq {n : ℕ∞} {s : Set E} (hs : IsOpen s) :
  ∃ f : E → ℝ, f.support = s ∧ ContDiff ℝ n f ∧ Set.range f ⊆ Set.Icc 0 1`
  (`Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean:83`; variables `[NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]`, lines 22–26).
  With `n = (⊤ : ℕ∞)` the coercion to `WithTop ℕ∞` is `∞` (C^∞), *not* `ω`. Then `Function.support_eq_iff`
  (to_additive of `Function.mulSupport_eq_iff`, `Mathlib/Algebra/Notation/Support.lean:54`):
  `(∀ p ∈ Cᶜ, g p ≠ 0) ∧ (∀ p ∉ Cᶜ, g p = 0)`, i.e. `g p = 0 ↔ p ∈ C`. The `[0,1]`-range is discarded.
  Instances needed: `FiniteDimensional ℝ ((Fin n → ℝ) × ℝ)` and `FiniteDimensional ℝ (Fin n → ℝ)`: `Module.Finite.prod`
  (`Mathlib/RingTheory/Finiteness/Prod.lean:46`), `Module.Finite.pi` (`Mathlib/RingTheory/Finiteness/Basic.lean:277`); normed-space instances for `Prod`/`Pi` are standard.

**A2 `isClosed_realEpigraph`** `LowerSemicontinuous f → IsClosed {p : X × ℝ | f p.1 ≤ (p.2 : EReal)}` for `f : X → EReal`.
  `hf.isClosed_epigraph` (alias at `Semicontinuity/Basic.lean:355`; `γ = EReal`, instances `OrderTopology EReal` `Topology/Order/Real.lean:37`),
  then `IsClosed.preimage (continuous_id.prodMap continuous_coe_real_ereal)` (`Mathlib/Topology/Continuous.lean:188`,
  `Continuous.prodMap` `Mathlib/Topology/Constructions/SumProd.lean:178`, `continuous_coe_real_ereal` `Topology/Instances/EReal/Lemmas.lean:52`);
  the preimage is definitionally the real epigraph (`Prod.map id coe p = (p.1, ↑p.2)`).

**T0 construction.** `h := W (epi_ℝ f)` on `(Fin n → ℝ) × ℝ`; `g := W {x | f x ≠ ⊤}` on `Fin n → ℝ` (hypothesis `hdom`).
  `P x y := y 0`,  `Q x y := h (x, y 0) ^ 2 + (g x * y 1) ^ 2 + (1 - y 1 * y 2) ^ 2`.

**T1 smoothness.** `Function.uncurry P = fun p => p.2 0`: `(contDiff_apply 0).comp contDiff_snd`
  (`contDiff_apply` `Mathlib/Analysis/Calculus/ContDiff/Operations.lean:146`, `contDiff_snd` `ContDiff/Comp.lean:344`).
  `Function.uncurry Q`: `((hh.comp (contDiff_fst.prodMk ((contDiff_apply 0).comp contDiff_snd))).pow 2).add
  ((((hg.comp contDiff_fst).mul ((contDiff_apply 1).comp contDiff_snd)).pow 2).add
  ((contDiff_const.sub (((contDiff_apply 1).comp contDiff_snd).mul ((contDiff_apply 2).comp contDiff_snd))).pow 2))`
  (`ContDiff.comp` `Comp.lean:155`, `ContDiff.prodMk` `ContDiff/Basic.lean:567`, `contDiff_fst` `Comp.lean:287`, `ContDiff.add` `Operations.lean:197`,
  `ContDiff.mul` `:462`, `ContDiff.pow` `:508`, `ContDiff.sub` `:325`, `contDiff_const` `Basic.lean:98`). S (mechanical; `fun_prop` may close it).

**T2 nonneg.** `∀ x y, 0 ≤ Q x y`: `add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)`
  (`sq_nonneg` `Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean:608`).

**T3 case `f x ≠ ⊤`** (x ∈ dom f). Then `g x = 0` (W). Let `Z := {y | f x ≤ ↑(y 0) ∧ y 1 * y 2 = 1}`.
  (a) `Q x y = 0 ↔ y ∈ Z`: `Q x y = h(x,y 0)^2 + 0 + (1 - y 1 * y 2)^2`; sum of two squares is 0 iff both are 0
  (`add_eq_zero_iff_of_nonneg` + `sq_eq_zero_iff` `Mathlib/Algebra/GroupWithZero/Basic.lean:262`); `h (x, y 0) = 0 ↔ (x, y 0) ∈ epi_ℝ f ↔ f x ≤ ↑(y 0)` (W); `1 - y1 y2 = 0 ↔ y1 y2 = 1` (`sub_eq_zero`).
  (b) `Z` nonempty: `y₀ := ![(f x).toReal, 1, 1]`; `f x ≤ ↑((f x).toReal)` is `EReal.le_coe_toReal (h : x ≠ ⊤)` (`Data/EReal/Basic.lean:420`) — works for `f x = ⊥` too. Simp with `Matrix.cons_val_zero/one` (`Mathlib/Data/Fin/VecNotation.lean:128/271`), `Matrix.head_cons` (`:224`).
  (c) `argminSet Q univ x = Z` by F4 + (a),(b).
  (d) `valueFun P Q univ x = ⨅ y ∈ Z, ↑(y 0) = f x`:
      `≥`: `le_iInf₂ fun y hy => hy.1`.
      `≤`: if `f x = ↑r`: `iInf₂_le ![r,1,1] ⟨le_rfl, by simp⟩`. If `f x = ⊥`: for every real `r`, `![r,1,1] ∈ Z` (`bot_le`), so `iInf ≤ ↑r` for all `r`;
      conclude `iInf = ⊥` by `EReal.eq_bot_iff_forall_lt` (`Data/EReal/Basic.lean:438`) + `EReal.exists_between_coe_real`/density (or `le_of_forall_lt`-style: `iInf ≤ ↑(r-1) < ↑r`).
      (Cases by `EReal.rec` on `f x`, the `⊤` case excluded by hypothesis.)

**T4 case `f x = ⊤`** (x ∉ dom f). Then `g x ≠ 0` (W, since `x ∉ {f ≠ ⊤}`). Claim `argminSet Q univ x = ∅` via F3:
  given `y`, put `v := (g x * y 1)^2 + (1 - y 1 * y 2)^2`. Then `0 < v`: if `y 1 = 0` the second summand is `1`; else `g x * y 1 ≠ 0`
  (`mul_ne_zero`) so the first is `> 0` (`pow_pos`/`sq_pos_of_ne_zero`), use `add_pos_of_pos_of_nonneg`/`add_pos_of_nonneg_of_pos`
  (to_additive at `Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:752`).
  Choose `ε := min 1 (v / (2 * (g x ^ 2 + 1)))`; then `0 < ε ≤ 1`, so `ε^2 ≤ ε` and `(g x * ε)^2 = g x^2 * ε^2 ≤ (g x^2 + 1) * ε ≤ v/2 < v`.
  Put `y' := ![y 0, ε, 1/ε]`; `1 - ε * (1/ε) = 0` (`mul_one_div_cancel hε.ne'`), so `Q x y' = h(x, y 0)^2 + (g x * ε)^2 < h(x,y 0)^2 + v = Q x y`.
  Hence by V1 `valueFun P Q univ x = ⊤ = f x`. (The `h`-term is left untouched: no need for separability or for the minimiser of `h(x,·)²`, which may well exist.)

**T5 assemble**: `funext x; by_cases hx : f x = ⊤` → T3/T4.

**Pessimistic Theorem 1.1'** (`f` usc, `{f ≠ ⊥}` closed): apply the theorem to `-f` (lsc by `Continuous.comp_upperSemicontinuous_antitone`
`Semicontinuity/Basic.lean:1033` with `continuous_neg`, `EReal.neg_strictAnti.antitone`; `{x | -f x ≠ ⊤} = {x | f x ≠ ⊥}` by `EReal.neg_eq_top_iff` `Operations.lean:242`),
get `P Q` with `valueFun P Q univ = -f`; set `P' := -P` (smooth by `ContDiff.neg` `Operations.lean:264`); V8 gives
`pvalueFun P' Q univ = -(valueFun (-P') Q univ) = -(valueFun P Q univ) = -(-f) = f` (`neg_neg` in EReal: `InvolutiveNeg`).

### 2.C Berge-type results (Thm 2.8 / Cor 2.9)

Setting as in §1.4. Helper: `hQx : Continuous (Q x) := hQ.comp (Continuous.prodMk_right x)` (`Mathlib/Topology/Constructions/SumProd.lean:144`),
`hPx` likewise.

**B1 `isClosed_graph_argminSet`.** `{p | p.2 ∈ Θ p.1} = Prod.snd ⁻¹' S ∩ ⋂ y' ∈ S, {p | Q p.1 p.2 ≤ Q p.1 y'}`.
  `IsClosed.preimage continuous_snd hS.isClosed`; each piece `isClosed_le (hQ) (hQ.comp (continuous_fst.prodMk continuous_const))`
  (`hQ : Continuous (Function.uncurry Q)` is `Continuous fun p => Q p.1 p.2` definitionally); `isClosed_biInter`, `IsClosed.inter` (`Topology/Basic.lean:176`).
  Outer semicontinuity in the paper's sequence form (Def 2.7) is the corollary **B1'**: `Tendsto xk atTop (𝓝 x) → Tendsto yk atTop (𝓝 y) → (∀ k, yk k ∈ Θ (xk k)) → y ∈ Θ x`
  by `IsClosed.mem_of_tendsto` (`Mathlib/Topology/Neighborhoods.lean:357`) with `hx.prodMk_nhds hy` (`Filter.Tendsto.prodMk_nhds` `Constructions/SumProd.lean:339`).
  (Mathlib also has `UpperHemicontinuous`/`isClosedMap_iff_upperHemicontinuous`, `Mathlib/Topology/Semicontinuity/Hemicontinuity.lean:117,659`; not needed.)

**B2 `argminSet_nonempty`.** `IsCompact.exists_isMinOn hS hne hQx.continuousOn` (`Mathlib/Topology/Order/Compact.lean:255`:
  `∃ x ∈ s, IsMinOn f s x`, needs `[ClosedIicTopology ℝ]` — available) gives `y ∈ S` with `∀ y' ∈ S, Q x y ≤ Q x y'`, i.e. `y ∈ Θ x` (F1).

**B3 `argminSet_isCompact`.** F8 with `hS` and `hS.isClosed` (or: slice of B1's closed graph intersected with `S`).

**B4 `exists_isMinOn_argminSet`.** `IsCompact.exists_isMinOn (B3 x) (B2 x) hPx.continuousOn`.

**B5 `valueFun_eq_coe_of_compact`** `∃ y₀ ∈ Θ x, valueFun P Q S x = ↑(P x y₀)` := V2 ∘ B4; hence `valueFun_ne_top` (`EReal.coe_ne_top` `Data/EReal/Basic.lean:270`), `valueFun_ne_bot` (`:258`).

**B6 `isClosed_sublevel_valueFun`** `∀ r : ℝ, IsClosed {x | valueFun P Q S x ≤ ↑r}`.
  Let `C : Set (X × ↥S) := {p | (p.2 : Y) ∈ Θ p.1 ∧ P p.1 p.2 ≤ r}`; closed: preimage of B1 under `Prod.map id Subtype.val` (continuous), intersected
  with `isClosed_le (hP.comp (continuous_id.prodMap continuous_subtype_val)) continuous_const`.
  `haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS` (`Mathlib/Topology/Compactness/Compact.lean:1051`).
  `isClosedMap_fst_of_compactSpace C hC : IsClosed (Prod.fst '' C)` (`Mathlib/Topology/Maps/Proper/Basic.lean:332`; `IsClosedMap` def `Topology/Defs/Basic.lean:171`).
  Show `Prod.fst '' C = {x | valueFun ≤ ↑r}`: (⊆) `(x, y) ∈ C` ⇒ `valueFun ≤ ↑(P x y) ≤ ↑r` (`iInf₂_le`, `EReal.coe_le_coe_iff`);
  (⊇) take `y₀` from B5, `↑(P x y₀) = valueFun ≤ ↑r`, so `(x, ⟨y₀, F2 _⟩) ∈ C`.

**B7 `lowerSemicontinuous_valueFun`.** `lowerSemicontinuous_iff_isClosed_preimage` (`Semicontinuity/Basic.lean:232`, `γ = EReal`): need `IsClosed (valueFun ⁻¹' Iic a)` for all `a : EReal`;
  `EReal.rec` on `a`: `⊥`: preimage `= ∅` by B5 (`valueFun ≠ ⊥`, `le_bot_iff`), `isClosed_empty`; `↑r`: B6; `⊤`: `= univ`, `isClosed_univ`.
  Bridge to the real-valued statement of the paper (**B7'**): for `f : X → ℝ`, `LowerSemicontinuous (fun x => (f x : EReal)) ↔ LowerSemicontinuous f`:
  (⇐) `continuous_coe_real_ereal.comp_lowerSemicontinuous hf EReal.coe_strictMono.monotone` (`Basic.lean:391`; `coe_strictMono` `Data/EReal/Basic.lean:48`);
  (⇒) unfold `lowerSemicontinuousAt_iff` (`Semicontinuity/Defs.lean:328`): given `y < f x`, apply hypothesis to `↑y < ↑(f x)` (`EReal.coe_lt_coe_iff`), then `Filter.Eventually.mono` with `EReal.coe_lt_coe_iff.1`.

**B8 `valueFun_bddOn_compact`.** For `K` compact: `hK.prod hS` compact (`Compact.lean:1071`); `IsCompact.bddAbove_image`/`bddBelow_image`
  (`Topology/Order/Compact.lean:359/354`) of `Function.uncurry P` give `m ≤ P x y ≤ M'` on `K ×ˢ S`; with `y₀` from B5, `φ x = ↑(P x y₀)` and `y₀ ∈ S`;
  take `M := max |m| |M'|` (or keep two bounds). No lsc needed (simpler than the paper).

**B9 (Remark 2.10, `P_bounded ⊆ LSC ∩ CB`).** Unpack the class, `IsBoundedBox.isCompact`, `.nonempty`, `continuous_uncurry_polyFun`, then B7, B8 (and B5 for real-valuedness).

**Pessimistic Cor 2.9'**: `UpperSemicontinuous (pvalueFun P Q S)`, real-valued, bounded on compacts: V8 + B7 applied to `-P` + `Continuous.comp_lowerSemicontinuous_antitone` (`Basic.lean:409`) with `Neg.neg`, or run B1–B8 with `IsMaxOn`/`IsCompact.exists_isMaxOn` (`Compact.lean:273`) and `upperSemicontinuous_iff_isClosed_preimage` (`Basic.lean:811`).

---------------------------------------------------------------------------------------------------------------------

## 3. Errors, gaps, typos in the paper (with fixes)

1. **Thm 1.1, hypothesis "proper" is unnecessary.** If `f ≡ +∞`, `dom f = ∅` is closed, W gives `g ≡ 1` (zero set ∅), and the construction yields `Θ(x) = ∅` for all `x`, `φ ≡ +∞ = f`. Fix: drop "proper" (our statement does).
2. **Thm 1.1, values `−∞` can be allowed.** With `f : ℝⁿ → ℝ∪{±∞}` lsc and `{f < +∞}` closed the same `P, Q` work: at `x` with `f(x) = −∞`, `Θ(x) = ℝ × {y₂y₃ = 1}` and `inf y₁ = −∞`. Only the case split in T3(d) changes. Fix: state for EReal-valued `f` (strengthening); the paper's version follows.
3. **Prop A.2 is stated for real-valued `f` but applied to extended-valued `f`** (epi(f) ⊆ ℝⁿ×ℝ with `f(x)=+∞` allowed). It is true in that generality (A2 above); the paper should say so. Note also the converse direction is never used.
4. **Proof of Thm 1.1, case 1, type error:** "Θ(x) = epi(f) ∩ {x}×ℝ" — Θ(x) ⊆ ℝ³. Should read Θ(x) = {y ∈ ℝ³ | (x,y₁) ∈ epi(f), y₂y₃ = 1}; and "φ(x) = min{y | y ∈ epi(f) ∩ {x}×ℝ}" should be φ(x) = min{y₁ | (x,y₁) ∈ epi(f)} = f(x), the minimum being attained at y₁ = f(x) because (x, f(x)) ∈ epi(f) (this attainment is exactly where x ∈ dom(f) is used).
5. **Proof of Thm 1.1, case 1, hidden step:** "Θ(x) is the set of y with h(x,y₁)=0 and y₂y₃=1" silently uses (i) `g(x)=0` (so the middle square vanishes), (ii) `Q ≥ 0` and (iii) **nonemptiness of the zero set** (if the zero set of `h(x,·)²` were empty, argmin of `h(x,·)²` could be a nonempty set with positive value). Fix: F4 with witness `(f(x),1,1)`.
6. **Proof of Thm 1.1, case 2:** "the infimum of p is zero … cannot be attained" is correct but incomplete as a proof that argmin_y Q = ∅: one must show every candidate `y` is strictly beaten (T4 gives the explicit `ε`). Also the separability identity "argmin_y Q = argmin h × argmin p" is asserted without proof; it is true unconditionally (F5) but T4 avoids it entirely. Worth remarking: in case 2 the minimiser of `h(x,·)²` may exist, which is precisely why the `(g, y₂, y₃)` gadget is indispensable.
7. **Thm 1.1 must say "optimistic".** For the constructed `(P,Q)`, the *pessimistic* value function is `+∞` on dom f (Θ(x) is unbounded above in y₁). Fix: state (BP-O); the pessimistic analogue needs usc `f`, `{f > −∞}` closed and `P = −y₁` (Theorem 1.1' above), or hypograph in place of epigraph.
8. **Thm A.1 "smooth" must mean C^∞, not analytic.** Zero sets of real-analytic functions are analytic sets (e.g. a Cantor set is not one), so the result is false for `C^ω`. In Mathlib terms: `ContDiff ℝ ∞`, never `ContDiff ℝ ⊤` (= `ω`). The cited Mathlib lemma gives C^∞ only.
9. **Thm 2.8 statement:** "g : ℝⁿ × ℝᵐ" lacks the codomain "→ ℝ"; Θ has nonempty values only if **𝒴 ≠ ∅** (missing hypothesis). Def 2.7 says "compact set-valued map" but compactness of values is irrelevant to the definition (closed-graph property); fix: drop "compact" in Def 2.7, add "nonempty" in Thm 2.8.
10. **Cor 2.9 needs 𝒴 ≠ ∅** (else `Θ ≡ ∅`, `φ ≡ +∞`, not real-valued). Fix: add "nonempty". Consequently `IsBoundedBox` requires `lo ≤ hi` (nonempty box) in the class definition.
11. **Cor 2.9 proof, step 2:** "Since Θ(x) is compact, there exists y_k ∈ Θ(x_k)" should be "Θ(x_k) is nonempty compact". "We can assume φ(x_k) → liminf" requires passing to a subsequence, then a further subsequence for the accumulation point `y`; "liminf φ(x_k) = P(x,y)" holds along that sub-subsequence by continuity of P. Correct but sloppy; our proof (B6–B7) has no sequences.
12. **Cor 2.9 proof, step 3:** the compact set and the bound are both called `C`; "max_{x∈C} φ(x)" presupposes attainment (should be sup); the lower bound "since φ is lsc it is lower-bounded on compacts" is true (Mathlib `LowerSemicontinuousOn.bddBelow_of_isCompact`, `Semicontinuity/Basic.lean:106`) but unnecessary: `φ(x) = P(x,y*) ≥ min_{C×𝒴} P` (B8).
13. **Def 2.11 vs Thm 2.12 type mismatch:** Def 2.11 defines 𝒫_boxtype as a set of functions `ℝⁿ → ℝ`, but Thm 2.12 asserts `𝒫_unbound = 𝒮𝒜` where 𝒮𝒜 (Def 2.2) contains extended-real-valued functions, and the value function itself takes values ±∞. Fix: classes are sets of functions `ℝⁿ → ℝ∪{±∞}` (EReal in Lean; §1.1).
14. **Def 2.11 "boxtype = unbound" is ambiguous** (any unbounded box? any box? only ℝᵐ?). Thm 2.12's proof uses 𝒴 = ℝᵐ, Prop 2.6 covers all boxes. Fix: let 𝒫_box be the class over *all* boxes (so 𝒫_bounded ⊆ 𝒫_box trivially); then 𝒮𝒜 ⊆ 𝒫_{𝒴=ℝᵐ} ⊆ 𝒫_box ⊆ 𝒮𝒜 gives the equality for every reasonable reading. Also the empty box (a_i > b_i) should be either excluded or noted harmless (φ ≡ +∞ ∈ 𝒮𝒜); it must be excluded from the bounded class (item 10).
15. **§1 text:** "φ_o(x) = +∞ if Θ(x) = ∅" — but φ_o(x) = −∞ is also possible (P unbounded below on Θ(x)); this is acknowledged only in §2.1 (dom(φ)⁻). Fix: mention both conventions in §1 (our `EReal` definition handles both).
16. **§2.1, dom(φ) formula** (item 1 before Prop 2.6) is a correct first-order description of "φ(x) = δ ∈ ℝ" (lemma V3); note it implies Θ(x) ≠ ∅, so the three sets are indeed a partition. No error, but V3 is the lemma R2 needs to make Prop 2.6 rigorous.
17. **Thm 2.15 proof opens with "To prove the equalities in Theorem 2.21"** — should be Theorem 2.15 (twice). (Noticed in passing; outside my scope.)
18. **Appendix A Discussion:** refers to "Proposition 1.1" (should be Theorem 1.1). The characteristic function of the Smith–Volterra–Cantor set is *upper* semicontinuous (as the text says), so it is **not** covered by Thm 1.1 as stated (which needs lsc); it is covered by the pessimistic counterpart (Thm 1.1') or via `−1_S` (lsc). Thomae's function `t` is usc, so `−t` is lsc as claimed. Weierstrass and Cantor staircase are continuous, fine. (Mathlib has `cantorSet`, `Mathlib/Topology/Instances/CantorSet.lean:57`, but none of Thomae/Weierstrass/SVC/Cantor-function; these examples are illustrative only and not part of the formalisation target.)
19. **Thm A.1 wording:** "the set zeros of a smooth function" → "the zero set".
20. **Section 2.4 bullet 1** claims the unbounded-box constructions "involve unique minimizers in the lower level". For Thm 2.12's construction this is false as written (e.g. in case dom(h)⁻ every `t ∈ ℝ` is part of a minimiser; and the `z, ν, u, v` coordinates are typically not unique: `uv = 1` has infinitely many solutions). What is true is that `P` is constant on Θ(x) when Θ(x) ≠ ∅ in the dom(h) case (lemma V5), and in the dom(h)⁻ case sup = +∞ ≠ inf = −∞. So the pessimistic value function of *that* construction is **not** `h` on dom(h)⁻. Fix for the blueprint: the pessimistic version of Thm 2.12 should be obtained from the optimistic one by negation (V8: `h ∈ 𝒮𝒜 ⇒ −h ∈ 𝒮𝒜`, so `pvalueFun(−P,Q,𝒴) = −valueFun(P,Q,𝒴)` with `P,Q` built for `−h`), not by the "unique minimiser" argument. R3 should double-check the convex constructions (Thm 2.18) for the same issue; V5 (constant `P` on Θ(x)) is the right invariant, and it implies `pvalueFun = valueFun` on {Θ ≠ ∅}.

---------------------------------------------------------------------------------------------------------------------

## 4. Mathlib inventory

| Need | Declaration | File:line | Note |
|---|---|---|---|
| Whitney: open set = support of smooth fn | `IsOpen.exists_contDiff_support_eq` | Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean:83 | `{n : ℕ∞}`, needs `[NormedSpace ℝ E] [FiniteDimensional ℝ E]` (lines 22–26); gives `f.support = s ∧ ContDiff ℝ n f ∧ range f ⊆ Icc 0 1` |
| support ↔ zero set | `Function.support_eq_iff` (to_additive of `mulSupport_eq_iff`) | Mathlib/Algebra/Notation/Support.lean:54 | also `mem_support` :44, `notMem_support` :38 |
| C^∞ vs analytic notation | `∞`, `ω`, `ℕ∞ω` | Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:116–120 | scoped `ContDiff`; `ContDiff` def Defs.lean:1067; `contDiff_infty` Defs.lean:1114 |
| ContDiff combinators | `ContDiff.add/mul/pow/sub/neg` | ContDiff/Operations.lean:197/462/508/325/264 | |
| | `contDiff_fst`, `contDiff_snd`, `ContDiff.comp`, `ContDiff.comp₂` | ContDiff/Comp.lean:287/344/155/425 | |
| | `ContDiff.prodMk`, `contDiff_const`, `contDiff_id` | ContDiff/Basic.lean:567/98/173 | |
| | `contDiff_apply`, `contDiff_pi` | ContDiff/Operations.lean:146/113 | coordinate projections on `Fin 3 → ℝ` |
| | `ContDiff.continuous` | ContDiff/Defs.lean:1150 | |
| finite-dimensionality of products/pi | `Module.Finite.prod`, `Module.Finite.pi` | Mathlib/RingTheory/Finiteness/Prod.lean:46, Basic.lean:277 | instances |
| lsc ⇔ closed epigraph | `lowerSemicontinuous_iff_isClosed_epigraph`, alias `LowerSemicontinuous.isClosed_epigraph` | Mathlib/Topology/Semicontinuity/Basic.lean:353/355 | `[LinearOrder γ] [TopologicalSpace γ] [ClosedIciTopology γ]`, epigraph in `α × γ` |
| usc ⇔ closed hypograph | `upperSemicontinuous_iff_IsClosed_hypograph` | Basic.lean:897 | |
| lsc ⇔ closed sublevel sets | `lowerSemicontinuous_iff_isClosed_preimage` | Basic.lean:232 | `[LinearOrder γ]`, no topology on γ needed |
| lsc ⇔ liminf | `lowerSemicontinuous_iff_le_liminf` | Basic.lean:289 | `[CompleteLinearOrder γ]` (EReal ok) — not used in chosen route |
| lsc definitions | `LowerSemicontinuous` (abbrev of `Semicontinuous (f · > ·)`), `lowerSemicontinuousAt_iff` | Mathlib/Topology/Semicontinuity/Defs.lean:293/328 | `∀ y < f x, ∀ᶠ x' in 𝓝 x, y < f x'` |
| monotone/antitone composition | `Continuous.comp_lowerSemicontinuous`, `…_antitone`, `Continuous.comp_upperSemicontinuous_antitone` | Basic.lean:391/409/1033 | |
| lsc attains min on compact | `LowerSemicontinuousOn.exists_isMinOn`, `.bddBelow_of_isCompact` | Basic.lean:77/106 | not needed (B8 avoids it) |
| continuous min on compact | `IsCompact.exists_isMinOn` / `exists_isMaxOn` | Mathlib/Topology/Order/Compact.lean:255/273 | `ContinuousOn f s`, `s.Nonempty` |
| bounds on compact | `IsCompact.bddBelow_image`, `.bddAbove_image` | Topology/Order/Compact.lean:354/359 | |
| compact Icc / pi | `CompactIccSpace.isCompact_Icc`, `isCompact_univ_pi`, `IsCompact.prod` | Topology/Order/Compact.lean:53–55; Topology/Compactness/Compact.lean:1172/1071 | |
| compact basics | `IsCompact.isClosed`, `IsCompact.inter_right`, `IsCompact.of_isClosed_subset`, `isCompact_iff_compactSpace` | Separation/Hausdorff.lean:600; Compactness/Compact.lean:86/105/1051 | |
| projection along compact factor is closed | `isClosedMap_fst_of_compactSpace`, `isClosedMap_snd_of_compactSpace` | Mathlib/Topology/Maps/Proper/Basic.lean:332/337 | `[CompactSpace Y]`; `IsClosedMap` def Topology/Defs/Basic.lean:171 |
| closed sets | `isClosed_le`, `isClosed_Icc`, `isClosed_Iic`, `ClosedIciTopology.isClosed_Ici` | Topology/Order/OrderClosed.lean:444/456/116/82 | `instance : ClosedIicTopology α` (:449, `@[to_dual]`) from `OrderClosedTopology` |
| | `isClosed_iInter`, `isClosed_biInter`, `IsClosed.inter`, `IsClosed.preimage`, `isClosed_set_pi` | Topology/Basic.lean:159/162/176; Topology/Continuous.lean:188; Topology/Constructions.lean:1127 | |
| limits into closed sets | `IsClosed.mem_of_tendsto`, `IsClosed.mem_of_frequently_of_tendsto`, `Filter.Tendsto.prodMk_nhds` | Topology/Neighborhoods.lean:357/353; Constructions/SumProd.lean:339 | for Def 2.7 form |
| sequential compactness | `IsCompact.tendsto_subseq` | Mathlib/Topology/Sequences.lean:298 | only for the rejected sequence route |
| product continuity | `Continuous.prodMap`, `Continuous.prodMk`, `Continuous.prodMk_left/right` | Constructions/SumProd.lean:178/139/147/144 | |
| EReal order/top/bot | `EReal.coe_le_coe_iff`, `coe_lt_coe_iff`, `coe_eq_coe_iff` (protected) | Mathlib/Data/EReal/Basic.lean:55/61/67 | |
| | `coe_strictMono`, `bot_lt_coe`, `coe_ne_bot`, `coe_lt_top`, `coe_ne_top`, `top_ne_coe`, `bot_ne_coe` | Data/EReal/Basic.lean:48/254/258/266/270/274/262 | |
| | `EReal.rec`, `toReal_coe`, `coe_toReal`, `le_coe_toReal`, `eq_top_iff_forall_lt`, `eq_bot_iff_forall_lt`, `exists_between_coe_real`, `lt_iff_exists_real_btwn` | Data/EReal/Basic.lean:113/250/416/420/430/438/448/863 | |
| EReal arithmetic | `coe_add`, `coe_mul`, `coe_neg`, `coe_sub` | Data/EReal/Basic.lean:310/155; Operations.lean:220/222 | |
| | `add_bot`, `bot_add`, `top_add_coe`, `coe_add_top`, `top_add_of_ne_bot`, `add_top_of_ne_bot` | Data/EReal/Operations.lean:46/50/68/108/73/81 | |
| | `coe_mul_top_of_pos`, `coe_mul_bot_of_pos`, `mul_top_of_pos`, `mul_bot_of_pos` | Operations.lean:579/615/591/627 | |
| | `neg_strictAnti`, `neg_le_neg_iff`, `neg_lt_neg_iff`, `neg_top`, `neg_bot`, `neg_eq_top_iff`, `neg_eq_bot_iff`, `negOrderIso` | Operations.lean:253/258/260/213/217/242/246/295 | |
| EReal topology | `instance : OrderTopology EReal`, `T2Space EReal` | Mathlib/Topology/Order/Real.lean:37/40 | hence `ClosedIciTopology`/`ClosedIicTopology` |
| | `continuous_coe_real_ereal`, `EReal.continuous_coe_iff`, `EReal.isEmbedding_coe`, `tendsto_coe` | Topology/Instances/EReal/Lemmas.lean:52/55/41/48 | |
| | `instance : ContinuousNeg EReal` | Mathlib/Topology/Algebra/Ring/Real.lean:65 | for `continuous_neg` on EReal |
| EReal lattice | `CompleteLinearOrder` (derived) | Data/EReal/Basic.lean:35–39 | |
| iInf API (all `@[to_dual]` of the iSup version; generated names) | `iInf_emptyset`←`iSup_emptyset`; `iInf_univ`←`iSup_univ` | Mathlib/Order/CompleteLattice/Basic.lean:584/587 | |
| | `iInf₂_le`←`le_iSup₂`; `le_iInf₂`←`iSup₂_le`; `iInf_le`←`le_iSup`; `le_iInf`←`iSup_le`; `iInf_le_of_le`←`le_iSup_of_le` | Basic.lean:226/239/211/235/222 | |
| | `le_iInf_iff`←`iSup_le_iff`; `le_iInf₂_iff`←`iSup₂_le_iff`; `iInf₂_mono`←`iSup₂_mono`; `iInf_le_iInf_of_subset`←`iSup_le_iSup_of_subset` | Basic.lean:280/284/251/607 | |
| | `iInf_le_iff`←`le_iSup_iff`; `iInf_eq_bot`←`iSup_eq_top`; `iInf_eq_top`←`iSup_eq_bot` | Order/CompleteLattice/Defs.lean:123/335; Basic.lean:351 | |
| | `iInf_eq_of_forall_ge_of_forall_gt_exists_lt`←`iSup_eq_of_forall_le_of_forall_lt_exists_gt` | Basic.lean:373–378 | for V3 |
| | `IsLeast.csInf_eq`←`IsGreatest.csSup_eq` | Mathlib/Order/ConditionallyCompletePartialOrder/Basic.lean:71 | alt. for V2 via `sInf` of image |
| | `map_iInf`←`map_iSup` (for `sInfHomClass`), `OrderIsoClass.toCompleteLatticeHomClass` | Mathlib/Order/Hom/CompleteLattice.lean:125/178 | for V8 |
| IsMinOn | `IsMinOn` def, `isMinOn_iff`, `isMinOn_univ_iff`, `IsMinOn.of_subset` | Mathlib/Order/Filter/Extr.lean:112/129/135/272 | `IsMinOn.on_subset` is deprecated |
| sets/boxes | `Set.mem_prod`, `Set.mem_univ_pi`, `Set.univ_pi_nonempty_iff`, `Set.nonempty_Icc` | Data/Set/Operations.lean:231/283; Data/Set/Prod.lean:656; Order/Interval/Set/Basic.lean:139 | |
| convexity | `ConvexOn` def, `convex_pi`, `convex_Icc`, `convex_Ici`, `convex_Iic`, `convex_univ` | Mathlib/Analysis/Convex/Function.lean:54; Convex/Basic.lean:108/257/254/248/89 | |
| boundedness of boxes | `Bornology.isBounded_pi` | Mathlib/Topology/Bornology/Constructions.lean:114 | if "bounded" is to be stated metrically |
| polynomial continuity | `MvPolynomial.continuous_eval` | Mathlib/Topology/Algebra/MvPolynomial.lean:31 | |
| reindexing | `finSumFinEquiv`, `Fin.appendEquiv`, `Equiv.sumArrowEquivProdArrow` | Logic/Equiv/Fin/Basic.lean:224/401; Logic/Equiv/Prod.lean:390 | for F7 |
| vectors `![a,b,c]` | `Matrix.cons_val_zero`, `cons_val_one`, `cons_val_succ`, `head_cons` | Mathlib/Data/Fin/VecNotation.lean:128/271/135/224 | `simp` handles `![…] 2` via `cons_val_succ` |
| real arithmetic | `sq_nonneg`, `mul_self_nonneg`, `sq_eq_zero_iff`, `pow_eq_zero_iff`, `pow_pos`, `add_pos_of_pos_of_nonneg` (to_additive) | Algebra/Order/Ring/Unbundled/Basic.lean:608/630; Algebra/GroupWithZero/Basic.lean:262/253; Algebra/Order/GroupWithZero/Basic.lean:588; Algebra/Order/Monoid/Unbundled/Basic.lean:752 | |
| Berge's maximum theorem | NOT IN MATHLIB | — | replaced by B1–B8 (closed graph + compact projection) |
| outer semicontinuity (Def 2.7) | NOT IN MATHLIB as such; nearest: `UpperHemicontinuous`, `isClosedMap_iff_upperHemicontinuous` | Topology/Semicontinuity/Defs.lean:659; Hemicontinuity.lean:117 | we use the closed-graph property B1 directly |
| Thomae/Weierstrass/SVC/Cantor function | NOT IN MATHLIB (only `cantorSet`, Topology/Instances/CantorSet.lean:57) | — | illustrative only, not a target |
| real-closed/semialgebraic sets | NOT IN MATHLIB | — | R2's scope |

---------------------------------------------------------------------------------------------------------------------

## 5. Lean encoding decisions and pitfalls

1. **`∞` vs `⊤` in `ContDiff`.** `ContDiff ℝ ⊤ f` is *analyticity* (`ω`) in current Mathlib. Write `ContDiff ℝ ∞ (Function.uncurry P)` with `open scoped ContDiff`, or `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`. Instantiating the Whitney lemma with `n := (⊤ : ℕ∞)` yields exactly `ContDiff ℝ ∞`.
2. **Domain of smoothness:** `(Fin n → ℝ) × (Fin 3 → ℝ)` with `Function.uncurry`. Keep `P Q : X → Y → ℝ` curried in the framework (so `argminSet`/`valueFun` read naturally) and state regularity on the uncurried map. Joint continuity hypothesis in Cor 2.9 is `Continuous (Function.uncurry P)` — *do not* assume only separate continuity (Berge needs joint continuity).
3. **`valueFun` is a double `iInf`:** `⨅ y ∈ Θ, …` is `⨅ y, ⨅ (_ : y ∈ Θ), …`; use `iInf₂_le`/`le_iInf₂` (generated by `@[to_dual]`, so the names do not appear literally in the source — the table lists the generating declaration). Empty Θ gives `⊤` (`iInf_emptyset`), unbounded below gives `⊥`. Never use `sInf` on `ℝ` (junk value 0 on empty/unbounded sets).
4. **Real-valued statements:** write `valueFun P Q S x = (r : EReal)` and use V3; for classes, EReal-valued functions throughout (fixes paper's type mismatch, §3 item 13). The bridge B7' converts lsc between `ℝ`- and `EReal`-valued presentations when a downstream agent has a real-valued `f`.
5. **Case analysis on EReal:** `EReal.rec` (`Data/EReal/Basic.lean:113`, motive-explicit; use `induction a using EReal.rec`), or `rcases` on `a = ⊥ ∨ a = ⊤ ∨ ∃ r : ℝ, a = r`. `EReal.coe_*_iff` lemmas are `protected`: write `EReal.coe_le_coe_iff`.
6. **Boxes.** `boxSet lo hi` with `lo hi : Fin m → EReal` is the cleanest way to encode `[a_i,b_i]` with `a_i,b_i ∈ ℝ∪{±∞}` in one shot; `boundedBox` as `Set.pi univ (Icc ∘ …)` gives direct access to `isCompact_univ_pi`, `convex_pi`, `Set.univ_pi_nonempty_iff`. Require `lo ≤ hi` for bounded boxes (nonempty) — needed by Cor 2.9 (§3 item 10).
7. **Variable blocks.** Prove constructions on product types and transport with F7; avoid `Fin.append`/`Fin.cast` arithmetic inside proofs.
8. **`isClosedMap_fst_of_compactSpace` needs a `CompactSpace` instance on the *type*:** use the subtype `↥S` and `haveI := isCompact_iff_compactSpace.mp hS`; map `(x, y) ↦ (x, ↑y)` via `Prod.map id Subtype.val` to pull back the closed graph.
9. **`IsCompact.exists_isMinOn` wants `ContinuousOn`**, obtained by `Continuous.continuousOn`; partial applications `Q x = fun y => Q x y` are continuous via `hQ.comp (Continuous.prodMk_right x)`.
10. **T2 for `Fin m → ℝ`** is automatic (`Pi` instance); needed for `IsCompact.isClosed`.
11. **Decidability:** none needed; everything is `Set`-level and classical (`noncomputable` on `valueFun`).
12. **`![a,b,c]` arithmetic:** `simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]` evaluates coordinates 0,1; coordinate 2 reduces through `Matrix.cons_val_succ`; `norm_num [Fin.succ]` may be needed. Alternative avoiding vector notation: state T3/T4 for `Y := ℝ × ℝ × ℝ` and transport with F7 — but `Fin 3 → ℝ` is what the theorem statement wants; the `simp` lemmas suffice.
13. **Division in T4:** `1/ε` with `ε > 0`; `mul_one_div_cancel`; keep `ε := min 1 (v / (2 * (g x ^ 2 + 1)))` to avoid `Real.sqrt`.
14. **`CB` definition** with two-sided EReal bounds (so that `⊤`/`⊥` are excluded automatically); provide `CB.ne_top`/`CB.ne_bot` (take `K = {x}`, `isCompact_singleton`).

---------------------------------------------------------------------------------------------------------------------

## 6. Alternatives considered and rejected

- **Sequence-based Berge proof (paper):** needs two nested subsequence extractions (`IsCompact.tendsto_subseq`) and liminf manipulation in EReal; the closed-map/sublevel-set route (B6) is ~5× shorter in Lean and uses only `isClosedMap_fst_of_compactSpace`.
- **Filter/cluster-point proof of lsc** (`IsCompact` as "every filter ≤ 𝓟 S has a cluster point"): workable but requires producing a cluster point of the pair map `x' ↦ (x', s x')`; no advantage over B6.
- **Closed epigraph route for B7** (`lowerSemicontinuous_iff_isClosed_epigraph`): same closed-map lemma but the projection `X × Y × ℝ → X × ℝ` needs reassociation; sublevel sets with a single `Prod.fst` are simpler.
- **Typing `f : X → WithTop ℝ`:** rejected (thin topology/semicontinuity API compared with `EReal`; `valueFun` is EReal anyway; the general EReal statement is free).
- **Using separability F5 in Thm 1.1:** requires splitting `Fin 3 → ℝ` into `ℝ × (ℝ × ℝ)`; the direct "beat the candidate" argument T4 and the zero-set lemma F4 avoid it. F5 remains in the API for Thms 2.12/2.18/3.2.
- **Whitney via smooth Urysohn (`exists_smooth_zero_one_of_isClosed`)**: only gives `0` on one closed set and `1` on another, not an exact zero set — unusable. `IsOpen.exists_contDiff_support_eq` is the right tool (its proof is a genuine Whitney-type construction with countably many bumps).
- **`EuclideanSpace ℝ (Fin n)`**: unnecessary; `ContDiff` is norm-independent in finite dimension and `Fin n → ℝ` has all instances.
- **Defining `IsBox` by a four-way case on each coordinate (Icc/Ici/Iic/univ):** more cases everywhere; the EReal-bounds encoding is uniform. (`Metric.isBounded`-based "bounded" is avoided; `IsBoundedBox` is syntactic.)
- **Stating Cor 2.9 for real-valued `φ`** (`∃ f : X → ℝ, valueFun = coe ∘ f ∧ LowerSemicontinuous f ∧ …`): equivalent via B7', but the EReal-valued form is what the class inclusions need; provide both (B7 and B7').

---------------------------------------------------------------------------------------------------------------------

## 7. Effort / risk per lemma (S < 1h, M ≈ half day, L ≈ 1–2 days, XL more)

| Lemma | Effort | Assume or prove |
|---|---|---|
| Definitions §1.1, F1–F4, F6, V1, V2, V5, V5' | S each | prove |
| F3, F5 (separability) | S | prove |
| F7 reindexing (argmin + valueFun) | M | prove (one-time investment, used by R3/R4/R5) |
| F8, box lemmas, `continuous_uncurry_polyFun` | S–M | prove |
| V3 (dom characterisation), V4 | M | prove (EReal ε-juggling) |
| V6, V7 (scaling/shift) | M | prove |
| V8 (pessimistic = −optimistic) | S/M | prove |
| W (Whitney wrapper) | S | prove (Mathlib does the work) |
| A2 (closed real epigraph) | S | prove |
| T1 smoothness | S | prove (mechanical) |
| T2, T3 | M | prove |
| T4 (no minimiser) | M | prove (explicit ε) |
| Theorem 1.1 assembly, Theorem 1.1' | S | prove |
| B1 closed graph | S/M | prove |
| B2–B5 | S | prove |
| B6 sublevel sets closed | M | prove (subtype/CompactSpace plumbing) |
| B7, B7', B8, B9 | S–M | prove |
| Pessimistic Cor 2.9' | S | prove (via V8) |
Nothing in my scope needs to be assumed; no semialgebraic geometry is involved except the label `IsSemialgebraic` in `C_cc` and the `SA` target class (R2). Overall risk: low; the only delicate Lean points are the `∞`/`⊤` convention and the `CompactSpace`-subtype plumbing in B6.

---------------------------------------------------------------------------------------------------------------------

## 8. Open questions for the auditor

1. Accept the strengthened Theorem 1.1 (EReal-valued `f`, no "proper", `−∞` allowed) as the blueprint statement, with the paper's version as a corollary? (Recommended: yes; it costs one extra `EReal.rec` branch.)
2. Class definitions: confirm `P_box` = "all boxes" reading of 𝒫_unbound (§3 item 14), EReal-valued classes (§3 item 13), and `lo ≤ hi` in `IsBoundedBox`. Should the empty box be excluded from `IsBox` too (it is harmless: `valueFun ≡ ⊤ ∈ SA`)?
3. "Q convex w.r.t. y" in Def 2.16: `ConvexOn ℝ Set.univ (polyFun Q x)` for every `x` (global convexity in `y`), or only on the box `S`? Global is what R3's constructions deliver (sums of squares of affine/convex pieces); the weaker `ConvexOn ℝ S` makes the class larger and the inclusion results stronger — R3 to decide; the definition above is parametric in `lowerOK` so either is a one-line change.
4. §3 item 20: the paper's claim that the pessimistic versions of the unbounded-box results follow from "unique minimisers" is not literally true for the Thm 2.12 construction; I propose negation (V8) as the blueprint route. R3/R4 should confirm their constructions have `P` constant on Θ(x) (V5) where Θ(x) ≠ ∅.
5. Should Def 2.7/Thm 2.8 appear in the blueprint at all, or only the closed-graph lemma B1 (+ B1' as a remark)? I recommend B1 only.
6. Is the real-valued bridge B7' wanted by other agents (R3's Thm 2.20 has real-valued lsc piecewise polynomials)? If so it belongs to the shared API file.
7. Theorem 1.1 is stated with `Y = Fin 3 → ℝ`; if the auditor prefers `ℝ × ℝ × ℝ` for proof convenience, F7 transports the result (cost: one more lemma application).
