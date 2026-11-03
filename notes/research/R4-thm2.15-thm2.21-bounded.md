# R4 report — Theorem 2.15 (P_bounded), Theorem 2.21 (C_cc), pessimistic counterparts

Paper: Bolte–Lê–Pauwels–Vaiter, arXiv:2407.12372v2. Sections used: 2.1 (Prop 2.4, 2.5, 2.6, Cor 2.9),
2.2 (Thm 2.15, Table 2, (8)–(10)), 2.3.1 (def. (18), Thm 2.21 + remarks), 2.4 (pessimistic).
Mathlib checkout: `<SCRATCH>/mathlib/mathlib4` (commit 1df8067a). All Mathlib names below were located by grep.

Conventions. `x : Fin n → ℝ` (upper), lower variable `y : ι → ℝ` with `[Fintype ι]` (see §5 for why I
deviate from `Fin m` *inside* the constructions; the final statements can be transported to `Fin m`).
`argminSet Q Y x := {y ∈ Y | ∀ y' ∈ Y, Q x y ≤ Q x y'}`, `valueFun P Q Y x : EReal := ⨅ y ∈ argminSet Q Y x, ((P x y : ℝ) : EReal)`,
`pessFun P Q Y x := ⨆ y ∈ argminSet Q Y x, ((P x y : ℝ) : EReal)`.
"T–S" = Tarski–Seidenberg (assumed, not in Mathlib). "FT" = finiteness theorem for closed semialgebraic sets (paper's Prop 2.4; assumed).

---------------------------------------------------------------------------------------------------
## 1. Scope — exact statements

### 1.1 Theorem 2.15  (P_bounded = SA ∩ LSC ∩ CB)

Math. Let f : ℝⁿ → ℝ. TFAE:
 (i) ∃ m, polynomials P, Q ∈ ℝ[x₁..x_n, y₁..y_m], and a bounded box Y = ∏_k [a_k, b_k] (a_k ≤ b_k real) with
     φ_{P,Q,Y}(x) = f(x) for all x (as extended reals; in particular Θ(x) ≠ ∅ and the inf is finite);
 (ii) graph f is semialgebraic, f is lower semicontinuous, and f is bounded on every compact set.

(⊆) (i)⇒(ii) is Prop 2.6 (semialgebraicity: T–S; agent R1/R2) + Cor 2.9 (lsc + CB; Berge; agent R1). Not re-proved here; only stated.
(⊇) (ii)⇒(i) is the construction, which is the object of this report.

Lean-style signatures (the predicate `IsSemialgebraic` is R2's; I only need it for sets in `(Fin n → ℝ) × ℝ`,
or equivalently `Fin (n+1) → ℝ` through `Fin.snoc`/`Fin.consEquiv`, see §5):

```lean
/-- bounded box in ι → ℝ -/
def boundedBox (a b : ι → ℝ) : Set (ι → ℝ) := Set.pi Set.univ (fun k => Set.Icc (a k) (b k))

def IsPolyFun (P : (Fin n → ℝ) → (ι → ℝ) → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n ⊕ ι) ℝ, ∀ x y, P x y = MvPolynomial.eval (Sum.elim x y) p

/-- Theorem 2.15, (⊇) direction, as the blueprint should state it (growth bound and FT as inputs). -/
theorem thm215_supset (f : (Fin n → ℝ) → ℝ)
    (hsa  : IsSemialgebraic {p : (Fin n → ℝ) × ℝ | p.2 = f p.1})          -- graph semialgebraic
    (hlsc : LowerSemicontinuous f)
    (hcb  : ∀ K : Set (Fin n → ℝ), IsCompact K → ∃ B, ∀ x ∈ K, |f x| ≤ B)
    (hgrowth : ∃ (B : ℝ) (M : ℕ), ∀ x, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M)   -- Prop 2.5 + CB (assumed lemma, §2.0)
    (hFT : ∀ C : Set ((Fin n → ℝ) × ℝ), IsClosed C → IsSemialgebraic C →
            ∃ (a b : ℕ) (p : Fin a → Fin b → MvPolynomial (Fin n ⊕ Unit) ℝ),
              C = {q | ∃ i, ∀ j, 0 ≤ MvPolynomial.eval (Sum.elim q.1 (fun _ => q.2)) (p i j)})  -- FT (assumed)
    (hTS : ...)   -- only to know that the epigraph (or closure of the graph) is semialgebraic, §2.1 L1
    : ∃ (ι : Type) (_ : Fintype ι) (P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ) (a b : ι → ℝ),
        IsPolyFun P ∧ IsPolyFun Q ∧ (∀ k, a k ≤ b k) ∧
        ∀ x, valueFun P Q (boundedBox a b) x = (f x : EReal)
```
(The set-level statement `P_bounded = SA ∩ LSC ∩ CB` is then `Set.ext` of `thm215_supset` and R1's results.)

### 1.2 Theorem 2.21  (C_cc = SA ∩ LSC ∩ CB)

Definition (18): h ∈ C_cc iff ∃ m, polynomials P, Q, and Y ⊆ ℝᵐ compact, convex, semialgebraic, with
Q(x,·) convex on Y for every x, and φ_{P,Q,Y} = h. "Convex in y" := `∀ x, ConvexOn ℝ Y (Q x)`
(`ConvexOn` = Mathlib/Analysis/Convex/Function.lean:54; it includes `Convex ℝ Y`).

Theorem 2.21: C_cc = SA ∩ LSC ∩ CB. (⊆): C_cc ⊆ P_{compact} ⊆ SA ∩ LSC ∩ CB by Prop 2.6 (needs the
version of Prop 2.6 for an arbitrary semialgebraic Y, not only boxes — see §3 item 12) and Cor 2.9.
(⊇): SA ∩ LSC ∩ CB = P_bounded (Thm 2.15) and P_bounded ⊆ C_cc by the *linearization lemma* (§2.3), which is
the whole content of the paper's proof.

```lean
theorem thm221_supset ... (same hypotheses as thm215_supset, plus Carathéodory-type `hTS` use for Y') :
    ∃ (κ : Type) (_ : Fintype κ) (P' Q' : (Fin n → ℝ) → (κ → ℝ) → ℝ) (Y' : Set (κ → ℝ)),
      IsPolyFun P' ∧ IsPolyFun Q' ∧ IsCompact Y' ∧ Convex ℝ Y' ∧ IsSemialgebraic Y' ∧
      (∀ x, ConvexOn ℝ Y' (Q' x)) ∧ ∀ x, valueFun P' Q' Y' x = (f x : EReal)
```

### 1.3 Pessimistic counterparts (Section 2.4)
Same statements with `valueFun` ↦ `pessFun` (⨆) and `LowerSemicontinuous` ↦ `UpperSemicontinuous`.
§2.4 shows the (⊇) constructions are *literally the same* (no adaptation needed beyond swapping the
epigraph for the hypograph); (⊆) needs the usc version of Cor 2.9 (R1).

---------------------------------------------------------------------------------------------------
## 2. Proof route (DAG of lemmas)

Overview of the chosen route for 2.15 (⊇) — it differs from the paper in three cheap ways, all justified below:
 (R-a) use the **epigraph** E := {(x,τ) | f x ≤ τ} instead of cl(graph f). E is closed iff f lsc (Mathlib has this
       verbatim), E is semialgebraic by ONE projection (T–S), and graph f ⊆ E ⊆ epi f is trivial. The paper's
       observation (2) ("f(x) = min{t : (x,t) ∈ cl graph f}") becomes unnecessary; it is still verified in L2' for the record.
 (R-b) do **not** normalize f to h = f/(B+‖x‖^N). Instead keep f and put the scaling polynomial w(x) into the gadget
       (substitute τ = t·w(x) in the P_ij) and into P: P(x,t,z) = t·w(x). This removes the need to prove that
       h is semialgebraic and lsc, and removes the "scaling lemma" for value functions.
 (R-c) split the theorem into (1) a *gadget lemma* turning a ⋃⋂{P_ij ≥ 0} description into a "projection of a
       zero set along a compact box", and (2) a *core lemma* that needs only such a projection description of some
       closed set E with graph f ⊆ E ⊆ epi f. The FT and the growth bound enter only as hypotheses of the top-level
       theorem.

### 2.0 Assumed inputs (NOT IN MATHLIB; T–S-strength real algebraic geometry)

**A1 (Tarski–Seidenberg, projection).** If S ⊆ ℝ^{k} × ℝ^{l} is semialgebraic then {u | ∃ v, (u,v) ∈ S} is semialgebraic.
   Plus elementary closure properties (finite ∩, ∪, complement, cylinders, preimages under polynomial maps) — R2.

**A2 (Finiteness theorem = Prop 2.4; BCR Thm 2.7.2, Benedetti–Risler Ex. 2.5.7).** Every closed semialgebraic
   C ⊆ ℝ^{k} equals ⋃_{i<a} ⋂_{j<b} {P_ij ≥ 0}. (Padding: one may always take a rectangular index set Fin a × Fin b by
   repeating polynomials, so the Lean statement with `Fin a → Fin b → MvPolynomial` loses nothing.)

**A3 (Growth bound under CB; corrected Prop 2.5, see §3 item 1).** If f : ℝⁿ → ℝ has semialgebraic graph and is bounded
   on compact sets, then ∃ B ≥ 0, M : ℕ, ∀ x, |f x| ≤ B + (1 + ∑ᵢ xᵢ²)^M.
   Derivation from the paper's Prop 2.5 (with the Euclidean norm): |f| ≤ ‖x‖^N for ‖x‖ ≥ C and |f| ≤ B on the ball
   ‖x‖ ≤ C (CB); ‖x‖^N ≤ (1+‖x‖²)^{⌈N/2⌉} = (1 + ∑ xᵢ²)^M. Both bounds are *two-sided* (the paper writes f(x) ≤ …,
   but |f(x)| ≤ … is what is used, since t must lie in [−1,1]).
   Why it is unavoidable: if φ_{P,Q,Y} = f with Y a bounded box then |f(x)| ≤ sup_{y∈Y} |P(x,y)| ≤ (polynomial in x),
   so polynomial growth is a *necessary* condition; any proof of 2.15 must produce it, and producing it from "SA ∩ CB"
   is a T–S-strength fact (the standard proof: g(r) := sup_{‖x‖≤r}|f(x)| is finite by CB, semialgebraic by T–S,
   then the one-variable growth lemma).

### 2.1 Lemmas for Theorem 2.15 (⊇)

Notation: w : (Fin n → ℝ) → ℝ, w(x) := B + (1 + ∑ᵢ xᵢ²)^M with B ≥ 0 from A3; so w is a polynomial in x and w(x) ≥ 1 > 0.
E := epigraph of f = {(x,τ) | f x ≤ τ} ⊆ (Fin n → ℝ) × ℝ.

**L1 (E closed and semialgebraic).**
 (a) `IsClosed E` ⟸ `hlsc` by `LowerSemicontinuous.isClosed_epigraph` (Mathlib/Topology/Semicontinuity/Basic.lean:357;
     the iff is `lowerSemicontinuous_iff_isClosed_epigraph`, :353, needs `[ClosedIciTopology ℝ]`, available).
     NB Mathlib's epigraph is literally `{p : α × γ | f p.1 ≤ p.2}` — exactly E, no conversion needed.
 (b) E semialgebraic: E = π_{(x,τ)}( {(x,τ,s) | (x,s) ∈ graph f ∧ 0 ≤ τ − s} ). The inner set is (cylinder over graph f) ∩
     (polynomial inequality) — elementary; the projection is A1. Dependency: R2's closure properties + A1.
 (Alternative, the paper's: C := closure(graph f); closed trivially; semialgebraic by "closure of SA is SA" (BCR Prop 2.2.2),
  which itself is A1 applied twice (∀ε∃y) plus complements. More expensive; see §6.)

**L2 (graph f ⊆ E ⊆ epi f).** Trivial: (x, f x) ∈ E since f x ≤ f x; the second inclusion is equality.
 **L2' (paper's observation (2), for the record; not used in the chosen route).** If f is lsc then for all x,
 (x, f x) ∈ cl(graph f) and ∀ τ, (x,τ) ∈ cl(graph f) → f x ≤ τ; hence f x = min{τ | (x,τ) ∈ cl(graph f)}.
 Proof: graph f ⊆ epi f (pointwise), epi f closed (L1a), so cl(graph f) ⊆ epi f by `closure_minimal`
 (Mathlib/Topology/Closure.lean:199); (x,f x) ∈ cl(graph f) by `subset_closure` (:193). The "min" is attained at τ = f x.
 (The sequential argument of the task description — t = lim f(x_k) ≥ liminf ≥ f(x) — is correct but unnecessary;
 the closed-epigraph argument is the Mathlib-native one. Closedness of {τ | (x,τ) ∈ cl graph f} is also not needed.)

**L3 (FT applied to E).** By A2 (hFT) applied to E (closed by L1a, SA by L1b): ∃ a b (p : Fin a → Fin b → MvPolynomial (Fin n ⊕ Unit) ℝ),
 ∀ x τ, (x,τ) ∈ E ↔ ∃ i, ∀ j, 0 ≤ eval (Sum.elim x (fun _ => τ)) (p i j).
 Define the real functions P_ij(x,τ) := eval (Sum.elim x (fun _ => τ)) (p i j), and the *rescaled* polynomials
 P̃_ij(x,t) := P_ij(x, t·w(x)) (a polynomial in (x,t): substitute `X (inr ())` ↦ `X (inr ()) * w̃` via `MvPolynomial.bind₁`/`aeval`;
 as a *function* it is just composition, and `IsPolyFun` closure under composition with polynomial maps is a small lemma).
 Hence: ∀ x t, (x, t·w(x)) ∈ E ↔ ∃ i, ∀ j, 0 ≤ P̃_ij(x,t).           (★)

**L4 (scalar gadget).** For p z : ℝ define G(p,z) := (p − (p²+1)·z)². Then
 (a) G(p,z) ≥ 0 (`sq_nonneg`).
 (b) G(p,z) = 0 ↔ p = (p²+1)·z (`sq_eq_zero'`/`pow_eq_zero_iff` (Mathlib/Algebra/GroupWithZero/Basic.lean:253) + `sub_eq_zero`).
 (c) (∃ z ∈ Icc 0 (1/2), G(p,z) = 0) ↔ 0 ≤ p.
     (→) p = (p²+1) z with z ≥ 0 and p²+1 > 0 ⇒ p ≥ 0 (`mul_nonneg`).
     (←) take z := p/(p²+1). z ≥ 0 (`div_nonneg`); z ≤ 1/2 ⟺ 2p ≤ p²+1 ⟺ 0 ≤ (p−1)² (`div_le_iff₀`, `sq_nonneg`); G = 0 since
         (p²+1)·(p/(p²+1)) = p (`mul_div_cancel₀`).
 (d) (not needed, verifies paper's (9)): for p < 0 and z ≥ 0, G(p,z) ≥ p² > 0, because p − (p²+1)z ≤ p < 0 so
     |p − (p²+1)z| ≥ |p|; min over [0,1/2] is p² at z = 0 (and the derivative −2(p²+1)(p−(p²+1)z) > 0 on z ≥ 0 confirms
     monotonicity — the task description's sign check is right). For p ≥ 0 the unconstrained minimizer p/(p²+1) ∈ [0,1/2]
     (it is in (−1/2,1/2] for all p, in [0,1/2] iff p ≥ 0), min 0, unique. So (9) is correct.
 The *only* facts used downstream are (a) and (c). No calculus, no uniqueness.

**L5 (box gadget: ⋃⋂{P̃_ij ≥ 0} as a projection of a zero set along a compact box).**
 Let Z := Icc 0 (1/2) ^ (Fin a × Fin b) = `Set.pi univ (fun _ => Icc 0 (1/2))`, and for z : Fin a × Fin b → ℝ put
   R(x,t,z) := ∏_{i : Fin a} ∑_{j : Fin b} G(P̃_ij(x,t), z (i,j)).
 (a) R ≥ 0: `Finset.prod_nonneg` (Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean:34) of
     `Finset.sum_nonneg` of L4a.
 (b) R(x,t,z) = 0 ↔ ∃ i, ∀ j, G(P̃_ij(x,t), z(i,j)) = 0: `Finset.prod_eq_zero_iff` (Mathlib/Algebra/BigOperators/GroupWithZero/Finset.lean:57)
     then `Finset.sum_eq_zero_iff_of_nonneg` (additive version of `Finset.prod_eq_one_iff_of_one_le`,
     Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:240) with L4a.
 (c) (∃ z ∈ Z, R(x,t,z) = 0) ↔ ∃ i, ∀ j, 0 ≤ P̃_ij(x,t).
     (→) from (b) and L4c(→) coordinatewise.
     (←) given i₀ and ∀ j, 0 ≤ P̃_{i₀ j}: by L4c(←) choose z_j ∈ Icc 0 (1/2) with G(P̃_{i₀ j}, z_j) = 0 (`Classical.choose` /
         `choose` tactic on `∀ j, ∃ z, …`); define z(i,j) := z_j if i = i₀ else 0 (0 ∈ Icc 0 (1/2)); then the i₀-th factor is 0.
         IMPORTANT (task item (d)): only ONE factor needs to vanish; the coordinates z(i,j) for i ≠ i₀ are arbitrary in Z.
 (d) R is `IsPolyFun` in (x,(t,z)): closure of polynomial functions under ∏, ∑, squares, composition (`MvPolynomial.eval_prod`
     Mathlib/Algebra/MvPolynomial/Eval.lean:299, `eval_sum` :295, `eval_mul` :289, `eval_pow` :292, `eval_X` :275, `eval_C` :271).
 Combined with (★): ∀ x t, (x, t·w(x)) ∈ E ↔ ∃ z ∈ Z, R(x,t,z) = 0.                                          (★★)

**L6 (core lemma — value function of the "zero-projection" bilevel problem).**
 Hypotheses (pure, no semialgebraicity): f : (Fin n → ℝ) → ℝ; w : (Fin n → ℝ) → ℝ with w x > 0 and |f x| ≤ w x for all x;
 E ⊆ (Fin n → ℝ) × ℝ with (∀ x, (x, f x) ∈ E) and (∀ x τ, (x,τ) ∈ E → f x ≤ τ);
 ζ a type with Fintype, Z ⊆ (ζ → ℝ) any set, R : (Fin n → ℝ) → ℝ → (ζ → ℝ) → ℝ with R ≥ 0 and (★★).
 Define the lower variable y = (t, z) ∈ ℝ × (ζ → ℝ) (index type ι := Unit ⊕ ζ, or Option ζ; see §5),
   Y := Icc (−1) 1 × Z,   Q(x,(t,z)) := R(x,t,z),   P(x,(t,z)) := t · w(x).
 Conclusion: ∀ x, valueFun P Q Y x = (f x : EReal).
 Proof (fix x; write t₀ := f x / w x):
  (i) t₀ ∈ Icc (−1) 1: |f x| ≤ w x and w x > 0 give |t₀| ≤ 1 (`abs_div`, `div_le_one`, `abs_le`).
  (ii) (x, t₀·w x) = (x, f x) ∈ E (`div_mul_cancel₀`), so by (★★) ∃ z₀ ∈ Z, R(x,t₀,z₀) = 0. Hence (t₀,z₀) ∈ Y and Q(x,(t₀,z₀)) = 0.
  (iii) argmin characterization: (t,z) ∈ argminSet Q Y x ↔ (t,z) ∈ Y ∧ R(x,t,z) = 0.
       (←) R ≥ 0 everywhere so 0 ≤ Q(x,y') for all y'. (→) (t,z) ∈ argmin ⇒ Q(x,(t,z)) ≤ Q(x,(t₀,z₀)) = 0 and ≥ 0.
  (iv) lower bound: for (t,z) ∈ argmin, by (iii) and (★★) (x, t·w x) ∈ E, hence f x ≤ t·w x = P(x,(t,z)).
       So `le_iInf₂` : (f x : EReal) ≤ ⨅ y ∈ argmin, (P x y : EReal), using `EReal.coe_le_coe_iff` (Mathlib/Data/EReal/Basic.lean:55).
  (v) upper bound: (t₀,z₀) ∈ argmin by (iii),(ii) and P(x,(t₀,z₀)) = t₀·w x = f x; so `iInf₂_le_of_le` (dual of `le_iSup₂_of_le`,
      Mathlib/Order/CompleteLattice/Basic.lean:229-232) gives ⨅ … ≤ f x.
  (vi) `le_antisymm`.
 Remarks. No compactness, no Berge, no attainment of min of Q is used: existence of a zero (ii) replaces all of it.
 The argmin set is {Q = 0} ∩ Y, i.e. {(t,z) ∈ Y | ∃ i, ∀ j, G_ij = 0}, matching the task's description; the value only
 depends on its t-projection {t ∈ [−1,1] | (x, t w(x)) ∈ E} = [−1,1] ∩ (1/w(x))·{τ | (x,τ) ∈ E}, whose inf is f(x)/w(x).

**L7 (assembly = Thm 2.15 (⊇)).** From A3 get B, M, w; from L1–L3 get the P_ij and (★); from L5 get R, Z, (★★);
 apply L6 with E = epi f (L2). Polynomiality of P, Q: P = X(inr t)·w̃, Q from L5d; Y is the bounded box with
 a = (−1, 0,…,0), b = (1, 1/2, …, 1/2). Dimension of the lower level: 1 + a·b.

### 2.2 (⊆) direction of 2.15 — dependencies only
 P_bounded ⊆ SA: Prop 2.6 (R1/R2; A1). P_bounded ⊆ LSC ∩ CB: Cor 2.9 (R1; Berge / `IsCompact.exists_isMinOn`
 Mathlib/Topology/Order/Compact.lean:255). Nothing to add, except: Cor 2.9's CB proof bounds φ above by max_{C×Y} P and
 below by lsc on a compact — fine; note also that "functions in CB have full domain" is used to make f real-valued.

### 2.3 Lemmas for Theorem 2.21 (⊇): the linearization lemma

Setting. ι a Fintype (lower variable), S : Finset (Fin n ⊕ ι →₀ ℕ) a finite set of exponent vectors (κ := ↥S as index type).
 Moment map  M_S : (ι → ℝ) → (S → ℝ),  M_S y d := ∏_{j : ι} (y j) ^ (d (Sum.inr j)).
 For a polynomial p : MvPolynomial (Fin n ⊕ ι) ℝ with p.support ⊆ S define the x-coefficients
   c_p d x := p.coeff d * ∏_{i : Fin n} (x i) ^ (d (Sum.inl i))                     (a polynomial in x for each d)
 and the linearized function  p^lin (x, λ) := ∑_{d ∈ S} c_p d x * λ d,  λ : S → ℝ.
 This differs from the paper (which indexes λ by y-monomials up to degree d, K_d = C(m+d, d) of them) by using the
 *full* exponent vectors of (x,y)-monomials as index; monomials with the same y-part appear several times, which is harmless
 and avoids any "split a polynomial in (x,y) into y-monomials with x-polynomial coefficients" API
 (`MvPolynomial.sumToIter`, Mathlib/Algebra/MvPolynomial/Equiv.lean:309, would do it but has no `eval` lemma — NOT IN MATHLIB).
 The paper's λ[t] is λ_d for d = single (inr t) 1 (requires d ≥ 1 in the paper; here: requires d ∈ S, automatic since
 P = t·w(x) has support {single(inr t) 1 + (x-exponent)}; see L10).

**L8 (splitting identity).** For p with p.support ⊆ S: ∀ x y, eval (Sum.elim x y) p = p^lin (x, M_S y).
 Proof: `MvPolynomial.eval_eq'` (Mathlib/Algebra/MvPolynomial/Eval.lean:263):
 eval X p = ∑ d ∈ p.support, coeff d p * ∏ i, X i ^ d i; split ∏ over `Fin n ⊕ ι` with `Fintype.prod_sum_type`;
 `Sum.elim_inl/inr`; extend the sum from p.support to S (`Finset.sum_subset`, extra terms have coeff 0). S.

**L9 (linearization lemma; general, no compactness, both optimistic and pessimistic).**
 Let P Q : MvPolynomial (Fin n ⊕ ι) ℝ, S ⊇ P.support ∪ Q.support, Y ⊆ (ι → ℝ) ANY set.
 Put Y' := convexHull ℝ (M_S '' Y), P' := P^lin, Q' := Q^lin (as functions of (x, λ)). Then for all x:
   valueFun P' Q' Y' x = valueFun P Q Y x   and   pessFun P' Q' Y' x = pessFun P Q Y x.
 Proof (fix x; q := Q(x,·) on ι → ℝ, ℓ := Q'(x,·), p := P(x,·), ℓ_P := P'(x,·); ℓ, ℓ_P are linear in λ:
 ℓ = ∑_{d∈S} c_d • proj_d, so ℓ.map_add/map_smul/`map_sum` hold; L8 gives ℓ (M_S y) = q y, ℓ_P (M_S y) = p y).
 Let A := argminSet Q Y x, A' := argminSet Q' Y' x.
  Claim 1: M_S '' A ⊆ A'. Let y ∈ A. M_S y ∈ Y' by `subset_convexHull` (Mathlib/Analysis/Convex/Hull.lean:52).
    For λ ∈ Y': `ConcaveOn.exists_le_of_mem_convexHull` (Mathlib/Analysis/Convex/Jensen.lean:386) with ℓ concave on univ
    (`LinearMap.concaveOn`, Mathlib/Analysis/Convex/Function.lean:392, with `convex_univ`) gives μ ∈ M_S '' Y, ℓ μ ≤ ℓ λ;
    μ = M_S y' with y' ∈ Y, so ℓ (M_S y) = q y ≤ q y' = ℓ μ ≤ ℓ λ.
  Claim 2: A' ⊆ convexHull ℝ (M_S '' A). Let λ ∈ A', m := ℓ λ. By `eq_pos_convex_span_of_mem_convexHull`
    (Mathlib/Analysis/Convex/Caratheodory.lean:123) λ = ∑ᵢ wᵢ • zᵢ with zᵢ ∈ M_S '' Y, wᵢ > 0, ∑ wᵢ = 1 (affine independence
    is not needed; `convexHull_eq` Mathlib/Analysis/Convex/Combination.lean:345 with nonneg weights also works but then one
    must discard zero weights). zᵢ = M_S yᵢ, yᵢ ∈ Y. ℓ λ = ∑ wᵢ ℓ zᵢ = ∑ wᵢ q yᵢ (`map_sum`, `map_smul`), and q yᵢ ≥ m for each i
    (M_S yᵢ ∈ Y', λ ∈ A'). So ∑ wᵢ (q yᵢ − m) = ℓ λ − m = 0 with nonneg terms ⇒ every term is 0
    (`Finset.sum_eq_zero_iff_of_nonneg`) ⇒ q yᵢ = m (wᵢ > 0) ⇒ yᵢ ∈ A (for y' ∈ Y, q y' = ℓ (M_S y') ≥ m).
    Hence λ = ∑ wᵢ • M_S yᵢ ∈ convexHull (M_S '' A) (`Finset.centerMass_mem_convexHull` Combination.lean:256 +
    `Finset.centerMass_eq_of_sum_1` :85, or `Convex.sum_mem`).
    *This is the "convex combination of values ≥ min equals min only if each equals min" argument; no strict convexity.*
  Value, optimistic:
    (≤) ∀ y ∈ A: M_S y ∈ A' (Claim 1) and ℓ_P (M_S y) = p y, so ⨅_{A'} ℓ_P ≤ p y; hence ⨅_{A'} ≤ ⨅_A (`le_iInf₂`, `iInf₂_le_of_le`).
    (≥) ∀ λ ∈ A': λ ∈ convexHull (M_S '' A) (Claim 2); `ConcaveOn.exists_le_of_mem_convexHull` for ℓ_P gives y ∈ A with
        p y ≤ ℓ_P λ; so ⨅_A ≤ p y ≤ ℓ_P λ; hence ⨅_A ≤ ⨅_{A'}.
    Empty case is automatic (both sides ⊤ when A = ∅ ⇒ A' = ∅ by Claim 2; the two inequalities are vacuous/trivial).
  Value, pessimistic: identical with `ConvexOn.exists_ge_of_mem_convexHull` (Jensen.lean:376) and ⨆.
  (Optional Claim 3: A' = convexHull (M_S '' A), since A' is convex — not needed.)

**L10 (the C_cc data).** With (P,Q,Y) from L7 (Y = bounded box, P = t·w(x)): take S := P.support ∪ Q.support.
 (a) P', Q' are `IsPolyFun` in (x, λ): P' = ∑_{d∈S} C(coeff) * ∏ X(inl i)^{d(inl i)} * X(inr d). S.
 (b) Q'(x,·) is convex on Y' for every x: it is linear; `LinearMap.convexOn` (Function.lean:388) with `convex_convexHull`
     (Hull.lean:55); or unfold `ConvexOn` and `simp [Finset.mul_sum, mul_add, Finset.sum_add_distrib]`. S.
     (Task (e): yes, Q' linear ⇒ convex; P' polynomial. ✓)
 (c) Y' convex: `convex_convexHull`. S.
 (d) Y' compact: L11. (e) Y' semialgebraic: L12.
 Then valueFun P' Q' Y' = valueFun P Q Y = f by L9 + L7. This proves Thm 2.21 (⊇) and, more generally,
 **P_{compact SA} ⊆ C_cc** (any polynomial bilevel problem with compact semialgebraic Y linearizes).

**L11 (Carathéodory representation ⇒ compactness of Y').**
 NOT IN MATHLIB: "convex hull of a compact set in a finite-dimensional real space is compact" (only
 `Set.Finite.isCompact_convexHull`, Mathlib/Analysis/Convex/Topology.lean:367, for *finite* sets). Proposed proof:
 (a) [Carathéodory, bounded cardinality] For E := (κ → ℝ), K := Fintype.card κ (= `Module.finrank ℝ E` by
     `Module.finrank_fintype_fun_eq_card`, Mathlib/LinearAlgebra/Dimension/Constructions.lean:322): every λ ∈ convexHull ℝ s
     is ∑_{i<K+1} wᵢ • zᵢ with zᵢ ∈ s, w ∈ stdSimplex ℝ (Fin (K+1)). From `eq_pos_convex_span_of_mem_convexHull`
     (Caratheodory.lean:123) we get a Fintype ι₀, affinely independent z : ι₀ → E, positive weights; then
     `AffineIndependent.card_le_finrank_succ` (Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean:348):
     card ι₀ ≤ finrank (vectorSpan …) + 1 ≤ finrank E + 1 = K+1 (`Submodule.finrank_le` Constructions.lean:401).
     Pad: an embedding ι₀ ↪ Fin (K+1) (`Function.Embedding.nonempty_of_card_le`), weights 0 and points := z i₀ (any point of s;
     s ≠ ∅ since λ ∈ hull s) on the complement. This is the fiddly step (M).
     Hence convexHull ℝ s = Φ '' (stdSimplex ℝ (Fin (K+1)) ×ˢ Set.pi univ (fun _ => s)) where Φ(w,z) := ∑ᵢ wᵢ • zᵢ;
     ⊇ by `Finset.centerMass_mem_convexHull`/`Convex.sum_mem`.
 (b) Compactness: stdSimplex is compact — `isCompact_stdSimplex` (Mathlib/Analysis/Convex/StdSimplex.lean:218) is
     DEPRECATED (2026-08-29) in favour of the new bundled `Convexity.StdSimplex.compactSpace`
     (Mathlib/Geometry/Convex/ConvexSpace/CompactSpaceStdSimplex.lean:69); the robust option is to re-prove it inline:
     `IsCompact.of_isClosed_subset isCompact_Icc (isClosed_stdSimplex ℝ _) (stdSimplex_subset_Icc ℝ)` (StdSimplex.lean:209, :86;
     `isCompact_Icc` from the `CompactIccSpace` instance for pi types, Mathlib/Topology/Order/Compact.lean:86-89).
     Then `IsCompact.prod` (Mathlib/Topology/Compactness/Compact.lean:1071), `isCompact_univ_pi` (:1172), `IsCompact.image` (:124)
     with Φ continuous (`continuous_finset_sum`, `Continuous.smul`, `continuous_apply`).
 (c) M_S '' Y compact: `IsCompact.image` with M_S continuous (`continuous_pi`, `continuous_finset_prod`, `Continuous.pow`);
     Y compact: `isCompact_univ_pi` of `isCompact_Icc`.
 Alternative using the new API: `Set.convexHull_eq_range_iConvexComb` (StdSimplex.lean:181) writes the hull as the range of
 `StdSimplex.affineMapMk` on `StdSimplex ℝ s` — but that simplex is indexed by the (infinite) set s itself, so compactness
 of the domain is not available; Carathéodory is still needed. Rejected.

**L12 (semialgebraicity of Y').** From L11(a): λ ∈ Y' ⟺ ∃ (w : Fin (K+1) → ℝ) (z : Fin (K+1) → ι → ℝ),
 (∀ i, 0 ≤ wᵢ) ∧ ∑ wᵢ = 1 ∧ (∀ i, z i ∈ Y) ∧ (∀ d ∈ S, λ d = ∑ᵢ wᵢ · M_S (z i) d).
 The matrix set is semialgebraic (polynomial equalities/inequalities in (λ,w,z) plus K+1 cylinders over Y, which is
 semialgebraic: a box is a finite intersection of {±(y_k − a_k) ≥ 0}; for a general semialgebraic Y use R2's cylinder lemma);
 Y' is its projection: A1 (one application). The number of quantified variables is (K+1)(1 + |ι|) — finite only thanks to
 Carathéodory's bound K+1; this is the ONLY place where Carathéodory's cardinality bound is essential (in L9 any finite
 convex combination suffices, and in L11 it is used for compactness).
 Exact Mathlib Carathéodory statements: `convexHull_eq_union` (Caratheodory.lean:106) — hull = ⋃ over finsets t ⊆ s with
 `AffineIndependent 𝕜 ((↑) : t → E)` of hull t; and `eq_pos_convex_span_of_mem_convexHull` (:123) — explicit positive combination
 over an affinely independent finite family. The "≤ finrank + 1 points" bound is NOT part of these statements; it comes from
 `AffineIndependent.card_le_finrank_succ` (AffineSpace/FiniteDimensional.lean:348) as in L11(a).

### 2.4 Pessimistic counterparts (Section 2.4 of the paper)

**L13 (core lemma, pessimistic).** Same as L6 with hypotheses "(x, f x) ∈ E and ((x,τ) ∈ E → τ ≤ f x)" (i.e. graph f ⊆ E ⊆ hypograph f),
 conclusion pessFun P Q Y x = f x. Proof identical with ⨆, `iInf`↔`iSup` lemmas swapped (`le_iSup₂_of_le`, `iSup₂_le`).
 With E := hypograph {(x,τ) | τ ≤ f x}: closed iff f usc — `upperSemicontinuous_iff_IsClosed_hypograph`
 (Mathlib/Topology/Semicontinuity/Basic.lean:898; alias `UpperSemicontinuous.IsClosed_hypograph` :901); semialgebraic by A1 as in L1b.
 So the pessimistic Thm 2.15 (⊇) is *the same construction*: P = t·w(x) and the pessimistic selection picks
 max{τ : |τ| ≤ w(x), (x,τ) ∈ E} = f(x). (Task (C): confirmed. With the paper's E = cl(graph f) one needs cl(graph f) ⊆ hypo f,
 which holds iff hypo f closed iff f usc — same lemma.) No "−t" trick needed.
**L14 (linearization, pessimistic)** is part of L9.
**(⊆) pessimistic**: usc of pessimistic value functions with compact Y (Berge; R1) and CB (same bound); SA by the first-order
 description with sup (R1/R2). The paper's remark "value function of pessimistic bilevel problems with compact lower level
 constraints are upper semicontinuous" is correct: φ_p(x) = max_{Θ(x)} P(x,·), and if x_k → x, y_k ∈ Θ(x_k) attain the max, a
 cluster point y of (y_k) lies in Θ(x) by outer semicontinuity, so limsup φ_p(x_k) = P(x,y) ≤ φ_p(x).
**Unbounded boxes (first bullet of §2.4)**: not my scope; the paper's claim (unique minimizers ⇒ any selection rule) is R3's.

---------------------------------------------------------------------------------------------------
## 3. Errors / gaps / typos in the paper, with fixes

1. **Prop 2.5 is false as stated** ("for every semi-algebraic f : ℝⁿ → ℝ there are N, C with |f(x)| ≤ ‖x‖^N for ‖x‖ ≥ C").
   Counterexample (n = 2): f(x,y) := 1/(x−y) for x ≠ y, f(x,x) := 0. Its graph {(x,y,t) : (x−y)t = 1} ∪ {(x,x,0)} is semialgebraic,
   but for any C, N, the points (s+ε, s) with s ≥ C and ε → 0⁺ have norm ≥ C and |f| = 1/ε → ∞. The correct classical statement
   (BCR Prop. 2.6.2 — cite and verify) requires f *continuous* on a closed semialgebraic set; the paper only ever applies
   Prop 2.5 to f ∈ CB, and under CB (or continuity) the statement is true (proof sketch in A3). FIX: add "bounded on compact
   sets" to Prop 2.5, or state A3 directly. (The citation [51, §4.12] could not be checked online; the counterexample is decisive.)
2. In observation (3) of the proof of 2.15: "f(x) ≤ B + ‖x‖^N" should be "|f(x)| ≤ B + ‖x‖^N"; the two-sided bound is what
   makes t = h(x) ∈ [−1,1] (the paper's next sentence silently uses it). Also "B ≥ 0" (or "positive") must be recorded so that
   B + ‖x‖^N ≥ B > 0 is justified (they say "positive constant B", fine).
3. "To prove the equalities in Theorem 2.21" and "the first claim of Theorem 2.21" inside the proof of Theorem 2.15 are
   cross-reference typos for Theorem 2.15.
4. "we may assume that f is bounded in [−1,1]" means "takes values in [−1,1]". The reduction f ↦ h = f/(B+‖x‖^N) is stated
   backwards ("the bilevel problem with (P(B+‖x‖^N), Q, Y) has a value function equal to f" is correct only after the problem
   for h has P = t; fine) but it relies on an unproved general *scaling lemma*: multiplying P by a positive function of x
   multiplies the optimistic value function by it (true: argmin unchanged, inf commutes with multiplication by a positive
   constant; in EReal needs `EReal` mul lemmas — avoidable). It also relies on h being semialgebraic (graph h is the preimage of
   graph f under the polynomial homeomorphism (x,s) ↦ (x, s(B+‖x‖^N)); elementary but unstated) and lsc (quotient of an lsc
   function by a positive continuous function — true, not in Mathlib in that form, unstated). FIX (R-b): skip h entirely;
   substitute τ = t·w(x) into the P_ij and take P = t·w(x) (L3, L6).
5. Case 2 of the proof: "the optimal value of Q is at least ∏_{ij} P_{ij_i}(x,t)²" — the product index should be ∏_{i∈I}.
6. Logical order: "if Q(x,t,z) = 0 then (t,z) ∈ argmin" and "for a minimizer (t,z), (x,t) ∈ cl graph f" both need that the
   minimum value of Q(x,·) is 0, i.e. that a zero exists; the paper establishes existence only afterwards ("such t always
   exists ... due to the boundedness of f"). Harmless; L6 orders it correctly (step (ii) before (iii)).
7. Observation (2) "f(x) = min{t : (x,t) ∈ cl graph f}" is asserted without proof. Proof: cl(graph f) ⊆ epi f because epi f is
   closed (f lsc) and contains graph f; (x,f x) ∈ cl(graph f). (L2'.) The paper never needs the "min" to be attained beyond
   t = f(x) itself.
8. Observation (1) "closure of graph f is semialgebraic [9, Prop 3.1]" is a T–S-strength fact; in the blueprint it must be an
   assumption (or derived from A1). The epigraph route (L1) needs a single projection instead.
9. In (9) the minimizer formula z* = P/(P²+1) is correct and lies in [0,1/2] (2P ≤ P²+1 ⟺ (P−1)² ≥ 0); the sentence
   "t/(1+t²) ∈ [0,1/2] ∀ t ≥ 0" is right. Not an error; but the argmin description of Q's minimizers is *not* "z = z*_ij for all i,j":
   only the active index i needs z_ij = z*_ij, the other z_ij are free (L5c). The paper does not claim otherwise but the
   reader may infer uniqueness.
10. Thm 2.21 proof: (a) it assumes a λ* minimizing λ[t] over argmin Q'(x,·) exists — true (argmin Q' is a closed subset of the
   compact Y', λ[t] continuous) but unproved; the two-inequality argument (L9) avoids attainment. (b) "for all i, λᵢ ∈ argmin Q'
   and λᵢ[t] also attains the minimum" is only valid for indices with cᵢ > 0 (Carathéodory as cited gives cᵢ ≥ 0; with cᵢ = 0
   the claim can fail). FIX: use positive weights (`eq_pos_convex_span_of_mem_convexHull`) or drop zero-weight terms.
   (c) The sentence "λᵢ = M_d((tᵢ,zᵢ)) where (tᵢ,zᵢ) ∈ argmin Q and tᵢ is the smallest possible such value. It implies tᵢ = f(x)"
   is correct only via (b); the cleaner route is: tᵢ ≥ f(x) for every (tᵢ,zᵢ) ∈ argmin Q (L6(iv)) gives λ*[t] = ∑ cᵢ tᵢ ≥ f(x),
   and M_d(f(x)/w(x)... ) ∈ argmin Q' gives ≤. (d) "K_d = C(n+d, n)" and "c ∈ ℝ^{R_d}" use two different names K_d, R_d for the
   same number; the map M_d is defined on Ω but then applied on ℝⁿ — cosmetic.
11. Thm 2.21 proof claims "the semi-algebraicity can be argued similarly (Carathéodory + Theorem 2.3)" — correct, L12 spells it out;
   note that Carathéodory's *cardinality bound* is essential there (first-order formulas must have finitely many quantified
   variables), whereas for the value-function argument any finite combination suffices.
12. The inclusion C_cc ⊆ SA ∩ LSC ∩ CB ("Using Theorem 2.15, we get an immediate relation") is NOT immediate from Thm 2.15:
   it needs Prop 2.6 for a general semialgebraic feasible set Y (Prop 2.6 is stated for boxes only) and Cor 2.9 (compact Y, fine).
   Prop 2.6's proof (first-order description of Θ(x) and of dom φ etc.) works verbatim for any semialgebraic Y. FIX: state
   Prop 2.6 for semialgebraic Y. (Also the displayed "C_bounded ⊆ C_cc" is immediate.)
13. Section 2.4: "all our constructions can be adapted" — for 2.15/2.21 no adaptation is needed (L13); correct but can be
   sharpened as in §2.4 above.
14. Definition 2.1 says "A set S ∈ ℝⁿ" (should be ⊆); Table 2 lists t with feasible set [−1,1] — consistent with (10).
15. Cor 2.9 proof item 3 writes max_{x∈C} φ(x) before knowing it is finite, and reuses the letter C for the bound; cosmetic (R1).

---------------------------------------------------------------------------------------------------
## 4. Mathlib inventory

| Need | Declaration | File:line | Note |
|---|---|---|---|
| lsc ⟺ epigraph closed | `lowerSemicontinuous_iff_isClosed_epigraph`, alias `LowerSemicontinuous.isClosed_epigraph` | Mathlib/Topology/Semicontinuity/Basic.lean:353, :357 | epigraph is `{p : α × γ \| f p.1 ≤ p.2}`; needs `ClosedIciTopology ℝ` ✓ |
| usc ⟺ hypograph closed | `upperSemicontinuous_iff_IsClosed_hypograph`, alias `UpperSemicontinuous.IsClosed_hypograph` | Mathlib/Topology/Semicontinuity/Basic.lean:898, :901 | for L13 |
| lsc definitions | `LowerSemicontinuousAt`, `LowerSemicontinuous` (abbrevs via `SemicontinuousAt (f · > ·)`) | Mathlib/Topology/Semicontinuity/Defs.lean:287, :293 | `UpperSemicontinuous` :317 |
| closure facts (L2') | `subset_closure`, `closure_minimal`, `IsClosed.closure_subset_iff`, `mem_closure_iff_nhds` | Mathlib/Topology/Closure.lean:193, :199, :240; Mathlib/Topology/ClusterPt.lean:301 | |
| product nhds (if sequential route) | `nhds_prod_eq`, `prod_mem_nhds` | Mathlib/Topology/Constructions/SumProd.lean:249, :306 | not needed in chosen route |
| compact interval / box | `isCompact_Icc` (field of `CompactIccSpace`), pi instance; `isCompact_univ_pi`; `IsCompact.prod` | Mathlib/Topology/Order/Compact.lean:53-56, :86-89; Mathlib/Topology/Compactness/Compact.lean:1172, :1071 | |
| continuous image compact | `IsCompact.image` | Mathlib/Topology/Compactness/Compact.lean:124 | |
| min attained on compact (Cor 2.9, R1) | `IsCompact.exists_isMinOn` | Mathlib/Topology/Order/Compact.lean:255 | `IsMinOn` = Mathlib/Order/Filter/Extr.lean:112 |
| convex box | `convex_pi`, `convex_Icc` | Mathlib/Analysis/Convex/Basic.lean:108, :257 | |
| convex hull basics | `subset_convexHull`, `convex_convexHull`, `convexHull_min`, `Convex.convexHull_subset_iff`, `convexHull_mono` | Mathlib/Analysis/Convex/Hull.lean:52, :55, :66, :68, :72 | |
| explicit convex combinations | `convexHull_eq`, `Finset.convexHull_eq`, `Finset.centerMass_mem_convexHull`, `Finset.centerMass_eq_of_sum_1`, `convexHull_eq_union_convexHull_finite_subsets` | Mathlib/Analysis/Convex/Combination.lean:345, :392, :256, :85, :432 | |
| Carathéodory | `convexHull_eq_union`; `eq_pos_convex_span_of_mem_convexHull` | Mathlib/Analysis/Convex/Caratheodory.lean:106; :123 | positive weights, affinely independent family; NO cardinality bound in the statement |
| cardinality bound | `AffineIndependent.card_le_finrank_succ`; `Submodule.finrank_le`; `Module.finrank_fintype_fun_eq_card` | Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean:348; Mathlib/LinearAlgebra/Dimension/Constructions.lean:401, :322 | gives card ≤ K+1 |
| min/max principle on hull | `ConcaveOn.exists_le_of_mem_convexHull`, `ConvexOn.exists_ge_of_mem_convexHull` | Mathlib/Analysis/Convex/Jensen.lean:386, :376 | core of L9 |
| linear ⇒ convex/concave | `LinearMap.convexOn`, `LinearMap.concaveOn` | Mathlib/Analysis/Convex/Function.lean:388, :392 | `ConvexOn` def :54 |
| image of hull under linear/affine map | `LinearMap.image_convexHull`, `AffineMap.image_convexHull` | Mathlib/Analysis/Convex/Hull.lean:164, :194 | optional |
| compact hull of compact set (finite dim) | **NOT IN MATHLIB** (only `Set.Finite.isCompact_convexHull`) | Mathlib/Analysis/Convex/Topology.lean:367 | prove via L11 |
| simplex compact | `isCompact_stdSimplex` (DEPRECATED 2026-08-29), `isClosed_stdSimplex`, `stdSimplex_subset_Icc`, `stdSimplex` def | Mathlib/Analysis/Convex/StdSimplex.lean:218, :209, :86, :40 | new bundled `Convexity.StdSimplex.compactSpace` Mathlib/Geometry/Convex/ConvexSpace/CompactSpaceStdSimplex.lean:69; `Set.convexHull_eq_range_iConvexComb` StdSimplex.lean:181 |
| sums/products ≥ 0, = 0 | `Finset.prod_nonneg`, `Finset.prod_pos`, `Finset.prod_eq_zero_iff`, `Finset.sum_eq_zero_iff_of_nonneg` (to_additive of `Finset.prod_eq_one_iff_of_one_le`) | Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean:34, :160; Mathlib/Algebra/BigOperators/GroupWithZero/Finset.lean:57; Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:240 | `Finset.sum_nonneg` in same Group/Finset file |
| squares | `sq_nonneg`, `pow_eq_zero_iff`, `mul_self_eq_zero` | Mathlib/Algebra/GroupWithZero/Basic.lean:253; Mathlib/Algebra/GroupWithZero/Defs.lean:315 | |
| division bounds (L6 i) | `div_le_one`, `abs_div` | Mathlib/Algebra/Order/Field/Basic.lean:43, :673 | |
| MvPolynomial eval | `eval_eq`, `eval_eq'`, `eval_monomial`, `eval_C`, `eval_X`, `eval_mul`, `eval_pow`, `eval_sum`, `eval_prod`, `as_sum`, `eval_rename` | Mathlib/Algebra/MvPolynomial/Eval.lean:259, :263, :267, :271, :275, :289, :292, :295, :299; Basic.lean:965; Rename.lean:244 | `eval_eq'` needs `[Fintype σ]` |
| polynomial continuity | `MvPolynomial.continuous_eval` | Mathlib/Topology/Algebra/MvPolynomial.lean:31 | for M_S, w continuity (or `fun_prop`) |
| splitting (x,y)-polynomials | `MvPolynomial.sumToIter`, `sumAlgEquiv` | Mathlib/Algebra/MvPolynomial/Equiv.lean:309, :354 | no `eval` lemma — avoided by L8 |
| ∏ over a sum type | `Fintype.prod_sum_type` | Mathlib/Data/Fintype/BigOperators.lean:268 | used in L8 |
| substitution τ = t·w(x) in a polynomial (L3) | `MvPolynomial.bind₁`, `bind₁_X_right`, `eval₂Hom_bind₁`, `aeval_bind₁` | Mathlib/Algebra/MvPolynomial/Monad.lean:136, :250, :254 | `eval` is `eval₂Hom (RingHom.id ℝ)`, so `eval₂Hom_bind₁` gives eval (bind₁ g φ) = eval₂ id (fun i => eval X (g i)) φ |
| projection along compact factor is closed (§6.2 remark only) | `isClosedMap_fst_of_compactSpace`, `isClosedMap_snd_of_compactSpace` | Mathlib/Topology/Maps/Proper/Basic.lean:332, :337 | not needed for the proofs |
| EReal coercions | `EReal.coe_le_coe_iff`, `EReal.coe_lt_coe_iff` | Mathlib/Data/EReal/Basic.lean:55, :61 | |
| iInf/iSup over bounded index | `le_iSup₂`/`iInf₂_le` (to_dual), `le_iSup₂_of_le`/`iInf₂_le_of_le`, `iSup₂_le`/`le_iInf₂` | Mathlib/Order/CompleteLattice/Basic.lean:225-240 | |
| index equivalences | `finProdFinEquiv`, `Fin.appendEquiv`, `Fin.cons`, `Fin.consEquiv`, `Fin.snoc`, `Fin.snocEquiv`, `Fintype.equivFin` | Mathlib/Logic/Equiv/Fin/Basic.lean:330, :401; Mathlib/Data/Fin/Tuple/Basic.lean:114, :184, :522, :722; Mathlib/Data/Fintype/EquivFin.lean:80 | for Fin m transport |
| T–S, FT, growth bound, closure-of-SA-is-SA, "semialgebraic" | **NOT IN MATHLIB** | — | A1, A2, A3 (assumptions) |

---------------------------------------------------------------------------------------------------
## 5. Lean encoding decisions and pitfalls

1. **Lower-variable index type.** The 2.15 construction has y = (t, z) with z : Fin a × Fin b → ℝ, and 2.21 has λ : S → ℝ with S a
   Finset of exponent vectors. Forcing `Fin m` everywhere costs an `Equiv` (`Fin.consEquiv`/`finProdFinEquiv`/`Fintype.equivFin`)
   and a `MvPolynomial.rename` on every statement. Recommendation: define `argminSet`, `valueFun`, `pessFun`, `boundedBox`,
   `IsPolyFun` for an arbitrary `[Fintype ι]`, define the classes P_bounded, C_cc as `∃ (ι : Type) [Fintype ι] …`, and prove ONE
   transport lemma `valueFun_comp_equiv (e : ι ≃ ι')` (argmin and box transport along `e`; polynomiality via
   `MvPolynomial.rename (Sum.map id e)` + `eval_rename`). Then the `Fin m` form is a corollary. Needs agreement with R1/R2.
2. **Polynomials as functions.** Carry `P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ` with an `IsPolyFun` side-condition. All value-function
   reasoning (L6, L9) is then about real functions; polynomiality is discharged by closure lemmas (sum, product, square, composition
   with polynomial maps, coordinate projections, constants). This avoids `MvPolynomial` term manipulation in the main proofs.
   Lemma needed once: `IsPolyFun` closed under `Finset.prod`/`Finset.sum` (`eval_prod`/`eval_sum`) and substitution of a polynomial
   for a variable (`MvPolynomial.bind₁` + `eval₂Hom_bind₁` (Mathlib/Algebra/MvPolynomial/Monad.lean:250); or simply reprove `IsPolyFun` of P̃_ij directly as `IsPolyFun` of (x,t) ↦ P_ij(x, t·w x) by induction
   on the polynomial `MvPolynomial.induction_on`). (M, one-off.)
3. **Semialgebraic sets in a product.** Graph/epigraph live in `(Fin n → ℝ) × ℝ`. If R2's `IsSemialgebraic` is over `Fin k → ℝ`,
   transport with `Fin.snocEquiv`/`Fin.consEquiv` (continuous both ways, so closedness transports; `Homeomorph` instance may be
   `Fin.consEquiv`-based — grep `Homeomorph.piFinSuccAbove` if needed). Simpler: let R2's predicate be parametrized by a `Fintype`
   index type and state the FT (A2) for `(Fin n → ℝ) × ℝ` via the polynomial ring `MvPolynomial (Fin n ⊕ Unit) ℝ` as in hFT above.
4. **EReal.** `valueFun` is `⨅ y ∈ A, ((P x y : ℝ) : EReal)`; over an empty A this is ⊤. L6/L9 only use `le_iInf₂`, `iInf₂_le_of_le`,
   `EReal.coe_le_coe_iff`, `le_antisymm` — no EReal arithmetic at all (that is the reason for route R-b: the paper's scaling lemma
   would need `EReal` multiplication). Statement "valueFun … x = (f x : EReal)" implicitly encodes Θ(x) ≠ ∅.
5. **Decidability.** L5c(←) defines z by `if i = i₀ then … else 0`: `Fin` has decidable eq; use `Function.update`/`Pi.single`-style
   or `fun ij => if ij.1 = i₀ then z' ij.2 else 0`. `Finset.sum_eq_zero_iff_of_nonneg` and `Finset.prod_eq_zero_iff` need
   `classical` in places.
6. **Moment map indexing.** With κ := ↥S (S : Finset (Fin n ⊕ ι →₀ ℕ)), `Fintype κ` is automatic (`Finset.fintypeCoeSort`),
   `finrank ℝ (κ → ℝ) = S.card`. Avoid `Finsupp.degree ≤ d` subtype indexing (needs a Fintype instance proof). `M_S y d = ∏ j, y j ^ d (Sum.inr j)`.
   L8 needs `Fintype.prod_sum_type` and `Finset.sum_subset`.
7. **Linear maps on κ → ℝ.** For `LinearMap.concaveOn` build ℓ as `∑ d, c d • LinearMap.proj d` (or `Fintype.linearCombination`);
   alternatively prove the two inequalities of L9 by hand with `Finset.sum` algebra (`Finset.mul_sum`, `Finset.sum_comm`,
   `Finset.sum_smul`), avoiding `LinearMap` bundling. Either is S.
8. **Deprecations.** `isCompact_stdSimplex` is deprecated (2026-08-29); reprove inline (L11b). `Finset.prod_eq_one_iff_of_one_le'`
   deprecated (2026-09-01) — use the unprimed name / its additive version `Finset.sum_eq_zero_iff_of_nonneg`.
9. **Growth polynomial.** Use w(x) = B + (1 + ∑ i, x i ^ 2) ^ M (sup norm on `Fin n → ℝ` is not polynomial; (1+∑x²)^M ≥ 1 avoids
   the "N even" fuss of the paper). Keep B ≥ 0 so w ≥ 1 > 0 (`add_pos_of_nonneg_of_pos`, `one_le_pow₀`).
10. `Set.Icc (-1) 1 ×ˢ Z` vs a single `Set.pi` over `Unit ⊕ (Fin a × Fin b)`: if the box is defined as `Set.pi univ (Icc ∘ …)`,
    represent t as the `Sum.inl ()` coordinate; membership unfolds by `Set.mem_pi`, `Sum.forall`. Fine either way.

---------------------------------------------------------------------------------------------------
## 6. Alternatives considered

1. **Paper's route via cl(graph f) and h = f/(B+‖x‖^N).** Rejected (see §3 items 4, 7, 8): needs "closure of SA is SA" (two
   quantifier alternations under A1), semialgebraicity and lsc of h, and a value-function scaling lemma in EReal. The epigraph +
   substituted-polynomials route (L1–L6) is strictly cheaper and proves the same theorem. The paper's route is kept as L2' for the
   auditor; if the blueprint insists on cl(graph f), replace L1 by [closure SA (assumed) + `isClosed_closure`] and L2 by L2'.
2. **Can the "≥ 0" (FT) representation be avoided?** (task (e)) No, and the obstruction is intrinsic:
   - Any construction of this kind produces, for the t-fibre, the set {(x,t) | ∃ z ∈ Z, Q(x,t,z) = min_Y Q(x,·)}; with Z a compact box
     and Q continuous, {(x,t) | ∃ z ∈ Z, Q(x,t,z) = 0} is the projection along a compact factor of a closed set, hence CLOSED
     (`isClosedMap_snd_of_compactSpace`-type fact). So the set encoded must be closed and must be presented as
     π_Z({R = 0} ∩ (ℝ^{n+1} × Z)); and {R = 0} ∩ (ℝ^{n+1} × Z) is itself a *basic closed* set (R = 0, z_k − a_k ≥ 0, b_k − z_k ≥ 0).
     Conversely the gadget L4/L5 shows every finite ⋃⋂{P_ij ≥ 0} has such a presentation. So the minimal hypothesis for the core
     is exactly (★★); producing (★★) for an arbitrary closed semialgebraic set from a description with strict inequalities
     is equivalent in strength to the FT (projections of basic closed sets along compact boxes are closed SA sets; showing every
     closed SA set is one is the FT's content).
   - Strict-inequality gadgets fail: "Q_j > 0 ⟺ ∃ u ∈ [0,c], u·Q_j = 1" needs u = 1/Q_j unbounded as Q_j → 0⁺, so a compact box cannot
     work, and with an unbounded box the argmin need not be closed/nonempty. Taking closures piecewise fails:
     cl{P = 0, Q > 0} ⊊ {P = 0, Q ≥ 0} in general (P = xy, Q = x: nonnegative x-axis vs. nonnegative x-axis ∪ y-axis), so the closure
     of a basic set has no cheap polynomial description.
   - "Zero set of a continuous semialgebraic function" (e.g. dist(·,C)) does not help: one still needs a polynomial description of
     that function's graph, i.e. the same problem one dimension up.
   Decision: state Thm 2.15' (= L7 with hFT, hgrowth as hypotheses) in the blueprint, plus A2 and A3 as separate assumed lemmas.
   The generalized core L6 is also useful on its own (no semialgebraicity in it at all).
3. **Thm 2.21 via the paper's degree-d moment map M_d.** Rejected in favour of the exponent-set moment map M_S (L8): avoids
   `Finsupp.degree`-bounded index subtypes, avoids splitting (x,y)-polynomials with `sumToIter` (no `eval` API), and makes
   P' = (x-polynomial coefficients)·λ automatically. Mathematically identical (K_d is replaced by |S| ≤ |supp P| + |supp Q|).
4. **Thm 2.21 using the paper's "λ*[t] attains the min over argmin Q'" claim.** Rejected (task (d)): needs attainment (compactness
   of argmin Q') and positivity of weights; the two-inequality proof L9 needs neither and also covers the pessimistic case and
   the empty-argmin case uniformly.
5. **Compactness of Y' via the new `ConvexSpace`/`StdSimplex` API** (`Set.convexHull_eq_range_iConvexComb`): rejected, the simplex
   there is indexed by the whole set s, so no compactness without Carathéodory anyway.
6. **Avoiding Carathéodory for L9**: done — L9 uses only `eq_pos_convex_span_of_mem_convexHull` for positivity of weights (any
   finite combination would do). Carathéodory's bound is needed only for L11 (compactness) and L12 (semialgebraicity).
7. **Pessimistic 2.15 via "−t" trick**: unnecessary (L13); the same P = t·w(x) works with E = hypograph.

---------------------------------------------------------------------------------------------------
## 7. Effort / risk per lemma (S < M < L < XL), assume vs prove

| Item | Effort | Assume/prove | Risk |
|---|---|---|---|
| A1 T–S (projection) + elementary closure properties | XL / M | ASSUME A1; prove closure properties (R2) | — |
| A2 Finiteness theorem | XL | ASSUME | statement padding to Fin a × Fin b must be included in the assumption |
| A3 growth bound (SA ∩ CB ⇒ polynomial growth) | L–XL | ASSUME (state in polynomial form) | paper's Prop 2.5 is wrong without CB (§3.1) |
| L1 E closed & SA | S (a) / S given A1 (b) | prove | none |
| L2, L2' | S | prove | none |
| L3 FT instance + substitution τ = t·w(x) | M | prove (IsPolyFun composition) | `bind₁`/`aeval` eval lemma to locate; fallback: induction |
| L4 scalar gadget | S | prove | none (pure `nlinarith`/field_simp) |
| L5 box gadget | M | prove | choice of z coordinates; Finset sum/prod zero lemmas |
| L6 core lemma | M | prove | EReal iInf bookkeeping only |
| L7 assembly + polynomiality bookkeeping | M | prove | index-type plumbing (§5.1) |
| L8 splitting identity | S–M | prove | `Fintype.prod_sum_type`, `Finset.sum_subset` |
| L9 linearization (opt + pess) | M | prove | positive weights from Caratheodory.lean:123; `map_sum`/`map_smul` on hand-rolled linear maps |
| L10 C_cc data (polynomiality, convexity) | S | prove | none |
| L11 compact hull of compact (Carathéodory + padding) | M–L | prove (NOT IN MATHLIB) | padding of ≤K+1 points to exactly K+1; deprecated `isCompact_stdSimplex` |
| L12 Y' semialgebraic | S given A1 + L11a | prove | depends on R2's cylinder/product lemmas |
| L13 pessimistic core | S (copy of L6) | prove | none |
| (⊆) directions | — | R1/R2 (Prop 2.6 for general SA Y!, Cor 2.9 and its usc twin) | §3.12 |
| Transport to `Fin m` | M | prove once | `rename`/`eval_rename` |

Total for my scope, excluding A1–A3 and (⊆): roughly 10 M-lemmas + a dozen S-lemmas; L11 is the riskiest purely-Mathlib piece.

---------------------------------------------------------------------------------------------------
## 8. Open questions for the auditor

1. Agree on the index-type policy (§5.1): arbitrary `[Fintype ι]` for lower variables + one transport lemma, vs. `Fin m` everywhere.
2. Agree that the blueprint states Thm 2.15 (⊇) with A2 (FT) and A3 (growth) as explicit hypotheses/assumed lemmas, and that
   the paper's Prop 2.5 is replaced by A3 (with CB). Does anyone want the one-variable growth lemma proved (L–XL)?
3. Epigraph route (L1) vs. the paper's closure route: confirm R2's assumed T–S interface makes "epi f semialgebraic" a one-liner
   (cylinder + polynomial inequality + one projection). If R2 instead assumes "closure of SA is SA" as a primitive, both routes cost
   the same and L2' replaces L2.
4. Prop 2.6 must be stated for arbitrary semialgebraic Y (not only boxes) for the (⊆) inclusion of Thm 2.21 — R1/R2 please confirm.
5. Should the blueprint record the stronger corollary of L9: "for any polynomial (P,Q) and compact semialgebraic Y, (P,Q,Y) and
   (P^lin, Q^lin, conv M_S(Y)) have the same optimistic and pessimistic value functions", hence C_cc = P_{compact SA} ⊇ P_bounded?
6. For L3 the substitution lemma is `MvPolynomial.eval₂Hom_bind₁` (Monad.lean:250) — resolved; the induction fallback is not needed.
7. The paper's Prop 2.5 citation [51, §4.12] could not be verified online (search returned only the paper's metadata:
   https://portal.mardi4nfdi.de/wiki/Publication:1922131); the counterexample in §3.1 stands regardless. BCR Prop. 2.6.2
   (continuous f on closed A) should be checked as the correct reference.
