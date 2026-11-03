# W4-c AUDIT (Convex/Linearize.lean, Convex/Hull.lean)

## 1. Verdict: ACCEPT (no required fixes; one optional usability improvement)
* Builds clean; no sorry/axiom/etc.; all 25 public decls have axioms ⊆ {propext, Classical.choice, Quot.sound}.
* t221_splitting, t221_linearize (value AND pvalue, arbitrary Y, no compactness/nonempty/convexity), cc_data, caratheodory_union,
  hull_compact all IDENTICAL to the blueprint (or strengthened: cc_data a/b without [Fintype ι]).
* Wart: the support-union hypothesis is awkward to discharge for concrete ι (see §5); not a faithfulness issue.

## 2. Build / hygiene / axioms
* `lake build HardnessBilevel.Convex.Linearize HardnessBilevel.Convex.Hull` -> "Build completed successfully" (only the unrelated Box.lean module-system warning).
* grep for sorry|axiom|native_decide|unsafe|admit|instance..Has(...)|maxHeartbeats|open Classical|stdSimplex|mem_setOf_eq in both files: no hits
  (stdSimplex only appears nowhere in code; header says it is not used; `Set.mem_ofPred_eq` is the non-deprecated name).
* `#print axioms` scratch file <SCRATCH>/lean/W4c.lean: 25 decls (Msp, cPoly, plin, plinLin, plinLin_apply, t221_splitting, t221_claim1/2,
  t221_linearize_value/_pvalue/t221_linearize, t221_cc_data_{isPolyFun,convexLower,convex,nonempty}, t221_cc_data, hullWeights, hullComb,
  t221_caratheodory_union, weights_isClosed/_isCompact, continuous_hullComb, isCompact_convexHull_of_isCompact, continuous_Msp,
  isCompact_convexHull_Msp): all 25 print `[propext, Classical.choice, Quot.sound]` (defs print no/subset axioms; count of matching lines = 25).

## 3. Faithfulness
| blueprint id | Lean | verdict | note |
|---|---|---|---|
| Msp | `Msp S y d = ∏ j, y j ^ d.1 (inr j)`, d : ↥S | IDENTICAL | |
| c_p | `cPoly p d x = p.coeff d.1 * ∏ i, x i ^ d.1 (inl i)` | IDENTICAL | x-dependent (E-15) |
| p^lin | `plin S p x l = ∑ d : S, cPoly p d x * l d` | IDENTICAL | |
| t221.splitting | `t221_splitting : p.support ⊆ S → eval (Sum.elim x y) p = plin S p x (Msp S y)` | IDENTICAL | |
| Claim 1 | `t221_claim1` | IDENTICAL | uses concaveOn.exists_le_of_mem_convexHull; chain `q y ≤ q y' = ℓ μ ≤ ℓ λ` correct |
| Claim 2 | `t221_claim2` | IDENTICAL | uses `eq_pos_convex_span_of_mem_convexHull` (positive weights); `Finset.sum_eq_zero_iff_of_nonneg` on `w i*(ℓ(z i)-m)`; `w i>0` ⇒ `ℓ(z i)=m`; then yv i ∈ A by m ≤ ℓ(Msp y') for y'∈Y; conclude via Convex.sum_mem. Re-derived by me: correct. |
| t221.linearize | `t221_linearize_value`, `_pvalue`, `t221_linearize` (conjunction of ∀x) | IDENTICAL | hyp only `P.support ∪ Q.support ⊆ S`; Y arbitrary; conclusion valueFun AND pvalueFun equalities with Pf x y = eval (Sum.elim x y) P. Empty-argmin: no hypothesis excludes it; value proof is two `le_iInf₂`/`iSup₂_le` directions (⊤ resp. ⊥ cases automatic via Claim 1/2). |
| t221.cc_data (a) | `t221_cc_data_isPolyFun` | STRENGTHENED | lower index `↥S : Type`; no [Fintype ι] needed; works for any p (P' and Q') |
| (b) | `t221_cc_data_convexLower : ConvexLower (plin S q)` | IDENTICAL | ConvexOn ℝ univ |
| (c) | `t221_cc_data_convex` | IDENTICAL | |
| (d) | `isCompact_convexHull_Msp` (Hull.lean) | IDENTICAL | Y compact ⇒ hull compact |
| (e) hull_sa | not provided | MISSING (justified) | needs A1; assigned elsewhere (W4-d) |
| (f) | `t221_cc_data_nonempty` | IDENTICAL | |
| t221.caratheodory_union | `t221_caratheodory_union (s : Set (κ → ℝ))`, [Fintype κ] | IDENTICAL | `hullWeights k = {w | (∀ i,0≤w i) ∧ ∑ w i = 1}`; range `k < card κ + 2`; image under `hullComb k` of `hullWeights k ×ˢ pi univ (fun _ => s)`; no stdSimplex |
| t221.weights_compact | `weights_isClosed`, `weights_isCompact` | IDENTICAL | |
| t221.hull_compact | `isCompact_convexHull_of_isCompact : IsCompact s → IsCompact (convexHull ℝ s)`, s : Set (κ → ℝ), [Fintype κ] | IDENTICAL | |
| (compact_sa_incl, hull_sa, subset/supset/eq) | — | MISSING (out of unit scope) | |

Scratch usage checks (<SCRATCH>/lean/W4c_use.lean, compiles): `t221_linearize` with n=1, ι=Fin 1, P = X(inr 0), Q = (X(inr 0) - X(inl 0))^2, Y = `boundedBox (fun _ => 0) (fun _ => 1)`, S := P.support ∪ Q.support (both `.1` and `.2` specialised at x); `isCompact_convexHull_of_isCompact` on `Set.pi univ fun _ : Fin 1 => Icc 0 1`; `isCompact_convexHull_Msp`; `t221_cc_data_isPolyFun`.

## 4. Required fixes
None.

## 5. Optional improvements
1. Usability: the hypothesis `P.support ∪ Q.support ⊆ S` elaborates with the `DecidableEq (Fin n ⊕ ι →₀ ℕ)` instance `FunLike.toDecidableEq` (via `[Fintype ι]`). For CONCRETE ι (e.g. Fin 1) a user-written `P.support ∪ Q.support` synthesises a different instance (`Finsupp.instDecidableEq`), so the obvious proofs `Finset.Subset.refl _`, `le_refl _`, `Finset.union_subset h1 h2`, `sup_le h1 h2` fail with type mismatch or whnf timeouts. What works: `(by intro d hd; simpa using hd)` (verified). Generic ι works. Suggest adding corollaries `t221_linearize_value'/pvalue'/t221_linearize'` taking `(hP : P.support ⊆ S) (hQ : Q.support ⊆ S)` (trivial via `Finset.union_subset`-in-proof inside the file, where instances agree), and have downstream W4-d use those. Equivalent mathematically, so no faithfulness impact.
2. `t221_cc_data` bundle omits nothing from (a),(b),(c),(f); fine. `hullWeights`/`hullComb` naming deviation is declared and harmless.
