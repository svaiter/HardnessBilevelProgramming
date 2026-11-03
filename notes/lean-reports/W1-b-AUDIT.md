# W1-b AUDIT (HardnessBilevel/Framework/Poly.lean)

## 1. Verdict: ACCEPT
- Definitions `IsPolyFun`/`polyFun` are literally the blueprint's; all closure and continuity lemmas present, in the shapes later waves need.
- Build clean, no hygiene hits, all 35 public declarations depend only on {propext, Classical.choice, Quot.sound}.
- Scratch usability tests (concrete instantiations) all compile. No required fixes.

## 2. Build / hygiene / axioms
- `lake build HardnessBilevel.Framework.Poly` -> "Build completed successfully" (only the generic "consider adding `module`" warning).
- grep for `sorry|axiom|native_decide|unsafe|admit|maxHeartbeats|open Classical|instance.*Has` over Poly.lean: no hits (`classical` tactic used only inside two proofs).
- `lake env lean <SCRATCH>/lean/W1b.lean`: `#print axioms` on all 35 public decls (IsPolyFun, polyFun, polyFun_apply, isPolyFun_polyFun, of_eq, iff_exists_polyFun, const/upper/lower/x/y, add/neg/sub/mul/pow/const_mul/mul_const/smul_const, finset_sum/prod, of_upper_only/of_lower_only, eval_bind₁', comp, comp_upper, comp_upper_poly, comp_lower, rename, rename_equiv, continuous_sumElim_prod, continuous_uncurry/right/left, continuous_polyFun): every one is [propext, Classical.choice, Quot.sound]; 0 errors.
- Usability examples in the same file (all compile): `IsPolyFun (fun (x : Fin 1 → ℝ) (y : Unit → ℝ) => (x 0 - y ())^2 + 1)` via `(((isPolyFun_upper 0).sub (isPolyFun_lower ())).pow 2).add (isPolyFun_const 1)`; `∑ j : Fin 3, x 0 * y j ^ 2` via `isPolyFun_finset_sum`; `hF.comp_upper_poly ![X 0 ^ 2, X 0 + 1]` for F on Fin 2 (result form `F (fun i => eval x' (q i)) y` matched by unification); `hF.rename e` with `e : Fin 3 → Unit ⊕ Fin 2`; `hF.continuous_uncurry : Continuous (Function.uncurry F)`.

## 3. Faithfulness
| blueprint id | Lean name | verdict | note |
|---|---|---|---|
| §4.A.1 IsPolyFun | `Bilevel.IsPolyFun` | IDENTICAL | `∃ p : MvPolynomial (Fin n ⊕ ι) ℝ, ∀ x y, F x y = MvPolynomial.eval (Sum.elim x y) p`; ι : Type* (more general than Type, fine) |
| §4.A.1 polyFun | `Bilevel.polyFun` | IDENTICAL | noncomputable, same body |
| fw.isPolyFun_closure: constants, coordinates | `isPolyFun_const/upper/lower` (+aliases `_x/_y`) | IDENTICAL | |
| +, -, *, ^k | `IsPolyFun.add/neg/sub/mul/pow` | IDENTICAL | pointwise-lambda form `fun x y => F x y + G x y` |
| Finset sum/prod | `isPolyFun_finset_sum/prod` | IDENTICAL | over any `κ : Type*`, `s : Finset κ`, `H : κ → …`, `∀ k ∈ s, IsPolyFun (H k)` |
| substitution of upper variable | `IsPolyFun.comp_upper_poly` (explicit `q : Fin n → MvPolynomial (Fin n') ℝ`), `comp_upper` (existential form), general `comp`, `comp_lower` | IDENTICAL/STRENGTHENED | `comp` allows simultaneous substitution of both variables by polyfuns, witness via `bind₁` |
| renaming along Equiv/injection | `IsPolyFun.rename` (arbitrary `e : ι → ι'`), `rename_equiv` | STRENGTHENED | arbitrary map; shape `fun x y' => F x (fun j => y' (e j))` as expected |
| fw.continuous_polyFun | `IsPolyFun.continuous_uncurry`, `continuous_right`, `continuous_left`, `continuous_polyFun` | IDENTICAL | `Continuous (Function.uncurry F)`, `Continuous (F x)` |
Extras (`of_eq`, `of_upper_only/lower_only`, `eval_bind₁'`, `isPolyFun_iff_exists_polyFun`, `continuous_sumElim_prod`, `const_mul` etc.) are harmless helpers; none alters a definition's meaning. Declared deviations: none; none found.

## 4. Required fixes
None.

## 5. Optional improvements
- `smul_const` is stated with `c • F x y` (fine); `comp_upper` existential hypothesis form could also have a `∀ x'` variant — not needed.
- `eval_bind₁'` is a public name in `Bilevel`; could be marked `private`/renamed if a Mathlib `eval_bind₁` appears later (collision risk is low).
- Aliases `isPolyFun_x/_y` duplicate `_upper/_lower`; harmless.
