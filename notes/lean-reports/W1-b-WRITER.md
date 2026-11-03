# W1-b WRITER report

Files delivered: /home/user/HardnessBilevelProgramming/HardnessBilevel/Framework/Poly.lean (imports Mathlib only; namespace Bilevel).

Blueprint ids implemented:
* §4.A.1 `IsPolyFun` (verbatim), `polyFun` (verbatim); plus `polyFun_apply` (simp, rfl), `isPolyFun_polyFun`,
  `IsPolyFun.of_eq` (transport along pointwise equality), `isPolyFun_iff_exists_polyFun`.
* fw.isPolyFun_closure: `isPolyFun_const`, `isPolyFun_upper` (+ alias `isPolyFun_x`), `isPolyFun_lower` (+ alias `isPolyFun_y`),
  `IsPolyFun.add/neg/sub/mul/pow/const_mul/mul_const/smul_const`, `isPolyFun_finset_sum`, `isPolyFun_finset_prod`,
  `IsPolyFun.of_upper_only`, `IsPolyFun.of_lower_only`,
  substitution: general `IsPolyFun.comp` (both variables replaced by IsPolyFun functions of (x',y'), witness `bind₁`),
  `IsPolyFun.comp_upper` (τ i x' = eval x' q, existential form), `IsPolyFun.comp_upper_poly` (explicit q : Fin n → MvPolynomial (Fin n') ℝ),
  `IsPolyFun.comp_lower` (σ j IsPolyFun in (x,y')),
  renaming: `IsPolyFun.rename` (any map e : ι → ι', `fun x y' => F x (fun j => y' (e j))`, witness `MvPolynomial.rename (Sum.map id e)`),
  `IsPolyFun.rename_equiv` (e : ι ≃ ι', `y' ∘ e`). Glue lemma `eval_bind₁'` (eval of bind₁, from `eval₂Hom_bind₁`).
* fw.continuous_polyFun: `IsPolyFun.continuous_uncurry`, `IsPolyFun.continuous_right`, `IsPolyFun.continuous_left`,
  `continuous_polyFun`; helper `continuous_sumElim_prod`.

Deviations: none in statements. Extras are strengthenings/helpers (rename for arbitrary maps, not only injections/Equivs;
general two-sided `comp`). `smul_const` is stated as `fun x y => c • F x y`; `const_mul`/`mul_const` also provided.
Not restated: `Sum.elim x y ∘ Sum.inl = x` / `∘ Sum.inr = y` are core simp lemmas `Sum.elim_comp_inl` / `Sum.elim_comp_inr`.

Mathlib names: no `MvPolynomial.eval_bind₁` exists at this commit; used `MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℝ)`
(Algebra/MvPolynomial/Monad.lean:250), packaged as `Bilevel.eval_bind₁'`. `MvPolynomial.eval_rename`, `MvPolynomial.continuous_eval`,
`Continuous.prodMk_right/left` as expected.

Not done: nothing.

Last build: `lake build HardnessBilevel.Framework.Poly` -> "Build completed successfully" (only the generic
"consider adding `module`" warning from importing Mathlib). `#print axioms` of all 33 theorems: [propext, Classical.choice, Quot.sound].
