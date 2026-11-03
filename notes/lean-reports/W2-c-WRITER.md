# W2-c WRITER report

## Files delivered
* /home/user/HardnessBilevelProgramming/HardnessBilevel/Gadgets/Scalar.lean (imports Mathlib)
* /home/user/HardnessBilevelProgramming/HardnessBilevel/Gadgets/ZeroLocus.lean (imports Scalar, Framework.Poly, Semialgebraic.Basic)
* /home/user/HardnessBilevelProgramming/HardnessBilevel/Unbounded/Thm212.lean (imports ZeroLocus, Framework.Basic/Value/Separable/Poly)
No sorry / axiom / native_decide / instance. `#print axioms` of all public theorems = [propext, Classical.choice, Quot.sound].

## Blueprint ids → Lean names (all in `Bilevel`)
* gad.G1: `gadgetStrict`, `gadgetStrict_nonneg`, `gadgetStrict_eq_zero_of_pos` (witness `Real.sqrt p⁻¹`),
  `one_le_gadgetStrict_of_nonpos`, `pos_of_gadgetStrict_eq_zero`.
* gad.G5: `escape`, (1) `escape_nonneg`, (2) `escape_one_one` (simp), (3) `escape_pos`, (4) `escape_lt`,
  (5) `escape_eq_zero`, (6) `escape_eq_zero_of`.
* gad.ZeroGadget: structure `ZeroGadget S τ` with fields `W, sel, nonneg, sel_zero, pos_of_notMem` exactly as §4.E.1;
  `ZeroGadget.mem_of_eval_eq_zero`, `ZeroGadget.mem_iff`.
* gad.G2: `ZeroGadget.basicW`, `ZeroGadget.eval_basicW`, `ZeroGadget.basic` (τ := κ, `[Fintype κ]`).
* gad.G3: `ZeroGadget.iUnion` (τ' := Σ i, τ i; needs only `[Fintype ι]`), `ZeroGadget.iUnion_W_eval`,
  uniform variant `ZeroGadget.iUnionUniform` (τ' := ι × κ), helpers `sumElim_comp_sumMap_sigma/prod`.
* gad.G4: `ZeroGadget.of_isSemialgebraic : IsSemialgebraic S → ∃ (τ : Type) (_ : Fintype τ), Nonempty (ZeroGadget S τ)`
  (τ := Fin m × Fin k, via `exists_uniform_basic` + `basic` + `iUnionUniform`).
* `Γ` (top-level `Bilevel.Γ`), index type `Thm212.Idx`, indices `iT iZ iN iU iV`, blocks `zc νc`, `mk`, renamings `ρΓ ρm`
  with composition identities `sumElim_comp_ρΓ/ρm`; `WΓ Wm a Qpoly Ppoly Qfun Pfun`.
* t212.eval (E1): `Thm212.eval_Qpoly`, `eval_Ppoly`, `Qfun_apply`, `Pfun_apply`.
* t212.a_lemma (E2): (1) `a_nonneg`, (2) `eq_or_bot_of_a_eq_zero`, (3) `a_sel_eq_zero_of_coe`, (4) `a_sel_eq_zero_of_bot`,
  (5) `a_pos`; plus `Qfun_nonneg`.
* t212.case_real / case_top / case_bot (M1–M3): `Thm212.case_real`, `case_top`, `case_bot`; `Thm212.valueFun_eq`
  (EReal split via `generalize hx : h x = e; induction e using EReal.rec`).
* t212.main: `exists_bilevel_valueFun_eq_of_gadgets` (with `[Fintype τΓ] [Fintype τm]`, gadgets as hypotheses) and
  `exists_bilevel_valueFun_eq` — statement EXACTLY as specified.
* t212.real_valued: `Thm212.real_valued_of_gadget` (explicit Q := polyFun (rename ρR 𝒢.W) = W_Γ(x,t,z), P := t, lower
  index `Unit ⊕ τ`: argmin nonempty and P x ≡ f x on it) and `exists_bilevel_real_valued`
  (`IsSemialgebraicMap f →` ∃ ι finite, polynomial P Q with (∀ x, argmin nonempty ∧ ∀ y ∈ argmin, P x y = f x) ∧
  valueFun = ↑f ∧ pvalueFun = ↑f).

## Deviations
* `escape_lt` (G5 (4)) drops the unused hypothesis `0 ≤ a` (strengthening).
* Identifier renaming: `τ₋ 𝒢₋ W₋ ρ₋` → `τm 𝒢m Wm ρm` (the character `₋` is not allowed in Lean identifiers).
* Blueprint ids `t212.*` live in namespace `Bilevel.Thm212` with descriptive names (map above).
* `fw.argmin_empty_of_pos_inf` / `fw.value_eq_bot_of_unbounded` were already in Framework.Basic (W1-a); reused.
* G4 is delivered here (the brief asked for it; PLAN listed it for Wave 3) because `exists_uniform_basic` already exists.
* t212.swap, t212.reindex, class membership: not done (out of scope per assignment).

## Mathlib names
* `EReal.top_ne_bot` does not exist; used root `top_ne_bot`. `push_neg` is deprecated → `push Not`.
  Otherwise blueprint names worked (`Real.sq_sqrt`, `mul_inv_cancel₀`, `exists_pos_mul_lt`, `add_eq_zero_iff_of_nonneg`,
  `Finset.single_le_sum`, `Finset.prod_eq_zero`, `Finset.prod_pos`, `Finset.prod_nonneg`, `eval_rename`, `map_prod`,
  `EReal.coe_eq_coe_iff`, `EReal.coe_ne_bot`, `EReal.coe_ne_top`).

## Last build commands
* `lake build HardnessBilevel.Gadgets.Scalar` — success
* `lake build HardnessBilevel.Gadgets.ZeroLocus` — success
* `lake build HardnessBilevel.Unbounded.Thm212` — "Build completed successfully" (no warnings from these files)
