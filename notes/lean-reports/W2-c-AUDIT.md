# W2-c AUDIT (Gadgets/Scalar, Gadgets/ZeroLocus, Unbounded/Thm212)

## 1. Verdict: ACCEPT
- Builds clean, no sorry/axiom/instance hygiene hits, all public axioms within {propext, Classical.choice, Quot.sound}.
- All statements are IDENTICAL to the blueprint (one declared STRENGTHENING: `escape_lt` drops unused `0 ≤ a`).
- The usability test (h = if x0=0 then ⊤ else 1/x0, n=1) compiled on first attempt using the Semialgebraic.Basic API.

## 2. Build / hygiene / axioms
- `lake build HardnessBilevel.Gadgets.Scalar`, `.Gadgets.ZeroLocus`, `.Unbounded.Thm212`: "Build completed successfully" (only the generic "imports Mathlib ... module system" lint warning on files importing Mathlib; no other warnings from the unit).
- grep for `sorry|axiom|native_decide|unsafe|admit|instance.*Has(...)|maxHeartbeats|open Classical`: only hit is ZeroLocus.lean:166, the docstring word "admits" (matches `admit`); no real hits. No deprecated names (`stdSimplex`, `Set.mem_setOf_eq`, `push_neg`, `ContDiff`) in the unit files.
- Scratch `<SCRATCH>/lean/W2cAudit.lean` (`lake env lean`): `#print axioms` on all 36 public decls (G1, G5, ZeroGadget + derived, basic/iUnion/iUnionUniform/of_isSemialgebraic, Γ, eval_*, a-lemmas, case_*, valueFun_eq, both main theorems, real_valued_of_gadget, exists_bilevel_real_valued): every one = [propext, Classical.choice, Quot.sound].

## 3. Faithfulness
| blueprint id | Lean | verdict | note |
|---|---|---|---|
| gad.G1 (1)-(4) | gadgetStrict_nonneg / _eq_zero_of_pos / one_le_gadgetStrict_of_nonpos / pos_of_gadgetStrict_eq_zero | IDENTICAL | g p z = (1 - p z^2)^2; witness √p⁻¹ |
| gad.ZeroGadget | `ZeroGadget S τ` | IDENTICAL | fields exactly W : MvPolynomial (σ ⊕ τ) ℝ, sel, nonneg, sel_zero (∀ w ∈ S, eval (Sum.elim w (sel w)) W = 0), pos_of_notMem (∀ w ∉ S, ∀ ξ, 0 < eval …) — confirmed via `#print` |
| derived | mem_of_eval_eq_zero, mem_iff | IDENTICAL | |
| gad.G2 | basicW, eval_basicW, basic | IDENTICAL | W_B = (rename inl P)^2 + ∑ (1 - rename inl (Q j) * X (inr j)^2)^2; sel = √(Q j)⁻¹; τ := κ |
| gad.G3 | iUnion (Σ), iUnion_W_eval, iUnionUniform (ι × κ) | IDENTICAL | empty index OK (prod = 1) |
| gad.G4 | ZeroGadget.of_isSemialgebraic | IDENTICAL | `IsSemialgebraic S → ∃ (τ : Type) (_ : Fintype τ), Nonempty (ZeroGadget S τ)`; uses exists_uniform_basic, σ universe-polymorphic (more general) |
| gad.G5 (1)-(6) | escape_nonneg, escape_one_one, escape_pos, escape_lt, escape_eq_zero, escape_eq_zero_of | IDENTICAL / STRENGTHENED | (4) drops `0 ≤ a` (declared, sound: statement is ∃ u v, escape a u v < ε for all ε>0) |
| Γ h | `Γ` | IDENTICAL | `{p : Fin n ⊕ Unit → ℝ | h (p ∘ Sum.inl) = ↑(p (Sum.inr ()))}` (confirmed via #print) |
| t212.eval | eval_Qpoly, eval_Ppoly (+ Qfun_apply, Pfun_apply) | IDENTICAL | Qpoly = rename ρΓ W_Γ * rename ρm W₋ * X(inr iU)^2 + (1 - X iU * X iV)^2; Ppoly = X (inr iT); Qfun/Pfun := polyFun; Idx = Unit ⊕ (τΓ ⊕ (τm ⊕ (Unit ⊕ Unit))) as in blueprint; eval_Qpoly gives `escape (a …) (y iU) (y iV)`, eval_Ppoly gives `y iT` (read) |
| t212.a_lemma (1)-(5) | a_nonneg, eq_or_bot_of_a_eq_zero, a_sel_eq_zero_of_coe, a_sel_eq_zero_of_bot, a_pos | IDENTICAL | |
| t212.case_real/top/bot | Thm212.case_real/case_top/case_bot, valueFun_eq | IDENTICAL | EReal split via generalize + EReal.rec; no use of A1 |
| t212.main | exists_bilevel_valueFun_eq | IDENTICAL | `{n} (h : (Fin n → ℝ) → EReal) (hΓ : IsSemialgebraic (Γ h)) (hbot : IsSemialgebraic {x | h x = ⊥}) : ∃ (ι : Type) (_ : Fintype ι) (P Q), IsPolyFun P ∧ IsPolyFun Q ∧ valueFun P Q Set.univ = h`; h arbitrary, no real-valuedness, no hypothesis on {h=⊤}. valueFun is `⨅ y ∈ argminSet Q S x, ((P x y : ℝ) : EReal)` (Framework.Basic) |
| (gadget form) | exists_bilevel_valueFun_eq_of_gadgets | extra | convenient, harmless |
| t212.real_valued | real_valued_of_gadget, exists_bilevel_real_valued | IDENTICAL | `IsSemialgebraicMap f → ∃ ι Fintype, P Q poly, (∀ x, argmin nonempty ∧ ∀ y ∈ argmin, P x y = f x) ∧ valueFun = ↑f ∧ pvalueFun = ↑f`; Q = W_Γ alone (polyFun (rename ρR W)), P = t |
| t212.thm212_sup / eq_SA / reindex / swap | — | MISSING (out of scope) | writer declared not done; thm212_sup needs IsExtSemialgebraic and class defs, belongs to a later unit |

## 4. Required fixes
None.

## 5. Optional improvements / notes
- Exports are API-stable: `Bilevel.Γ` is top-level (not in Thm212), as blueprint; `τ₋ → τm`, `W₋ → Wm`, `ρ₋ → ρm` renaming is forced by Lean identifiers (declared).
- `Thm212.Qpoly`/`Qfun` take both gadgets explicitly; later waves (`thm212_sup`, class membership) should call `exists_bilevel_valueFun_eq` and need `IsExtSemialgebraic → IsSemialgebraic (Γ h) ∧ IsSemialgebraic {h = ⊥}` (not in this unit).
- The `IsSemialgebraic` hypotheses ride on `generateSetAlgebra`; Semialgebraic.Basic's `isSemialgebraic_setOf_and`, `isSemialgebraic_eval_ne_zero`, `isSemialgebraic_eval_eq`, `isSemialgebraic_empty` made the usability test easy.

## 6. Usability test (scratch `<SCRATCH>/lean/W2cAudit.lean`)
`h := fun x : Fin 1 → ℝ => if x 0 = 0 then ⊤ else ((1 / x 0 : ℝ) : EReal)`.
- `{h = ⊥} = ∅`: `ext; split_ifs; top_ne_bot / EReal.coe_ne_bot` — 4 lines.
- `Γ h = {p | p (inl 0) ≠ 0 ∧ p (inl 0) * p (inr ()) = 1}`: ~12 lines (split_ifs, EReal.coe_eq_coe_iff, field_simp). Needed `(p ∘ Sum.inl) 0 = p (Sum.inl 0)` by rfl.
- semialgebraicity via `isSemialgebraic_setOf_and` + `isSemialgebraic_eval_ne_zero (X (inl 0))` + `isSemialgebraic_eval_eq (X (inl 0) * X (inr ())) 1`, each closed with `.of_eq (by ext p; simp)`; `isSemialgebraic_empty`.
- `exists_bilevel_valueFun_eq hT hT_sa_Γ hT_sa_bot` type-checks: FEASIBLE and not awkward. `#print axioms hT_realized` = [propext, Classical.choice, Quot.sound]. Only warnings were deprecation of `Set.mem_setOf_eq` in my own scratch.
