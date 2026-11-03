# W4-a-core AUDIT (HardnessBilevel/Bounded/Thm215Core.lean)

## 1. Verdict: ACCEPT
- All checks A-F pass; no required fixes.
- `t215_core` is exactly blueprint §4.F.2 (only difference: `[Fintype ζ]` dropped = strengthening); `thm215_of_presentation` has exactly the intended hypotheses and conclusion.
- Sample instantiation n=1, f x = |x 0| elaborates and proves: a polynomial bilevel problem over a bounded box with value function `↑|x 0|`.

## 2. Build / hygiene / axioms
- `lake build HardnessBilevel.Bounded.Thm215Core` -> Build completed successfully (only the Mathlib "module" lint warning from other files).
- grep for sorry|axiom|native_decide|unsafe|admit|Has[A-Z]|maxHeartbeats|open Classical|decide in the file: no hits.
- Scratch file `<SCRATCH>/lean/W4aCoreAudit.lean`, `lake env lean`: `#print axioms` on all 15 declarations (t215_core_gen, t215_core_gen_value, t215_core_isLeast, t215_core, sumBox, t215_core_sum, t215Lo, t215Hi, t215Lo_le_t215Hi, sumBox_gadgetBox, isClosed_epigraph_sum, rescaledPoly, isPolyFun_rescaledPoly, exists_rescaledPoly_iff, thm215_of_presentation): all = [propext, Classical.choice, Quot.sound].

## 3. Faithfulness
| blueprint id | Lean name | verdict | note |
|---|---|---|---|
| t215.core | `t215_core` | IDENTICAL (strengthened: no `[Fintype ζ]`) | hypotheses hw,hfw,E,hE1,hE2,Z,R,hR0,hRE in blueprint order; conclusion `valueFun (fun x y => y.1 * w x) (fun x y => R x y.1 y.2) (Icc (-1) 1 ×ˢ Z) x = ↑(f x)`; matches `#check`. valueFun is the literal `⨅ y ∈ argminSet Q S x, ((P x y:ℝ):EReal)`. |
| t215.core (attained) | `t215_core_isLeast`, `t215_core_gen(_value)` | extra | generic Θ/T form; fine |
| t215.epi_closed | `isClosed_epigraph_sum` | IDENTICAL | `LowerSemicontinuous f → IsClosed {z : Fin n ⊕ Unit → ℝ \| f (z ∘ Sum.inl) ≤ z (Sum.inr ())}` |
| §4.F.3 step 5 | `rescaledPoly`, `isPolyFun_rescaledPoly`, `exists_rescaledPoly_iff` | OK | |
| §4.F.3 steps 6-7 | `thm215_of_presentation` | OK (strengthened: α β arbitrary Fintypes in Type) | hypotheses exactly: wq with `0 < eval x wq`, `\|f x\| ≤ eval x wq`; p : α → β → MvPolynomial (Fin n ⊕ Unit) ℝ; hE1 (`∃ i, ∀ j, 0 ≤ eval (Sum.elim x fun _ => f x) (p i j)`); hE2 (`... τ ... → f x ≤ τ`). Nothing more. Conclusion `∃ (ι : Type) (_ : Fintype ι) P Q a b, IsPolyFun P ∧ IsPolyFun Q ∧ (∀ k, a k ≤ b k) ∧ ∀ x, valueFun P Q (boundedBox a b) x = ↑(f x)` as required. ι = Unit ⊕ (α × β) : Type. |
| (4) no Has* class | whole file | OK | grep clean; imports only Framework.{Basic,Box,Poly}, Gadgets.Box |
Mathematics re-derived: t0=f x/w x in [-1,1]; E x (t0 w x)=E x (f x) gives a zero (t0,z0); R ≥ 0 so argmin = {y∈Y | R=0} (`argminSet_eq_zeroSet`); every argmin point has E x (t w x) so f x ≤ t w x; (t0,z0) attains f x. Correct, uses `valueFun_eq_of_isLeast`.

## 4. Required fixes
None.

## 5. Optional improvements
- Header could mention that `[Fintype ζ]` of the blueprint is dropped in `t215_core` (strengthening).
- `thm215_of_presentation` leaves α β Fintype instance-implicit after `{α β}`; downstream must supply `(α := Fin a) (β := Fin b)` or let unification do it (worked in sample).

## Sample instantiation (feasibility: YES)
In `<SCRATCH>/lean/W4aCoreAudit.lean`: `n=1`, `f x = |x 0|`, `wq = 1 + X 0 ^ 2`, `α = Unit`, `β = Bool`, `p () j = X(inr ()) - X(inl 0)` (true) / `X(inr ()) + X(inl 0)` (false). Using `refine thm215_of_presentation ...` all four side goals closed (positivity; nlinarith for |x| ≤ 1+x²; two linear inequalities), yielding
`∃ ι _ P Q a b, IsPolyFun P ∧ IsPolyFun Q ∧ (∀ k, a k ≤ b k) ∧ ∀ x, valueFun P Q (boundedBox a b) x = ↑|x 0|`. Compiles with no errors.
