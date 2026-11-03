# W2-g AUDIT: HardnessBilevel/Gadgets/Box.lean

## 1. Verdict: ACCEPT
- Builds, hygiene clean, all 18 public decls have axioms ⊆ {propext, Classical.choice, Quot.sound}.
- gad.G6 (a)(c) and G7 (a)(b)(c)(d) are present, identical or strengthened (arbitrary Fintype α β, any parameter type U, any universe); (★★) has no extra hypotheses.
- Edge cases (empty α, empty β) and the Fin 1 / p = id instantiation, plus a concrete polynomial instance of `isPolyFun_unionGadget_sum`, check in a scratch file.

## 2. Build / hygiene / axioms
- `lake build HardnessBilevel.Gadgets.Box` -> "Build completed successfully" (only the pre-existing Poly.lean `module` warning).
- grep for sorry|axiom|native_decide|unsafe|admit|instance.*Has…|maxHeartbeats|open Classical in Box.lean: no matches (`classical` tactic used inside one proof only).
- Scratch /tmp/claude-0/-home-user-HardnessBilevelProgramming/418e0315-f899-5121-bf9e-35c4125b9a45/scratchpad/lean/W2gAudit.lean: `#print axioms` on gadgetGe, gadgetGe_nonneg, gadgetGe_eq_zero_iff, gadgetGe_witness, gadgetGe_witness_eq_zero, gadgetGe_witness_mem, nonneg_of_gadgetGe_eq_zero, exists_gadgetGe_eq_zero_iff, gadgetGe_pos_of_neg, gadgetBox, mem_gadgetBox, unionGadget, unionGadget_nonneg, unionGadget_eq_zero_iff, exists_unionGadget_eq_zero_iff, isPolyFun_gadgetGe, isPolyFun_unionGadget, isPolyFun_unionGadget_sum: all `[propext, Classical.choice, Quot.sound]`.
- Same scratch file (`lake env lean`) compiles these checks with no errors:
  * `gadgetGe p z = (p - (p^2+1)*z)^2 := rfl`
  * `gadgetBox α β = Set.pi Set.univ (fun _ : α × β => Icc 0 (1/2)) := rfl`
  * `unionGadget p u z = ∏ i, ∑ j, gadgetGe (p i j u) (z (i,j)) := rfl`
  * α=β=Fin 1, p _ _ u = u: `(∃ z ∈ gadgetBox _ _, unionGadget _ u z = 0) ↔ 0 ≤ u` via `rw [exists_unionGadget_eq_zero_iff]; simp`
  * empty α: LHS refutable (no zero); empty β (Fin 2 × Fin 0): LHS holds; both agree with RHS through the unconditional (★★) statement.
  * `isPolyFun_unionGadget_sum` applied to p i j x t = x 0 * t + x 1 ^ 2 - 1, hypotheses discharged with isPolyFun_upper/lower/const combinators; conclusion has exactly the Thm 2.15 shape.

## 3. Faithfulness
| blueprint id | Lean name | verdict | note |
|---|---|---|---|
| G6 def | gadgetGe | IDENTICAL | rfl to (p-(p^2+1)z)^2 |
| G6(a) | gadgetGe_nonneg | IDENTICAL | |
| G6(b) | gadgetGe_eq_zero_iff | IDENTICAL | p = (p^2+1)*z |
| G6(c) | exists_gadgetGe_eq_zero_iff | IDENTICAL | `(∃ z ∈ Icc 0 (1/2), G p z = 0) ↔ 0 ≤ p`, no hypotheses |
| G7 box Z | gadgetBox | STRENGTHENED | rfl to Set.pi univ (Icc 0 (1/2)); α×β arbitrary Fintype instead of Fin a × Fin b (Fin a×Fin b recovered by instantiation) |
| G7 R | unionGadget | STRENGTHENED | ∏ i, ∑ j, G(p i j u)(z (i,j)); general U, α, β |
| G7(a) | unionGadget_nonneg | IDENTICAL | |
| G7(b) | unionGadget_eq_zero_iff | IDENTICAL | |
| G7(c)/(★★) | exists_unionGadget_eq_zero_iff | STRENGTHENED | no extra hypotheses; empty cases fine |
| G7(d) | isPolyFun_unionGadget, isPolyFun_unionGadget_sum | IDENTICAL/usable | Thm 2.15 shape matches exactly (lower index Unit ⊕ (α×β), t = y (inl ()), z ij = y (inr ij)); hypothesis `IsPolyFun fun x (t : Unit → ℝ) => p i j x (t ())` as requested |
Extras (harmless): gadgetGe_witness(+_mem, _eq_zero), nonneg_of_gadgetGe_eq_zero, gadgetGe_pos_of_neg, isPolyFun_gadgetGe, mem_gadgetBox.

## 4. Required fixes
None.

## 5. Optional improvements
- Names `isPolyFun_unionGadget[_sum]` are writer-chosen (blueprint only says "fw.isPolyFun_closure"); later waves should cite the API list.
- `Type*` universes (rather than blueprint's `Type`) are a strengthening; downstream with `Fin a`/`Fin b` works.
- `unionGadget` is a plain `def` (computable) — fine.
