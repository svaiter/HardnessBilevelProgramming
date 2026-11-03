# W2-b WRITER report (Berge-type results, blueprint §4.D)

## File delivered
/home/user/HardnessBilevelProgramming/HardnessBilevel/Framework/Berge.lean (namespace Bilevel; imports Framework.Basic, .Value, .Semicont)

## Blueprint ids implemented
| id | Lean name(s) |
|---|---|
| helper (Q x continuous) | `continuous_section_of_uncurry` |
| berge.isClosed_graph (B1) | `isClosed_argminSet_graph` (hQ + `IsClosed S`) |
| berge.outer_semicont | `argminSet_outer_semicont` (any `l.NeBot` filter) |
| berge.argmin_nonempty (B2) | `argminSet_nonempty_of_isCompact` |
| berge.argmin_isCompact (B3) | `argminSet_isCompact_of_continuous` |
| berge.exists_isMinOn (B4) | `exists_isMinOn_argminSet` |
| berge.value_attained (B5) | `valueFun_attained`, `valueFun_ne_top_of_isCompact` (needs S.Nonempty), `valueFun_ne_bot_of_isCompact` (unconditional) |
| berge.isClosed_sublevel (B6) | `isClosed_valueFun_sublevel` (unconditional) |
| berge.lsc (B7) | `lowerSemicontinuous_valueFun` (unconditional) |
| berge.bdd_on_compact (B8) | `valueFun_bddOn_compact`; generic helper `bddOn_compact_of_attained` |
| berge.cor29 | `cor29` (lsc ∧ (∀x, ≠⊤ ∧ ≠⊥) ∧ bounded on compacts) |
| berge.pess | `continuous_uncurry_neg`, `upperSemicontinuous_pvalueFun` (unconditional), `pvalueFun_attained`, `pvalueFun_ne_top_of_isCompact` (unconditional), `pvalueFun_ne_bot_of_isCompact`, `pvalueFun_bddOn_compact`, `cor29_pess` |

`berge.rem210` not done (moved to Wave 3 per PLAN). `berge.lsc_real` not separately stated (it is `lowerSemicontinuous_coe_iff` from Semicont).

## Deviations (all strengthenings)
* No `[T2Space Y]` needed: B6 works in `X × ↥S` with the argmin condition written as `⋂ y' ∈ S, {p | Q p.1 p.2 ≤ Q p.1 y'}`, which is closed without `S` closed (B1 itself is not used by B6).
* B6 and `valueFun_ne_bot_of_isCompact` need no `S.Nonempty` (S = ∅ handled separately: valueFun ≡ ⊤).
* Outer semicontinuity stated for an arbitrary NeBot filter (covers `atTop` on ℕ).
* `berge.pess` extras: `pvalueFun_attained` proven via `pvalueFun_eq_neg_valueFun_neg` + `EReal.coe_neg`.

## Mathlib names
All blueprint names matched (`lowerSemicontinuous_iff_isClosed_preimage`, `isClosedMap_fst_of_compactSpace`, `isCompact_iff_compactSpace`, `IsCompact.exists_isMinOn`, `IsCompact.bddBelow_image/bddAbove_image`, `Continuous.prodMk_right`, `Filter.Tendsto.prodMk_nhds`, `IsClosed.mem_of_tendsto`). `EReal.top_ne_bot` does not exist: used root `top_ne_bot`. Used `EReal.neg_eq_top_iff`.

## Build
`lake env lean HardnessBilevel/Framework/Berge.lean`: no errors, no warnings.
`lake build HardnessBilevel.Framework.Berge`: Build completed successfully (only a pre-existing module-system warning on Semicont.lean).
No sorry/axiom; #print axioms of all 21 declarations ⊆ {propext, Classical.choice, Quot.sound}.
