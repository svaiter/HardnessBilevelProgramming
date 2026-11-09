import HardnessBilevelUnconditional

/-!
Axiom check for the assumption-free forms of the main theorems (library `HardnessBilevelUnconditional`).
Run with `lake lean scripts/CheckAxiomsUnconditional.lean` (or `scripts/check.sh`). Every line must print
exactly `[propext, Classical.choice, Quot.sound]`: the three real-algebraic-geometry facts A1–A3 are proved
(Semialgebraic companion library on top of TauCeti), not assumed.
-/

open Bilevel

-- the three proved instances
#print axioms instHasSemialgebraicProjections
#print axioms instHasFinitenessTheorem
#print axioms instHasGrowthBound
-- Proposition 2.6 and its pessimistic twin
#print axioms Unconditional.valueFun_isExtSemialgebraic
#print axioms Unconditional.pvalueFun_isExtSemialgebraic
-- Theorem 2.12
#print axioms Unconditional.thm212_eq_SA
#print axioms Unconditional.pess_thm212
-- Theorem 2.15
#print axioms Unconditional.thm215_supset
#print axioms Unconditional.thm215_eq
#print axioms Unconditional.pess_thm215
-- Theorem 2.18
#print axioms Unconditional.thm218_main
#print axioms Unconditional.pess_thm218
-- Theorem 2.20
#print axioms Unconditional.thm220_supset
#print axioms Unconditional.thm220_main
#print axioms Unconditional.pess_thm220
-- Theorem 2.21
#print axioms Unconditional.thm221_compact_sa_incl
#print axioms Unconditional.thm221_compact_sa_incl_pess
#print axioms Unconditional.thm221_eq
#print axioms Unconditional.pess_thm221
