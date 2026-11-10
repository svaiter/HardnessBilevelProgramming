import HardnessBilevel

/-!
Axiom check for the main results. Run with `lake lean scripts/CheckAxioms.lean`
(or `scripts/check.sh`). Every line must print only `propext`, `Classical.choice`, `Quot.sound`;
the assumption classes A1–A3 are hypotheses of the theorems that need them, never axioms.
-/

open Bilevel

-- Theorem 1.1 (smooth data) and its pessimistic twin
#print axioms exists_smooth_of_lowerSemicontinuous
#print axioms exists_smooth_of_upperSemicontinuous
-- Corollary 2.9 (Berge-type)
#print axioms cor29
#print axioms cor29_pess
-- Theorem 2.12 (unconstrained lower level)
#print axioms exists_bilevel_valueFun_eq
#print axioms exists_bilevel_real_valued
#print axioms thm212_supset
#print axioms thm212_eq_SA
-- Proposition 2.6
#print axioms valueFun_isExtSemialgebraic
-- Theorem 2.15 (bounded box)
#print axioms thm215_supset
#print axioms thm215_eq
-- Lemma 2.19, Theorem 2.18
#print axioms lemma219
#print axioms sum_indicator_semialgebraic
#print axioms thm218_PP_subset
#print axioms thm218_main
-- Theorem 2.20
#print axioms t220_core
#print axioms thm220_supset
#print axioms thm220_main
-- Theorem 2.21
#print axioms t221_linearize
#print axioms thm221_compact_sa_incl
#print axioms thm221_eq
-- Section 3 (Lemma 3.3, reduction)
#print axioms SSI.lemma33
#print axioms reduce_correct
#print axioms SSI.totalDegree_Pp
#print axioms SSI.totalDegree_Qp
-- Pessimistic counterparts
#print axioms pess_thm11
#print axioms pess_cor29
#print axioms pess_thm212
#print axioms pess_thm215
#print axioms pess_thm218
#print axioms pess_thm220
#print axioms pess_thm221
