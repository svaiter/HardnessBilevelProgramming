# W3-c WRITER report

File delivered: /home/user/HardnessBilevelProgramming/HardnessBilevel/Framework/Classes.lean (namespace Bilevel,
`noncomputable section`). API: reports/W3-c-API.md. No sorry/axiom; all 38 theorems: #print axioms =
[propext, Classical.choice, Quot.sound]. No assumption classes needed.

## Blueprint ids -> Lean names
* §4.A.1 classes: `valueFunClass`, `P_unbound`, `P_bounded`, `C_unbound`, `C_bounded`, `C_cc` (Nonempty ∧ IsCompact ∧
  Convex ∧ IsSemialgebraic), pessimistic `Pp_unbound`, `Pp_bounded`, `Cp_unbound`, `Cp_bounded`, `Cp_cc`; auxiliary
  `P_box`, `Pp_box` (IsBox); targets `LSC`, `USC`, `CB`, `SA`; `PP` (Def 2.17, real-valued); `coeFun`, `PPe := coeFun '' PP n`.
  `ConvexLower` imported from Convex.Toolkit (not redefined).
* fw.class_incl: `valueFunClass_mono` (generic), `P_bounded_subset_P_box`, `P_unbound_subset_P_box`,
  `C_bounded_subset_C_cc` (via `IsBoundedBox.cc`), `C_unbound_subset_P_unbound`, `C_bounded_subset_P_bounded`, and
  pessimistic `Pp_bounded_subset_Pp_box`, `Pp_unbound_subset_Pp_box`, `Cp_bounded_subset_Cp_cc`,
  `Cp_unbound_subset_Pp_unbound`, `Cp_bounded_subset_Pp_bounded`.
* fw.CB_real: `CB_real`.
* fw.pvalue_class_neg: `mem_pvalueFunClass_iff_neg` (generic), `mem_Pp_unbound_iff`, `mem_Pp_bounded_iff`, `mem_Pp_box_iff`,
  `mem_Cp_unbound_iff`, `mem_Cp_bounded_iff`, `mem_Cp_cc_iff`; plus `neg_mem_SA_iff`, `neg_mem_CB_iff`,
  `neg_mem_LSC_iff_USC`, `neg_mem_USC_iff_LSC`.
* berge.rem210: `valueFun_mem_LSC_CB`, `pvalueFun_mem_USC_CB` (cores), `P_bounded_subset_LSC_CB`, `C_cc_subset_LSC_CB`,
  `C_bounded_subset_LSC_CB`, `Pp_bounded_subset_USC_CB`, `Cp_cc_subset_USC_CB`, `Cp_bounded_subset_USC_CB`.
* t212.thm212_sup: `thm212_supset : SA n ⊆ P_unbound n`, `thm212_supset_pess : SA n ⊆ Pp_unbound n`.
* t218.PP_sub_Cunbound: `PP_eq_sum_indicator` (partition identity), `thm218_PP_subset'` (pointwise: `f ∈ PP n →
  coeFun f ∈ C_unbound n ∧ coeFun f ∈ Cp_unbound n`), `thm218_PP_subset : PPe n ⊆ C_unbound n`,
  `thm218_PP_subset_pess : PPe n ⊆ Cp_unbound n`.

## Deviations / route notes
* Statements as specified. Real-valued convention: chose `PPe n := coeFun '' PP n` (documented in file header).
* thm212_supset: `exists_bilevel_valueFun_eq` hides its index type, so nonemptiness of ι was not available from it;
  instead the proof re-runs its two-line body: `ZeroGadget.of_isSemialgebraic` on `hh.graph` (= `Γ h` definitionally)
  and `hh.bot`, then uses `Thm212.Idx τΓ τm = Unit ⊕ …` (nonempty via `Sum.inl ()`), `isUnboundedBox_univ`,
  `isPolyFun_polyFun`, `Thm212.valueFun_eq`. No dummy coordinate needed.
* Pessimistic SA inclusion via `IsExtSemialgebraic` negation + `mem_Pp_unbound_iff`; pessimistic PP inclusion directly
  from the `pvalueFun` conjunct of `sum_indicator_semialgebraic`.
* Mathlib names: `Set.indicator_of_notMem`, `ne_bot_of_le_ne_bot`, `EReal.neg_le`, `EReal.neg_le_neg_iff` (as expected).
* Note: `open Function` is needed for the `on` notation in `PP`; `eval` must then be written `MvPolynomial.eval`.

## Not done: nothing.

## Last build
`lake build HardnessBilevel.Framework.Classes` → "Build completed successfully" (only the pre-existing `module` warning
for Gadgets/Scalar.lean). `lake env lean HardnessBilevel/Framework/Classes.lean` → no output.
