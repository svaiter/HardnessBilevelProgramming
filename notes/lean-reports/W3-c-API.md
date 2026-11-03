# W3-c API: HardnessBilevel/Framework/Classes.lean (namespace Bilevel; whole file is `noncomputable section`)

Imports: Framework.{Berge,Separable,Poly,Box,Semicont}, Semialgebraic.Ext, Convex.{Toolkit,Thm218}, Unbounded.Thm212.
Opens: MvPolynomial Function. All 38 theorems: `#print axioms` = [propext, Classical.choice, Quot.sound]. No assumption classes.

Definitions (all classes are `Set ((Fin n → ℝ) → EReal)` except `PP`):
* `valueFunClass n V boxOK qOK := {h | ∃ (ι : Type) (_ : Fintype ι) P Q (S : Set (ι → ℝ)), IsPolyFun P ∧ IsPolyFun Q ∧ boxOK ι S ∧ qOK ι Q ∧ h = V P Q S}`
* boxOK used: `fun _ _ S => IsUnboundedBox S` (`*_unbound`), `IsBoundedBox S` (`*_bounded`), `IsBox S` (`P_box`, `Pp_box`),
  `S.Nonempty ∧ IsCompact S ∧ Convex ℝ S ∧ IsSemialgebraic S` (`C_cc`, `Cp_cc`); qOK: `fun _ _ _ => True` (P-classes),
  `fun _ _ Q => ConvexLower Q` (C-classes). Optimistic classes use `valueFun`, `Pp_*`/`Cp_*` use `pvalueFun`.
* `LSC n`, `USC n`, `CB n` (two-sided real bounds on compacts), `SA n := {h | IsExtSemialgebraic h}`.
* `PP n : Set ((Fin n → ℝ) → ℝ)` (blueprint Def 2.17 verbatim, with `MvPolynomial.eval`).
* `coeFun f := fun x => ((f x : ℝ) : EReal)`; `PPe n := coeFun '' PP n` (the EReal view of PP; inclusions stated for PPe).

Signatures (`#check`, printed with `open Bilevel`):
```
valueFunClass : (n : ℕ) →
  ({ι : Type} → ((Fin n → ℝ) → (ι → ℝ) → ℝ) → ((Fin n → ℝ) → (ι → ℝ) → ℝ) → Set (ι → ℝ) → (Fin n → ℝ) → EReal) →
    ((ι : Type) → [Fintype ι] → Set (ι → ℝ) → Prop) →
      ((ι : Type) → [Fintype ι] → ((Fin n → ℝ) → (ι → ℝ) → ℝ) → Prop) → Set ((Fin n → ℝ) → EReal)
P_unbound : (n : ℕ) → Set ((Fin n → ℝ) → EReal)
P_bounded : (n : ℕ) → Set ((Fin n → ℝ) → EReal)
P_box : (n : ℕ) → Set ((Fin n → ℝ) → EReal)
C_unbound : (n : ℕ) → Set ((Fin n → ℝ) → EReal)
C_bounded : (n : ℕ) → Set ((Fin n → ℝ) → EReal)
C_cc : (n : ℕ) → Set ((Fin n → ℝ) → EReal)
Pp_unbound : (n : ℕ) → Set ((Fin n → ℝ) → EReal)
Pp_bounded : (n : ℕ) → Set ((Fin n → ℝ) → EReal)
Pp_box : (n : ℕ) → Set ((Fin n → ℝ) → EReal)
Cp_unbound : (n : ℕ) → Set ((Fin n → ℝ) → EReal)
Cp_bounded : (n : ℕ) → Set ((Fin n → ℝ) → EReal)
Cp_cc : (n : ℕ) → Set ((Fin n → ℝ) → EReal)
LSC : (n : ℕ) → Set ((Fin n → ℝ) → EReal)
USC : (n : ℕ) → Set ((Fin n → ℝ) → EReal)
CB : (n : ℕ) → Set ((Fin n → ℝ) → EReal)
SA : (n : ℕ) → Set ((Fin n → ℝ) → EReal)
PP : (n : ℕ) → Set ((Fin n → ℝ) → ℝ)
@coeFun : {n : ℕ} → ((Fin n → ℝ) → ℝ) → (Fin n → ℝ) → EReal
PPe : (n : ℕ) → Set ((Fin n → ℝ) → EReal)
@valueFunClass_mono : ∀ {n : ℕ}
  {V : {ι : Type} → ((Fin n → ℝ) → (ι → ℝ) → ℝ) → ((Fin n → ℝ) → (ι → ℝ) → ℝ) → Set (ι → ℝ) → (Fin n → ℝ) → EReal}
  {boxOK boxOK' : (ι : Type) → [Fintype ι] → Set (ι → ℝ) → Prop}
  {qOK qOK' : (ι : Type) → [Fintype ι] → ((Fin n → ℝ) → (ι → ℝ) → ℝ) → Prop},
  (∀ (ι : Type) [inst : Fintype ι] (S : Set (ι → ℝ)), boxOK ι S → boxOK' ι S) →
    (∀ (ι : Type) [inst : Fintype ι] (Q : (Fin n → ℝ) → (ι → ℝ) → ℝ), qOK ι Q → qOK' ι Q) →
      valueFunClass n (fun {ι} => V) boxOK qOK ⊆ valueFunClass n (fun {ι} => V) boxOK' qOK'
@IsBoundedBox.cc : ∀ {ι : Type} [Fintype ι] {S : Set (ι → ℝ)},
  IsBoundedBox S → S.Nonempty ∧ IsCompact S ∧ Convex ℝ S ∧ IsSemialgebraic S
@P_bounded_subset_P_box : ∀ {n : ℕ}, P_bounded n ⊆ P_box n
@P_unbound_subset_P_box : ∀ {n : ℕ}, P_unbound n ⊆ P_box n
@C_bounded_subset_C_cc : ∀ {n : ℕ}, C_bounded n ⊆ C_cc n
@C_unbound_subset_P_unbound : ∀ {n : ℕ}, C_unbound n ⊆ P_unbound n
@C_bounded_subset_P_bounded : ∀ {n : ℕ}, C_bounded n ⊆ P_bounded n
@Pp_bounded_subset_Pp_box : ∀ {n : ℕ}, Pp_bounded n ⊆ Pp_box n
@Pp_unbound_subset_Pp_box : ∀ {n : ℕ}, Pp_unbound n ⊆ Pp_box n
@Cp_bounded_subset_Cp_cc : ∀ {n : ℕ}, Cp_bounded n ⊆ Cp_cc n
@Cp_unbound_subset_Pp_unbound : ∀ {n : ℕ}, Cp_unbound n ⊆ Pp_unbound n
@Cp_bounded_subset_Pp_bounded : ∀ {n : ℕ}, Cp_bounded n ⊆ Pp_bounded n
@CB_real : ∀ {n : ℕ} {h : (Fin n → ℝ) → EReal}, h ∈ CB n → ∀ (x : Fin n → ℝ), h x ≠ ⊤ ∧ h x ≠ ⊥
@mem_pvalueFunClass_iff_neg : ∀ {n : ℕ} {boxOK : (ι : Type) → [Fintype ι] → Set (ι → ℝ) → Prop}
  {qOK : (ι : Type) → [Fintype ι] → ((Fin n → ℝ) → (ι → ℝ) → ℝ) → Prop} {h : (Fin n → ℝ) → EReal},
  h ∈ valueFunClass n (fun {ι} => pvalueFun) boxOK qOK ↔
    (fun x => -h x) ∈ valueFunClass n (fun {ι} => valueFun) boxOK qOK
@mem_Pp_unbound_iff : ∀ {n : ℕ} {h : (Fin n → ℝ) → EReal}, h ∈ Pp_unbound n ↔ (fun x => -h x) ∈ P_unbound n
@mem_Pp_bounded_iff : ∀ {n : ℕ} {h : (Fin n → ℝ) → EReal}, h ∈ Pp_bounded n ↔ (fun x => -h x) ∈ P_bounded n
@mem_Pp_box_iff : ∀ {n : ℕ} {h : (Fin n → ℝ) → EReal}, h ∈ Pp_box n ↔ (fun x => -h x) ∈ P_box n
@mem_Cp_unbound_iff : ∀ {n : ℕ} {h : (Fin n → ℝ) → EReal}, h ∈ Cp_unbound n ↔ (fun x => -h x) ∈ C_unbound n
@mem_Cp_bounded_iff : ∀ {n : ℕ} {h : (Fin n → ℝ) → EReal}, h ∈ Cp_bounded n ↔ (fun x => -h x) ∈ C_bounded n
@mem_Cp_cc_iff : ∀ {n : ℕ} {h : (Fin n → ℝ) → EReal}, h ∈ Cp_cc n ↔ (fun x => -h x) ∈ C_cc n
@neg_mem_SA_iff : ∀ {n : ℕ} {h : (Fin n → ℝ) → EReal}, (fun x => -h x) ∈ SA n ↔ h ∈ SA n
@neg_mem_CB_iff : ∀ {n : ℕ} {h : (Fin n → ℝ) → EReal}, (fun x => -h x) ∈ CB n ↔ h ∈ CB n
@neg_mem_LSC_iff_USC : ∀ {n : ℕ} {h : (Fin n → ℝ) → EReal}, (fun x => -h x) ∈ LSC n ↔ h ∈ USC n
@neg_mem_USC_iff_LSC : ∀ {n : ℕ} {h : (Fin n → ℝ) → EReal}, (fun x => -h x) ∈ USC n ↔ h ∈ LSC n
@valueFun_mem_LSC_CB : ∀ {n : ℕ} {ι : Type} [Fintype ι] {P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} {S : Set (ι → ℝ)},
  IsPolyFun P → IsPolyFun Q → IsCompact S → S.Nonempty → valueFun P Q S ∈ LSC n ∩ CB n
@pvalueFun_mem_USC_CB : ∀ {n : ℕ} {ι : Type} [Fintype ι] {P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ} {S : Set (ι → ℝ)},
  IsPolyFun P → IsPolyFun Q → IsCompact S → S.Nonempty → pvalueFun P Q S ∈ USC n ∩ CB n
@P_bounded_subset_LSC_CB : ∀ {n : ℕ}, P_bounded n ⊆ LSC n ∩ CB n
@C_cc_subset_LSC_CB : ∀ {n : ℕ}, C_cc n ⊆ LSC n ∩ CB n
@C_bounded_subset_LSC_CB : ∀ {n : ℕ}, C_bounded n ⊆ LSC n ∩ CB n
@Pp_bounded_subset_USC_CB : ∀ {n : ℕ}, Pp_bounded n ⊆ USC n ∩ CB n
@Cp_cc_subset_USC_CB : ∀ {n : ℕ}, Cp_cc n ⊆ USC n ∩ CB n
@Cp_bounded_subset_USC_CB : ∀ {n : ℕ}, Cp_bounded n ⊆ USC n ∩ CB n
@thm212_supset : ∀ {n : ℕ}, SA n ⊆ P_unbound n
@thm212_supset_pess : ∀ {n : ℕ}, SA n ⊆ Pp_unbound n
@PP_eq_sum_indicator : ∀ {n N : ℕ} {S : Fin N → Set (Fin n → ℝ)} {p : Fin N → MvPolynomial (Fin n) ℝ}
  {f : (Fin n → ℝ) → ℝ},
  Pairwise (Function.onFun Disjoint S) →
    ⋃ i, S i = Set.univ →
      (∀ (i : Fin N), ∀ x ∈ S i, f x = (MvPolynomial.eval x) (p i)) →
        ∀ (x : Fin n → ℝ), f x = ∑ i, (S i).indicator 1 x * (MvPolynomial.eval x) (p i)
@thm218_PP_subset' : ∀ {n : ℕ} {f : (Fin n → ℝ) → ℝ}, f ∈ PP n → coeFun f ∈ C_unbound n ∧ coeFun f ∈ Cp_unbound n
@thm218_PP_subset : ∀ {n : ℕ}, PPe n ⊆ C_unbound n
@thm218_PP_subset_pess : ∀ {n : ℕ}, PPe n ⊆ Cp_unbound n
```
