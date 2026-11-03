/-
Copyright: HardnessBilevel project.

# Value-function classes (blueprint §2.3, §4.A.1) and class-level corollaries

Implements:
* `valueFunClass`, the optimistic classes `P_unbound`, `P_bounded`, `C_unbound`, `C_bounded`, `C_cc`
  (Def 2.11, Def 2.16, eq. (18); `C_cc` requires a NONEMPTY lower set, erratum E-7), their pessimistic
  twins `Pp_unbound`, `Pp_bounded`, `Cp_unbound`, `Cp_bounded`, `Cp_cc` (with `pvalueFun`), the auxiliary
  class `P_box` (and `Pp_box`) of arbitrary boxes, the target classes `LSC`, `USC`, `CB`, `SA`, and the
  piecewise-polynomial class `PP` (Def 2.17) of REAL-valued functions.
* `fw.class_incl`, `fw.CB_real`, `fw.pvalue_class_neg`, `berge.rem210`, `t212.thm212_sup`
  (`thm212_supset`), `t218.PP_sub_Cunbound` (`thm218_PP_subset`), with pessimistic twins.

Conventions.
* `ConvexLower` is imported from `HardnessBilevel.Convex.Toolkit` (not redefined).
* Real-valued classes: membership of `f : (Fin n → ℝ) → ℝ` in an `EReal`-valued class means membership
  of `coeFun f := fun x => ((f x : ℝ) : EReal)`. We define `PPe n := coeFun '' PP n` and state
  `PPe n ⊆ C_unbound n` (`thm218_PP_subset`), together with the pointwise form
  `thm218_PP_subset' : f ∈ PP n → coeFun f ∈ C_unbound n`.

Deviations: none. No assumption classes are used.
-/
import HardnessBilevel.Framework.Berge
import HardnessBilevel.Framework.Separable
import HardnessBilevel.Framework.Poly
import HardnessBilevel.Framework.Box
import HardnessBilevel.Framework.Semicont
import HardnessBilevel.Semialgebraic.Ext
import HardnessBilevel.Convex.Toolkit
import HardnessBilevel.Convex.Thm218
import HardnessBilevel.Unbounded.Thm212

noncomputable section

namespace Bilevel

open MvPolynomial Function

section Classes

variable (n : ℕ)

/-- The class of value functions of polynomial bilevel problems with lower set satisfying `boxOK` and
lower objective satisfying `qOK`. `V` is `valueFun` (optimistic) or `pvalueFun` (pessimistic). -/
def valueFunClass
    (V : ∀ {ι : Type}, ((Fin n → ℝ) → (ι → ℝ) → ℝ) → ((Fin n → ℝ) → (ι → ℝ) → ℝ) →
          Set (ι → ℝ) → (Fin n → ℝ) → EReal)
    (boxOK : ∀ ι : Type, [Fintype ι] → Set (ι → ℝ) → Prop)
    (qOK : ∀ ι : Type, [Fintype ι] → ((Fin n → ℝ) → (ι → ℝ) → ℝ) → Prop) :
    Set ((Fin n → ℝ) → EReal) :=
  {h | ∃ (ι : Type) (_ : Fintype ι) (P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ) (S : Set (ι → ℝ)),
        IsPolyFun P ∧ IsPolyFun Q ∧ boxOK ι S ∧ qOK ι Q ∧ h = V P Q S}

/-- `𝒫_unbound` (Def 2.11). -/
def P_unbound : Set ((Fin n → ℝ) → EReal) :=
  valueFunClass n valueFun (fun _ _ S => IsUnboundedBox S) (fun _ _ _ => True)
/-- `𝒫_bounded` (Def 2.11). -/
def P_bounded : Set ((Fin n → ℝ) → EReal) :=
  valueFunClass n valueFun (fun _ _ S => IsBoundedBox S) (fun _ _ _ => True)
/-- Auxiliary: arbitrary boxes (`fw.class_incl`). -/
def P_box : Set ((Fin n → ℝ) → EReal) :=
  valueFunClass n valueFun (fun _ _ S => IsBox S) (fun _ _ _ => True)
/-- `𝒞_unbound` (Def 2.16). -/
def C_unbound : Set ((Fin n → ℝ) → EReal) :=
  valueFunClass n valueFun (fun _ _ S => IsUnboundedBox S) (fun _ _ Q => ConvexLower Q)
/-- `𝒞_bounded` (Def 2.16). -/
def C_bounded : Set ((Fin n → ℝ) → EReal) :=
  valueFunClass n valueFun (fun _ _ S => IsBoundedBox S) (fun _ _ Q => ConvexLower Q)
/-- `𝒞_cc` (eq. (18)); the lower set is required NONEMPTY (erratum E-7). -/
def C_cc : Set ((Fin n → ℝ) → EReal) :=
  valueFunClass n valueFun (fun _ _ S => S.Nonempty ∧ IsCompact S ∧ Convex ℝ S ∧ IsSemialgebraic S)
    (fun _ _ Q => ConvexLower Q)

/-- `𝒫^p_unbound`. -/
def Pp_unbound : Set ((Fin n → ℝ) → EReal) :=
  valueFunClass n pvalueFun (fun _ _ S => IsUnboundedBox S) (fun _ _ _ => True)
/-- `𝒫^p_bounded`. -/
def Pp_bounded : Set ((Fin n → ℝ) → EReal) :=
  valueFunClass n pvalueFun (fun _ _ S => IsBoundedBox S) (fun _ _ _ => True)
/-- Auxiliary pessimistic class with arbitrary boxes. -/
def Pp_box : Set ((Fin n → ℝ) → EReal) :=
  valueFunClass n pvalueFun (fun _ _ S => IsBox S) (fun _ _ _ => True)
/-- `𝒞^p_unbound`. -/
def Cp_unbound : Set ((Fin n → ℝ) → EReal) :=
  valueFunClass n pvalueFun (fun _ _ S => IsUnboundedBox S) (fun _ _ Q => ConvexLower Q)
/-- `𝒞^p_bounded`. -/
def Cp_bounded : Set ((Fin n → ℝ) → EReal) :=
  valueFunClass n pvalueFun (fun _ _ S => IsBoundedBox S) (fun _ _ Q => ConvexLower Q)
/-- `𝒞^p_cc`. -/
def Cp_cc : Set ((Fin n → ℝ) → EReal) :=
  valueFunClass n pvalueFun (fun _ _ S => S.Nonempty ∧ IsCompact S ∧ Convex ℝ S ∧ IsSemialgebraic S)
    (fun _ _ Q => ConvexLower Q)

/-- Lower semicontinuous functions. -/
def LSC : Set ((Fin n → ℝ) → EReal) := {h | LowerSemicontinuous h}
/-- Upper semicontinuous functions. -/
def USC : Set ((Fin n → ℝ) → EReal) := {h | UpperSemicontinuous h}
/-- Functions bounded (two-sided, by reals) on compacts; this forces real values (`CB_real`). -/
def CB : Set ((Fin n → ℝ) → EReal) :=
  {h | ∀ K, IsCompact K → ∃ M : ℝ, ∀ x ∈ K, ((-M : ℝ) : EReal) ≤ h x ∧ h x ≤ (M : EReal)}
/-- Extended-real semialgebraic functions. -/
def SA : Set ((Fin n → ℝ) → EReal) := {h | IsExtSemialgebraic h}

/-- Piecewise polynomial functions (Def 2.17), real-valued. -/
def PP : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ (N : ℕ) (S : Fin N → Set (Fin n → ℝ)) (p : Fin N → MvPolynomial (Fin n) ℝ),
    (∀ i, IsSemialgebraic (S i)) ∧ Pairwise (Disjoint on S) ∧ (⋃ i, S i) = Set.univ ∧
      ∀ i, ∀ x ∈ S i, f x = MvPolynomial.eval x (p i)}

variable {n}

/-- Coercion of a real-valued function to an extended-real-valued one. -/
def coeFun (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → EReal := fun x => ((f x : ℝ) : EReal)

variable (n) in
/-- `PP n` viewed as a set of `EReal`-valued functions. -/
def PPe : Set ((Fin n → ℝ) → EReal) := coeFun '' PP n

end Classes

section Incl

variable {n : ℕ}

/-- Monotonicity of `valueFunClass` in the box and lower-objective conditions. -/
theorem valueFunClass_mono
    {V : ∀ {ι : Type}, ((Fin n → ℝ) → (ι → ℝ) → ℝ) → ((Fin n → ℝ) → (ι → ℝ) → ℝ) →
          Set (ι → ℝ) → (Fin n → ℝ) → EReal}
    {boxOK boxOK' : ∀ ι : Type, [Fintype ι] → Set (ι → ℝ) → Prop}
    {qOK qOK' : ∀ ι : Type, [Fintype ι] → ((Fin n → ℝ) → (ι → ℝ) → ℝ) → Prop}
    (hb : ∀ (ι : Type) [Fintype ι] (S : Set (ι → ℝ)), boxOK ι S → boxOK' ι S)
    (hq : ∀ (ι : Type) [Fintype ι] (Q : (Fin n → ℝ) → (ι → ℝ) → ℝ), qOK ι Q → qOK' ι Q) :
    valueFunClass n V boxOK qOK ⊆ valueFunClass n V boxOK' qOK' := by
  rintro h ⟨ι, _, P, Q, S, hP, hQ, hS, hQ', rfl⟩
  exact ⟨ι, inferInstance, P, Q, S, hP, hQ, hb ι S hS, hq ι Q hQ', rfl⟩

/-- A nonempty bounded box is nonempty, compact, convex and semialgebraic. -/
theorem IsBoundedBox.cc {ι : Type} [Fintype ι] {S : Set (ι → ℝ)} (hS : IsBoundedBox S) :
    S.Nonempty ∧ IsCompact S ∧ Convex ℝ S ∧ IsSemialgebraic S :=
  ⟨hS.nonempty, hS.isCompact, hS.convex, hS.isSemialgebraic⟩

/-- `fw.class_incl`: `𝒫_bounded ⊆ 𝒫_box`. -/
theorem P_bounded_subset_P_box : P_bounded n ⊆ P_box n :=
  valueFunClass_mono (fun _ _ _ hS => hS.isBox) (fun _ _ _ h => h)
/-- `fw.class_incl`: `𝒫_unbound ⊆ 𝒫_box`. -/
theorem P_unbound_subset_P_box : P_unbound n ⊆ P_box n :=
  valueFunClass_mono (fun _ _ _ hS => hS.isBox) (fun _ _ _ h => h)
/-- `fw.class_incl`: `𝒞_bounded ⊆ 𝒞_cc`. -/
theorem C_bounded_subset_C_cc : C_bounded n ⊆ C_cc n :=
  valueFunClass_mono (fun _ _ _ hS => hS.cc) (fun _ _ _ h => h)
/-- `fw.class_incl`: `𝒞_unbound ⊆ 𝒫_unbound`. -/
theorem C_unbound_subset_P_unbound : C_unbound n ⊆ P_unbound n :=
  valueFunClass_mono (fun _ _ _ hS => hS) (fun _ _ _ _ => trivial)
/-- `fw.class_incl`: `𝒞_bounded ⊆ 𝒫_bounded`. -/
theorem C_bounded_subset_P_bounded : C_bounded n ⊆ P_bounded n :=
  valueFunClass_mono (fun _ _ _ hS => hS) (fun _ _ _ _ => trivial)

theorem Pp_bounded_subset_Pp_box : Pp_bounded n ⊆ Pp_box n :=
  valueFunClass_mono (fun _ _ _ hS => hS.isBox) (fun _ _ _ h => h)
theorem Pp_unbound_subset_Pp_box : Pp_unbound n ⊆ Pp_box n :=
  valueFunClass_mono (fun _ _ _ hS => hS.isBox) (fun _ _ _ h => h)
theorem Cp_bounded_subset_Cp_cc : Cp_bounded n ⊆ Cp_cc n :=
  valueFunClass_mono (fun _ _ _ hS => hS.cc) (fun _ _ _ h => h)
theorem Cp_unbound_subset_Pp_unbound : Cp_unbound n ⊆ Pp_unbound n :=
  valueFunClass_mono (fun _ _ _ hS => hS) (fun _ _ _ _ => trivial)
theorem Cp_bounded_subset_Pp_bounded : Cp_bounded n ⊆ Pp_bounded n :=
  valueFunClass_mono (fun _ _ _ hS => hS) (fun _ _ _ _ => trivial)

/-- `fw.CB_real`: functions bounded on compacts are real-valued. -/
theorem CB_real {h : (Fin n → ℝ) → EReal} (hh : h ∈ CB n) (x : Fin n → ℝ) :
    h x ≠ ⊤ ∧ h x ≠ ⊥ := by
  obtain ⟨M, hM⟩ := hh {x} isCompact_singleton
  obtain ⟨h1, h2⟩ := hM x rfl
  exact ⟨ne_top_of_le_ne_top (EReal.coe_ne_top M) h2, ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1⟩

end Incl

section Neg

variable {n : ℕ}

/-- `fw.pvalue_class_neg`, general form. -/
theorem mem_pvalueFunClass_iff_neg
    {boxOK : ∀ ι : Type, [Fintype ι] → Set (ι → ℝ) → Prop}
    {qOK : ∀ ι : Type, [Fintype ι] → ((Fin n → ℝ) → (ι → ℝ) → ℝ) → Prop}
    {h : (Fin n → ℝ) → EReal} :
    h ∈ valueFunClass n pvalueFun boxOK qOK ↔
      (fun x => -h x) ∈ valueFunClass n valueFun boxOK qOK := by
  constructor
  · rintro ⟨ι, _, P, Q, S, hP, hQ, hS, hQ', rfl⟩
    refine ⟨ι, inferInstance, fun x y => -P x y, Q, S, hP.neg, hQ, hS, hQ', ?_⟩
    funext x
    dsimp only
    rw [pvalueFun_eq_neg_valueFun_neg, neg_neg]
  · rintro ⟨ι, _, P, Q, S, hP, hQ, hS, hQ', hh⟩
    refine ⟨ι, inferInstance, fun x y => -P x y, Q, S, hP.neg, hQ, hS, hQ', ?_⟩
    funext x
    dsimp only
    rw [pvalueFun_eq_neg_valueFun_neg]
    have hx : -h x = valueFun P Q S x := congrFun hh x
    simp only [neg_neg]
    rw [← hx, neg_neg]

theorem mem_Pp_unbound_iff {h : (Fin n → ℝ) → EReal} :
    h ∈ Pp_unbound n ↔ (fun x => -h x) ∈ P_unbound n := mem_pvalueFunClass_iff_neg
theorem mem_Pp_bounded_iff {h : (Fin n → ℝ) → EReal} :
    h ∈ Pp_bounded n ↔ (fun x => -h x) ∈ P_bounded n := mem_pvalueFunClass_iff_neg
theorem mem_Pp_box_iff {h : (Fin n → ℝ) → EReal} :
    h ∈ Pp_box n ↔ (fun x => -h x) ∈ P_box n := mem_pvalueFunClass_iff_neg
theorem mem_Cp_unbound_iff {h : (Fin n → ℝ) → EReal} :
    h ∈ Cp_unbound n ↔ (fun x => -h x) ∈ C_unbound n := mem_pvalueFunClass_iff_neg
theorem mem_Cp_bounded_iff {h : (Fin n → ℝ) → EReal} :
    h ∈ Cp_bounded n ↔ (fun x => -h x) ∈ C_bounded n := mem_pvalueFunClass_iff_neg
theorem mem_Cp_cc_iff {h : (Fin n → ℝ) → EReal} :
    h ∈ Cp_cc n ↔ (fun x => -h x) ∈ C_cc n := mem_pvalueFunClass_iff_neg

theorem neg_mem_SA_iff {h : (Fin n → ℝ) → EReal} :
    (fun x => -h x) ∈ SA n ↔ h ∈ SA n := isExtSemialgebraic_neg_iff

theorem neg_mem_CB_iff {h : (Fin n → ℝ) → EReal} :
    (fun x => -h x) ∈ CB n ↔ h ∈ CB n := by
  have key : ∀ g : (Fin n → ℝ) → EReal, g ∈ CB n → (fun x => -g x) ∈ CB n := by
    intro g hg K hK
    obtain ⟨M, hM⟩ := hg K hK
    refine ⟨M, fun x hx => ⟨?_, ?_⟩⟩
    · rw [EReal.coe_neg, EReal.neg_le_neg_iff]; exact (hM x hx).2
    · rw [EReal.neg_le, ← EReal.coe_neg]; exact (hM x hx).1
  refine ⟨fun hh => ?_, key h⟩
  simpa only [neg_neg] using key _ hh

theorem neg_mem_LSC_iff_USC {h : (Fin n → ℝ) → EReal} :
    (fun x => -h x) ∈ LSC n ↔ h ∈ USC n :=
  (upperSemicontinuous_iff_lowerSemicontinuous_neg h).symm

theorem neg_mem_USC_iff_LSC {h : (Fin n → ℝ) → EReal} :
    (fun x => -h x) ∈ USC n ↔ h ∈ LSC n :=
  (lowerSemicontinuous_iff_upperSemicontinuous_neg h).symm

end Neg

section Rem210

variable {n : ℕ}

/-- Core of `berge.rem210`: polynomial data with nonempty compact lower set give an lsc, compactly
bounded optimistic value function. -/
theorem valueFun_mem_LSC_CB {ι : Type} [Fintype ι] {P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ}
    {S : Set (ι → ℝ)} (hP : IsPolyFun P) (hQ : IsPolyFun Q) (hc : IsCompact S) (hne : S.Nonempty) :
    valueFun P Q S ∈ LSC n ∩ CB n :=
  ⟨lowerSemicontinuous_valueFun hP.continuous_uncurry hQ.continuous_uncurry hc,
    fun _ hK => valueFun_bddOn_compact hP.continuous_uncurry hQ.continuous_uncurry hc hne hK⟩

theorem pvalueFun_mem_USC_CB {ι : Type} [Fintype ι] {P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ}
    {S : Set (ι → ℝ)} (hP : IsPolyFun P) (hQ : IsPolyFun Q) (hc : IsCompact S) (hne : S.Nonempty) :
    pvalueFun P Q S ∈ USC n ∩ CB n :=
  ⟨upperSemicontinuous_pvalueFun hP.continuous_uncurry hQ.continuous_uncurry hc,
    fun _ hK => pvalueFun_bddOn_compact hP.continuous_uncurry hQ.continuous_uncurry hc hne hK⟩

/-- `berge.rem210` (Remark 2.10): `𝒫_bounded ⊆ LSC ∩ CB`. -/
theorem P_bounded_subset_LSC_CB : P_bounded n ⊆ LSC n ∩ CB n := by
  rintro h ⟨ι, _, P, Q, S, hP, hQ, hS, -, rfl⟩
  exact valueFun_mem_LSC_CB hP hQ hS.isCompact hS.nonempty

/-- `berge.rem210`: `𝒞_cc ⊆ LSC ∩ CB`. -/
theorem C_cc_subset_LSC_CB : C_cc n ⊆ LSC n ∩ CB n := by
  rintro h ⟨ι, _, P, Q, S, hP, hQ, hS, -, rfl⟩
  exact valueFun_mem_LSC_CB hP hQ hS.2.1 hS.1

/-- `berge.rem210`: `𝒞_bounded ⊆ LSC ∩ CB`. -/
theorem C_bounded_subset_LSC_CB : C_bounded n ⊆ LSC n ∩ CB n :=
  C_bounded_subset_C_cc.trans C_cc_subset_LSC_CB

/-- Pessimistic `berge.rem210`: `𝒫^p_bounded ⊆ USC ∩ CB`. -/
theorem Pp_bounded_subset_USC_CB : Pp_bounded n ⊆ USC n ∩ CB n := by
  rintro h ⟨ι, _, P, Q, S, hP, hQ, hS, -, rfl⟩
  exact pvalueFun_mem_USC_CB hP hQ hS.isCompact hS.nonempty

/-- Pessimistic `berge.rem210`: `𝒞^p_cc ⊆ USC ∩ CB`. -/
theorem Cp_cc_subset_USC_CB : Cp_cc n ⊆ USC n ∩ CB n := by
  rintro h ⟨ι, _, P, Q, S, hP, hQ, hS, -, rfl⟩
  exact pvalueFun_mem_USC_CB hP hQ hS.2.1 hS.1

theorem Cp_bounded_subset_USC_CB : Cp_bounded n ⊆ USC n ∩ CB n :=
  Cp_bounded_subset_Cp_cc.trans Cp_cc_subset_USC_CB

end Rem210

section Thm212

variable {n : ℕ}

/-- `t212.thm212_sup` (Thm 2.12, ⊇): every extended-real semialgebraic function is in `𝒫_unbound`.
The lower index type of the construction, `Thm212.Idx τΓ τm = Unit ⊕ …`, is nonempty, so
`Set.univ` is an unbounded box in the literal sense. -/
theorem thm212_supset : SA n ⊆ P_unbound n := by
  intro h hh
  obtain ⟨τΓ, _, ⟨𝒢Γ⟩⟩ := ZeroGadget.of_isSemialgebraic (show IsSemialgebraic (Γ h) from hh.graph)
  obtain ⟨τm, _, ⟨𝒢m⟩⟩ := ZeroGadget.of_isSemialgebraic hh.bot
  have : Nonempty (Thm212.Idx τΓ τm) := ⟨Sum.inl ()⟩
  exact ⟨Thm212.Idx τΓ τm, inferInstance, Thm212.Pfun, Thm212.Qfun 𝒢Γ 𝒢m, Set.univ,
    isPolyFun_polyFun _, isPolyFun_polyFun _, isUnboundedBox_univ, trivial,
    (Thm212.valueFun_eq 𝒢Γ 𝒢m).symm⟩

/-- Pessimistic `t212.thm212_sup`: `SA ⊆ 𝒫^p_unbound` (via negation). -/
theorem thm212_supset_pess : SA n ⊆ Pp_unbound n := fun _ hh =>
  mem_Pp_unbound_iff.2 (thm212_supset (neg_mem_SA_iff.2 hh))

end Thm212

section Thm218

variable {n : ℕ}

/-- On a partition, a piecewise polynomial is the indicator-weighted sum of its pieces. -/
theorem PP_eq_sum_indicator {N : ℕ} {S : Fin N → Set (Fin n → ℝ)}
    {p : Fin N → MvPolynomial (Fin n) ℝ} {f : (Fin n → ℝ) → ℝ}
    (hdisj : Pairwise (Disjoint on S)) (hcov : (⋃ i, S i) = Set.univ)
    (hf : ∀ i, ∀ x ∈ S i, f x = MvPolynomial.eval x (p i)) (x : Fin n → ℝ) :
    f x = ∑ i, (S i).indicator 1 x * MvPolynomial.eval x (p i) := by
  have hx : x ∈ ⋃ i, S i := hcov ▸ Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  rw [Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem hi, Pi.one_apply, one_mul, hf i x hi]
  · intro j _ hji
    have : x ∉ S j := fun hj => Set.disjoint_left.1 (hdisj hji) hj hi
    rw [Set.indicator_of_notMem this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `t218.PP_sub_Cunbound`, pointwise form. -/
theorem thm218_PP_subset' {f : (Fin n → ℝ) → ℝ} (hf : f ∈ PP n) :
    coeFun f ∈ C_unbound n ∧ coeFun f ∈ Cp_unbound n := by
  obtain ⟨N, S, p, hS, hdisj, hcov, hfp⟩ := hf
  obtain ⟨ι, _, P, Q, Y, hP, hQ, hc, hY, -, hv, hpv⟩ := sum_indicator_semialgebraic S hS p
  have hfe : coeFun f = fun x => ((∑ i, (S i).indicator 1 x * MvPolynomial.eval x (p i) : ℝ) : EReal) := by
    funext x; simp only [coeFun, PP_eq_sum_indicator hdisj hcov hfp x]
  exact ⟨⟨ι, inferInstance, P, Q, Y, hP, hQ, hY, hc, hfe.trans hv.symm⟩,
    ⟨ι, inferInstance, P, Q, Y, hP, hQ, hY, hc, hfe.trans hpv.symm⟩⟩

/-- `t218.PP_sub_Cunbound` (Thm 2.18, first inclusion): `PP ⊆ 𝒞_unbound`. -/
theorem thm218_PP_subset : PPe n ⊆ C_unbound n := by
  rintro _ ⟨f, hf, rfl⟩; exact (thm218_PP_subset' hf).1

/-- Pessimistic `t218.PP_sub_Cunbound`: `PP ⊆ 𝒞^p_unbound`. -/
theorem thm218_PP_subset_pess : PPe n ⊆ Cp_unbound n := by
  rintro _ ⟨f, hf, rfl⟩; exact (thm218_PP_subset' hf).2

end Thm218

end Bilevel

end
