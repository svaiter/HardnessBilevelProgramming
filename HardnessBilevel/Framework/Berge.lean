import HardnessBilevel.Framework.Basic
import HardnessBilevel.Framework.Value
import HardnessBilevel.Framework.Semicont

/-!
# Berge-type results: Theorem 2.8, Corollary 2.9 (blueprint §4.D, ids `berge.*`)

Generic setting: topological spaces `X Y`, `P Q : X → Y → ℝ` jointly continuous
(`Continuous (Function.uncurry P)`), `S : Set Y` compact.

* `berge.isClosed_graph`: `isClosed_argminSet_graph` (needs only `hQ` and `S` closed);
  sequence/filter form `berge.outer_semicont`: `argminSet_outer_semicont`.
* `berge.argmin_nonempty`: `argminSet_nonempty_of_isCompact`.
* `berge.argmin_isCompact`: `argminSet_isCompact_of_continuous`.
* `berge.exists_isMinOn`: `exists_isMinOn_argminSet`.
* `berge.value_attained`: `valueFun_attained`, `valueFun_ne_top_of_isCompact`,
  `valueFun_ne_bot_of_isCompact` (the latter unconditional).
* `berge.isClosed_sublevel`: `isClosed_valueFun_sublevel` (unconditional).
* `berge.lsc`: `lowerSemicontinuous_valueFun` (unconditional, no `S.Nonempty`).
* `berge.bdd_on_compact`: `valueFun_bddOn_compact`.
* `berge.cor29`: `cor29`.
* `berge.pess`: `upperSemicontinuous_pvalueFun` (unconditional), `pvalueFun_attained`,
  `pvalueFun_ne_top_of_isCompact`, `pvalueFun_ne_bot_of_isCompact`, `pvalueFun_bddOn_compact`,
  `cor29_pess`.

Deviations (strengthenings only): no `[T2Space Y]` is needed anywhere (the sublevel-set argument
works inside `X × ↥S`, where the argmin condition is closed without `S` being closed); the
outer-semicontinuity statement is for an arbitrary non-trivial filter instead of `atTop` on `ℕ`;
`isClosed_valueFun_sublevel`, `valueFun_ne_bot_of_isCompact` need no `S.Nonempty`.
-/

namespace Bilevel

open Filter Topology Set

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {P Q : X → Y → ℝ} {S : Set Y}

/-- A section of a jointly continuous function is continuous. -/
theorem continuous_section_of_uncurry (hQ : Continuous (Function.uncurry Q)) (x : X) :
    Continuous (Q x) :=
  hQ.comp (Continuous.prodMk_right x)

/-- `berge.isClosed_graph` (Thm 2.8 (i)): the graph of `Θ = argminSet Q S` is closed. -/
theorem isClosed_argminSet_graph (hQ : Continuous (Function.uncurry Q)) (hS : IsClosed S) :
    IsClosed {p : X × Y | p.2 ∈ argminSet Q S p.1} := by
  have h : {p : X × Y | p.2 ∈ argminSet Q S p.1} =
      Prod.snd ⁻¹' S ∩ ⋂ y' ∈ S, {p : X × Y | Q p.1 p.2 ≤ Q p.1 y'} := by
    ext p
    simp [argminSet]
  rw [h]
  refine (hS.preimage continuous_snd).inter (isClosed_biInter fun y' _ => ?_)
  exact isClosed_le hQ (hQ.comp (continuous_fst.prodMk continuous_const))

/-- `berge.outer_semicont` (Def 2.7, sequence/filter form). -/
theorem argminSet_outer_semicont (hQ : Continuous (Function.uncurry Q)) (hS : IsClosed S)
    {ι : Type*} {l : Filter ι} [l.NeBot] {xk : ι → X} {yk : ι → Y} {x : X} {y : Y}
    (hx : Tendsto xk l (𝓝 x)) (hy : Tendsto yk l (𝓝 y))
    (hk : ∀ k, yk k ∈ argminSet Q S (xk k)) : y ∈ argminSet Q S x :=
  (isClosed_argminSet_graph hQ hS).mem_of_tendsto (hx.prodMk_nhds hy) (Eventually.of_forall hk)

/-- `berge.argmin_nonempty`. -/
theorem argminSet_nonempty_of_isCompact (hQ : Continuous (Function.uncurry Q))
    (hS : IsCompact S) (hne : S.Nonempty) (x : X) : (argminSet Q S x).Nonempty := by
  obtain ⟨y, hy, hmin⟩ := hS.exists_isMinOn hne (continuous_section_of_uncurry hQ x).continuousOn
  exact ⟨y, mem_argminSet_iff.2 ⟨hy, hmin⟩⟩

/-- `berge.argmin_isCompact`. -/
theorem argminSet_isCompact_of_continuous (hQ : Continuous (Function.uncurry Q))
    (hS : IsCompact S) (x : X) : IsCompact (argminSet Q S x) :=
  argminSet_isCompact (continuous_section_of_uncurry hQ x) hS

/-- `berge.exists_isMinOn`. -/
theorem exists_isMinOn_argminSet (hP : Continuous (Function.uncurry P))
    (hQ : Continuous (Function.uncurry Q)) (hS : IsCompact S) (hne : S.Nonempty) (x : X) :
    ∃ y₀ ∈ argminSet Q S x, IsMinOn (P x) (argminSet Q S x) y₀ :=
  (argminSet_isCompact_of_continuous hQ hS x).exists_isMinOn
    (argminSet_nonempty_of_isCompact hQ hS hne x) (continuous_section_of_uncurry hP x).continuousOn

/-- `berge.value_attained`. -/
theorem valueFun_attained (hP : Continuous (Function.uncurry P))
    (hQ : Continuous (Function.uncurry Q)) (hS : IsCompact S) (hne : S.Nonempty) (x : X) :
    ∃ y₀ ∈ argminSet Q S x, valueFun P Q S x = ((P x y₀ : ℝ) : EReal) := by
  obtain ⟨y₀, hy₀, hmin⟩ := exists_isMinOn_argminSet hP hQ hS hne x
  exact ⟨y₀, hy₀, valueFun_eq_of_isMinOn hy₀ hmin⟩

/-- `berge.value_attained`, consequence: `valueFun ≠ ⊤`. -/
theorem valueFun_ne_top_of_isCompact (hP : Continuous (Function.uncurry P))
    (hQ : Continuous (Function.uncurry Q)) (hS : IsCompact S) (hne : S.Nonempty) (x : X) :
    valueFun P Q S x ≠ ⊤ := by
  obtain ⟨y₀, -, h⟩ := valueFun_attained hP hQ hS hne x
  rw [h]
  exact EReal.coe_ne_top _

/-- `berge.value_attained`, consequence: `valueFun ≠ ⊥` (no nonemptiness needed: for `S = ∅`
the value is `⊤`). -/
theorem valueFun_ne_bot_of_isCompact (hP : Continuous (Function.uncurry P))
    (hQ : Continuous (Function.uncurry Q)) (hS : IsCompact S) (x : X) :
    valueFun P Q S x ≠ ⊥ := by
  rcases S.eq_empty_or_nonempty with h | hne
  · have : valueFun P Q S x = ⊤ :=
      valueFun_eq_top_iff.2 (Set.subset_empty_iff.1 (h ▸ argminSet_subset))
    rw [this]
    exact top_ne_bot
  · obtain ⟨y₀, -, h⟩ := valueFun_attained hP hQ hS hne x
    rw [h]
    exact EReal.coe_ne_bot _

/-- `berge.isClosed_sublevel`: real sublevel sets of the optimistic value function are closed
(unconditionally; for `S = ∅` they are empty). -/
theorem isClosed_valueFun_sublevel (hP : Continuous (Function.uncurry P))
    (hQ : Continuous (Function.uncurry Q)) (hS : IsCompact S) (r : ℝ) :
    IsClosed {x | valueFun P Q S x ≤ (r : EReal)} := by
  rcases S.eq_empty_or_nonempty with h | hne
  · have : {x | valueFun P Q S x ≤ (r : EReal)} = ∅ := by
      ext x
      have hx : valueFun P Q S x = ⊤ :=
        valueFun_eq_top_iff.2 (Set.subset_empty_iff.1 (h ▸ argminSet_subset))
      simp only [mem_ofPred_eq, hx, top_le_iff, mem_empty_iff_false, iff_false]
      exact EReal.coe_ne_top r
    rw [this]
    exact isClosed_empty
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let C : Set (X × S) :=
    (⋂ y' ∈ S, {p : X × S | Q p.1 p.2 ≤ Q p.1 y'}) ∩ {p : X × S | P p.1 p.2 ≤ r}
  have hC : IsClosed C := by
    have hv : Continuous fun p : X × S => (p.1, (p.2 : Y)) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    refine (isClosed_biInter fun y' _ => ?_).inter ?_
    · exact isClosed_le (hQ.comp hv) (hQ.comp (continuous_fst.prodMk continuous_const))
    · exact isClosed_le (hP.comp hv) continuous_const
  have himg : Prod.fst '' C = {x | valueFun P Q S x ≤ (r : EReal)} := by
    ext x
    constructor
    · rintro ⟨⟨x', ⟨y, hyS⟩⟩, hpC, rfl⟩
      simp only [C, mem_inter_iff, mem_iInter, mem_ofPred_eq] at hpC
      have hy : y ∈ argminSet Q S x' := ⟨hyS, hpC.1⟩
      exact (valueFun_le_coe_of_mem hy).trans (EReal.coe_le_coe_iff.2 hpC.2)
    · intro hx
      obtain ⟨y₀, hy₀, heq⟩ := valueFun_attained hP hQ hS hne x
      have hle : P x y₀ ≤ r := by
        have hx' : valueFun P Q S x ≤ (r : EReal) := hx
        rw [heq] at hx'
        exact EReal.coe_le_coe_iff.1 hx'
      refine ⟨(x, ⟨y₀, hy₀.1⟩), ?_, rfl⟩
      simp only [C, mem_inter_iff, mem_iInter, mem_ofPred_eq]
      exact ⟨hy₀.2, hle⟩
  rw [← himg]
  exact isClosedMap_fst_of_compactSpace C hC

/-- `berge.lsc` (Cor 2.9, lsc part): the optimistic value function is lower semicontinuous,
unconditionally (no `S.Nonempty`). -/
theorem lowerSemicontinuous_valueFun (hP : Continuous (Function.uncurry P))
    (hQ : Continuous (Function.uncurry Q)) (hS : IsCompact S) :
    LowerSemicontinuous (valueFun P Q S) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro a
  induction a using EReal.rec with
  | bot =>
    have : valueFun P Q S ⁻¹' Iic ⊥ = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iic, le_bot_iff, mem_empty_iff_false, iff_false]
      exact valueFun_ne_bot_of_isCompact hP hQ hS x
    rw [this]
    exact isClosed_empty
  | coe r => exact isClosed_valueFun_sublevel hP hQ hS r
  | top =>
    rw [Iic_top, preimage_univ]
    exact isClosed_univ

/-- Generic boundedness on compacts for a function attained by `P` at points of `S`. -/
theorem bddOn_compact_of_attained (hP : Continuous (Function.uncurry P)) (hS : IsCompact S)
    {f : X → EReal} (hf : ∀ x, ∃ y₀ ∈ S, f x = ((P x y₀ : ℝ) : EReal))
    {K : Set X} (hK : IsCompact K) :
    ∃ M : ℝ, ∀ x ∈ K, (((-M : ℝ)) : EReal) ≤ f x ∧ f x ≤ (M : EReal) := by
  obtain ⟨m, hm⟩ := (hK.prod hS).bddBelow_image hP.continuousOn
  obtain ⟨M', hM'⟩ := (hK.prod hS).bddAbove_image hP.continuousOn
  refine ⟨max |m| |M'|, fun x hx => ?_⟩
  obtain ⟨y₀, hy₀, heq⟩ := hf x
  have h1 : m ≤ P x y₀ := hm (mem_image_of_mem _ (mk_mem_prod hx hy₀))
  have h2 : P x y₀ ≤ M' := hM' (mem_image_of_mem _ (mk_mem_prod hx hy₀))
  rw [heq, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
  have := neg_abs_le m
  have := le_abs_self M'
  have := le_max_left |m| |M'|
  have := le_max_right |m| |M'|
  constructor <;> linarith

/-- `berge.bdd_on_compact` (Cor 2.9, boundedness). -/
theorem valueFun_bddOn_compact (hP : Continuous (Function.uncurry P))
    (hQ : Continuous (Function.uncurry Q)) (hS : IsCompact S) (hne : S.Nonempty)
    {K : Set X} (hK : IsCompact K) :
    ∃ M : ℝ, ∀ x ∈ K, (((-M : ℝ)) : EReal) ≤ valueFun P Q S x ∧ valueFun P Q S x ≤ (M : EReal) :=
  bddOn_compact_of_attained hP hS (fun x => by
    obtain ⟨y₀, hy₀, h⟩ := valueFun_attained hP hQ hS hne x
    exact ⟨y₀, hy₀.1, h⟩) hK

/-- `berge.cor29` (Cor 2.9, clarified): for jointly continuous `P Q` and compact nonempty `S`,
the optimistic value function is lsc, real-valued, and bounded on compacts. -/
theorem cor29 (hP : Continuous (Function.uncurry P))
    (hQ : Continuous (Function.uncurry Q)) (hS : IsCompact S) (hne : S.Nonempty) :
    LowerSemicontinuous (valueFun P Q S) ∧
      (∀ x, valueFun P Q S x ≠ ⊤ ∧ valueFun P Q S x ≠ ⊥) ∧
      ∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ x ∈ K,
        (((-M : ℝ)) : EReal) ≤ valueFun P Q S x ∧ valueFun P Q S x ≤ (M : EReal) :=
  ⟨lowerSemicontinuous_valueFun hP hQ hS,
    fun x => ⟨valueFun_ne_top_of_isCompact hP hQ hS hne x, valueFun_ne_bot_of_isCompact hP hQ hS x⟩,
    fun _ hK => valueFun_bddOn_compact hP hQ hS hne hK⟩

/-! ### Pessimistic version (`berge.pess`) -/

theorem continuous_uncurry_neg (hP : Continuous (Function.uncurry P)) :
    Continuous (Function.uncurry fun x y => -P x y) :=
  hP.neg

/-- `berge.pess`: the pessimistic value function is upper semicontinuous, unconditionally. -/
theorem upperSemicontinuous_pvalueFun (hP : Continuous (Function.uncurry P))
    (hQ : Continuous (Function.uncurry Q)) (hS : IsCompact S) :
    UpperSemicontinuous (pvalueFun P Q S) := by
  rw [upperSemicontinuous_iff_lowerSemicontinuous_neg]
  have h : (fun x => -pvalueFun P Q S x) = valueFun (fun x y => -P x y) Q S := by
    funext x
    rw [pvalueFun_eq_neg_valueFun_neg, neg_neg]
  rw [h]
  exact lowerSemicontinuous_valueFun (continuous_uncurry_neg hP) hQ hS

/-- `berge.pess`: the pessimistic value is attained. -/
theorem pvalueFun_attained (hP : Continuous (Function.uncurry P))
    (hQ : Continuous (Function.uncurry Q)) (hS : IsCompact S) (hne : S.Nonempty) (x : X) :
    ∃ y₀ ∈ argminSet Q S x, pvalueFun P Q S x = ((P x y₀ : ℝ) : EReal) := by
  obtain ⟨y₀, hy₀, h⟩ := valueFun_attained (continuous_uncurry_neg hP) hQ hS hne x
  refine ⟨y₀, hy₀, ?_⟩
  rw [pvalueFun_eq_neg_valueFun_neg, h, EReal.coe_neg, neg_neg]

/-- `berge.pess`: `pvalueFun ≠ ⊤` (unconditional: for `S = ∅` the value is `⊥`). -/
theorem pvalueFun_ne_top_of_isCompact (hP : Continuous (Function.uncurry P))
    (hQ : Continuous (Function.uncurry Q)) (hS : IsCompact S) (x : X) :
    pvalueFun P Q S x ≠ ⊤ := by
  rw [pvalueFun_eq_neg_valueFun_neg]
  intro h
  exact valueFun_ne_bot_of_isCompact (continuous_uncurry_neg hP) hQ hS x
    (EReal.neg_eq_top_iff.1 h)

/-- `berge.pess`: `pvalueFun ≠ ⊥` for compact nonempty `S`. -/
theorem pvalueFun_ne_bot_of_isCompact (hP : Continuous (Function.uncurry P))
    (hQ : Continuous (Function.uncurry Q)) (hS : IsCompact S) (hne : S.Nonempty) (x : X) :
    pvalueFun P Q S x ≠ ⊥ := by
  obtain ⟨y₀, -, h⟩ := pvalueFun_attained hP hQ hS hne x
  rw [h]
  exact EReal.coe_ne_bot _

/-- `berge.pess`: boundedness on compacts of the pessimistic value function. -/
theorem pvalueFun_bddOn_compact (hP : Continuous (Function.uncurry P))
    (hQ : Continuous (Function.uncurry Q)) (hS : IsCompact S) (hne : S.Nonempty)
    {K : Set X} (hK : IsCompact K) :
    ∃ M : ℝ, ∀ x ∈ K, (((-M : ℝ)) : EReal) ≤ pvalueFun P Q S x ∧ pvalueFun P Q S x ≤ (M : EReal) :=
  bddOn_compact_of_attained hP hS (fun x => by
    obtain ⟨y₀, hy₀, h⟩ := pvalueFun_attained hP hQ hS hne x
    exact ⟨y₀, hy₀.1, h⟩) hK

/-- `berge.pess` (pessimistic Cor 2.9′): usc, real-valued, bounded on compacts. -/
theorem cor29_pess (hP : Continuous (Function.uncurry P))
    (hQ : Continuous (Function.uncurry Q)) (hS : IsCompact S) (hne : S.Nonempty) :
    UpperSemicontinuous (pvalueFun P Q S) ∧
      (∀ x, pvalueFun P Q S x ≠ ⊤ ∧ pvalueFun P Q S x ≠ ⊥) ∧
      ∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ x ∈ K,
        (((-M : ℝ)) : EReal) ≤ pvalueFun P Q S x ∧ pvalueFun P Q S x ≤ (M : EReal) :=
  ⟨upperSemicontinuous_pvalueFun hP hQ hS,
    fun x => ⟨pvalueFun_ne_top_of_isCompact hP hQ hS x,
      pvalueFun_ne_bot_of_isCompact hP hQ hS hne x⟩,
    fun _ hK => pvalueFun_bddOn_compact hP hQ hS hne hK⟩

end Bilevel
