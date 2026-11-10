import Mathlib

/-!
# Semicontinuity helpers (blueprint §4.A.4)

* `fw.lsc_real_bridge`: `lowerSemicontinuous_coe_iff`, and its twin `upperSemicontinuous_coe_iff`.
* `fw.usc_neg` / `fw.lsc_neg`: `upperSemicontinuous_iff_lowerSemicontinuous_neg`,
  `lowerSemicontinuous_iff_upperSemicontinuous_neg` for `EReal`-valued maps; real-valued versions
  `lowerSemicontinuous_neg_iff_real`, `upperSemicontinuous_neg_iff_real` (re-exports of Mathlib's
  `lowerSemiContinuous_neg_iff`, `upperSemiContinuous_neg_iff`).
* `t11.isClosed_realEpigraph`: `isClosed_realEpigraph`, and the usc twin `isClosed_realHypograph`.
-/

namespace Bilevel

variable {X : Type*} [TopologicalSpace X]

/-- `fw.lsc_real_bridge`: lower semicontinuity of a real map is the same as that of its
`EReal`-valued coercion. -/
theorem lowerSemicontinuous_coe_iff (f : X → ℝ) :
    LowerSemicontinuous (fun x => ((f x : ℝ) : EReal)) ↔ LowerSemicontinuous f := by
  constructor
  · intro h x y hy
    exact (h x (y : EReal) (EReal.coe_lt_coe_iff.2 hy)).mono fun _ hx' => EReal.coe_lt_coe_iff.1 hx'
  · intro h
    exact continuous_coe_real_ereal.comp_lowerSemicontinuous h EReal.coe_strictMono.monotone

/-- Usc twin of `fw.lsc_real_bridge`. -/
theorem upperSemicontinuous_coe_iff (f : X → ℝ) :
    UpperSemicontinuous (fun x => ((f x : ℝ) : EReal)) ↔ UpperSemicontinuous f := by
  constructor
  · intro h x y hy
    exact (h x (y : EReal) (EReal.coe_lt_coe_iff.2 hy)).mono fun _ hx' => EReal.coe_lt_coe_iff.1 hx'
  · intro h
    exact continuous_coe_real_ereal.comp_upperSemicontinuous h EReal.coe_strictMono.monotone

/-- `fw.usc_neg`: for `EReal`-valued maps, upper semicontinuity of `h` is lower semicontinuity of
`-h`. -/
theorem upperSemicontinuous_iff_lowerSemicontinuous_neg (h : X → EReal) :
    UpperSemicontinuous h ↔ LowerSemicontinuous (fun x => -h x) := by
  constructor
  · intro hh
    exact continuous_neg.comp_upperSemicontinuous_antitone hh EReal.neg_strictAnti.antitone
  · intro hh
    have := continuous_neg.comp_lowerSemicontinuous_antitone hh EReal.neg_strictAnti.antitone
    simpa [Function.comp_def, neg_neg] using this

/-- `fw.lsc_neg`: for `EReal`-valued maps, lower semicontinuity of `h` is upper semicontinuity of
`-h`. -/
theorem lowerSemicontinuous_iff_upperSemicontinuous_neg (h : X → EReal) :
    LowerSemicontinuous h ↔ UpperSemicontinuous (fun x => -h x) := by
  rw [upperSemicontinuous_iff_lowerSemicontinuous_neg]
  simp only [neg_neg]

/-- Real-valued version (re-export of Mathlib's `lowerSemiContinuous_neg_iff`). -/
theorem lowerSemicontinuous_neg_iff_real (f : X → ℝ) :
    LowerSemicontinuous (fun x => -f x) ↔ UpperSemicontinuous f :=
  lowerSemiContinuous_neg_iff (f := f)

/-- Real-valued version (re-export of Mathlib's `upperSemiContinuous_neg_iff`). -/
theorem upperSemicontinuous_neg_iff_real (f : X → ℝ) :
    UpperSemicontinuous (fun x => -f x) ↔ LowerSemicontinuous f :=
  upperSemiContinuous_neg_iff (f := f)

/-- `t11.isClosed_realEpigraph`: the real epigraph of an lsc `EReal`-valued map is closed. -/
theorem isClosed_realEpigraph {f : X → EReal} (hf : LowerSemicontinuous f) :
    IsClosed {p : X × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} := by
  have hc : Continuous (Prod.map id (fun t : ℝ => (t : EReal)) : X × ℝ → X × EReal) :=
    continuous_id.prodMap continuous_coe_real_ereal
  exact hf.isClosed_epigraph.preimage hc

/-- Usc twin: the real hypograph of a usc `EReal`-valued map is closed. -/
theorem isClosed_realHypograph {f : X → EReal} (hf : UpperSemicontinuous f) :
    IsClosed {p : X × ℝ | ((p.2 : ℝ) : EReal) ≤ f p.1} := by
  have hc : Continuous (Prod.map id (fun t : ℝ => (t : EReal)) : X × ℝ → X × EReal) :=
    continuous_id.prodMap continuous_coe_real_ereal
  exact hf.IsClosed_hypograph.preimage hc

end Bilevel
