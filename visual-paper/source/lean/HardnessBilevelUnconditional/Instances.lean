/-
Copyright: HardnessBilevel project.

# Proved instances of the assumption classes A1, A2, A3

The classes of `HardnessBilevel/Assumptions/Classes.lean` are inhabited here by the interface theorems of the
`Semialgebraic` companion library (https://github.com/svaiter/Semialgebraic), which proves them over `ℝ` on top of
TauCeti's real algebraic geometry:

* A1 `HasSemialgebraicProjections` — `Semialgebraic.Interface.image_comp_inl` (Tarski–Seidenberg; TauCeti's
  cylindrical algebraic decomposition);
* A2 `HasFinitenessTheorem` — `Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg` (finiteness theorem, through
  a weighted Łojasiewicz inequality);
* A3 `HasGrowthBound` — `Semialgebraic.Interface.growth`.

`Bilevel.IsSemialgebraic` and `TauCeti.IsSemialgebraic` have the same body, so each instance is the interface
theorem itself, with no glue (`isSemialgebraic_iff_tauCeti` is `Iff.rfl`).

These instances live in the separate library `HardnessBilevelUnconditional`; the core library `HardnessBilevel`
declares no instance and keeps its binder-form statements.
-/
import HardnessBilevel.Assumptions.Classes
import Semialgebraic.Interface.Finiteness
import Semialgebraic.Interface.Growth
import Semialgebraic.Interface.Projection

namespace Bilevel

/-- The semialgebraicity predicate of this library is definitionally TauCeti's, over `ℝ`. -/
theorem isSemialgebraic_iff_tauCeti {ι : Type*} (s : Set (ι → ℝ)) :
    IsSemialgebraic s ↔ TauCeti.IsSemialgebraic s := Iff.rfl

/-- A1 (Tarski–Seidenberg), proved. -/
instance instHasSemialgebraicProjections : HasSemialgebraicProjections :=
  ⟨Semialgebraic.Interface.image_comp_inl⟩

/-- A2 (finiteness theorem), proved. -/
instance instHasFinitenessTheorem : HasFinitenessTheorem :=
  ⟨Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg⟩

/-- A3 (growth bound), proved. -/
instance instHasGrowthBound : HasGrowthBound :=
  ⟨Semialgebraic.Interface.growth⟩

end Bilevel
