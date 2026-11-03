import HardnessBilevel.Assumptions.Classes
import HardnessBilevel.Bounded.Thm215
import HardnessBilevel.Bounded.Thm215Core
import HardnessBilevel.Convex.Hull
import HardnessBilevel.Convex.Lemma219
import HardnessBilevel.Convex.Linearize
import HardnessBilevel.Convex.Thm218
import HardnessBilevel.Convex.Thm220
import HardnessBilevel.Convex.Thm220Core
import HardnessBilevel.Convex.Thm221
import HardnessBilevel.Convex.Toolkit
import HardnessBilevel.Framework.Basic
import HardnessBilevel.Framework.Berge
import HardnessBilevel.Framework.Box
import HardnessBilevel.Framework.Classes
import HardnessBilevel.Framework.Poly
import HardnessBilevel.Framework.Semicont
import HardnessBilevel.Framework.Separable
import HardnessBilevel.Framework.Value
import HardnessBilevel.Gadgets.Box
import HardnessBilevel.Gadgets.Scalar
import HardnessBilevel.Gadgets.ZeroLocus
import HardnessBilevel.Hardness.Analysis
import HardnessBilevel.Hardness.Construction
import HardnessBilevel.Hardness.Reduction
import HardnessBilevel.Hardness.SSI
import HardnessBilevel.Pessimistic
import HardnessBilevel.Semialgebraic.Basic
import HardnessBilevel.Semialgebraic.Ext
import HardnessBilevel.Semialgebraic.Hull
import HardnessBilevel.Semialgebraic.Poly
import HardnessBilevel.Semialgebraic.Projection
import HardnessBilevel.Semialgebraic.Value
import HardnessBilevel.Smooth.Thm11
import HardnessBilevel.Smooth.Whitney
import HardnessBilevel.Unbounded.Thm212

/-!
# HardnessBilevel

Lean 4 + Mathlib formalization of the results of
"Geometric and computational hardness of bilevel programming" (Bolte, Lê, Pauwels, Vaiter, arXiv:2407.12372),
following `blueprint.md`. This root module imports every file of the library.
-/
