import HardnessBilevel

/-!
The core library has no instance of the assumption classes in scope: this file imports only `HardnessBilevel` and
compiles if and only if instance search fails for each of the three classes.
Run with `lake lean scripts/CheckNoInstance.lean` (or `scripts/check.sh`); it must print nothing.
-/

open Bilevel

example : True := by
  fail_if_success (have : HasSemialgebraicProjections := inferInstance)
  fail_if_success (have : HasFinitenessTheorem := inferInstance)
  fail_if_success (have : HasGrowthBound := inferInstance)
  trivial
