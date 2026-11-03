import Mathlib

/-!
# The subset-sum interval problem (blueprint §4.I.1, paper Problem 3.1)

An SSI instance consists of natural numbers `q₀, …, q_{k-1}`, `R` and `r`. It is a YES-instance iff
there is an integer `S` with `R ≤ S < R + 2^r` (i.e. `R ≤ S ≤ R + 2^r - 1`) that is *not* a subset
sum of the `q i`.

Positivity of `q i`, `R`, `r` and `r ≤ k` are not used by the mathematics of Lemma 3.3 and are not
part of the structure (a superset of the paper's instances; harmless for hardness, blueprint E-24).
-/

namespace Bilevel

/-- An instance of the subset-sum interval problem (paper Problem 3.1). -/
structure SSI where
  /-- number of items -/
  k : ℕ
  /-- the item sizes `q₀, …, q_{k-1}` -/
  q : Fin k → ℕ
  /-- left end of the target interval -/
  R : ℕ
  /-- the interval `[R, R + 2^r - 1]` has length `2^r` -/
  r : ℕ

/-- `S` is a subset sum of the items of `I`. -/
def SSI.subsetSum (I : SSI) (S : ℕ) : Prop := ∃ T : Finset (Fin I.k), ∑ i ∈ T, I.q i = S

/-- YES-instance: some `S` with `R ≤ S ≤ R + 2^r - 1` is not a subset sum. -/
def SSI.Yes (I : SSI) : Prop := ∃ S, I.R ≤ S ∧ S < I.R + 2 ^ I.r ∧ ¬ I.subsetSum S

end Bilevel
