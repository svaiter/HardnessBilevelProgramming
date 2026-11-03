import HardnessBilevel.Framework.Basic
import HardnessBilevel.Framework.Value
import HardnessBilevel.Framework.Poly
import HardnessBilevel.Convex.Toolkit

/-!
# Theorem 2.21: the linearization lemma (blueprint §4.H.1)

Blueprint ids implemented here:
* `t221.splitting`  — `Bilevel.t221_splitting`
* `t221.linearize`  — `Bilevel.t221_linearize_value`, `Bilevel.t221_linearize_pvalue`, `Bilevel.t221_linearize`
* `t221.cc_data` (a), (b), (c), (f) — `Bilevel.t221_cc_data_isPolyFun_P`, `..._Q`, `Bilevel.t221_cc_data_convexLower`,
  `Bilevel.t221_cc_data_convex`, `Bilevel.t221_cc_data_nonempty`, bundled in `Bilevel.t221_cc_data`.

Parts (d) (compactness) is in `HardnessBilevel/Convex/Hull.lean`; part (e) (semialgebraicity, `t221.hull_sa`) needs A1 and
is not provided here.

Setting: `S : Finset (Fin n ⊕ ι →₀ ℕ)` a finite set of exponent vectors, the moment map
`Msp S y d = ∏ j, y j ^ d (inr j)`, coefficients `cPoly p d x = coeff d p * ∏ i, x i ^ d (inl i)` and the linearization
`plin S p x λ = ∑ d : S, cPoly p d x * λ d`.
-/

namespace Bilevel

open MvPolynomial

section Defs

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The moment map `y ↦ (∏ j, y j ^ d (inr j))_{d ∈ S}` (blueprint §4.H.1). -/
noncomputable def Msp (S : Finset (Fin n ⊕ ι →₀ ℕ)) (y : ι → ℝ) : S → ℝ :=
  fun d => ∏ j : ι, (y j) ^ (d.1 (Sum.inr j))

/-- The `x`-dependent coefficient of the moment `d` in `p` (blueprint §4.H.1, erratum E-15). -/
noncomputable def cPoly {S : Finset (Fin n ⊕ ι →₀ ℕ)} (p : MvPolynomial (Fin n ⊕ ι) ℝ) (d : S)
    (x : Fin n → ℝ) : ℝ :=
  p.coeff d.1 * ∏ i : Fin n, (x i) ^ (d.1 (Sum.inl i))

/-- The linearization `p^lin (x, λ) = ∑_{d ∈ S} c_p d x * λ d` (blueprint §4.H.1). -/
noncomputable def plin (S : Finset (Fin n ⊕ ι →₀ ℕ)) (p : MvPolynomial (Fin n ⊕ ι) ℝ)
    (x : Fin n → ℝ) (l : S → ℝ) : ℝ :=
  ∑ d : S, cPoly p d x * l d

/-- `plin S p x` as a linear map in `λ`. -/
noncomputable def plinLin (S : Finset (Fin n ⊕ ι →₀ ℕ)) (p : MvPolynomial (Fin n ⊕ ι) ℝ)
    (x : Fin n → ℝ) : (S → ℝ) →ₗ[ℝ] ℝ where
  toFun l := plin S p x l
  map_add' a b := by
    simp only [plin, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [plin, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => by ring

@[simp] theorem plinLin_apply (S : Finset (Fin n ⊕ ι →₀ ℕ)) (p : MvPolynomial (Fin n ⊕ ι) ℝ)
    (x : Fin n → ℝ) (l : S → ℝ) : plinLin S p x l = plin S p x l := rfl

/-- **t221.splitting** (L8). -/
theorem t221_splitting {S : Finset (Fin n ⊕ ι →₀ ℕ)} {p : MvPolynomial (Fin n ⊕ ι) ℝ}
    (hS : p.support ⊆ S) (x : Fin n → ℝ) (y : ι → ℝ) :
    MvPolynomial.eval (Sum.elim x y) p = plin S p x (Msp S y) := by
  rw [MvPolynomial.eval_eq']
  simp only [plin, cPoly, Msp, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_coe_sort S (fun d => p.coeff d * (∏ i : Fin n, x i ^ d (Sum.inl i)) *
      ∏ j : ι, y j ^ d (Sum.inr j))]
  rw [Finset.sum_subset hS]
  · refine Finset.sum_congr rfl fun d _ => by ring
  · intro d _ hd
    rw [MvPolynomial.notMem_support_iff.mp hd]
    ring

end Defs
