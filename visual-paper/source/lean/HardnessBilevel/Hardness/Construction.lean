import HardnessBilevel.Hardness.SSI
import HardnessBilevel.Framework.Poly

/-!
# The polynomials of Lemma 3.3 (blueprint §4.I.1)

For an SSI instance `I` (with `r := I.r`, `k := I.k`), upper variables `x : Fin r → ℝ`, lower
variables `y : Fin (k+1) → ℝ` with `z = y 0` and `t = Fin.tail y` (i.e. `t i = y i.succ`):

* `F x := R + ∑ j, 2^j * x j` (0-based: `x j` carries weight `2^j`), `G t := ∑ i, t i * q i`,
* `H x t := ∑ i, (t i * (1 - t i))^2 + (F x - G t)^2`,
* `L x z := z * ((z - 1)^2 + ∑ j, ((1 - x j) * x j)^2)`,
* `Q x y := L x (y 0) + H x (tail y)`, `P x y := 1 - y 0 * (H x (tail y) + 1)`,
* lower-level feasible set `I.box = [0,1]^(k+1)` (`cube (k+1)`).

All I-dependent objects live in namespace `Bilevel.SSI` (dot notation `I.Pfun`, `I.Qfun`, ...).

**Evaluation encoding (the only one used):** the integer polynomials `Pp Qp : MvPolynomial (Fin r ⊕
Fin (k+1)) ℤ` are evaluated at real points by `MvPolynomial.aeval (Sum.elim x y)` (upper variables
`Sum.inl j ↦ x j`, lower variables `Sum.inr i ↦ y i`). The identities `Pfun_eq_aeval`, `Qfun_eq_aeval`
connect them to the real functions; `aeval_eq_eval_map` is the glue to `eval ∘ map`, which gives
`isPolyFun_Pfun`, `isPolyFun_Qfun` (`s3.integer_coeff`: integrality is by construction).
-/

namespace Bilevel
namespace SSI

open MvPolynomial

/-- The unit cube `[0,1]^n`. -/
def cube (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)

/-- The lower-level feasible set `𝒴 = [0,1] × [0,1]^k ⊆ ℝ^(k+1)` of Lemma 3.3. -/
def box (I : SSI) : Set (Fin (I.k + 1) → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)

theorem box_eq_cube (I : SSI) : I.box = cube (I.k + 1) := rfl

/-- `F x = R + ∑ j, 2^j x_j`. -/
noncomputable def Ffun (I : SSI) (x : Fin I.r → ℝ) : ℝ := (I.R : ℝ) + ∑ j : Fin I.r, (2 : ℝ) ^ (j : ℕ) * x j

/-- `G t = ∑ i, t_i q_i`. -/
noncomputable def Gfun (I : SSI) (t : Fin I.k → ℝ) : ℝ := ∑ i, t i * (I.q i : ℝ)

/-- `H x t = ∑ i, (t_i (1 - t_i))^2 + (F x - G t)^2`. -/
noncomputable def Hfun (I : SSI) (x : Fin I.r → ℝ) (t : Fin I.k → ℝ) : ℝ :=
  ∑ i, (t i * (1 - t i)) ^ 2 + (I.Ffun x - I.Gfun t) ^ 2

/-- `L x z = z ((z - 1)^2 + ∑ j, ((1 - x_j) x_j)^2)`. -/
noncomputable def Lfun {r : ℕ} (x : Fin r → ℝ) (z : ℝ) : ℝ :=
  z * ((z - 1) ^ 2 + ∑ j, ((1 - x j) * x j) ^ 2)

/-- Lower-level objective `Q x y = L x (y 0) + H x (tail y)`. -/
noncomputable def Qfun (I : SSI) (x : Fin I.r → ℝ) (y : Fin (I.k + 1) → ℝ) : ℝ :=
  Lfun x (y 0) + I.Hfun x (Fin.tail y)

/-- Upper-level objective `P x y = 1 - y 0 (H x (tail y) + 1)`. -/
noncomputable def Pfun (I : SSI) (x : Fin I.r → ℝ) (y : Fin (I.k + 1) → ℝ) : ℝ :=
  1 - y 0 * (I.Hfun x (Fin.tail y) + 1)

/-! ### Integer polynomials -/

/-- The variable type `Fin r ⊕ Fin (k+1)`. -/
abbrev Var (I : SSI) := Fin I.r ⊕ Fin (I.k + 1)

/-- polynomial `F` -/
noncomputable def Fp (I : SSI) : MvPolynomial I.Var ℤ :=
  C (I.R : ℤ) + ∑ j : Fin I.r, C ((2 : ℤ) ^ (j : ℕ)) * X (Sum.inl j)

/-- polynomial `G` -/
noncomputable def Gp (I : SSI) : MvPolynomial I.Var ℤ :=
  ∑ i : Fin I.k, X (Sum.inr i.succ) * C (I.q i : ℤ)

/-- polynomial `H` -/
noncomputable def Hp (I : SSI) : MvPolynomial I.Var ℤ :=
  ∑ i : Fin I.k, (X (Sum.inr i.succ) * (1 - X (Sum.inr i.succ))) ^ 2 + (I.Fp - I.Gp) ^ 2

/-- polynomial `L` -/
noncomputable def Lp (I : SSI) : MvPolynomial I.Var ℤ :=
  X (Sum.inr 0) * ((X (Sum.inr 0) - 1) ^ 2 + ∑ j : Fin I.r, ((1 - X (Sum.inl j)) * X (Sum.inl j)) ^ 2)

/-- The lower-level polynomial `Q = L + H` (integer coefficients). -/
noncomputable def Qp (I : SSI) : MvPolynomial I.Var ℤ := I.Lp + I.Hp

/-- The upper-level polynomial `P = 1 - z (H + 1)` (integer coefficients). -/
noncomputable def Pp (I : SSI) : MvPolynomial I.Var ℤ := 1 - X (Sum.inr 0) * (I.Hp + 1)

/-! ### Evaluation identities -/

section eval
variable (I : SSI) (x : Fin I.r → ℝ) (y : Fin (I.k + 1) → ℝ)

theorem aeval_Fp : aeval (Sum.elim x y) I.Fp = I.Ffun x := by
  simp [Fp, Ffun]

theorem aeval_Gp : aeval (Sum.elim x y) I.Gp = I.Gfun (Fin.tail y) := by
  simp [Gp, Gfun, Fin.tail]

theorem aeval_Hp : aeval (Sum.elim x y) I.Hp = I.Hfun x (Fin.tail y) := by
  simp [Hp, Hfun, aeval_Fp, aeval_Gp, Fin.tail]

theorem aeval_Lp : aeval (Sum.elim x y) I.Lp = Lfun x (y 0) := by
  simp [Lp, Lfun]

theorem Qfun_eq_aeval : I.Qfun x y = aeval (Sum.elim x y) I.Qp := by
  simp [Qp, Qfun, aeval_Lp, aeval_Hp]

theorem Pfun_eq_aeval : I.Pfun x y = aeval (Sum.elim x y) I.Pp := by
  simp [Pp, Pfun, aeval_Hp]

end eval

/-- Glue between `aeval` (ℤ-polynomials) and `eval ∘ map`. -/
theorem aeval_eq_eval_map {σ : Type*} (f : σ → ℝ) (p : MvPolynomial σ ℤ) :
    aeval f p = eval f (map (algebraMap ℤ ℝ) p) := by
  rw [aeval_def, eval₂_eq_eval_map]

theorem isPolyFun_Pfun (I : SSI) : IsPolyFun I.Pfun :=
  ⟨map (algebraMap ℤ ℝ) I.Pp, fun x y => by rw [Pfun_eq_aeval, aeval_eq_eval_map]⟩

theorem isPolyFun_Qfun (I : SSI) : IsPolyFun I.Qfun :=
  ⟨map (algebraMap ℤ ℝ) I.Qp, fun x y => by rw [Qfun_eq_aeval, aeval_eq_eval_map]⟩

end SSI
end Bilevel
