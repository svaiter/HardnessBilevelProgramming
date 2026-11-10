import HardnessBilevel.Hardness.Analysis

/-!
# The reduction SSI → bilevel instances (blueprint §4.I.1, §4.I.2: `s3.reduce_correct`,
`s3.degree`, `s3.integer_coeff`)

`BilevelInstance` is the instance type of Theorem 3.2: integer polynomials `P Q` of total degree
`≤ 5` in `n` upper and `m` lower variables, a bounded box `∏ [lo i, hi i]` with integer endpoints,
and an integer threshold `c`. The real evaluation of `P, Q` is `MvPolynomial.aeval (Sum.elim x y)`
(the same encoding as in `Hardness/Construction.lean`). `Yes` means `optVal < c` (cast through `ℝ`).

`reduce` maps an SSI instance to `(n, m, P, Q, lo, hi, c) = (r, k+1, Pp, Qp, 0, 1, 0)`;
`reduce_correct : (reduce I).Yes ↔ I.Yes`. Σ₂ᵖ-hardness itself (`s3.thm32`) is not formalized
(no complexity theory in Mathlib). `s3.integer_coeff` holds by construction (`Pp Qp` are
`MvPolynomial _ ℤ`). The optional `s3.coeff_bound` is not formalized.
-/

namespace Bilevel

open MvPolynomial

/-! ### s3.degree -/

namespace SSI

section degree
variable {σ : Type*}

private theorem td_add {a b : MvPolynomial σ ℤ} {n : ℕ} (ha : a.totalDegree ≤ n)
    (hb : b.totalDegree ≤ n) : (a + b).totalDegree ≤ n :=
  (totalDegree_add a b).trans (max_le ha hb)

private theorem td_sub {a b : MvPolynomial σ ℤ} {n : ℕ} (ha : a.totalDegree ≤ n)
    (hb : b.totalDegree ≤ n) : (a - b).totalDegree ≤ n :=
  (totalDegree_sub a b).trans (max_le ha hb)

private theorem td_mul {a b : MvPolynomial σ ℤ} {n m : ℕ} (ha : a.totalDegree ≤ n)
    (hb : b.totalDegree ≤ m) : (a * b).totalDegree ≤ n + m :=
  (totalDegree_mul a b).trans (Nat.add_le_add ha hb)

private theorem td_sq {a : MvPolynomial σ ℤ} {n : ℕ} (ha : a.totalDegree ≤ n) :
    (a ^ 2).totalDegree ≤ 2 * n :=
  (totalDegree_pow a 2).trans (Nat.mul_le_mul_left 2 ha)

private theorem td_sum {ι : Type*} (s : Finset ι) {f : ι → MvPolynomial σ ℤ} {n : ℕ}
    (hf : ∀ i, (f i).totalDegree ≤ n) : (∑ i ∈ s, f i).totalDegree ≤ n :=
  (totalDegree_finsetSum s f).trans (Finset.sup_le fun i _ => hf i)

private theorem td_C (c : ℤ) {n : ℕ} : (C c : MvPolynomial σ ℤ).totalDegree ≤ n := by
  rw [totalDegree_C]; exact Nat.zero_le _

private theorem td_one {n : ℕ} : (1 : MvPolynomial σ ℤ).totalDegree ≤ n := by
  rw [totalDegree_one]; exact Nat.zero_le _

private theorem td_X (s : σ) : (X s : MvPolynomial σ ℤ).totalDegree ≤ 1 := by
  rw [totalDegree_X]

theorem totalDegree_Fp (I : SSI) : I.Fp.totalDegree ≤ 1 :=
  td_add (td_C _) (td_sum _ fun _ => (td_mul (n := 0) (td_C _) (td_X _)).trans_eq (zero_add 1))

theorem totalDegree_Gp (I : SSI) : I.Gp.totalDegree ≤ 1 :=
  td_sum _ fun _ => td_mul (m := 0) (td_X _) (td_C _)

theorem totalDegree_Hp (I : SSI) : I.Hp.totalDegree ≤ 4 :=
  td_add (td_sum _ fun i => td_sq (td_mul (td_X _) (td_sub td_one (td_X _))))
    ((td_sq (td_sub I.totalDegree_Fp I.totalDegree_Gp)).trans (by norm_num))

theorem totalDegree_Lp (I : SSI) : I.Lp.totalDegree ≤ 5 := by
  have h1 : ((X (Sum.inr 0) - 1 : MvPolynomial I.Var ℤ) ^ 2).totalDegree ≤ 4 :=
    (td_sq (td_sub (td_X _) td_one)).trans (by norm_num)
  have h2 := td_sum (Finset.univ : Finset (Fin I.r))
    (f := fun j => ((1 - X (Sum.inl j) : MvPolynomial I.Var ℤ) * X (Sum.inl j)) ^ 2)
    fun j => td_sq (td_mul (td_sub td_one (td_X _)) (td_X _))
  exact td_mul (td_X _) (td_add h1 h2)

/-- `s3.degree`: `deg Q ≤ 5`. (Only `≤`; `= 5` is false for `r = 0`, blueprint E-28.) -/
theorem totalDegree_Qp (I : SSI) : I.Qp.totalDegree ≤ 5 :=
  td_add I.totalDegree_Lp (I.totalDegree_Hp.trans (by norm_num))

/-- `s3.degree`: `deg P ≤ 5`. (Only `≤`; `= 5` is false for `k = 0`, blueprint E-28.) -/
theorem totalDegree_Pp (I : SSI) : I.Pp.totalDegree ≤ 5 :=
  td_sub td_one (td_mul (td_X _) (td_add I.totalDegree_Hp td_one))

end degree

end SSI

/-! ### The instance type of Theorem 3.2 -/

/-- An instance of the decision problem of Theorem 3.2 (`BILEVEL₅`). -/
structure BilevelInstance where
  /-- number of upper-level variables -/
  n : ℕ
  /-- number of lower-level variables -/
  m : ℕ
  /-- upper-level objective -/
  P : MvPolynomial (Fin n ⊕ Fin m) ℤ
  /-- lower-level objective -/
  Q : MvPolynomial (Fin n ⊕ Fin m) ℤ
  degP : P.totalDegree ≤ 5
  degQ : Q.totalDegree ≤ 5
  /-- lower box endpoints (`lo i > hi i` gives an empty box: harmless) -/
  lo : Fin m → ℤ
  /-- upper box endpoints -/
  hi : Fin m → ℤ
  /-- threshold -/
  c : ℤ

namespace BilevelInstance

variable (I : BilevelInstance)

/-- The bounded box `∏ [lo i, hi i]`. -/
def box : Set (Fin I.m → ℝ) :=
  Set.pi Set.univ fun i => Set.Icc ((I.lo i : ℤ) : ℝ) ((I.hi i : ℤ) : ℝ)

/-- Real evaluation of `P`. -/
noncomputable def Pfun (x : Fin I.n → ℝ) (y : Fin I.m → ℝ) : ℝ := aeval (Sum.elim x y) I.P

/-- Real evaluation of `Q`. -/
noncomputable def Qfun (x : Fin I.n → ℝ) (y : Fin I.m → ℝ) : ℝ := aeval (Sum.elim x y) I.Q

/-- Optimal value of the optimistic bilevel problem (upper-level set `ℝⁿ`). -/
noncomputable def optVal : EReal := ⨅ x : Fin I.n → ℝ, valueFun I.Pfun I.Qfun I.box x

/-- YES-instance: optimal value strictly below `c` (cast `ℤ → ℝ → EReal`). -/
def Yes : Prop := I.optVal < ((I.c : ℝ) : EReal)

theorem isPolyFun_Pfun : IsPolyFun I.Pfun :=
  ⟨map (algebraMap ℤ ℝ) I.P, fun _ _ => SSI.aeval_eq_eval_map _ _⟩

theorem isPolyFun_Qfun : IsPolyFun I.Qfun :=
  ⟨map (algebraMap ℤ ℝ) I.Q, fun _ _ => SSI.aeval_eq_eval_map _ _⟩

end BilevelInstance

/-- The reduction of Lemma 3.3: `(n, m, P, Q, lo, hi, c) = (r, k+1, Pp, Qp, 0, 1, 0)`. -/
noncomputable def reduce (I : SSI) : BilevelInstance where
  n := I.r
  m := I.k + 1
  P := I.Pp
  Q := I.Qp
  degP := I.totalDegree_Pp
  degQ := I.totalDegree_Qp
  lo := fun _ => 0
  hi := fun _ => 1
  c := 0

theorem reduce_box (I : SSI) : (reduce I).box = I.box := by
  simp [BilevelInstance.box, reduce, SSI.box]

theorem reduce_optVal (I : SSI) : (reduce I).optVal = optVal I.Pfun I.Qfun I.box := by
  have hP : (reduce I).Pfun = I.Pfun := by
    funext x y; exact (I.Pfun_eq_aeval x y).symm
  have hQ : (reduce I).Qfun = I.Qfun := by
    funext x y; exact (I.Qfun_eq_aeval x y).symm
  unfold BilevelInstance.optVal optVal
  rw [hP, hQ, reduce_box]
  rfl

/-- `s3.reduce_correct` -/
theorem reduce_correct (I : SSI) : (reduce I).Yes ↔ I.Yes := by
  rw [BilevelInstance.Yes, reduce_optVal, ← SSI.lemma33]
  simp [reduce]

end Bilevel
