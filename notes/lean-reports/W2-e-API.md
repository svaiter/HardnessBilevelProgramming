# W2-e API: Section 3 (Lemma 3.3, reduction, Theorem 3.2 instance type)

Files: `HardnessBilevel/Hardness/{SSI,Construction,Analysis,Reduction}.lean`. Import chain:
SSI (Mathlib) <- Construction (+Framework.Poly) <- Analysis (+Framework.Basic/Value/Separable) <- Reduction.
All construction objects depending on an instance live in `Bilevel.SSI` (dot notation `I.Pfun`, `I.box`, ...).
Evaluation encoding: `MvPolynomial.aeval (Sum.elim x y)` on `MvPolynomial (Fin r ⊕ Fin (k+1)) ℤ`
(`Sum.inl j ↦ x j`, `Sum.inr 0 ↦ z = y 0`, `Sum.inr i.succ ↦ t i = Fin.tail y i`); glue `SSI.aeval_eq_eval_map`.
Every theorem: `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.

Key results:
* `Bilevel.SSI.lemma33 (I : SSI) : optVal I.Pfun I.Qfun I.box < 0 ↔ I.Yes`
* `Bilevel.SSI.lemma33_no (I : SSI) (h : ¬ I.Yes) : optVal I.Pfun I.Qfun I.box = 0`
* `Bilevel.SSI.valueFun_eq : valueFun I.Pfun I.Qfun I.box x = ↑(if IsBinary x then -I.mval x else 1)`
* `Bilevel.reduce_correct (I : SSI) : (reduce I).Yes ↔ I.Yes`
* `Bilevel.SSI.totalDegree_Pp/Qp : _ ≤ 5`

Signatures (`#check @Bilevel.<name>`, with `open Bilevel`):

```
SSI : Type
SSI.subsetSum : SSI → ℕ → Prop
SSI.Yes : SSI → Prop
SSI.cube : (n : ℕ) → Set (Fin n → ℝ)
SSI.box : (I : SSI) → Set (Fin (I.k + 1) → ℝ)
SSI.box_eq_cube : ∀ (I : SSI), I.box = SSI.cube (I.k + 1)
SSI.Ffun : (I : SSI) → (Fin I.r → ℝ) → ℝ
SSI.Gfun : (I : SSI) → (Fin I.k → ℝ) → ℝ
SSI.Hfun : (I : SSI) → (Fin I.r → ℝ) → (Fin I.k → ℝ) → ℝ
@SSI.Lfun : {r : ℕ} → (Fin r → ℝ) → ℝ → ℝ
SSI.Qfun : (I : SSI) → (Fin I.r → ℝ) → (Fin (I.k + 1) → ℝ) → ℝ
SSI.Pfun : (I : SSI) → (Fin I.r → ℝ) → (Fin (I.k + 1) → ℝ) → ℝ
SSI.Var : SSI → Type
SSI.Fp : (I : SSI) → MvPolynomial I.Var ℤ
SSI.Gp : (I : SSI) → MvPolynomial I.Var ℤ
SSI.Hp : (I : SSI) → MvPolynomial I.Var ℤ
SSI.Lp : (I : SSI) → MvPolynomial I.Var ℤ
SSI.Qp : (I : SSI) → MvPolynomial I.Var ℤ
SSI.Pp : (I : SSI) → MvPolynomial I.Var ℤ
SSI.aeval_Fp : ∀ (I : SSI) (x : Fin I.r → ℝ) (y : Fin (I.k + 1) → ℝ),
  (MvPolynomial.aeval (Sum.elim x y)) I.Fp = I.Ffun x
SSI.aeval_Gp : ∀ (I : SSI) (x : Fin I.r → ℝ) (y : Fin (I.k + 1) → ℝ),
  (MvPolynomial.aeval (Sum.elim x y)) I.Gp = I.Gfun (Fin.tail y)
SSI.aeval_Hp : ∀ (I : SSI) (x : Fin I.r → ℝ) (y : Fin (I.k + 1) → ℝ),
  (MvPolynomial.aeval (Sum.elim x y)) I.Hp = I.Hfun x (Fin.tail y)
SSI.aeval_Lp : ∀ (I : SSI) (x : Fin I.r → ℝ) (y : Fin (I.k + 1) → ℝ),
  (MvPolynomial.aeval (Sum.elim x y)) I.Lp = SSI.Lfun x (y 0)
SSI.Qfun_eq_aeval : ∀ (I : SSI) (x : Fin I.r → ℝ) (y : Fin (I.k + 1) → ℝ),
  I.Qfun x y = (MvPolynomial.aeval (Sum.elim x y)) I.Qp
SSI.Pfun_eq_aeval : ∀ (I : SSI) (x : Fin I.r → ℝ) (y : Fin (I.k + 1) → ℝ),
  I.Pfun x y = (MvPolynomial.aeval (Sum.elim x y)) I.Pp
@SSI.aeval_eq_eval_map : ∀ {σ : Type u_1} (f : σ → ℝ) (p : MvPolynomial σ ℤ),
  (MvPolynomial.aeval f) p = (MvPolynomial.eval f) ((MvPolynomial.map (algebraMap ℤ ℝ)) p)
SSI.isPolyFun_Pfun : ∀ (I : SSI), IsPolyFun I.Pfun
SSI.isPolyFun_Qfun : ∀ (I : SSI), IsPolyFun I.Qfun
@SSI.isMinOn_cons_iff : ∀ {k : ℕ} {f : ℝ → ℝ} {g : (Fin k → ℝ) → ℝ} {A : Set ℝ} {B : Set (Fin k → ℝ)}
  {y : Fin (k + 1) → ℝ},
  y 0 ∈ A ∧ Fin.tail y ∈ B →
    (IsMinOn (fun (y : Fin (k + 1) → ℝ) => f (y 0) + g (Fin.tail y)) {y : Fin (k + 1) → ℝ | y 0 ∈ A ∧ Fin.tail y ∈ B}
        y ↔
      IsMinOn f A (y 0) ∧ IsMinOn g B (Fin.tail y))
@SSI.argminSet_cons : ∀ {X : Type u_1} {k : ℕ} (A : X → ℝ → ℝ) (B : X → (Fin k → ℝ) → ℝ) (S₁ : Set ℝ)
  (S₂ : Set (Fin k → ℝ)) (x : X),
  argminSet (fun (x : X) (y : Fin (k + 1) → ℝ) => A x (y 0) + B x (Fin.tail y))
      {y : Fin (k + 1) → ℝ | y 0 ∈ S₁ ∧ Fin.tail y ∈ S₂} x =
    {y : Fin (k + 1) → ℝ | y 0 ∈ argminSet A S₁ x ∧ Fin.tail y ∈ argminSet B S₂ x}
@SSI.mem_cube_iff : ∀ {n : ℕ} {t : Fin n → ℝ}, t ∈ SSI.cube n ↔ ∀ (i : Fin n), t i ∈ Set.Icc 0 1
SSI.zero_mem_cube : ∀ (n : ℕ), 0 ∈ SSI.cube n
SSI.isCompact_cube : ∀ (n : ℕ), IsCompact (SSI.cube n)
SSI.mem_box_iff : ∀ (I : SSI) {y : Fin (I.k + 1) → ℝ}, y ∈ I.box ↔ y 0 ∈ Set.Icc 0 1 ∧ Fin.tail y ∈ SSI.cube I.k
SSI.box_eq : ∀ (I : SSI), I.box = {y : Fin (I.k + 1) → ℝ | y 0 ∈ Set.Icc 0 1 ∧ Fin.tail y ∈ SSI.cube I.k}
@SSI.IsBinary : {n : ℕ} → (Fin n → ℝ) → Prop
@SSI.mul_one_sub_eq_zero_iff : ∀ {a : ℝ}, a * (1 - a) = 0 ↔ a = 0 ∨ a = 1
@SSI.one_sub_mul_eq_zero_iff : ∀ {a : ℝ}, (1 - a) * a = 0 ↔ a = 0 ∨ a = 1
@SSI.sum_sq_eq_zero_iff' : ∀ {n : ℕ} (a : Fin n → ℝ), ∑ j : Fin n, a j ^ 2 = 0 ↔ ∀ (j : Fin n), a j = 0
@SSI.Lfun_nonneg : ∀ {r : ℕ} (x : Fin r → ℝ) {z : ℝ}, z ∈ Set.Icc 0 1 → 0 ≤ SSI.Lfun x z
@SSI.Lfun_zero : ∀ {r : ℕ} (x : Fin r → ℝ), SSI.Lfun x 0 = 0
@SSI.Lfun_eq_zero_iff : ∀ {r : ℕ} (x : Fin r → ℝ) (z : ℝ), SSI.Lfun x z = 0 ↔ z = 0 ∨ z = 1 ∧ SSI.IsBinary x
@SSI.isMinOn_Lfun_iff : ∀ {r : ℕ} (x : Fin r → ℝ) {z : ℝ},
  z ∈ Set.Icc 0 1 → (IsMinOn (SSI.Lfun x) (Set.Icc 0 1) z ↔ SSI.Lfun x z = 0)
@SSI.Zset : {r : ℕ} → (Fin r → ℝ) → Set ℝ
@SSI.mem_Zset_iff : ∀ {r : ℕ} (x : Fin r → ℝ) (z : ℝ), z ∈ SSI.Zset x ↔ z = 0 ∨ z = 1 ∧ SSI.IsBinary x
@SSI.Zset_eq : ∀ {r : ℕ} (x : Fin r → ℝ), SSI.Zset x = if SSI.IsBinary x then {0, 1} else {0}
SSI.Hfun_nonneg : ∀ (I : SSI) (x : Fin I.r → ℝ) (t : Fin I.k → ℝ), 0 ≤ I.Hfun x t
SSI.Hfun_eq_zero_iff : ∀ (I : SSI) (x : Fin I.r → ℝ) (t : Fin I.k → ℝ),
  I.Hfun x t = 0 ↔ SSI.IsBinary t ∧ I.Ffun x = I.Gfun t
SSI.continuous_Hfun : ∀ (I : SSI) (x : Fin I.r → ℝ), Continuous (I.Hfun x)
SSI.Tset : (I : SSI) → (Fin I.r → ℝ) → Set (Fin I.k → ℝ)
SSI.Tset_nonempty : ∀ (I : SSI) (x : Fin I.r → ℝ), (I.Tset x).Nonempty
SSI.Tset_subset : ∀ (I : SSI) (x : Fin I.r → ℝ), I.Tset x ⊆ SSI.cube I.k
SSI.mval : (I : SSI) → (Fin I.r → ℝ) → ℝ
SSI.isLeast_of_mem_Tset : ∀ (I : SSI) {x : Fin I.r → ℝ} {t : Fin I.k → ℝ},
  t ∈ I.Tset x → IsLeast (I.Hfun x '' SSI.cube I.k) (I.Hfun x t)
SSI.Hfun_eq_mval : ∀ (I : SSI) {x : Fin I.r → ℝ} {t : Fin I.k → ℝ}, t ∈ I.Tset x → I.Hfun x t = I.mval x
SSI.mval_le : ∀ (I : SSI) {x : Fin I.r → ℝ} {t : Fin I.k → ℝ}, t ∈ SSI.cube I.k → I.mval x ≤ I.Hfun x t
SSI.mval_nonneg : ∀ (I : SSI) (x : Fin I.r → ℝ), 0 ≤ I.mval x
SSI.mval_eq_zero_iff : ∀ (I : SSI) (x : Fin I.r → ℝ), I.mval x = 0 ↔ ∃ t ∈ SSI.cube I.k, I.Hfun x t = 0
SSI.argminSet_Qfun : ∀ (I : SSI) (x : Fin I.r → ℝ),
  argminSet I.Qfun I.box x = {y : Fin (I.k + 1) → ℝ | y 0 ∈ SSI.Zset x ∧ Fin.tail y ∈ I.Tset x}
SSI.mem_argminSet_Qfun_iff : ∀ (I : SSI) (x : Fin I.r → ℝ) (y : Fin (I.k + 1) → ℝ),
  y ∈ argminSet I.Qfun I.box x ↔ y ∈ I.box ∧ y 0 ∈ SSI.Zset x ∧ Fin.tail y ∈ I.Tset x
SSI.cons_mem_argminSet_Qfun : ∀ (I : SSI) {x : Fin I.r → ℝ} {z : ℝ} {t : Fin I.k → ℝ},
  z ∈ SSI.Zset x → t ∈ I.Tset x → Fin.cons z t ∈ argminSet I.Qfun I.box x
SSI.argminSet_Qfun_nonempty : ∀ (I : SSI) (x : Fin I.r → ℝ), (argminSet I.Qfun I.box x).Nonempty
@SSI.isBinary_iff_exists_fin_two : ∀ {n : ℕ} (x : Fin n → ℝ),
  SSI.IsBinary x ↔ ∃ (f : Fin n → Fin 2), x = fun (j : Fin n) => ↑↑(f j)
SSI.Ffun_fin_two : ∀ (I : SSI) (f : Fin I.r → Fin 2),
  (I.Ffun fun (j : Fin I.r) => ↑↑(f j)) = ↑(I.R + ↑(finFunctionFinEquiv f))
SSI.exists_nat_of_isBinary : ∀ (I : SSI) {x : Fin I.r → ℝ},
  SSI.IsBinary x → ∃ (S : ℕ), I.Ffun x = ↑S ∧ I.R ≤ S ∧ S < I.R + 2 ^ I.r
SSI.exists_isBinary_Ffun_eq : ∀ (I : SSI) {S : ℕ},
  I.R ≤ S → S < I.R + 2 ^ I.r → ∃ (x : Fin I.r → ℝ), SSI.IsBinary x ∧ I.Ffun x = ↑S
@SSI.tInd : {k : ℕ} → Finset (Fin k) → Fin k → ℝ
@SSI.tInd_mem_cube : ∀ {k : ℕ} (T : Finset (Fin k)), SSI.tInd T ∈ SSI.cube k
@SSI.isBinary_tInd : ∀ {k : ℕ} (T : Finset (Fin k)), SSI.IsBinary (SSI.tInd T)
SSI.Gfun_tInd : ∀ (I : SSI) (T : Finset (Fin I.k)), I.Gfun (SSI.tInd T) = ↑(∑ i ∈ T, I.q i)
SSI.Gfun_of_isBinary : ∀ (I : SSI) {t : Fin I.k → ℝ}, SSI.IsBinary t → I.Gfun t = ↑(∑ i : Fin I.k with t i = 1, I.q i)
SSI.Pfun_of_mem_argminSet : ∀ (I : SSI) {x : Fin I.r → ℝ} {y : Fin (I.k + 1) → ℝ},
  y ∈ argminSet I.Qfun I.box x → I.Pfun x y = 1 - y 0 * (I.mval x + 1)
SSI.valueFun_eq : ∀ (I : SSI) (x : Fin I.r → ℝ),
  valueFun I.Pfun I.Qfun I.box x = ↑(if SSI.IsBinary x then -I.mval x else 1)
SSI.valueFun_of_isBinary : ∀ (I : SSI) {x : Fin I.r → ℝ}, SSI.IsBinary x → valueFun I.Pfun I.Qfun I.box x = ↑(-I.mval x)
SSI.valueFun_of_not_isBinary : ∀ (I : SSI) {x : Fin I.r → ℝ}, ¬SSI.IsBinary x → valueFun I.Pfun I.Qfun I.box x = ↑1
SSI.optVal_lt_zero_of_yes : ∀ (I : SSI), I.Yes → optVal I.Pfun I.Qfun I.box < 0
SSI.valueFun_nonneg_of_not_yes : ∀ (I : SSI), ¬I.Yes → ∀ (x : Fin I.r → ℝ), 0 ≤ valueFun I.Pfun I.Qfun I.box x
@SSI.isBinary_zero : ∀ {n : ℕ}, SSI.IsBinary 0
SSI.valueFun_zero_of_not_yes : ∀ (I : SSI), ¬I.Yes → valueFun I.Pfun I.Qfun I.box 0 = 0
SSI.lemma33_no : ∀ (I : SSI), ¬I.Yes → optVal I.Pfun I.Qfun I.box = 0
SSI.lemma33 : ∀ (I : SSI), optVal I.Pfun I.Qfun I.box < 0 ↔ I.Yes
SSI.totalDegree_Fp : ∀ (I : SSI), I.Fp.totalDegree ≤ 1
SSI.totalDegree_Gp : ∀ (I : SSI), I.Gp.totalDegree ≤ 1
SSI.totalDegree_Hp : ∀ (I : SSI), I.Hp.totalDegree ≤ 4
SSI.totalDegree_Lp : ∀ (I : SSI), I.Lp.totalDegree ≤ 5
SSI.totalDegree_Qp : ∀ (I : SSI), I.Qp.totalDegree ≤ 5
SSI.totalDegree_Pp : ∀ (I : SSI), I.Pp.totalDegree ≤ 5
BilevelInstance : Type
BilevelInstance.box : (I : BilevelInstance) → Set (Fin I.m → ℝ)
BilevelInstance.Pfun : (I : BilevelInstance) → (Fin I.n → ℝ) → (Fin I.m → ℝ) → ℝ
BilevelInstance.Qfun : (I : BilevelInstance) → (Fin I.n → ℝ) → (Fin I.m → ℝ) → ℝ
BilevelInstance.optVal : BilevelInstance → EReal
BilevelInstance.Yes : BilevelInstance → Prop
BilevelInstance.isPolyFun_Pfun : ∀ (I : BilevelInstance), IsPolyFun I.Pfun
BilevelInstance.isPolyFun_Qfun : ∀ (I : BilevelInstance), IsPolyFun I.Qfun
reduce : SSI → BilevelInstance
reduce_box : ∀ (I : SSI), (reduce I).box = I.box
reduce_optVal : ∀ (I : SSI), (reduce I).optVal = optVal I.Pfun I.Qfun I.box
reduce_correct : ∀ (I : SSI), (reduce I).Yes ↔ I.Yes
```
