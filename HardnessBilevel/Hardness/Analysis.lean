import HardnessBilevel.Hardness.Construction
import HardnessBilevel.Framework.Basic
import HardnessBilevel.Framework.Value
import HardnessBilevel.Framework.Separable

/-!
# Analysis of the Lemma 3.3 construction (blueprint §4.I.2, `s3.L0`–`s3.L8`, `s3.lemma33`)

Lean names (all in `Bilevel.SSI`):
* `s3.L0`: `isMinOn_cons_iff` (pointwise), `argminSet_cons` (set form), on
  `{y | y 0 ∈ A ∧ Fin.tail y ∈ B}`; `box_eq`, `mem_box_iff` rewrite `I.box` into that shape.
* `s3.L1`: `IsBinary`, `Lfun_nonneg` (a), `Lfun_zero` (b), `Lfun_eq_zero_iff` (c),
  `isMinOn_Lfun_iff` (d), `Zset`, `mem_Zset_iff`, `Zset_eq` (e).
* `s3.L2`: `Hfun_nonneg` (a), `Hfun_eq_zero_iff` (b), `continuous_Hfun` (c), `Tset`,
  `Tset_nonempty` (d, compactness), `mval`, `Hfun_eq_mval` (H constant on `T x`), `mval_le`,
  `mval_nonneg`, `mval_eq_zero_iff` (e).
* `s3.L3`: `argminSet_Qfun`, `mem_argminSet_Qfun_iff`, `cons_mem_argminSet_Qfun`,
  `argminSet_Qfun_nonempty`.
* `s3.L4`: `isBinary_iff_exists_fin_two` (a), `Ffun_fin_two`, `exists_nat_of_isBinary` (b),
  `exists_isBinary_Ffun_eq` (c) — via `finFunctionFinEquiv` with `m = 2`.
* `s3.L5`: `tInd`, `tInd_mem_cube`, `isBinary_tInd`, `Gfun_tInd` (a), `Gfun_of_isBinary` (b).
* `s3.L6`: `valueFun_eq` (+ `valueFun_of_isBinary`, `valueFun_of_not_isBinary`).
* `s3.L7`: `optVal_lt_zero_of_yes`. `s3.L8`: `valueFun_nonneg_of_not_yes`,
  `valueFun_zero_of_not_yes`, `lemma33_no`. `s3.lemma33`: `lemma33`.

Choices (no change of meaning): `Zset x := argminSet Lfun (Icc 0 1) x` and
`Tset x := argminSet Hfun (cube k) x`, which by `mem_argminSet_iff` are the blueprint's
`{z ∈ Icc 0 1 | IsMinOn (L x) (Icc 0 1) z}` / `{t ∈ box | IsMinOn (H x) box t}`;
`mval x := sInf (H x '' cube k)`, shown to be the attained minimum. `IsBinary` gets a
(noncomputable, via `Real.decidableEq`) `DecidablePred` instance so the `if` in `Zset_eq` /
`valueFun_eq` elaborates without `open Classical`. The lower box is `I.box` (= blueprint
`box I.k`, the cube `[0,1]^(k+1)`).
-/

namespace Bilevel
namespace SSI

/-! ### s3.L0: separable argmin on a head/tail split -/

/-- `s3.L0` (pointwise form). -/
theorem isMinOn_cons_iff {k : ℕ} {f : ℝ → ℝ} {g : (Fin k → ℝ) → ℝ} {A : Set ℝ}
    {B : Set (Fin k → ℝ)} {y : Fin (k + 1) → ℝ} (hy : y 0 ∈ A ∧ Fin.tail y ∈ B) :
    IsMinOn (fun y : Fin (k + 1) → ℝ => f (y 0) + g (Fin.tail y))
        {y : Fin (k + 1) → ℝ | y 0 ∈ A ∧ Fin.tail y ∈ B} y ↔
      IsMinOn f A (y 0) ∧ IsMinOn g B (Fin.tail y) := by
  simp only [isMinOn_iff]
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · have := h (Fin.cons a (Fin.tail y)) ⟨by simpa using ha, by simpa using hy.2⟩
      simp only [Fin.cons_zero, Fin.tail_cons] at this
      linarith
    · have := h (Fin.cons (y 0) b) ⟨by simpa using hy.1, by simpa using hb⟩
      simp only [Fin.cons_zero, Fin.tail_cons] at this
      linarith
  · rintro ⟨h1, h2⟩ y' hy'
    have := h1 _ hy'.1
    have := h2 _ hy'.2
    linarith

/-- `s3.L0` (set form, unconditional). -/
theorem argminSet_cons {X : Type*} {k : ℕ} (A : X → ℝ → ℝ) (B : X → (Fin k → ℝ) → ℝ)
    (S₁ : Set ℝ) (S₂ : Set (Fin k → ℝ)) (x : X) :
    argminSet (fun x (y : Fin (k + 1) → ℝ) => A x (y 0) + B x (Fin.tail y))
        {y : Fin (k + 1) → ℝ | y 0 ∈ S₁ ∧ Fin.tail y ∈ S₂} x =
      {y : Fin (k + 1) → ℝ | y 0 ∈ argminSet A S₁ x ∧ Fin.tail y ∈ argminSet B S₂ x} := by
  ext y
  rw [mem_argminSet_iff]
  constructor
  · rintro ⟨hy, h⟩
    have h' := (isMinOn_cons_iff (f := A x) (g := B x) hy).1 h
    exact ⟨mem_argminSet_iff.2 ⟨hy.1, h'.1⟩, mem_argminSet_iff.2 ⟨hy.2, h'.2⟩⟩
  · rintro ⟨h1, h2⟩
    rw [mem_argminSet_iff] at h1 h2
    exact ⟨⟨h1.1, h2.1⟩, (isMinOn_cons_iff (f := A x) (g := B x) ⟨h1.1, h2.1⟩).2 ⟨h1.2, h2.2⟩⟩

theorem mem_cube_iff {n : ℕ} {t : Fin n → ℝ} : t ∈ cube n ↔ ∀ i, t i ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [cube, Set.mem_univ_pi]

theorem zero_mem_cube (n : ℕ) : (0 : Fin n → ℝ) ∈ cube n := by
  simp [mem_cube_iff]

theorem isCompact_cube (n : ℕ) : IsCompact (cube n) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem mem_box_iff (I : SSI) {y : Fin (I.k + 1) → ℝ} :
    y ∈ I.box ↔ y 0 ∈ Set.Icc (0 : ℝ) 1 ∧ Fin.tail y ∈ cube I.k := by
  simp only [box, cube, Set.mem_univ_pi, Fin.forall_fin_succ, Fin.tail]

theorem box_eq (I : SSI) :
    I.box = {y : Fin (I.k + 1) → ℝ | y 0 ∈ Set.Icc (0 : ℝ) 1 ∧ Fin.tail y ∈ cube I.k} := by
  ext y; exact I.mem_box_iff

/-! ### s3.L1: analysis of `L` -/

/-- `x` is a 0/1 vector. -/
def IsBinary {n : ℕ} (x : Fin n → ℝ) : Prop := ∀ j, x j = 0 ∨ x j = 1

noncomputable instance {n : ℕ} : DecidablePred (IsBinary (n := n)) :=
  fun x => inferInstanceAs (Decidable (∀ j, x j = 0 ∨ x j = 1))

theorem mul_one_sub_eq_zero_iff {a : ℝ} : a * (1 - a) = 0 ↔ a = 0 ∨ a = 1 := by
  rw [mul_eq_zero, sub_eq_zero, eq_comm (a := (1 : ℝ))]

theorem one_sub_mul_eq_zero_iff {a : ℝ} : (1 - a) * a = 0 ↔ a = 0 ∨ a = 1 := by
  rw [mul_comm, mul_one_sub_eq_zero_iff]

theorem sum_sq_eq_zero_iff' {n : ℕ} (a : Fin n → ℝ) : ∑ j, a j ^ 2 = 0 ↔ ∀ j, a j = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (a j))]
  simp

/-- `s3.L1(a)` -/
theorem Lfun_nonneg {r : ℕ} (x : Fin r → ℝ) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ Lfun x z :=
  mul_nonneg hz.1 (by positivity)

/-- `s3.L1(b)` -/
@[simp] theorem Lfun_zero {r : ℕ} (x : Fin r → ℝ) : Lfun x 0 = 0 := by simp [Lfun]

/-- `s3.L1(c)` -/
theorem Lfun_eq_zero_iff {r : ℕ} (x : Fin r → ℝ) (z : ℝ) :
    Lfun x z = 0 ↔ z = 0 ∨ (z = 1 ∧ IsBinary x) := by
  unfold Lfun
  rw [mul_eq_zero, add_eq_zero_iff_of_nonneg (sq_nonneg _) (by positivity),
    sum_sq_eq_zero_iff', sq_eq_zero_iff, sub_eq_zero]
  simp only [one_sub_mul_eq_zero_iff, IsBinary]

/-- `s3.L1(d)` -/
theorem isMinOn_Lfun_iff {r : ℕ} (x : Fin r → ℝ) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    IsMinOn (Lfun x) (Set.Icc 0 1) z ↔ Lfun x z = 0 := by
  rw [isMinOn_iff]
  constructor
  · intro h
    have := h 0 ⟨le_rfl, zero_le_one⟩
    rw [Lfun_zero] at this
    exact le_antisymm this (Lfun_nonneg x hz)
  · intro h z' hz'
    rw [h]; exact Lfun_nonneg x hz'

/-- The `z`-part of the lower-level argmin. -/
noncomputable def Zset {r : ℕ} (x : Fin r → ℝ) : Set ℝ := argminSet (fun x z => Lfun (r := r) x z) (Set.Icc 0 1) x

theorem mem_Zset_iff {r : ℕ} (x : Fin r → ℝ) (z : ℝ) :
    z ∈ Zset x ↔ z = 0 ∨ (z = 1 ∧ IsBinary x) := by
  unfold Zset
  rw [mem_argminSet_iff]
  constructor
  · rintro ⟨hz, h⟩
    exact (Lfun_eq_zero_iff x z).1 ((isMinOn_Lfun_iff x hz).1 h)
  · intro h
    have hz : z ∈ Set.Icc (0 : ℝ) 1 := by
      rcases h with rfl | ⟨rfl, -⟩ <;> simp
    exact ⟨hz, (isMinOn_Lfun_iff x hz).2 ((Lfun_eq_zero_iff x z).2 h)⟩

/-- `s3.L1(e)` -/
theorem Zset_eq {r : ℕ} (x : Fin r → ℝ) :
    Zset x = if IsBinary x then ({0, 1} : Set ℝ) else {0} := by
  ext z
  rw [mem_Zset_iff]
  split_ifs with hb <;> simp [hb]

/-! ### s3.L2: analysis of `H` -/

section H
variable (I : SSI)

/-- `s3.L2(a)` -/
theorem Hfun_nonneg (x : Fin I.r → ℝ) (t : Fin I.k → ℝ) : 0 ≤ I.Hfun x t := by
  unfold Hfun; positivity

/-- `s3.L2(b)` -/
theorem Hfun_eq_zero_iff (x : Fin I.r → ℝ) (t : Fin I.k → ℝ) :
    I.Hfun x t = 0 ↔ IsBinary t ∧ I.Ffun x = I.Gfun t := by
  unfold Hfun
  rw [add_eq_zero_iff_of_nonneg (by positivity) (sq_nonneg _), sum_sq_eq_zero_iff', sq_eq_zero_iff,
    sub_eq_zero]
  simp only [mul_one_sub_eq_zero_iff, IsBinary]

/-- `s3.L2(c)` -/
theorem continuous_Hfun (x : Fin I.r → ℝ) : Continuous (I.Hfun x) := by
  unfold Hfun Gfun; fun_prop

/-- The `t`-part of the lower-level argmin: minimisers of `H x` over the cube. -/
noncomputable def Tset (x : Fin I.r → ℝ) : Set (Fin I.k → ℝ) := argminSet I.Hfun (cube I.k) x

/-- `s3.L2(d)`: a minimiser of `H x` over the compact cube exists. -/
theorem Tset_nonempty (x : Fin I.r → ℝ) : (I.Tset x).Nonempty := by
  obtain ⟨t, ht, hmin⟩ := (isCompact_cube I.k).exists_isMinOn ⟨0, zero_mem_cube I.k⟩
    (I.continuous_Hfun x).continuousOn
  exact ⟨t, mem_argminSet_iff.2 ⟨ht, hmin⟩⟩

theorem Tset_subset (x : Fin I.r → ℝ) : I.Tset x ⊆ cube I.k := argminSet_subset

/-- `m x := min_{t ∈ [0,1]^k} H x t`. -/
noncomputable def mval (x : Fin I.r → ℝ) : ℝ := sInf (I.Hfun x '' cube I.k)

theorem isLeast_of_mem_Tset {x : Fin I.r → ℝ} {t : Fin I.k → ℝ} (ht : t ∈ I.Tset x) :
    IsLeast (I.Hfun x '' cube I.k) (I.Hfun x t) := by
  rw [Tset, mem_argminSet_iff, isMinOn_iff] at ht
  exact ⟨⟨t, ht.1, rfl⟩, by rintro _ ⟨t', ht', rfl⟩; exact ht.2 t' ht'⟩

/-- `H x` is constant (`= m x`) on the argmin `T x`. -/
theorem Hfun_eq_mval {x : Fin I.r → ℝ} {t : Fin I.k → ℝ} (ht : t ∈ I.Tset x) :
    I.Hfun x t = I.mval x :=
  (I.isLeast_of_mem_Tset ht).csInf_eq.symm

theorem mval_le {x : Fin I.r → ℝ} {t : Fin I.k → ℝ} (ht : t ∈ cube I.k) :
    I.mval x ≤ I.Hfun x t := by
  obtain ⟨t₀, h₀⟩ := I.Tset_nonempty x
  exact (I.Hfun_eq_mval h₀) ▸ (I.isLeast_of_mem_Tset h₀).2 ⟨t, ht, rfl⟩

/-- `s3.L2(e)` -/
theorem mval_nonneg (x : Fin I.r → ℝ) : 0 ≤ I.mval x := by
  obtain ⟨t₀, h₀⟩ := I.Tset_nonempty x
  rw [← I.Hfun_eq_mval h₀]; exact I.Hfun_nonneg x t₀

/-- `s3.L2(e)` -/
theorem mval_eq_zero_iff (x : Fin I.r → ℝ) :
    I.mval x = 0 ↔ ∃ t ∈ cube I.k, I.Hfun x t = 0 := by
  constructor
  · intro h
    obtain ⟨t₀, h₀⟩ := I.Tset_nonempty x
    exact ⟨t₀, I.Tset_subset x h₀, (I.Hfun_eq_mval h₀).trans h⟩
  · rintro ⟨t, ht, h⟩
    exact le_antisymm (h ▸ I.mval_le ht) (I.mval_nonneg x)

end H

/-! ### s3.L3: separability (paper eq. (20)) -/

theorem argminSet_Qfun (I : SSI) (x : Fin I.r → ℝ) :
    argminSet I.Qfun I.box x = {y : Fin (I.k + 1) → ℝ | y 0 ∈ Zset x ∧ Fin.tail y ∈ I.Tset x} := by
  rw [box_eq]
  exact argminSet_cons (fun x z => Lfun x z) I.Hfun (Set.Icc 0 1) (cube I.k) x

/-- `s3.L3` -/
theorem mem_argminSet_Qfun_iff (I : SSI) (x : Fin I.r → ℝ) (y : Fin (I.k + 1) → ℝ) :
    y ∈ argminSet I.Qfun I.box x ↔ y ∈ I.box ∧ y 0 ∈ Zset x ∧ Fin.tail y ∈ I.Tset x := by
  rw [argminSet_Qfun]
  refine ⟨fun h => ⟨I.mem_box_iff.2 ⟨argminSet_subset h.1, I.Tset_subset x h.2⟩, h⟩,
    fun h => h.2⟩

theorem cons_mem_argminSet_Qfun (I : SSI) {x : Fin I.r → ℝ} {z : ℝ} {t : Fin I.k → ℝ}
    (hz : z ∈ Zset x) (ht : t ∈ I.Tset x) :
    (Fin.cons z t : Fin (I.k + 1) → ℝ) ∈ argminSet I.Qfun I.box x := by
  rw [argminSet_Qfun]
  exact ⟨by simpa using hz, by simpa using ht⟩

/-- Corollary of `s3.L3`: the lower-level argmin is never empty. -/
theorem argminSet_Qfun_nonempty (I : SSI) (x : Fin I.r → ℝ) :
    (argminSet I.Qfun I.box x).Nonempty := by
  obtain ⟨t, ht⟩ := I.Tset_nonempty x
  exact ⟨_, I.cons_mem_argminSet_Qfun ((mem_Zset_iff x 0).2 (Or.inl rfl)) ht⟩

/-! ### s3.L4: binary expansions -/

/-- `s3.L4(a)` -/
theorem isBinary_iff_exists_fin_two {n : ℕ} (x : Fin n → ℝ) :
    IsBinary x ↔ ∃ f : Fin n → Fin 2, x = fun j => ((f j : ℕ) : ℝ) := by
  constructor
  · intro h
    refine ⟨fun j => if x j = 0 then 0 else 1, funext fun j => ?_⟩
    rcases h j with h | h <;> simp [h]
  · rintro ⟨f, rfl⟩ j
    have : ((f j : ℕ)) = 0 ∨ (f j : ℕ) = 1 := by omega
    rcases this with h | h <;> simp [h]

/-- `s3.L4(b)` -/
theorem Ffun_fin_two (I : SSI) (f : Fin I.r → Fin 2) :
    I.Ffun (fun j => ((f j : ℕ) : ℝ)) = ((I.R + (finFunctionFinEquiv f : ℕ) : ℕ) : ℝ) := by
  rw [finFunctionFinEquiv_apply, Ffun]
  push_cast
  simp only [mul_comm]

/-- `s3.L4(b)`: on binary points `F x` is a natural number in `[R, R + 2^r)`. -/
theorem exists_nat_of_isBinary (I : SSI) {x : Fin I.r → ℝ} (hx : IsBinary x) :
    ∃ S : ℕ, I.Ffun x = S ∧ I.R ≤ S ∧ S < I.R + 2 ^ I.r := by
  obtain ⟨f, rfl⟩ := (isBinary_iff_exists_fin_two x).1 hx
  refine ⟨I.R + (finFunctionFinEquiv f : ℕ), I.Ffun_fin_two f, Nat.le_add_right _ _, ?_⟩
  have := (finFunctionFinEquiv f).isLt
  omega

/-- `s3.L4(c)` -/
theorem exists_isBinary_Ffun_eq (I : SSI) {S : ℕ} (h1 : I.R ≤ S) (h2 : S < I.R + 2 ^ I.r) :
    ∃ x : Fin I.r → ℝ, IsBinary x ∧ I.Ffun x = S := by
  have hn : S - I.R < 2 ^ I.r := by omega
  set f : Fin I.r → Fin 2 := (finFunctionFinEquiv : (Fin I.r → Fin 2) ≃ Fin (2 ^ I.r)).symm
    ⟨S - I.R, hn⟩ with hf
  refine ⟨fun j => ((f j : ℕ) : ℝ), (isBinary_iff_exists_fin_two _).2 ⟨f, rfl⟩, ?_⟩
  rw [I.Ffun_fin_two f, hf, Equiv.apply_symm_apply]
  congr 1
  simp only
  omega

/-! ### s3.L5: subset sums and binary `t` -/

/-- The indicator vector of `T`. -/
noncomputable def tInd {k : ℕ} (T : Finset (Fin k)) : Fin k → ℝ := fun i => if i ∈ T then 1 else 0

/-- `s3.L5(a)` -/
theorem tInd_mem_cube {k : ℕ} (T : Finset (Fin k)) : tInd T ∈ cube k := by
  rw [mem_cube_iff]; intro i; unfold tInd; split_ifs <;> simp

/-- `s3.L5(a)` -/
theorem isBinary_tInd {k : ℕ} (T : Finset (Fin k)) : IsBinary (tInd T) := by
  intro i; unfold tInd; split_ifs <;> simp

/-- `s3.L5(a)` -/
theorem Gfun_tInd (I : SSI) (T : Finset (Fin I.k)) :
    I.Gfun (tInd T) = ((∑ i ∈ T, I.q i : ℕ) : ℝ) := by
  simp only [Gfun, tInd, ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter,
    Nat.cast_sum]

/-- `s3.L5(b)` -/
theorem Gfun_of_isBinary (I : SSI) {t : Fin I.k → ℝ} (ht : IsBinary t) :
    I.Gfun t = ((∑ i ∈ Finset.univ.filter (fun i => t i = 1), I.q i : ℕ) : ℝ) := by
  rw [Nat.cast_sum, Finset.sum_filter, Gfun]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases ht i with h | h <;> simp [h]

/-! ### s3.L6: the value function (paper eq. (21)) -/

theorem Pfun_of_mem_argminSet (I : SSI) {x : Fin I.r → ℝ} {y : Fin (I.k + 1) → ℝ}
    (hy : y ∈ argminSet I.Qfun I.box x) : I.Pfun x y = 1 - y 0 * (I.mval x + 1) := by
  rw [Pfun, I.Hfun_eq_mval ((I.mem_argminSet_Qfun_iff x y).1 hy).2.2]

/-- `s3.L6`: `φ x = -m x` on binary `x`, `φ x = 1` otherwise. -/
theorem valueFun_eq (I : SSI) (x : Fin I.r → ℝ) :
    valueFun I.Pfun I.Qfun I.box x = ((if IsBinary x then -(I.mval x) else 1 : ℝ) : EReal) := by
  obtain ⟨t, ht⟩ := I.Tset_nonempty x
  split_ifs with hb
  · apply valueFun_eq_of_isLeast
    have hmem := I.cons_mem_argminSet_Qfun ((mem_Zset_iff x 1).2 (Or.inr ⟨rfl, hb⟩)) ht
    refine ⟨⟨_, hmem, ?_⟩, ?_⟩
    · rw [I.Pfun_of_mem_argminSet hmem, Fin.cons_zero]; ring
    · rintro _ ⟨y, hy, rfl⟩
      rw [I.Pfun_of_mem_argminSet hy]
      have hm := I.mval_nonneg x
      rcases (mem_Zset_iff x (y 0)).1 ((I.mem_argminSet_Qfun_iff x y).1 hy).2.1 with h | ⟨h, -⟩
      · rw [h]; linarith
      · rw [h]; linarith
  · apply valueFun_eq_of_const (I.argminSet_Qfun_nonempty x)
    intro y hy
    rw [I.Pfun_of_mem_argminSet hy]
    rcases (mem_Zset_iff x (y 0)).1 ((I.mem_argminSet_Qfun_iff x y).1 hy).2.1 with h | ⟨-, h⟩
    · rw [h]; ring
    · exact absurd h hb

/-- `φ` is real-valued and `≤ 0` on binary points, `= 1` elsewhere. -/
theorem valueFun_of_isBinary (I : SSI) {x : Fin I.r → ℝ} (hx : IsBinary x) :
    valueFun I.Pfun I.Qfun I.box x = ((-(I.mval x) : ℝ) : EReal) := by
  rw [valueFun_eq, ite_eq_left hx]

theorem valueFun_of_not_isBinary (I : SSI) {x : Fin I.r → ℝ} (hx : ¬ IsBinary x) :
    valueFun I.Pfun I.Qfun I.box x = ((1 : ℝ) : EReal) := by
  rw [valueFun_eq, ite_eq_right hx]

/-! ### s3.L7: YES ⇒ optimal value < 0 -/

/-- `s3.L7` -/
theorem optVal_lt_zero_of_yes (I : SSI) (h : I.Yes) :
    optVal I.Pfun I.Qfun I.box < (0 : EReal) := by
  obtain ⟨S, h1, h2, hS⟩ := h
  obtain ⟨x, hx, hFx⟩ := I.exists_isBinary_Ffun_eq h1 h2
  have hm : I.mval x ≠ 0 := by
    intro hm0
    obtain ⟨t, -, hHt⟩ := (I.mval_eq_zero_iff x).1 hm0
    obtain ⟨htb, hFG⟩ := (I.Hfun_eq_zero_iff x t).1 hHt
    apply hS
    refine ⟨Finset.univ.filter (fun i => t i = 1), ?_⟩
    have := hFx.symm.trans (hFG.trans (I.Gfun_of_isBinary htb))
    exact_mod_cast this.symm
  have hpos : 0 < I.mval x := lt_of_le_of_ne (I.mval_nonneg x) (Ne.symm hm)
  unfold optVal
  rw [iInf_lt_iff]
  refine ⟨x, ?_⟩
  rw [I.valueFun_of_isBinary hx, ← EReal.coe_zero, EReal.coe_lt_coe_iff]
  linarith

/-! ### s3.L8: NO ⇒ optimal value = 0, attained -/

theorem valueFun_nonneg_of_not_yes (I : SSI) (h : ¬ I.Yes) (x : Fin I.r → ℝ) :
    (0 : EReal) ≤ valueFun I.Pfun I.Qfun I.box x := by
  by_cases hx : IsBinary x
  · rw [I.valueFun_of_isBinary hx]
    obtain ⟨S, hFS, h1, h2⟩ := I.exists_nat_of_isBinary hx
    have hsub : I.subsetSum S := by
      by_contra hc; exact h ⟨S, h1, h2, hc⟩
    obtain ⟨T, hT⟩ := hsub
    have hH : I.Hfun x (tInd T) = 0 :=
      (I.Hfun_eq_zero_iff x _).2 ⟨isBinary_tInd T, by rw [hFS, I.Gfun_tInd, hT]⟩
    have hm : I.mval x = 0 := (I.mval_eq_zero_iff x).2 ⟨_, tInd_mem_cube T, hH⟩
    rw [hm, neg_zero, EReal.coe_zero]
  · rw [I.valueFun_of_not_isBinary hx, ← EReal.coe_zero, EReal.coe_le_coe_iff]
    exact zero_le_one

theorem isBinary_zero {n : ℕ} : IsBinary (0 : Fin n → ℝ) := fun _ => Or.inl rfl

/-- `s3.L8` (attained at `x = 0`). -/
theorem valueFun_zero_of_not_yes (I : SSI) (h : ¬ I.Yes) :
    valueFun I.Pfun I.Qfun I.box 0 = 0 := by
  refine le_antisymm ?_ (I.valueFun_nonneg_of_not_yes h 0)
  rw [I.valueFun_of_isBinary isBinary_zero]
  have hm := I.mval_nonneg 0
  rw [← EReal.coe_zero, EReal.coe_le_coe_iff]
  linarith

/-- `s3.lemma33_no` (`s3.L8`): on NO-instances the optimal value is `0`. -/
theorem lemma33_no (I : SSI) (h : ¬ I.Yes) : optVal I.Pfun I.Qfun I.box = 0 :=
  le_antisymm (iInf_le_of_le 0 (I.valueFun_zero_of_not_yes h).le)
    (le_iInf (I.valueFun_nonneg_of_not_yes h))

/-- `s3.lemma33` (Lemma 3.3 (b),(c)): the optimal value is `< 0` iff `I` is a YES-instance. -/
theorem lemma33 (I : SSI) : optVal I.Pfun I.Qfun I.box < (0 : EReal) ↔ I.Yes := by
  refine ⟨fun hlt => ?_, I.optVal_lt_zero_of_yes⟩
  by_contra h
  rw [I.lemma33_no h] at hlt
  exact lt_irrefl _ hlt

end SSI
end Bilevel
