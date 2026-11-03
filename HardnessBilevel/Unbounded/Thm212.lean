/-
Copyright: HardnessBilevel project.

# Theorem 2.12, construction direction (blueprint §4.E.2)

Every extended-real function `h : ℝⁿ → EReal` whose finite-part graph `Γ h` and whose `⊥`-set
`{x | h x = ⊥}` are semialgebraic is the optimistic value function of a bilevel problem with
polynomial `P, Q` and unconstrained lower level `Y = univ`.

Simplified construction (blueprint §4.E.2, not the paper's eqs (5)–(7)):
`Q(x; t, z, ν, u, v) = W_Γ(x,t,z) · W₋(x,ν) · u² + (1 − u v)²`, `P(x; y) = t`,
lower index type `ι := Unit ⊕ (τ_Γ ⊕ (τ₋ ⊕ (Unit ⊕ Unit)))`.

Blueprint ids → Lean names (namespace `Bilevel.Thm212` unless stated):
* `t212.eval` (E1): `eval_Qpoly`, `eval_Ppoly`, `Qfun_apply`, `Pfun_apply`;
* `t212.a_lemma` (E2): `a_nonneg`, `eq_or_bot_of_a_eq_zero`, `a_sel_eq_zero_of_coe`,
  `a_sel_eq_zero_of_bot`, `a_pos`;
* `t212.case_real/case_top/case_bot` (M1–M3): `case_real`, `case_top`, `case_bot`;
* `t212.main`: `Bilevel.exists_bilevel_valueFun_eq_of_gadgets` (gadgets as hypotheses) and
  `Bilevel.exists_bilevel_valueFun_eq` (semialgebraic hypotheses, via `gad.G4`);
* `t212.real_valued`: `Bilevel.Thm212.real_valued_of_gadget` and `Bilevel.exists_bilevel_real_valued`.

No assumption (A1–A3) is used. Semialgebraicity of `{h = ⊤}` / `dom h` is not needed.
-/
import HardnessBilevel.Gadgets.ZeroLocus
import HardnessBilevel.Framework.Basic
import HardnessBilevel.Framework.Value
import HardnessBilevel.Framework.Separable
import HardnessBilevel.Framework.Poly

namespace Bilevel

open MvPolynomial

/-- `Γ h = graph(h|dom h) ⊆ ℝⁿ × ℝ`, as a subset of `Fin n ⊕ Unit → ℝ` (value coordinate
`Sum.inr ()`); blueprint §4.E.2 (erratum E-13). -/
def Γ {n : ℕ} (h : (Fin n → ℝ) → EReal) : Set (Fin n ⊕ Unit → ℝ) :=
  {p | h (p ∘ Sum.inl) = ↑(p (Sum.inr ()))}

namespace Thm212

/-! ### Lower index type and named indices -/

/-- The lower variable index type, for the variables `(t, z, ν, u, v)`. -/
abbrev Idx (τΓ τm : Type) : Type := Unit ⊕ (τΓ ⊕ (τm ⊕ (Unit ⊕ Unit)))

variable {τΓ τm : Type}

/-- index of `t` -/
def iT : Idx τΓ τm := .inl ()
/-- indices of `z` -/
def iZ : τΓ → Idx τΓ τm := fun j => .inr (.inl j)
/-- indices of `ν` -/
def iN : τm → Idx τΓ τm := fun j => .inr (.inr (.inl j))
/-- index of `u` -/
def iU : Idx τΓ τm := .inr (.inr (.inr (.inl ())))
/-- index of `v` -/
def iV : Idx τΓ τm := .inr (.inr (.inr (.inr ())))

/-- the `z`-block of a lower point -/
def zc (y : Idx τΓ τm → ℝ) : τΓ → ℝ := fun j => y (iZ j)
/-- the `ν`-block of a lower point -/
def νc (y : Idx τΓ τm → ℝ) : τm → ℝ := fun j => y (iN j)

/-- assemble a lower point from its blocks -/
def mk (t : ℝ) (z : τΓ → ℝ) (ν : τm → ℝ) (u v : ℝ) : Idx τΓ τm → ℝ :=
  Sum.elim (fun _ => t) (Sum.elim z (Sum.elim ν (Sum.elim (fun _ => u) (fun _ => v))))

@[simp] theorem mk_iT (t : ℝ) (z : τΓ → ℝ) (ν : τm → ℝ) (u v : ℝ) : mk t z ν u v iT = t := rfl
@[simp] theorem mk_iU (t : ℝ) (z : τΓ → ℝ) (ν : τm → ℝ) (u v : ℝ) : mk t z ν u v iU = u := rfl
@[simp] theorem mk_iV (t : ℝ) (z : τΓ → ℝ) (ν : τm → ℝ) (u v : ℝ) : mk t z ν u v iV = v := rfl
@[simp] theorem zc_mk (t : ℝ) (z : τΓ → ℝ) (ν : τm → ℝ) (u v : ℝ) : zc (mk t z ν u v) = z := rfl
@[simp] theorem νc_mk (t : ℝ) (z : τΓ → ℝ) (ν : τm → ℝ) (u v : ℝ) : νc (mk t z ν u v) = ν := rfl

variable {n : ℕ}

/-- variable renaming for `W_Γ`: `(x, t) ↦ (x, t)`, `z ↦ z` -/
def ρΓ : (Fin n ⊕ Unit) ⊕ τΓ → Fin n ⊕ Idx τΓ τm :=
  Sum.elim (Sum.elim Sum.inl (fun _ => Sum.inr iT)) (fun j => Sum.inr (iZ j))

/-- variable renaming for `W₋`: `x ↦ x`, `ν ↦ ν` -/
def ρm : Fin n ⊕ τm → Fin n ⊕ Idx τΓ τm := Sum.map id iN

theorem sumElim_comp_ρΓ (x : Fin n → ℝ) (y : Idx τΓ τm → ℝ) :
    Sum.elim x y ∘ (ρΓ (τm := τm)) = Sum.elim (Sum.elim x fun _ => y iT) (zc y) := by
  funext p; rcases p with (i | ⟨⟩) | j <;> rfl

theorem sumElim_comp_ρm (x : Fin n → ℝ) (y : Idx τΓ τm → ℝ) :
    Sum.elim x y ∘ (ρm (τΓ := τΓ)) = Sum.elim x (νc y) := by
  funext p; rcases p with i | j <;> rfl

/-! ### The construction -/

variable {h : (Fin n → ℝ) → EReal}
variable (𝒢Γ : ZeroGadget (Γ h) τΓ) (𝒢m : ZeroGadget {x | h x = ⊥} τm)

/-- `W_Γ(x, t, z)` -/
noncomputable def WΓ (x : Fin n → ℝ) (t : ℝ) (z : τΓ → ℝ) : ℝ :=
  MvPolynomial.eval (Sum.elim (Sum.elim x (fun _ => t)) z) 𝒢Γ.W

/-- `W₋(x, ν)` -/
noncomputable def Wm (x : Fin n → ℝ) (ν : τm → ℝ) : ℝ :=
  MvPolynomial.eval (Sum.elim x ν) 𝒢m.W

/-- `a(x, t, z, ν) = W_Γ(x,t,z) · W₋(x,ν)` -/
noncomputable def a (x : Fin n → ℝ) (t : ℝ) (z : τΓ → ℝ) (ν : τm → ℝ) : ℝ :=
  WΓ 𝒢Γ x t z * Wm 𝒢m x ν

/-- the lower objective polynomial `Q = W_Γ W₋ u² + (1 − u v)²` -/
noncomputable def Qpoly : MvPolynomial (Fin n ⊕ Idx τΓ τm) ℝ :=
  rename ρΓ 𝒢Γ.W * rename ρm 𝒢m.W * X (Sum.inr iU) ^ 2 +
    (1 - X (Sum.inr iU) * X (Sum.inr iV)) ^ 2

/-- the upper objective polynomial `P = t` -/
noncomputable def Ppoly : MvPolynomial (Fin n ⊕ Idx τΓ τm) ℝ := X (Sum.inr iT)

/-- `Q` as a function -/
noncomputable def Qfun : (Fin n → ℝ) → (Idx τΓ τm → ℝ) → ℝ := polyFun (Qpoly 𝒢Γ 𝒢m)

/-- `P` as a function -/
noncomputable def Pfun : (Fin n → ℝ) → (Idx τΓ τm → ℝ) → ℝ := polyFun (Ppoly (τΓ := τΓ) (τm := τm))

/-- t212.eval (E1), `Q` part. -/
theorem eval_Qpoly (x : Fin n → ℝ) (y : Idx τΓ τm → ℝ) :
    MvPolynomial.eval (Sum.elim x y) (Qpoly 𝒢Γ 𝒢m) =
      escape (a 𝒢Γ 𝒢m x (y iT) (zc y) (νc y)) (y iU) (y iV) := by
  simp only [Qpoly, escape, a, WΓ, Wm, map_add, map_mul, map_pow, map_sub, map_one, eval_X,
    eval_rename, sumElim_comp_ρΓ, sumElim_comp_ρm, Sum.elim_inr]

/-- t212.eval (E1), `P` part. -/
theorem eval_Ppoly (x : Fin n → ℝ) (y : Idx τΓ τm → ℝ) :
    MvPolynomial.eval (Sum.elim x y) (Ppoly (τΓ := τΓ) (τm := τm)) = y iT := by
  simp only [Ppoly, eval_X, Sum.elim_inr]

theorem Qfun_apply (x : Fin n → ℝ) (y : Idx τΓ τm → ℝ) :
    Qfun 𝒢Γ 𝒢m x y = escape (a 𝒢Γ 𝒢m x (y iT) (zc y) (νc y)) (y iU) (y iV) :=
  eval_Qpoly 𝒢Γ 𝒢m x y

theorem Pfun_apply (x : Fin n → ℝ) (y : Idx τΓ τm → ℝ) :
    Pfun (τΓ := τΓ) (τm := τm) x y = y iT :=
  eval_Ppoly x y

/-! ### t212.a_lemma (E2) -/

/-- E2 (1) -/
theorem a_nonneg (x : Fin n → ℝ) (t : ℝ) (z : τΓ → ℝ) (ν : τm → ℝ) : 0 ≤ a 𝒢Γ 𝒢m x t z ν :=
  mul_nonneg (𝒢Γ.nonneg _ _) (𝒢m.nonneg _ _)

/-- E2 (2) -/
theorem eq_or_bot_of_a_eq_zero {x : Fin n → ℝ} {t : ℝ} {z : τΓ → ℝ} {ν : τm → ℝ}
    (ha : a 𝒢Γ 𝒢m x t z ν = 0) : h x = ↑t ∨ h x = ⊥ := by
  rcases mul_eq_zero.1 ha with h1 | h1
  · left
    have := 𝒢Γ.mem_of_eval_eq_zero h1
    simpa [Γ] using this
  · right
    exact 𝒢m.mem_of_eval_eq_zero h1

/-- E2 (3) -/
theorem a_sel_eq_zero_of_coe {x : Fin n → ℝ} {t : ℝ} (hx : h x = ↑t) (ν : τm → ℝ) :
    a 𝒢Γ 𝒢m x t (𝒢Γ.sel (Sum.elim x fun _ => t)) ν = 0 := by
  have hmem : (Sum.elim x fun _ => t) ∈ Γ h := by
    simpa [Γ] using hx
  simp only [a, WΓ, 𝒢Γ.sel_zero _ hmem, zero_mul]

/-- E2 (4) -/
theorem a_sel_eq_zero_of_bot {x : Fin n → ℝ} (hx : h x = ⊥) (t : ℝ) (z : τΓ → ℝ) :
    a 𝒢Γ 𝒢m x t z (𝒢m.sel x) = 0 := by
  simp only [a, Wm, 𝒢m.sel_zero x hx, mul_zero]

/-- E2 (5) -/
theorem a_pos {x : Fin n → ℝ} (hbot : h x ≠ ⊥) (hreal : ∀ t : ℝ, h x ≠ ↑t)
    (t : ℝ) (z : τΓ → ℝ) (ν : τm → ℝ) : 0 < a 𝒢Γ 𝒢m x t z ν := by
  have hΓ : (Sum.elim x fun _ => t) ∉ Γ h := by
    simpa [Γ] using hreal t
  exact mul_pos (𝒢Γ.pos_of_notMem _ hΓ z) (𝒢m.pos_of_notMem x hbot ν)

theorem Qfun_nonneg (x : Fin n → ℝ) (y : Idx τΓ τm → ℝ) : 0 ≤ Qfun 𝒢Γ 𝒢m x y := by
  rw [Qfun_apply]; exact escape_nonneg (a_nonneg 𝒢Γ 𝒢m _ _ _ _) _ _

/-! ### Case analysis (M1–M3) -/

/-- t212.case_real (M1) -/
theorem case_real {x : Fin n → ℝ} {r : ℝ} (hx : h x = ↑r) :
    valueFun Pfun (Qfun 𝒢Γ 𝒢m) Set.univ x = ↑r := by
  set y₀ : Idx τΓ τm → ℝ := mk r (𝒢Γ.sel (Sum.elim x fun _ => r)) 0 1 1 with hy₀
  have hQ₀ : Qfun 𝒢Γ 𝒢m x y₀ = 0 := by
    rw [Qfun_apply, hy₀, mk_iT, zc_mk, νc_mk, mk_iU, mk_iV, a_sel_eq_zero_of_coe 𝒢Γ 𝒢m hx,
      escape_one_one]
  have hy₀mem : y₀ ∈ argminSet (Qfun 𝒢Γ 𝒢m) Set.univ x :=
    mem_argminSet_of_nonneg_zero (fun y _ => Qfun_nonneg 𝒢Γ 𝒢m x y) (Set.mem_univ _) hQ₀
  refine valueFun_eq_of_const ⟨y₀, hy₀mem⟩ fun y hy => ?_
  have hQy : Qfun 𝒢Γ 𝒢m x y = 0 :=
    le_antisymm (hQ₀ ▸ mem_argminSet_univ.1 hy y₀) (Qfun_nonneg 𝒢Γ 𝒢m x y)
  rw [Qfun_apply] at hQy
  obtain ⟨ha, -⟩ := escape_eq_zero (a_nonneg 𝒢Γ 𝒢m _ _ _ _) hQy
  rw [Pfun_apply]
  rcases eq_or_bot_of_a_eq_zero 𝒢Γ 𝒢m ha with h1 | h1
  · rw [hx] at h1; exact (EReal.coe_eq_coe_iff.1 h1).symm
  · rw [hx] at h1; exact absurd h1 (EReal.coe_ne_bot r)

/-- t212.case_top (M2) -/
theorem case_top {x : Fin n → ℝ} (hx : h x = ⊤) :
    valueFun Pfun (Qfun 𝒢Γ 𝒢m) Set.univ x = ⊤ := by
  have hbot : h x ≠ ⊥ := by rw [hx]; exact top_ne_bot
  have hreal : ∀ t : ℝ, h x ≠ ↑t := fun t => by rw [hx]; exact (EReal.coe_ne_top t).symm
  refine valueFun_eq_top_iff.2 (argminSet_univ_empty_of_pos_inf (fun y => ?_) fun ε hε => ?_)
  · rw [Qfun_apply]; exact escape_pos (a_pos 𝒢Γ 𝒢m hbot hreal _ _ _) _ _
  · obtain ⟨u, v, huv⟩ := escape_lt (a 𝒢Γ 𝒢m x 0 0 0) hε
    exact ⟨mk 0 0 0 u v, by rw [Qfun_apply, mk_iT, zc_mk, νc_mk, mk_iU, mk_iV]; exact huv⟩

/-- t212.case_bot (M3) -/
theorem case_bot {x : Fin n → ℝ} (hx : h x = ⊥) :
    valueFun Pfun (Qfun 𝒢Γ 𝒢m) Set.univ x = ⊥ := by
  refine valueFun_eq_bot_of_unbounded fun r => ⟨mk r 0 (𝒢m.sel x) 1 1, ?_, ?_⟩
  · refine mem_argminSet_of_nonneg_zero (fun y _ => Qfun_nonneg 𝒢Γ 𝒢m x y) (Set.mem_univ _) ?_
    rw [Qfun_apply, mk_iT, zc_mk, νc_mk, mk_iU, mk_iV, a_sel_eq_zero_of_bot 𝒢Γ 𝒢m hx,
      escape_one_one]
  · rw [Pfun_apply, mk_iT]

/-- The value function of the construction equals `h`. -/
theorem valueFun_eq : valueFun Pfun (Qfun 𝒢Γ 𝒢m) Set.univ = h := by
  funext x
  generalize hx : h x = e
  induction e using EReal.rec with
  | bot => exact case_bot 𝒢Γ 𝒢m hx
  | coe r => exact case_real 𝒢Γ 𝒢m hx
  | top => exact case_top 𝒢Γ 𝒢m hx

end Thm212

/-- t212.main, gadget-parametrized form. -/
theorem exists_bilevel_valueFun_eq_of_gadgets {n : ℕ} (h : (Fin n → ℝ) → EReal)
    {τΓ τm : Type} [Fintype τΓ] [Fintype τm]
    (𝒢Γ : ZeroGadget (Γ h) τΓ) (𝒢m : ZeroGadget {x | h x = ⊥} τm) :
    ∃ (ι : Type) (_ : Fintype ι) (P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ),
      IsPolyFun P ∧ IsPolyFun Q ∧ valueFun P Q Set.univ = h :=
  ⟨Thm212.Idx τΓ τm, inferInstance, Thm212.Pfun, Thm212.Qfun 𝒢Γ 𝒢m,
    isPolyFun_polyFun _, isPolyFun_polyFun _, Thm212.valueFun_eq 𝒢Γ 𝒢m⟩

/-- t212.main (Thm 2.12, ⊇ direction): an extended-real function whose finite-part graph and
`⊥`-set are semialgebraic is the optimistic value function of a polynomial bilevel problem with
unconstrained lower level. -/
theorem exists_bilevel_valueFun_eq {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hΓ : IsSemialgebraic (Γ h)) (hbot : IsSemialgebraic {x | h x = ⊥}) :
    ∃ (ι : Type) (_ : Fintype ι) (P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ),
      IsPolyFun P ∧ IsPolyFun Q ∧ valueFun P Q Set.univ = h := by
  obtain ⟨τΓ, _, ⟨𝒢Γ⟩⟩ := ZeroGadget.of_isSemialgebraic hΓ
  obtain ⟨τm, _, ⟨𝒢m⟩⟩ := ZeroGadget.of_isSemialgebraic hbot
  exact exists_bilevel_valueFun_eq_of_gadgets h 𝒢Γ 𝒢m

/-! ### t212.real_valued (Remark 2.14 / §2.4 fix) -/

namespace Thm212

variable {n : ℕ} {τ : Type}

/-- renaming for the real-valued construction: `(x, t) ↦ (x, t)`, `z ↦ z`, lower index
`Unit ⊕ τ` (`t` at `Sum.inl ()`). -/
def ρR : (Fin n ⊕ Unit) ⊕ τ → Fin n ⊕ (Unit ⊕ τ) :=
  Sum.elim (Sum.elim Sum.inl (fun _ => Sum.inr (Sum.inl ()))) (fun j => Sum.inr (Sum.inr j))

theorem sumElim_comp_ρR (x : Fin n → ℝ) (y : Unit ⊕ τ → ℝ) :
    Sum.elim x y ∘ (ρR (τ := τ)) =
      Sum.elim (Sum.elim x fun _ => y (Sum.inl ())) (fun j => y (Sum.inr j)) := by
  funext p; rcases p with (i | ⟨⟩) | j <;> rfl

/-- t212.real_valued, gadget form: with `Q := W_Γ(x, t, z)` alone and `P := t`, the argmin is
nonempty at every `x` and `P` is constantly `f x` on it. -/
theorem real_valued_of_gadget (f : (Fin n → ℝ) → ℝ) (𝒢 : ZeroGadget (graphSet f) τ)
    (x : Fin n → ℝ) :
    (argminSet (polyFun (rename ρR 𝒢.W)) Set.univ x).Nonempty ∧
      ∀ y ∈ argminSet (polyFun (rename ρR 𝒢.W)) Set.univ x,
        polyFun (X (Sum.inr (Sum.inl ())) : MvPolynomial (Fin n ⊕ (Unit ⊕ τ)) ℝ) x y = f x := by
  have hQ : ∀ y : Unit ⊕ τ → ℝ, polyFun (rename ρR 𝒢.W) x y =
      MvPolynomial.eval (Sum.elim (Sum.elim x fun _ => y (Sum.inl ())) (fun j => y (Sum.inr j)))
        𝒢.W := fun y => by
    rw [polyFun_apply, eval_rename, sumElim_comp_ρR]
  have hnn : ∀ y ∈ (Set.univ : Set (Unit ⊕ τ → ℝ)), 0 ≤ polyFun (rename ρR 𝒢.W) x y :=
    fun y _ => by rw [hQ]; exact 𝒢.nonneg _ _
  set y₀ : Unit ⊕ τ → ℝ := Sum.elim (fun _ => f x) (𝒢.sel (Sum.elim x fun _ => f x)) with hy₀
  have hmem : (Sum.elim x fun _ => f x) ∈ graphSet f := by
    simp [graphSet]
  have hQ₀ : polyFun (rename ρR 𝒢.W) x y₀ = 0 := by
    rw [hQ]; exact 𝒢.sel_zero _ hmem
  refine ⟨⟨y₀, mem_argminSet_of_nonneg_zero hnn (Set.mem_univ _) hQ₀⟩, fun y hy => ?_⟩
  have hQy : polyFun (rename ρR 𝒢.W) x y = 0 :=
    le_antisymm (hQ₀ ▸ mem_argminSet_univ.1 hy y₀) (hnn y (Set.mem_univ _))
  rw [hQ] at hQy
  have := 𝒢.mem_of_eval_eq_zero hQy
  simp only [graphSet, Set.mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_inr] at this
  rw [polyFun_apply, eval_X, Sum.elim_inr]
  exact this.symm

end Thm212

/-- t212.real_valued (Remark 2.14 / corrected §2.4 remark): a semialgebraic real function is the
value function of a polynomial bilevel problem whose lower-level argmin is nonempty everywhere and
on which the upper objective is constant (`= f x`); hence optimistic = pessimistic = `f`, and every
selection of the argmin gives `f x`. The construction is `Q := W_Γ(x,t,z)`, `P := t`. -/
theorem exists_bilevel_real_valued {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsSemialgebraicMap f) :
    ∃ (ι : Type) (_ : Fintype ι) (P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ),
      IsPolyFun P ∧ IsPolyFun Q ∧
      (∀ x, (argminSet Q Set.univ x).Nonempty ∧ ∀ y ∈ argminSet Q Set.univ x, P x y = f x) ∧
      valueFun P Q Set.univ = (fun x => ((f x : ℝ) : EReal)) ∧
      pvalueFun P Q Set.univ = (fun x => ((f x : ℝ) : EReal)) := by
  obtain ⟨τ, _, ⟨𝒢⟩⟩ := ZeroGadget.of_isSemialgebraic hf
  have key := Thm212.real_valued_of_gadget f 𝒢
  refine ⟨Unit ⊕ τ, inferInstance, polyFun (X (Sum.inr (Sum.inl ()))),
    polyFun (rename Thm212.ρR 𝒢.W), isPolyFun_polyFun _, isPolyFun_polyFun _, key, ?_, ?_⟩
  · funext x; exact valueFun_eq_of_const (key x).1 (key x).2
  · funext x; exact pvalueFun_eq_of_const (key x).1 (key x).2

end Bilevel
