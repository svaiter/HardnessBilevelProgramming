# W2-c API: Gadgets/Scalar, Gadgets/ZeroLocus, Unbounded/Thm212 (namespace Bilevel)

Modules: `HardnessBilevel.Gadgets.Scalar` (imports Mathlib), `HardnessBilevel.Gadgets.ZeroLocus`
(imports Scalar, Framework.Poly, Semialgebraic.Basic), `HardnessBilevel.Unbounded.Thm212` (imports ZeroLocus,
Framework.Basic/Value/Separable/Poly). All `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
Printed with `open Bilevel` (prefix omitted). Note: identifiers use `τm`/`𝒢m`/`Wm`/`ρm` for the blueprint's
`τ₋`/`𝒢₋`/`W₋`/`ρ₋` (`₋` is not a legal identifier character).

Definitions: `gadgetStrict p z := (1 - p * z ^ 2) ^ 2`; `escape a u v := a * u ^ 2 + (1 - u * v) ^ 2`;
`Γ h := {p : Fin n ⊕ Unit → ℝ | h (p ∘ Sum.inl) = ↑(p (Sum.inr ()))}`;
`Thm212.Idx τΓ τm := Unit ⊕ (τΓ ⊕ (τm ⊕ (Unit ⊕ Unit)))` (abbrev);
`Thm212.Qpoly 𝒢Γ 𝒢m := rename ρΓ 𝒢Γ.W * rename ρm 𝒢m.W * X (inr iU) ^ 2 + (1 - X (inr iU) * X (inr iV)) ^ 2`,
`Thm212.Ppoly := X (inr iT)`, `Qfun := polyFun Qpoly`, `Pfun := polyFun Ppoly`.
`ZeroGadget.iUnion` uses `W := ∏ i, rename (Sum.map id (Sigma.mk i)) (𝒢 i).W`, `sel w p := (𝒢 p.1).sel w p.2`;
`iUnionUniform` the same with `Prod.mk i`. `ZeroGadget.basic` uses `W := basicW P Q`,
`sel w j := √(eval w (Q j))⁻¹`.

```lean
gadgetStrict : ℝ → ℝ → ℝ
gadgetStrict_nonneg : ∀ (p z : ℝ), 0 ≤ gadgetStrict p z
@gadgetStrict_eq_zero_of_pos : ∀ {p : ℝ}, 0 < p → gadgetStrict p √p⁻¹ = 0
@one_le_gadgetStrict_of_nonpos : ∀ {p : ℝ}, p ≤ 0 → ∀ (z : ℝ), 1 ≤ gadgetStrict p z
@pos_of_gadgetStrict_eq_zero : ∀ {p z : ℝ}, gadgetStrict p z = 0 → 0 < p
escape : ℝ → ℝ → ℝ → ℝ
@escape_nonneg : ∀ {a : ℝ}, 0 ≤ a → ∀ (u v : ℝ), 0 ≤ escape a u v
escape_one_one : ∀ (a : ℝ), escape a 1 1 = a
@escape_pos : ∀ {a : ℝ}, 0 < a → ∀ (u v : ℝ), 0 < escape a u v
escape_lt : ∀ (a : ℝ) {ε : ℝ}, 0 < ε → ∃ u v, escape a u v < ε
@escape_eq_zero : ∀ {a u v : ℝ}, 0 ≤ a → escape a u v = 0 → a = 0 ∧ u * v = 1
@escape_eq_zero_of : ∀ {a u v : ℝ}, a = 0 → u * v = 1 → escape a u v = 0
@ZeroGadget : {σ : Type u_1} → Set (σ → ℝ) → Type u_2 → Type (max u_1 u_2)
@ZeroGadget.W : {σ : Type u_1} → {S : Set (σ → ℝ)} → {τ : Type u_2} → ZeroGadget S τ → MvPolynomial (σ ⊕ τ) ℝ
@ZeroGadget.sel : {σ : Type u_1} → {S : Set (σ → ℝ)} → {τ : Type u_2} → ZeroGadget S τ → (σ → ℝ) → τ → ℝ
@ZeroGadget.nonneg : ∀ {σ : Type u_1} {S : Set (σ → ℝ)} {τ : Type u_2} (self : ZeroGadget S τ) (w : σ → ℝ) (ξ : τ → ℝ),
  0 ≤ (MvPolynomial.eval (Sum.elim w ξ)) self.W
@ZeroGadget.sel_zero : ∀ {σ : Type u_1} {S : Set (σ → ℝ)} {τ : Type u_2} (self : ZeroGadget S τ),
  ∀ w ∈ S, (MvPolynomial.eval (Sum.elim w (self.sel w))) self.W = 0
@ZeroGadget.pos_of_notMem : ∀ {σ : Type u_1} {S : Set (σ → ℝ)} {τ : Type u_2} (self : ZeroGadget S τ),
  ∀ w ∉ S, ∀ (ξ : τ → ℝ), 0 < (MvPolynomial.eval (Sum.elim w ξ)) self.W
@ZeroGadget.mem_of_eval_eq_zero : ∀ {σ : Type u_1} {τ : Type u_2} {S : Set (σ → ℝ)} (𝒢 : ZeroGadget S τ) {w : σ → ℝ}
  {ξ : τ → ℝ}, (MvPolynomial.eval (Sum.elim w ξ)) 𝒢.W = 0 → w ∈ S
@ZeroGadget.mem_iff : ∀ {σ : Type u_1} {τ : Type u_2} {S : Set (σ → ℝ)} (𝒢 : ZeroGadget S τ) {w : σ → ℝ},
  w ∈ S ↔ ∃ ξ, (MvPolynomial.eval (Sum.elim w ξ)) 𝒢.W = 0
@ZeroGadget.basicW : {σ : Type u_1} →
  {κ : Type u_2} → [Fintype κ] → MvPolynomial σ ℝ → (κ → MvPolynomial σ ℝ) → MvPolynomial (σ ⊕ κ) ℝ
@ZeroGadget.eval_basicW : ∀ {σ : Type u_1} {κ : Type u_2} [inst : Fintype κ] (P : MvPolynomial σ ℝ)
  (Q : κ → MvPolynomial σ ℝ) (w : σ → ℝ) (ξ : κ → ℝ),
  (MvPolynomial.eval (Sum.elim w ξ)) (ZeroGadget.basicW P Q) =
    (MvPolynomial.eval w) P ^ 2 + ∑ j, gadgetStrict ((MvPolynomial.eval w) (Q j)) (ξ j)
@ZeroGadget.basic : {σ : Type u_1} →
  {κ : Type u_2} →
    [Fintype κ] →
      (P : MvPolynomial σ ℝ) →
        (Q : κ → MvPolynomial σ ℝ) →
          ZeroGadget {w | (MvPolynomial.eval w) P = 0 ∧ ∀ (j : κ), 0 < (MvPolynomial.eval w) (Q j)} κ
@ZeroGadget.sumElim_comp_sumMap_sigma : ∀ {σ : Type u_1} {ι : Type u_2} {τ : ι → Type u_3} (w : σ → ℝ)
  (ξ : (i : ι) × τ i → ℝ) (i : ι), Sum.elim w ξ ∘ Sum.map id (Sigma.mk i) = Sum.elim w fun j => ξ ⟨i, j⟩
@ZeroGadget.iUnion : {σ : Type u_1} →
  {ι : Type u_2} →
    [Fintype ι] →
      {τ : ι → Type u_3} →
        {S : ι → Set (σ → ℝ)} → ((i : ι) → ZeroGadget (S i) (τ i)) → ZeroGadget (⋃ i, S i) ((i : ι) × τ i)
@ZeroGadget.iUnion_W_eval : ∀ {σ : Type u_1} {ι : Type u_2} [inst : Fintype ι] {τ : ι → Type u_3} {S : ι → Set (σ → ℝ)}
  (𝒢 : (i : ι) → ZeroGadget (S i) (τ i)) (w : σ → ℝ) (ξ : (i : ι) × τ i → ℝ),
  (MvPolynomial.eval (Sum.elim w ξ)) (ZeroGadget.iUnion 𝒢).W =
    ∏ i, (MvPolynomial.eval (Sum.elim w fun j => ξ ⟨i, j⟩)) (𝒢 i).W
@ZeroGadget.sumElim_comp_sumMap_prod : ∀ {σ : Type u_1} {ι : Type u_2} {κ : Type u_3} (w : σ → ℝ) (ξ : ι × κ → ℝ)
  (i : ι), Sum.elim w ξ ∘ Sum.map id (Prod.mk i) = Sum.elim w fun j => ξ (i, j)
@ZeroGadget.iUnionUniform : {σ : Type u_1} →
  {ι : Type u_2} →
    [Fintype ι] →
      {κ : Type u_3} → {S : ι → Set (σ → ℝ)} → ((i : ι) → ZeroGadget (S i) κ) → ZeroGadget (⋃ i, S i) (ι × κ)
@ZeroGadget.of_isSemialgebraic : ∀ {σ : Type u_1} {S : Set (σ → ℝ)},
  IsSemialgebraic S → ∃ τ x, Nonempty (ZeroGadget S τ)
@Γ : {n : ℕ} → ((Fin n → ℝ) → EReal) → Set (Fin n ⊕ Unit → ℝ)
Thm212.Idx : Type → Type → Type
@Thm212.iT : {τΓ τm : Type} → Thm212.Idx τΓ τm
@Thm212.iZ : {τΓ τm : Type} → τΓ → Thm212.Idx τΓ τm
@Thm212.iN : {τΓ τm : Type} → τm → Thm212.Idx τΓ τm
@Thm212.iU : {τΓ τm : Type} → Thm212.Idx τΓ τm
@Thm212.iV : {τΓ τm : Type} → Thm212.Idx τΓ τm
@Thm212.zc : {τΓ τm : Type} → (Thm212.Idx τΓ τm → ℝ) → τΓ → ℝ
@Thm212.νc : {τΓ τm : Type} → (Thm212.Idx τΓ τm → ℝ) → τm → ℝ
@Thm212.mk : {τΓ τm : Type} → ℝ → (τΓ → ℝ) → (τm → ℝ) → ℝ → ℝ → Thm212.Idx τΓ τm → ℝ
@Thm212.ρΓ : {τΓ τm : Type} → {n : ℕ} → (Fin n ⊕ Unit) ⊕ τΓ → Fin n ⊕ Thm212.Idx τΓ τm
@Thm212.ρm : {τΓ τm : Type} → {n : ℕ} → Fin n ⊕ τm → Fin n ⊕ Thm212.Idx τΓ τm
@Thm212.sumElim_comp_ρΓ : ∀ {τΓ τm : Type} {n : ℕ} (x : Fin n → ℝ) (y : Thm212.Idx τΓ τm → ℝ),
  Sum.elim x y ∘ Thm212.ρΓ = Sum.elim (Sum.elim x fun x => y Thm212.iT) (Thm212.zc y)
@Thm212.sumElim_comp_ρm : ∀ {τΓ τm : Type} {n : ℕ} (x : Fin n → ℝ) (y : Thm212.Idx τΓ τm → ℝ),
  Sum.elim x y ∘ Thm212.ρm = Sum.elim x (Thm212.νc y)
@Thm212.WΓ : {τΓ : Type} → {n : ℕ} → {h : (Fin n → ℝ) → EReal} → ZeroGadget (Γ h) τΓ → (Fin n → ℝ) → ℝ → (τΓ → ℝ) → ℝ
@Thm212.Wm : {τm : Type} →
  {n : ℕ} → {h : (Fin n → ℝ) → EReal} → ZeroGadget {x | h x = ⊥} τm → (Fin n → ℝ) → (τm → ℝ) → ℝ
@Thm212.a : {τΓ τm : Type} →
  {n : ℕ} →
    {h : (Fin n → ℝ) → EReal} →
      ZeroGadget (Γ h) τΓ → ZeroGadget {x | h x = ⊥} τm → (Fin n → ℝ) → ℝ → (τΓ → ℝ) → (τm → ℝ) → ℝ
@Thm212.Qpoly : {τΓ τm : Type} →
  {n : ℕ} →
    {h : (Fin n → ℝ) → EReal} →
      ZeroGadget (Γ h) τΓ → ZeroGadget {x | h x = ⊥} τm → MvPolynomial (Fin n ⊕ Thm212.Idx τΓ τm) ℝ
@Thm212.Ppoly : {τΓ τm : Type} → {n : ℕ} → MvPolynomial (Fin n ⊕ Thm212.Idx τΓ τm) ℝ
@Thm212.Qfun : {τΓ τm : Type} →
  {n : ℕ} →
    {h : (Fin n → ℝ) → EReal} →
      ZeroGadget (Γ h) τΓ → ZeroGadget {x | h x = ⊥} τm → (Fin n → ℝ) → (Thm212.Idx τΓ τm → ℝ) → ℝ
@Thm212.Pfun : {τΓ τm : Type} → {n : ℕ} → (Fin n → ℝ) → (Thm212.Idx τΓ τm → ℝ) → ℝ
@Thm212.eval_Qpoly : ∀ {τΓ τm : Type} {n : ℕ} {h : (Fin n → ℝ) → EReal} (𝒢Γ : ZeroGadget (Γ h) τΓ)
  (𝒢m : ZeroGadget {x | h x = ⊥} τm) (x : Fin n → ℝ) (y : Thm212.Idx τΓ τm → ℝ),
  (MvPolynomial.eval (Sum.elim x y)) (Thm212.Qpoly 𝒢Γ 𝒢m) =
    escape (Thm212.a 𝒢Γ 𝒢m x (y Thm212.iT) (Thm212.zc y) (Thm212.νc y)) (y Thm212.iU) (y Thm212.iV)
@Thm212.eval_Ppoly : ∀ {τΓ τm : Type} {n : ℕ} (x : Fin n → ℝ) (y : Thm212.Idx τΓ τm → ℝ),
  (MvPolynomial.eval (Sum.elim x y)) Thm212.Ppoly = y Thm212.iT
@Thm212.Qfun_apply : ∀ {τΓ τm : Type} {n : ℕ} {h : (Fin n → ℝ) → EReal} (𝒢Γ : ZeroGadget (Γ h) τΓ)
  (𝒢m : ZeroGadget {x | h x = ⊥} τm) (x : Fin n → ℝ) (y : Thm212.Idx τΓ τm → ℝ),
  Thm212.Qfun 𝒢Γ 𝒢m x y =
    escape (Thm212.a 𝒢Γ 𝒢m x (y Thm212.iT) (Thm212.zc y) (Thm212.νc y)) (y Thm212.iU) (y Thm212.iV)
@Thm212.Pfun_apply : ∀ {τΓ τm : Type} {n : ℕ} (x : Fin n → ℝ) (y : Thm212.Idx τΓ τm → ℝ), Thm212.Pfun x y = y Thm212.iT
@Thm212.a_nonneg : ∀ {τΓ τm : Type} {n : ℕ} {h : (Fin n → ℝ) → EReal} (𝒢Γ : ZeroGadget (Γ h) τΓ)
  (𝒢m : ZeroGadget {x | h x = ⊥} τm) (x : Fin n → ℝ) (t : ℝ) (z : τΓ → ℝ) (ν : τm → ℝ), 0 ≤ Thm212.a 𝒢Γ 𝒢m x t z ν
@Thm212.eq_or_bot_of_a_eq_zero : ∀ {τΓ τm : Type} {n : ℕ} {h : (Fin n → ℝ) → EReal} (𝒢Γ : ZeroGadget (Γ h) τΓ)
  (𝒢m : ZeroGadget {x | h x = ⊥} τm) {x : Fin n → ℝ} {t : ℝ} {z : τΓ → ℝ} {ν : τm → ℝ},
  Thm212.a 𝒢Γ 𝒢m x t z ν = 0 → h x = ↑t ∨ h x = ⊥
@Thm212.a_sel_eq_zero_of_coe : ∀ {τΓ τm : Type} {n : ℕ} {h : (Fin n → ℝ) → EReal} (𝒢Γ : ZeroGadget (Γ h) τΓ)
  (𝒢m : ZeroGadget {x | h x = ⊥} τm) {x : Fin n → ℝ} {t : ℝ},
  h x = ↑t → ∀ (ν : τm → ℝ), Thm212.a 𝒢Γ 𝒢m x t (𝒢Γ.sel (Sum.elim x fun x => t)) ν = 0
@Thm212.a_sel_eq_zero_of_bot : ∀ {τΓ τm : Type} {n : ℕ} {h : (Fin n → ℝ) → EReal} (𝒢Γ : ZeroGadget (Γ h) τΓ)
  (𝒢m : ZeroGadget {x | h x = ⊥} τm) {x : Fin n → ℝ},
  h x = ⊥ → ∀ (t : ℝ) (z : τΓ → ℝ), Thm212.a 𝒢Γ 𝒢m x t z (𝒢m.sel x) = 0
@Thm212.a_pos : ∀ {τΓ τm : Type} {n : ℕ} {h : (Fin n → ℝ) → EReal} (𝒢Γ : ZeroGadget (Γ h) τΓ)
  (𝒢m : ZeroGadget {x | h x = ⊥} τm) {x : Fin n → ℝ},
  h x ≠ ⊥ → (∀ (t : ℝ), h x ≠ ↑t) → ∀ (t : ℝ) (z : τΓ → ℝ) (ν : τm → ℝ), 0 < Thm212.a 𝒢Γ 𝒢m x t z ν
@Thm212.Qfun_nonneg : ∀ {τΓ τm : Type} {n : ℕ} {h : (Fin n → ℝ) → EReal} (𝒢Γ : ZeroGadget (Γ h) τΓ)
  (𝒢m : ZeroGadget {x | h x = ⊥} τm) (x : Fin n → ℝ) (y : Thm212.Idx τΓ τm → ℝ), 0 ≤ Thm212.Qfun 𝒢Γ 𝒢m x y
@Thm212.case_real : ∀ {τΓ τm : Type} {n : ℕ} {h : (Fin n → ℝ) → EReal} (𝒢Γ : ZeroGadget (Γ h) τΓ)
  (𝒢m : ZeroGadget {x | h x = ⊥} τm) {x : Fin n → ℝ} {r : ℝ},
  h x = ↑r → valueFun Thm212.Pfun (Thm212.Qfun 𝒢Γ 𝒢m) Set.univ x = ↑r
@Thm212.case_top : ∀ {τΓ τm : Type} {n : ℕ} {h : (Fin n → ℝ) → EReal} (𝒢Γ : ZeroGadget (Γ h) τΓ)
  (𝒢m : ZeroGadget {x | h x = ⊥} τm) {x : Fin n → ℝ}, h x = ⊤ → valueFun Thm212.Pfun (Thm212.Qfun 𝒢Γ 𝒢m) Set.univ x = ⊤
@Thm212.case_bot : ∀ {τΓ τm : Type} {n : ℕ} {h : (Fin n → ℝ) → EReal} (𝒢Γ : ZeroGadget (Γ h) τΓ)
  (𝒢m : ZeroGadget {x | h x = ⊥} τm) {x : Fin n → ℝ}, h x = ⊥ → valueFun Thm212.Pfun (Thm212.Qfun 𝒢Γ 𝒢m) Set.univ x = ⊥
@Thm212.valueFun_eq : ∀ {τΓ τm : Type} {n : ℕ} {h : (Fin n → ℝ) → EReal} (𝒢Γ : ZeroGadget (Γ h) τΓ)
  (𝒢m : ZeroGadget {x | h x = ⊥} τm), valueFun Thm212.Pfun (Thm212.Qfun 𝒢Γ 𝒢m) Set.univ = h
@exists_bilevel_valueFun_eq_of_gadgets : ∀ {n : ℕ} (h : (Fin n → ℝ) → EReal) {τΓ τm : Type} [Fintype τΓ] [Fintype τm]
  (𝒢Γ : ZeroGadget (Γ h) τΓ) (𝒢m : ZeroGadget {x | h x = ⊥} τm),
  ∃ ι x P Q, IsPolyFun P ∧ IsPolyFun Q ∧ valueFun P Q Set.univ = h
@exists_bilevel_valueFun_eq : ∀ {n : ℕ} (h : (Fin n → ℝ) → EReal),
  IsSemialgebraic (Γ h) →
    IsSemialgebraic {x | h x = ⊥} → ∃ ι x P Q, IsPolyFun P ∧ IsPolyFun Q ∧ valueFun P Q Set.univ = h
@Thm212.ρR : {n : ℕ} → {τ : Type} → (Fin n ⊕ Unit) ⊕ τ → Fin n ⊕ Unit ⊕ τ
@Thm212.sumElim_comp_ρR : ∀ {n : ℕ} {τ : Type} (x : Fin n → ℝ) (y : Unit ⊕ τ → ℝ),
  Sum.elim x y ∘ Thm212.ρR = Sum.elim (Sum.elim x fun x => y (Sum.inl ())) fun j => y (Sum.inr j)
@Thm212.real_valued_of_gadget : ∀ {n : ℕ} {τ : Type} (f : (Fin n → ℝ) → ℝ) (𝒢 : ZeroGadget (graphSet f) τ)
  (x : Fin n → ℝ),
  (argminSet (polyFun ((MvPolynomial.rename Thm212.ρR) 𝒢.W)) Set.univ x).Nonempty ∧
    ∀ y ∈ argminSet (polyFun ((MvPolynomial.rename Thm212.ρR) 𝒢.W)) Set.univ x,
      polyFun (MvPolynomial.X (Sum.inr (Sum.inl ()))) x y = f x
@exists_bilevel_real_valued : ∀ {n : ℕ} (f : (Fin n → ℝ) → ℝ),
  IsSemialgebraicMap f →
    ∃ ι x P Q,
      IsPolyFun P ∧
        IsPolyFun Q ∧
          (∀ (x : Fin n → ℝ), (argminSet Q Set.univ x).Nonempty ∧ ∀ y ∈ argminSet Q Set.univ x, P x y = f x) ∧
            (valueFun P Q Set.univ = fun x => ↑(f x)) ∧ pvalueFun P Q Set.univ = fun x => ↑(f x)
```
