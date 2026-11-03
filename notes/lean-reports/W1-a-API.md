# W1-a API (Framework core)

Every declaration is `Bilevel.<name>` (printed with `open Bilevel`, so the prefix is omitted below).
All `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}. Signatures as printed by `#check @Bilevel.<name>`.

## HardnessBilevel/Framework/Basic.lean

```lean
@argminSet : {X : Type u_1} → {Y : Type u_2} → (X → Y → ℝ) → Set Y → X → Set Y
```
```lean
@valueFun : {X : Type u_1} → {Y : Type u_2} → (X → Y → ℝ) → (X → Y → ℝ) → Set Y → X → EReal
```
```lean
@pvalueFun : {X : Type u_1} → {Y : Type u_2} → (X → Y → ℝ) → (X → Y → ℝ) → Set Y → X → EReal
```
```lean
@optVal : {X : Type u_1} → {Y : Type u_2} → (X → Y → ℝ) → (X → Y → ℝ) → Set Y → EReal
```
```lean
@mem_argminSet_iff : ∀ {X : Type u_1} {Y : Type u_2} {Q : X → Y → ℝ} {S : Set Y} {x : X} {y : Y},
  y ∈ argminSet Q S x ↔ y ∈ S ∧ IsMinOn (Q x) S y
```
```lean
@argminSet_subset : ∀ {X : Type u_1} {Y : Type u_2} {Q : X → Y → ℝ} {S : Set Y} {x : X}, argminSet Q S x ⊆ S
```
```lean
@mem_argminSet_univ : ∀ {X : Type u_1} {Y : Type u_2} {Q : X → Y → ℝ} {x : X} {y : Y},
  y ∈ argminSet Q Set.univ x ↔ ∀ (y' : Y), Q x y ≤ Q x y'
```
```lean
@argminSet_eq_empty_iff : ∀ {X : Type u_1} {Y : Type u_2} {Q : X → Y → ℝ} {S : Set Y} {x : X},
  argminSet Q S x = ∅ ↔ ∀ y ∈ S, ∃ y' ∈ S, Q x y' < Q x y
```
```lean
@argminSet_eq_zeroSet : ∀ {X : Type u_1} {Y : Type u_2} {Q : X → Y → ℝ} {S : Set Y} {x : X},
  (∀ y ∈ S, 0 ≤ Q x y) → (∃ y₀ ∈ S, Q x y₀ = 0) → argminSet Q S x = {y | y ∈ S ∧ Q x y = 0}
```
```lean
@mem_argminSet_of_nonneg_zero : ∀ {X : Type u_1} {Y : Type u_2} {Q : X → Y → ℝ} {S : Set Y} {x : X} {y : Y},
  (∀ y ∈ S, 0 ≤ Q x y) → y ∈ S → Q x y = 0 → y ∈ argminSet Q S x
```
```lean
@argminSet_mul_pos : ∀ {X : Type u_1} {Y : Type u_2} {Q : X → Y → ℝ} {S : Set Y} {x : X} {c : X → ℝ},
  0 < c x → argminSet (fun x y => c x * Q x y) S x = argminSet Q S x
```
```lean
@argminSet_add_left : ∀ {X : Type u_1} {Y : Type u_2} {Q : X → Y → ℝ} {S : Set Y} {x : X} (a : X → ℝ),
  argminSet (fun x y => a x + Q x y) S x = argminSet Q S x
```
```lean
@argminSet_eq_inter : ∀ {X : Type u_1} {Y : Type u_2} {Q : X → Y → ℝ} {S : Set Y} {x : X},
  argminSet Q S x = S ∩ ⋂ y' ∈ S, {y | Q x y ≤ Q x y'}
```
```lean
@argminSet_isClosed : ∀ {X : Type u_1} {Y : Type u_2} {Q : X → Y → ℝ} {S : Set Y} {x : X} [inst : TopologicalSpace Y],
  Continuous (Q x) → IsClosed S → IsClosed (argminSet Q S x)
```
```lean
@argminSet_isCompact : ∀ {X : Type u_1} {Y : Type u_2} {Q : X → Y → ℝ} {S : Set Y} {x : X} [inst : TopologicalSpace Y],
  Continuous (Q x) → IsCompact S → IsCompact (argminSet Q S x)
```
```lean
@argminSet_empty_of_pos_inf : ∀ {X : Type u_1} {Y : Type u_2} {Q : X → Y → ℝ} {S : Set Y} {x : X},
  (∀ y ∈ S, 0 < Q x y) → (∀ ε > 0, ∃ y ∈ S, Q x y < ε) → argminSet Q S x = ∅
```
```lean
@argminSet_univ_empty_of_pos_inf : ∀ {X : Type u_1} {Y : Type u_2} {Q : X → Y → ℝ} {x : X},
  (∀ (y : Y), 0 < Q x y) → (∀ ε > 0, ∃ y, Q x y < ε) → argminSet Q Set.univ x = ∅
```
```lean
@valueFun_le_coe_of_mem : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X} {y : Y},
  y ∈ argminSet Q S x → valueFun P Q S x ≤ ↑(P x y)
```
```lean
@coe_le_pvalueFun_of_mem : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X} {y : Y},
  y ∈ argminSet Q S x → ↑(P x y) ≤ pvalueFun P Q S x
```
```lean
@coe_le_valueFun_of_forall : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X} {r : ℝ},
  (∀ y ∈ argminSet Q S x, r ≤ P x y) → ↑r ≤ valueFun P Q S x
```
```lean
@pvalueFun_le_coe_of_forall : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X} {r : ℝ},
  (∀ y ∈ argminSet Q S x, P x y ≤ r) → pvalueFun P Q S x ≤ ↑r
```
```lean
@valueFun_eq_top_iff : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X},
  valueFun P Q S x = ⊤ ↔ argminSet Q S x = ∅
```
```lean
@pvalueFun_eq_bot_iff : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X},
  pvalueFun P Q S x = ⊥ ↔ argminSet Q S x = ∅
```
```lean
@valueFun_eq_of_isMinOn : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X} {y₀ : Y},
  y₀ ∈ argminSet Q S x → IsMinOn (P x) (argminSet Q S x) y₀ → valueFun P Q S x = ↑(P x y₀)
```
```lean
@pvalueFun_eq_of_isMaxOn : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X} {y₀ : Y},
  y₀ ∈ argminSet Q S x → IsMaxOn (P x) (argminSet Q S x) y₀ → pvalueFun P Q S x = ↑(P x y₀)
```
```lean
@valueFun_eq_of_isLeast : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X} {r : ℝ},
  IsLeast (P x '' argminSet Q S x) r → valueFun P Q S x = ↑r
```
```lean
@pvalueFun_eq_of_isGreatest : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X} {r : ℝ},
  IsGreatest (P x '' argminSet Q S x) r → pvalueFun P Q S x = ↑r
```
```lean
@valueFun_eq_of_const : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X} {v : ℝ},
  (argminSet Q S x).Nonempty → (∀ y ∈ argminSet Q S x, P x y = v) → valueFun P Q S x = ↑v
```
```lean
@pvalueFun_eq_of_const : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X} {v : ℝ},
  (argminSet Q S x).Nonempty → (∀ y ∈ argminSet Q S x, P x y = v) → pvalueFun P Q S x = ↑v
```
```lean
@valueFun_unique : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X} {y₀ : Y},
  argminSet Q S x = {y₀} → valueFun P Q S x = ↑(P x y₀) ∧ pvalueFun P Q S x = ↑(P x y₀)
```
```lean
@valueFun_eq_bot_of_unbounded : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X},
  (∀ (r : ℝ), ∃ y ∈ argminSet Q S x, P x y ≤ r) → valueFun P Q S x = ⊥
```
```lean
@pvalueFun_eq_top_of_unbounded : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X},
  (∀ (r : ℝ), ∃ y ∈ argminSet Q S x, r ≤ P x y) → pvalueFun P Q S x = ⊤
```
```lean
@value_shift_attained : ∀ {X : Type u_1} {Y : Type u_2} {P : X → Y → ℝ} {g : X → ℝ} {Θ : Set Y} {x : X} {r : ℝ},
  IsLeast (P x '' Θ) r → IsLeast ((fun y => P x y + g x) '' Θ) (r + g x)
```

## HardnessBilevel/Framework/Value.lean

```lean
@valueFun_eq_coe_iff : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X} {r : ℝ},
  valueFun P Q S x = ↑r ↔ (∀ y ∈ argminSet Q S x, r ≤ P x y) ∧ ∀ ε > 0, ∃ y ∈ argminSet Q S x, P x y < r + ε
```
```lean
@valueFun_eq_bot_iff : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X},
  valueFun P Q S x = ⊥ ↔ ∀ (r : ℝ), ∃ y ∈ argminSet Q S x, P x y < r
```
```lean
@pvalueFun_eq_neg_valueFun_neg : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X},
  pvalueFun P Q S x = -valueFun (fun x y => -P x y) Q S x
```
```lean
@valueFun_eq_neg_pvalueFun_neg : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X},
  valueFun P Q S x = -pvalueFun (fun x y => -P x y) Q S x
```
```lean
@pvalueFun_eq_coe_iff : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X} {r : ℝ},
  pvalueFun P Q S x = ↑r ↔ (∀ y ∈ argminSet Q S x, P x y ≤ r) ∧ ∀ ε > 0, ∃ y ∈ argminSet Q S x, r - ε < P x y
```
```lean
@pvalueFun_eq_top_iff : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X},
  pvalueFun P Q S x = ⊤ ↔ ∀ (r : ℝ), ∃ y ∈ argminSet Q S x, r < P x y
```
```lean
@valueFun_real_iff : ∀ {X : Type u_1} {Y : Type u_2} {P Q : X → Y → ℝ} {S : Set Y} {x : X},
  valueFun P Q S x ≠ ⊤ ∧ valueFun P Q S x ≠ ⊥ ↔ (argminSet Q S x).Nonempty ∧ BddBelow (P x '' argminSet Q S x)
```

## HardnessBilevel/Framework/Separable.lean

```lean
@argminSet_prod_add : ∀ {X : Type u_1} {Y₁ : Type u_2} {Y₂ : Type u_3} (A : X → Y₁ → ℝ) (B : X → Y₂ → ℝ) (S₁ : Set Y₁)
  (S₂ : Set Y₂) (x : X), argminSet (fun x y => A x y.1 + B x y.2) (S₁ ×ˢ S₂) x = argminSet A S₁ x ×ˢ argminSet B S₂ x
```
```lean
@argminSet_comp_equiv : ∀ {X : Type u_1} {Y : Type u_2} {Y' : Type u_3} (Q : X → Y → ℝ) (S : Set Y) (e : Y' ≃ Y)
  (x : X), argminSet (fun x y' => Q x (e y')) (⇑e ⁻¹' S) x = ⇑e ⁻¹' argminSet Q S x
```
```lean
@valueFun_comp_equiv : ∀ {X : Type u_1} {Y : Type u_2} {Y' : Type u_3} (P Q : X → Y → ℝ) (S : Set Y) (e : Y' ≃ Y),
  valueFun (fun x y' => P x (e y')) (fun x y' => Q x (e y')) (⇑e ⁻¹' S) = valueFun P Q S
```
```lean
@pvalueFun_comp_equiv : ∀ {X : Type u_1} {Y : Type u_2} {Y' : Type u_3} (P Q : X → Y → ℝ) (S : Set Y) (e : Y' ≃ Y),
  pvalueFun (fun x y' => P x (e y')) (fun x y' => Q x (e y')) (⇑e ⁻¹' S) = pvalueFun P Q S
```
```lean
@argminSet_pi_sum : ∀ {X : Type u_1} {ι : Type u_2} [inst : Fintype ι] {E : ι → Type u_3} (Y : (i : ι) → Set (E i))
  (g : X → (i : ι) → E i → ℝ) (x : X),
  argminSet (fun x y => ∑ i, g x i (y i)) (Set.univ.pi Y) x =
    Set.univ.pi fun i => argminSet (fun x v => g x i v) (Y i) x
```
```lean
@pi_sum_min_eq : ∀ {ι : Type u_1} [inst : Fintype ι] {E : ι → Type u_2} (Y : (i : ι) → Set (E i))
  (g : (i : ι) → E i → ℝ),
  {y | y ∈ Set.univ.pi Y ∧ ∀ y' ∈ Set.univ.pi Y, ∑ i, g i (y i) ≤ ∑ i, g i (y' i)} =
    Set.univ.pi fun i => {v | v ∈ Y i ∧ ∀ v' ∈ Y i, g i v ≤ g i v'}
```
```lean
@argminSet_sum_elim : ∀ {X : Type u_1} {α : Type u_2} {β : Type u_3} {Z : Type u_4} (A : X → (α → Z) → ℝ)
  (B : X → (β → Z) → ℝ) (S₁ : Set (α → Z)) (S₂ : Set (β → Z)) (x : X),
  argminSet (fun x y => A x (y ∘ Sum.inl) + B x (y ∘ Sum.inr)) {y | y ∘ Sum.inl ∈ S₁ ∧ y ∘ Sum.inr ∈ S₂} x =
    {y | y ∘ Sum.inl ∈ argminSet A S₁ x ∧ y ∘ Sum.inr ∈ argminSet B S₂ x}
```
