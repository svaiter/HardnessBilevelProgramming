# W2-f API: HardnessBilevel/Convex/{Toolkit,Lemma219,Thm218}.lean (namespace Bilevel)

Imports: Toolkit imports Framework.{Basic,Value,Separable,Poly,Box}; Lemma219 imports Toolkit; Thm218 imports Lemma219
and Semialgebraic.Basic. All theorems: `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.

Key facts:
* `ConvexLower Q := ∀ x, ConvexOn ℝ Set.univ (fun y => Q x y)` is DEFINED in Convex/Toolkit.lean (W3-c's
  Framework/Classes.lean should import it rather than redefine it).
* Lemma 2.19 objects: `basicSet P Q`, `gadQ P Q`, `gadP P Q`, `gadY J`; main theorem `lemma219`.
* Thm 2.18 construction: `t218Idx J K`, `t218Q PT QT`, `t218P PT QT p`, `t218Y J K`; main theorems `sum_indicator`
  (data form), `sum_indicator_basic` (`IsBasicSA` form), `sum_indicator_semialgebraic` (`IsSemialgebraic` form).
  `basicSet (PT i j) (QT i j)` is literally the set in `IsBasicSA`'s definition.

Signatures (`#check @Bilevel.<name>`, printed with `open Bilevel MvPolynomial`):

```lean
@ConvexLower : {n : ℕ} → {ι : Type u_1} → ((Fin n → ℝ) → (ι → ℝ) → ℝ) → Prop
argmin_scalar_univ : ∀ (c : ℝ), {t | ∀ (t' : ℝ), (1 - c * t) ^ 2 ≤ (1 - c * t') ^ 2} = if c = 0 then Set.univ else {c⁻¹}
@mul_eq_of_isMin_univ : ∀ {c t : ℝ}, (∀ (t' : ℝ), (1 - c * t) ^ 2 ≤ (1 - c * t') ^ 2) → c * t = if c = 0 then 0 else 1
isMin_univ_witness : ∀ (c t' : ℝ), (1 - c * if c = 0 then 0 else c⁻¹) ^ 2 ≤ (1 - c * t') ^ 2
argmin_scalar_Ici : ∀ (c : ℝ),
  {u | u ∈ Set.Ici 0 ∧ ∀ u' ∈ Set.Ici 0, (1 - c * u) ^ 2 ≤ (1 - c * u') ^ 2} =
    if 0 < c then {c⁻¹} else if c = 0 then Set.Ici 0 else {0}
@mul_eq_of_isMin_Ici : ∀ {c u : ℝ},
  0 ≤ u → (∀ (u' : ℝ), 0 ≤ u' → (1 - c * u) ^ 2 ≤ (1 - c * u') ^ 2) → c * u = if 0 < c then 1 else 0
isMin_Ici_witness : ∀ (c : ℝ),
  (0 ≤ if 0 < c then c⁻¹ else 0) ∧ ∀ (u' : ℝ), 0 ≤ u' → (1 - c * if 0 < c then c⁻¹ else 0) ^ 2 ≤ (1 - c * u') ^ 2
isMin_one_Icc_iff : ∀ (c : ℝ), (∀ z' ∈ Set.Icc 0 1, -c * 1 ≤ -c * z') ↔ 0 ≤ c
@eq_zero_of_isMin_Icc : ∀ {c z : ℝ}, c < 0 → z ∈ Set.Icc 0 1 → (∀ z' ∈ Set.Icc 0 1, -c * z ≤ -c * z') → z = 0
@convexOn_sq_affine : ∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : Module ℝ E] (ℓ : E →ₗ[ℝ] ℝ) (c : ℝ),
  ConvexOn ℝ Set.univ fun v => (c - ℓ v) ^ 2
@convexOn_finset_sum : ∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : Module ℝ E] {κ : Type u_2} {t : Set E},
  Convex ℝ t → ∀ (s : Finset κ) {f : κ → E → ℝ}, (∀ k ∈ s, ConvexOn ℝ t (f k)) → ConvexOn ℝ t fun v => ∑ k ∈ s, f k v
@convexOn_linear_coord : ∀ {ι : Type u_1} (j : ι) (c : ℝ), ConvexOn ℝ Set.univ fun y => c * y j
@convexOn_sq_one_sub_mul_coord : ∀ {ι : Type u_1} (a : ℝ) (j : ι), ConvexOn ℝ Set.univ fun y => (1 - a * y j) ^ 2
@ConvexLower.add : ∀ {n : ℕ} {ι : Type u_1} {Q R : (Fin n → ℝ) → (ι → ℝ) → ℝ},
  ConvexLower Q → ConvexLower R → ConvexLower fun x y => Q x y + R x y
@ConvexLower.finset_sum : ∀ {n : ℕ} {ι : Type u_1} {κ : Type u_2} (s : Finset κ) {Q : κ → (Fin n → ℝ) → (ι → ℝ) → ℝ},
  (∀ k ∈ s, ConvexLower (Q k)) → ConvexLower fun x y => ∑ k ∈ s, Q k x y
@convexLower_const : ∀ {n : ℕ} {ι : Type u_1} (c : (Fin n → ℝ) → ℝ), ConvexLower fun x x_1 => c x
@ConvexLower.comp_reindex : ∀ {n : ℕ} {ι : Type u_1} {ι' : Type u_2} {Q : (Fin n → ℝ) → (ι → ℝ) → ℝ},
  ConvexLower Q → ∀ (g : ι → ι'), ConvexLower fun x y => Q x fun k => y (g k)
@ConvexLower.convexOn : ∀ {n : ℕ} {ι : Type u_1} {Q : (Fin n → ℝ) → (ι → ℝ) → ℝ},
  ConvexLower Q → ∀ {Y : Set (ι → ℝ)}, Convex ℝ Y → ∀ (x : Fin n → ℝ), ConvexOn ℝ Y (Q x)
@isUnboundedBox_pi_univ_or_Ici : ∀ {ι : Type u_1} (I : ι → Set ℝ),
  (∀ (i : ι), I i = Set.univ ∨ I i = Set.Ici 0) → (∃ i, I i = Set.univ) → IsUnboundedBox (Set.univ.pi I)
@basicSet : {n : ℕ} → {J : Type u_1} → MvPolynomial (Fin n) ℝ → (J → MvPolynomial (Fin n) ℝ) → Set (Fin n → ℝ)
@gadQ : {n : ℕ} →
  {J : Type u_1} →
    [Fintype J] → MvPolynomial (Fin n) ℝ → (J → MvPolynomial (Fin n) ℝ) → (Fin n → ℝ) → (Unit ⊕ J → ℝ) → ℝ
@gadP : {n : ℕ} →
  {J : Type u_1} →
    [Fintype J] → MvPolynomial (Fin n) ℝ → (J → MvPolynomial (Fin n) ℝ) → (Fin n → ℝ) → (Unit ⊕ J → ℝ) → ℝ
gadY : (J : Type u_1) → Set (Unit ⊕ J → ℝ)
@gadMin : {n : ℕ} → {J : Type u_1} → MvPolynomial (Fin n) ℝ → (J → MvPolynomial (Fin n) ℝ) → (Fin n → ℝ) → Unit ⊕ J → ℝ
@mem_argminSet_gadQ_iff : ∀ {n : ℕ} {J : Type u_1} [inst : Fintype J] (P : MvPolynomial (Fin n) ℝ)
  (Q : J → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (y : Unit ⊕ J → ℝ),
  y ∈ argminSet (gadQ P Q) (gadY J) x ↔
    (∀ (t : ℝ), (1 - (eval x) P * y (Sum.inl ())) ^ 2 ≤ (1 - (eval x) P * t) ^ 2) ∧
      ∀ (j : J),
        0 ≤ y (Sum.inr j) ∧ ∀ (u : ℝ), 0 ≤ u → (1 - (eval x) (Q j) * y (Sum.inr j)) ^ 2 ≤ (1 - (eval x) (Q j) * u) ^ 2
@gadMin_mem : ∀ {n : ℕ} {J : Type u_1} [inst : Fintype J] (P : MvPolynomial (Fin n) ℝ) (Q : J → MvPolynomial (Fin n) ℝ)
  (x : Fin n → ℝ), gadMin P Q x ∈ argminSet (gadQ P Q) (gadY J) x
@argminSet_gadQ_nonempty : ∀ {n : ℕ} {J : Type u_1} [inst : Fintype J] (P : MvPolynomial (Fin n) ℝ)
  (Q : J → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ), (argminSet (gadQ P Q) (gadY J) x).Nonempty
@gadP_eq_indicator : ∀ {n : ℕ} {J : Type u_1} [inst : Fintype J] (P : MvPolynomial (Fin n) ℝ)
  (Q : J → MvPolynomial (Fin n) ℝ) {x : Fin n → ℝ} {y : Unit ⊕ J → ℝ},
  y ∈ argminSet (gadQ P Q) (gadY J) x → gadP P Q x y = (basicSet P Q).indicator 1 x
@isPolyFun_gadQ : ∀ {n : ℕ} {J : Type u_1} [inst : Fintype J] (P : MvPolynomial (Fin n) ℝ)
  (Q : J → MvPolynomial (Fin n) ℝ), IsPolyFun (gadQ P Q)
@isPolyFun_gadP : ∀ {n : ℕ} {J : Type u_1} [inst : Fintype J] (P : MvPolynomial (Fin n) ℝ)
  (Q : J → MvPolynomial (Fin n) ℝ), IsPolyFun (gadP P Q)
@convexLower_gadQ : ∀ {n : ℕ} {J : Type u_1} [inst : Fintype J] (P : MvPolynomial (Fin n) ℝ)
  (Q : J → MvPolynomial (Fin n) ℝ), ConvexLower (gadQ P Q)
isUnboundedBox_gadY : ∀ (J : Type u_1), IsUnboundedBox (gadY J)
@lemma219 : ∀ {n : ℕ} {J : Type u_1} [inst : Fintype J] (P : MvPolynomial (Fin n) ℝ) (Q : J → MvPolynomial (Fin n) ℝ),
  IsPolyFun (gadP P Q) ∧
    IsPolyFun (gadQ P Q) ∧
      ConvexLower (gadQ P Q) ∧
        IsUnboundedBox (gadY J) ∧
          (∀ (x : Fin n → ℝ),
              (argminSet (gadQ P Q) (gadY J) x).Nonempty ∧
                ∀ y ∈ argminSet (gadQ P Q) (gadY J) x, gadP P Q x y = (basicSet P Q).indicator 1 x) ∧
            (valueFun (gadP P Q) (gadQ P Q) (gadY J) = fun x => ↑((basicSet P Q).indicator 1 x)) ∧
              pvalueFun (gadP P Q) (gadQ P Q) (gadY J) = fun x => ↑((basicSet P Q).indicator 1 x)
@lemma219_exists : ∀ {n : ℕ} {J : Type} [Fintype J] (P : MvPolynomial (Fin n) ℝ) (Q : J → MvPolynomial (Fin n) ℝ),
  ∃ ι x P' Q' Y,
    IsPolyFun P' ∧
      IsPolyFun Q' ∧
        ConvexLower Q' ∧
          IsUnboundedBox Y ∧
            (∀ (x : Fin n → ℝ),
                (argminSet Q' Y x).Nonempty ∧ ∀ y ∈ argminSet Q' Y x, P' x y = (basicSet P Q).indicator 1 x) ∧
              (valueFun P' Q' Y = fun x => ↑((basicSet P Q).indicator 1 x)) ∧
                pvalueFun P' Q' Y = fun x => ↑((basicSet P Q).indicator 1 x)
@mem_argminSet_comp_inr_iff : ∀ {X : Type u_1} {α : Type u_2} {β : Type u_3} (B : X → (β → ℝ) → ℝ) (W : Set (β → ℝ))
  (x : X) (y : α ⊕ β → ℝ),
  y ∈ argminSet (fun x y => B x (y ∘ Sum.inr)) {y | y ∘ Sum.inr ∈ W} x ↔ y ∘ Sum.inr ∈ argminSet B W x
@mem_argminSet_sigma_iff : ∀ {X : Type u_1} {B : Type u_2} [inst : Fintype B] {κ : B → Type u_3}
  (W : (b : B) → Set (κ b → ℝ)) (g : (b : B) → X → (κ b → ℝ) → ℝ) (x : X) (y : (b : B) × κ b → ℝ),
  y ∈ argminSet (fun x y => ∑ b, g b x fun k => y ⟨b, k⟩) {y | ∀ (b : B), (fun k => y ⟨b, k⟩) ∈ W b} x ↔
    ∀ (b : B), (fun k => y ⟨b, k⟩) ∈ argminSet (g b) (W b) x
@one_sub_prod_one_sub_indicator : ∀ {X : Type u_1} {κ : Type u_2} [inst : Fintype κ] (T : κ → Set X) (x : X),
  1 - ∏ j, (1 - (T j).indicator 1 x) = (⋃ j, T j).indicator 1 x
@t218Idx : {N : ℕ} → (J : Fin N → ℕ) → ((i : Fin N) → Fin (J i) → ℕ) → Type
@t218Blk : {N : ℕ} →
  (J : Fin N → ℕ) →
    (K : (i : Fin N) → Fin (J i) → ℕ) →
      (b : (i : Fin N) × Fin (J i)) → (t218Idx J K → ℝ) → Unit ⊕ Fin (K b.fst b.snd) → ℝ
@t218Q : {n N : ℕ} →
  {J : Fin N → ℕ} →
    {K : (i : Fin N) → Fin (J i) → ℕ} →
      ((i : Fin N) → Fin (J i) → MvPolynomial (Fin n) ℝ) →
        ((i : Fin N) → (j : Fin (J i)) → Fin (K i j) → MvPolynomial (Fin n) ℝ) → (Fin n → ℝ) → (t218Idx J K → ℝ) → ℝ
@t218P : {n N : ℕ} →
  {J : Fin N → ℕ} →
    {K : (i : Fin N) → Fin (J i) → ℕ} →
      ((i : Fin N) → Fin (J i) → MvPolynomial (Fin n) ℝ) →
        ((i : Fin N) → (j : Fin (J i)) → Fin (K i j) → MvPolynomial (Fin n) ℝ) →
          (Fin N → MvPolynomial (Fin n) ℝ) → (Fin n → ℝ) → (t218Idx J K → ℝ) → ℝ
@t218Y : {N : ℕ} → (J : Fin N → ℕ) → (K : (i : Fin N) → Fin (J i) → ℕ) → Set (t218Idx J K → ℝ)
@mem_argminSet_t218Q_iff : ∀ {n N : ℕ} {J : Fin N → ℕ} {K : (i : Fin N) → Fin (J i) → ℕ}
  (PT : (i : Fin N) → Fin (J i) → MvPolynomial (Fin n) ℝ)
  (QT : (i : Fin N) → (j : Fin (J i)) → Fin (K i j) → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (y : t218Idx J K → ℝ),
  y ∈ argminSet (t218Q PT QT) (t218Y J K) x ↔
    ∀ (b : (i : Fin N) × Fin (J i)),
      t218Blk J K b y ∈ argminSet (gadQ (PT b.fst b.snd) (QT b.fst b.snd)) (gadY (Fin (K b.fst b.snd))) x
@argminSet_t218Q_nonempty : ∀ {n N : ℕ} {J : Fin N → ℕ} {K : (i : Fin N) → Fin (J i) → ℕ}
  (PT : (i : Fin N) → Fin (J i) → MvPolynomial (Fin n) ℝ)
  (QT : (i : Fin N) → (j : Fin (J i)) → Fin (K i j) → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ),
  (argminSet (t218Q PT QT) (t218Y J K) x).Nonempty
@t218P_eq_on_argmin : ∀ {n N : ℕ} {J : Fin N → ℕ} {K : (i : Fin N) → Fin (J i) → ℕ}
  (PT : (i : Fin N) → Fin (J i) → MvPolynomial (Fin n) ℝ)
  (QT : (i : Fin N) → (j : Fin (J i)) → Fin (K i j) → MvPolynomial (Fin n) ℝ) (p : Fin N → MvPolynomial (Fin n) ℝ)
  (S : Fin N → Set (Fin n → ℝ)),
  (∀ (i : Fin N), S i = ⋃ j, basicSet (PT i j) (QT i j)) →
    ∀ {x : Fin n → ℝ} {y : t218Idx J K → ℝ},
      y ∈ argminSet (t218Q PT QT) (t218Y J K) x → t218P PT QT p x y = ∑ i, (S i).indicator 1 x * (eval x) (p i)
@isPolyFun_t218Q : ∀ {n N : ℕ} {J : Fin N → ℕ} {K : (i : Fin N) → Fin (J i) → ℕ}
  (PT : (i : Fin N) → Fin (J i) → MvPolynomial (Fin n) ℝ)
  (QT : (i : Fin N) → (j : Fin (J i)) → Fin (K i j) → MvPolynomial (Fin n) ℝ), IsPolyFun (t218Q PT QT)
@isPolyFun_t218P : ∀ {n N : ℕ} {J : Fin N → ℕ} {K : (i : Fin N) → Fin (J i) → ℕ}
  (PT : (i : Fin N) → Fin (J i) → MvPolynomial (Fin n) ℝ)
  (QT : (i : Fin N) → (j : Fin (J i)) → Fin (K i j) → MvPolynomial (Fin n) ℝ) (p : Fin N → MvPolynomial (Fin n) ℝ),
  IsPolyFun (t218P PT QT p)
@convexLower_t218Q : ∀ {n N : ℕ} {J : Fin N → ℕ} {K : (i : Fin N) → Fin (J i) → ℕ}
  (PT : (i : Fin N) → Fin (J i) → MvPolynomial (Fin n) ℝ)
  (QT : (i : Fin N) → (j : Fin (J i)) → Fin (K i j) → MvPolynomial (Fin n) ℝ), ConvexLower (t218Q PT QT)
@isUnboundedBox_t218Y : ∀ {N : ℕ} (J : Fin N → ℕ) (K : (i : Fin N) → Fin (J i) → ℕ), IsUnboundedBox (t218Y J K)
@sum_indicator : ∀ {n N : ℕ} (J : Fin N → ℕ) (K : (i : Fin N) → Fin (J i) → ℕ)
  (PT : (i : Fin N) → Fin (J i) → MvPolynomial (Fin n) ℝ)
  (QT : (i : Fin N) → (j : Fin (J i)) → Fin (K i j) → MvPolynomial (Fin n) ℝ) (S : Fin N → Set (Fin n → ℝ)),
  (∀ (i : Fin N), S i = ⋃ j, basicSet (PT i j) (QT i j)) →
    ∀ (p : Fin N → MvPolynomial (Fin n) ℝ),
      ∃ ι x P Q Y,
        IsPolyFun P ∧
          IsPolyFun Q ∧
            ConvexLower Q ∧
              IsUnboundedBox Y ∧
                (∀ (x : Fin n → ℝ),
                    (argminSet Q Y x).Nonempty ∧
                      ∀ y ∈ argminSet Q Y x, P x y = ∑ i, (S i).indicator 1 x * (eval x) (p i)) ∧
                  (valueFun P Q Y = fun x => ↑(∑ i, (S i).indicator 1 x * (eval x) (p i))) ∧
                    pvalueFun P Q Y = fun x => ↑(∑ i, (S i).indicator 1 x * (eval x) (p i))
@sum_indicator_basic : ∀ {n N : ℕ} (S : Fin N → Set (Fin n → ℝ)),
  (∀ (i : Fin N), ∃ m T, (∀ (j : Fin m), IsBasicSA (T j)) ∧ S i = ⋃ j, T j) →
    ∀ (p : Fin N → MvPolynomial (Fin n) ℝ),
      ∃ ι x P Q Y,
        IsPolyFun P ∧
          IsPolyFun Q ∧
            ConvexLower Q ∧
              IsUnboundedBox Y ∧
                (∀ (x : Fin n → ℝ),
                    (argminSet Q Y x).Nonempty ∧
                      ∀ y ∈ argminSet Q Y x, P x y = ∑ i, (S i).indicator 1 x * (eval x) (p i)) ∧
                  (valueFun P Q Y = fun x => ↑(∑ i, (S i).indicator 1 x * (eval x) (p i))) ∧
                    pvalueFun P Q Y = fun x => ↑(∑ i, (S i).indicator 1 x * (eval x) (p i))
@sum_indicator_semialgebraic : ∀ {n N : ℕ} (S : Fin N → Set (Fin n → ℝ)),
  (∀ (i : Fin N), IsSemialgebraic (S i)) →
    ∀ (p : Fin N → MvPolynomial (Fin n) ℝ),
      ∃ ι x P Q Y,
        IsPolyFun P ∧
          IsPolyFun Q ∧
            ConvexLower Q ∧
              IsUnboundedBox Y ∧
                (∀ (x : Fin n → ℝ),
                    (argminSet Q Y x).Nonempty ∧
                      ∀ y ∈ argminSet Q Y x, P x y = ∑ i, (S i).indicator 1 x * (eval x) (p i)) ∧
                  (valueFun P Q Y = fun x => ↑(∑ i, (S i).indicator 1 x * (eval x) (p i))) ∧
                    pvalueFun P Q Y = fun x => ↑(∑ i, (S i).indicator 1 x * (eval x) (p i))
```
