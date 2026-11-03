# W4-b-core API: HardnessBilevel/Convex/Thm220Core.lean (namespace Bilevel)

Imports: Convex.Toolkit, Semialgebraic.Basic, Framework.Classes. No assumption classes. All theorems: #print axioms ⊆ {propext, Classical.choice, Quot.sound}.

Main entry points for the assembly unit (t220.supset): `t220_D_closed` + `t220_D_sa` give closedness and semialgebraicity of `D_i = {f ≤ p_i}`; feed A2's output into `t220_of_presentations` / `t220_mem_C_bounded_of_presentations`.

```lean
@t220_normalise : ∀ {n : ℕ} {L : Type u_1} [inst : Fintype L] (p : L → MvPolynomial (Fin n) ℝ) (l : L) (x : Fin n → ℝ),
  (eval x) (p l) - (eval x) (C (1 / 4) + ∑ l, p l ^ 2) ≤ 0
@lowerSemicontinuous_sub_poly : ∀ {n : ℕ} {f : (Fin n → ℝ) → ℝ},
  LowerSemicontinuous f → ∀ (q : MvPolynomial (Fin n) ℝ), LowerSemicontinuous fun x => f x - (eval x) q
t220A : (L : Type) → [Fintype L] → (n : ℕ) → (Fin n → ℝ) → (L → ℝ) → ℝ
@t220B : {n : ℕ} →
  {L : Type} →
    [Fintype L] →
      {K : L → Type} →
        [(l : L) → Fintype (K l)] → ((l : L) → K l → MvPolynomial (Fin n) ℝ) → (Fin n → ℝ) → ((l : L) × K l → ℝ) → ℝ
@t220Q : {n : ℕ} →
  {L : Type} →
    [Fintype L] →
      {K : L → Type} →
        [(l : L) → Fintype (K l)] → ((l : L) → K l → MvPolynomial (Fin n) ℝ) → (Fin n → ℝ) → (L ⊕ (l : L) × K l → ℝ) → ℝ
@t220P : {n : ℕ} →
  {L : Type} →
    [Fintype L] →
      {K : L → Type} →
        [(l : L) → Fintype (K l)] → (L → MvPolynomial (Fin n) ℝ) → (Fin n → ℝ) → (L ⊕ (l : L) × K l → ℝ) → ℝ
@boundedBox_sum_eq : ∀ {α : Type u_1} {β : Type u_2},
  boundedBox 0 1 = {y | y ∘ Sum.inl ∈ boundedBox 0 1 ∧ y ∘ Sum.inr ∈ boundedBox 0 1}
@mem_argminSet_t220A_iff : ∀ {n : ℕ} {L : Type} [inst : Fintype L] [Nonempty L] (x : Fin n → ℝ) (s : L → ℝ),
  s ∈ argminSet (t220A L n) (boundedBox 0 1) x ↔ (∀ (l : L), 0 ≤ s l) ∧ ∑ l, s l = 1
@mem_argminSet_t220B_iff : ∀ {n : ℕ} {L : Type} [inst : Fintype L] {K : L → Type} [inst_1 : (l : L) → Fintype (K l)]
  (R : (l : L) → K l → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (z : (l : L) × K l → ℝ),
  z ∈ argminSet (t220B R) (boundedBox 0 1) x ↔
    ∀ (lk : (l : L) × K l),
      z lk ∈ Set.Icc 0 1 ∧ ∀ v ∈ Set.Icc 0 1, -(eval x) (R lk.fst lk.snd) * z lk ≤ -(eval x) (R lk.fst lk.snd) * v
@mem_argminSet_t220Q_iff : ∀ {n : ℕ} {L : Type} [inst : Fintype L] {K : L → Type} [inst_1 : (l : L) → Fintype (K l)]
  (R : (l : L) → K l → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (y : L ⊕ (l : L) × K l → ℝ),
  y ∈ argminSet (t220Q R) (boundedBox 0 1) x ↔
    y ∘ Sum.inl ∈ argminSet (t220A L n) (boundedBox 0 1) x ∧ y ∘ Sum.inr ∈ argminSet (t220B R) (boundedBox 0 1) x
@mem_argminSet_t220Q_iff' : ∀ {n : ℕ} {L : Type} [inst : Fintype L] {K : L → Type} [inst_1 : (l : L) → Fintype (K l)]
  [Nonempty L] (R : (l : L) → K l → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (y : L ⊕ (l : L) × K l → ℝ),
  y ∈ argminSet (t220Q R) (boundedBox 0 1) x ↔
    ((∀ (l : L), 0 ≤ y (Sum.inl l)) ∧ ∑ l, y (Sum.inl l) = 1) ∧
      ∀ (lk : (l : L) × K l),
        y (Sum.inr lk) ∈ Set.Icc 0 1 ∧
          ∀ v ∈ Set.Icc 0 1, -(eval x) (R lk.fst lk.snd) * y (Sum.inr lk) ≤ -(eval x) (R lk.fst lk.snd) * v
@le_t220P_of_mem : ∀ {n : ℕ} {L : Type} [inst : Fintype L] {K : L → Type} [inst_1 : (l : L) → Fintype (K l)]
  (p : L → MvPolynomial (Fin n) ℝ) (R : (l : L) → K l → MvPolynomial (Fin n) ℝ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ),
  (∀ (l : L), (eval x) (p l) ≤ 0) →
    IsLeast {r | ∃ l, (∀ (k : K l), 0 ≤ (eval x) (R l k)) ∧ r = (eval x) (p l)} (f x) →
      ∀ {y : L ⊕ (l : L) × K l → ℝ}, y ∈ argminSet (t220Q R) (boundedBox 0 1) x → f x ≤ t220P p x y
@exists_mem_argminSet_t220P_eq : ∀ {n : ℕ} {L : Type} [inst : Fintype L] {K : L → Type}
  [inst_1 : (l : L) → Fintype (K l)] (p : L → MvPolynomial (Fin n) ℝ) (R : (l : L) → K l → MvPolynomial (Fin n) ℝ)
  (x : Fin n → ℝ) (l₀ : L),
  (∀ (k : K l₀), 0 ≤ (eval x) (R l₀ k)) → ∃ y ∈ argminSet (t220Q R) (boundedBox 0 1) x, t220P p x y = (eval x) (p l₀)
@isLeast_t220P_of_nonpos : ∀ {n : ℕ} {L : Type} [inst : Fintype L] {K : L → Type} [inst_1 : (l : L) → Fintype (K l)]
  (p : L → MvPolynomial (Fin n) ℝ) (R : (l : L) → K l → MvPolynomial (Fin n) ℝ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ),
  (∀ (l : L), (eval x) (p l) ≤ 0) →
    IsLeast {r | ∃ l, (∀ (k : K l), 0 ≤ (eval x) (R l k)) ∧ r = (eval x) (p l)} (f x) →
      IsLeast (t220P p x '' argminSet (t220Q R) (boundedBox 0 1) x) (f x)
@isPolyFun_t220Q : ∀ {n : ℕ} {L : Type} [inst : Fintype L] {K : L → Type} [inst_1 : (l : L) → Fintype (K l)]
  (R : (l : L) → K l → MvPolynomial (Fin n) ℝ), IsPolyFun (t220Q R)
@isPolyFun_t220P : ∀ {n : ℕ} {L : Type} [inst : Fintype L] {K : L → Type} [inst_1 : (l : L) → Fintype (K l)]
  (p : L → MvPolynomial (Fin n) ℝ), IsPolyFun (t220P p)
@convexLower_t220Q : ∀ {n : ℕ} {L : Type} [inst : Fintype L] {K : L → Type} [inst_1 : (l : L) → Fintype (K l)]
  (R : (l : L) → K l → MvPolynomial (Fin n) ℝ), ConvexLower (t220Q R)
@t220_core : ∀ {n : ℕ} {L : Type} [Fintype L] {K : L → Type} [(l : L) → Fintype (K l)] (p : L → MvPolynomial (Fin n) ℝ)
  (R : (l : L) → K l → MvPolynomial (Fin n) ℝ) (f : (Fin n → ℝ) → ℝ),
  (∀ (x : Fin n → ℝ), IsLeast {r | ∃ l, (∀ (k : K l), 0 ≤ (eval x) (R l k)) ∧ r = (eval x) (p l)} (f x)) →
    ∃ ι x P Q a b,
      IsPolyFun P ∧
        IsPolyFun Q ∧
          ConvexLower Q ∧
            (∀ (i : ι), a i ≤ b i) ∧ ∀ (x : Fin n → ℝ), IsLeast (P x '' argminSet Q (boundedBox a b) x) (f x)
@t220_core_valueFun : ∀ {n : ℕ} {L : Type} [Fintype L] {K : L → Type} [(l : L) → Fintype (K l)]
  (p : L → MvPolynomial (Fin n) ℝ) (R : (l : L) → K l → MvPolynomial (Fin n) ℝ) (f : (Fin n → ℝ) → ℝ),
  (∀ (x : Fin n → ℝ), IsLeast {r | ∃ l, (∀ (k : K l), 0 ≤ (eval x) (R l k)) ∧ r = (eval x) (p l)} (f x)) →
    ∃ ι x P Q a b,
      IsPolyFun P ∧
        IsPolyFun Q ∧
          ConvexLower Q ∧ (∀ (i : ι), a i ≤ b i) ∧ ∀ (x : Fin n → ℝ), valueFun P Q (boundedBox a b) x = ↑(f x)
@t220_D_closed : ∀ {n : ℕ} {f : (Fin n → ℝ) → ℝ},
  LowerSemicontinuous f → ∀ (q : MvPolynomial (Fin n) ℝ), IsClosed {x | f x ≤ (eval x) q}
@t220_D_eq_of_poly : ∀ {n N : ℕ} {S : Fin N → Set (Fin n → ℝ)} {p : Fin N → MvPolynomial (Fin n) ℝ}
  {f : (Fin n → ℝ) → ℝ},
  ⋃ i, S i = Set.univ →
    (∀ (i : Fin N), ∀ x ∈ S i, f x = (eval x) (p i)) →
      ∀ (q : MvPolynomial (Fin n) ℝ), {x | f x ≤ (eval x) q} = ⋃ k, S k ∩ {x | (eval x) (p k) ≤ (eval x) q}
@t220_D_eq : ∀ {n N : ℕ} {S : Fin N → Set (Fin n → ℝ)} {p : Fin N → MvPolynomial (Fin n) ℝ} {f : (Fin n → ℝ) → ℝ},
  ⋃ i, S i = Set.univ →
    (∀ (i : Fin N), ∀ x ∈ S i, f x = (eval x) (p i)) →
      ∀ (i : Fin N), {x | f x ≤ (eval x) (p i)} = ⋃ k, S k ∩ {x | (eval x) (p k) ≤ (eval x) (p i)}
@t220_D_sa : ∀ {n N : ℕ} {S : Fin N → Set (Fin n → ℝ)} {p : Fin N → MvPolynomial (Fin n) ℝ} {f : (Fin n → ℝ) → ℝ},
  (∀ (i : Fin N), IsSemialgebraic (S i)) →
    ⋃ i, S i = Set.univ →
      (∀ (i : Fin N), ∀ x ∈ S i, f x = (eval x) (p i)) → ∀ (i : Fin N), IsSemialgebraic {x | f x ≤ (eval x) (p i)}
@t220_isLeast_of_presentation : ∀ {n N : ℕ} {S : Fin N → Set (Fin n → ℝ)} {p : Fin N → MvPolynomial (Fin n) ℝ}
  {f : (Fin n → ℝ) → ℝ},
  ⋃ i, S i = Set.univ →
    (∀ (i : Fin N), ∀ x ∈ S i, f x = (eval x) (p i)) →
      ∀ (J : Fin N → ℕ) (K : (i : Fin N) → Fin (J i) → ℕ)
        (R : (i : Fin N) → (j : Fin (J i)) → Fin (K i j) → MvPolynomial (Fin n) ℝ),
        (∀ (i : Fin N), {x | f x ≤ (eval x) (p i)} = ⋃ j, ⋂ k, {x | 0 ≤ (eval x) (R i j k)}) →
          ∀ (x : Fin n → ℝ),
            IsLeast {r | ∃ l, (∀ (k : Fin (K l.fst l.snd)), 0 ≤ (eval x) (R l.fst l.snd k)) ∧ r = (eval x) (p l.fst)}
              (f x)
@t220_of_presentations : ∀ {n N : ℕ} {S : Fin N → Set (Fin n → ℝ)} {p : Fin N → MvPolynomial (Fin n) ℝ}
  {f : (Fin n → ℝ) → ℝ},
  ⋃ i, S i = Set.univ →
    (∀ (i : Fin N), ∀ x ∈ S i, f x = (eval x) (p i)) →
      ∀ (J : Fin N → ℕ) (K : (i : Fin N) → Fin (J i) → ℕ)
        (R : (i : Fin N) → (j : Fin (J i)) → Fin (K i j) → MvPolynomial (Fin n) ℝ),
        (∀ (i : Fin N), {x | f x ≤ (eval x) (p i)} = ⋃ j, ⋂ k, {x | 0 ≤ (eval x) (R i j k)}) →
          ∃ ι x P Q a b,
            IsPolyFun P ∧
              IsPolyFun Q ∧
                ConvexLower Q ∧ (∀ (i : ι), a i ≤ b i) ∧ ∀ (x : Fin n → ℝ), valueFun P Q (boundedBox a b) x = ↑(f x)
@t220_mem_C_bounded_of_presentations : ∀ {n N : ℕ} {S : Fin N → Set (Fin n → ℝ)} {p : Fin N → MvPolynomial (Fin n) ℝ}
  {f : (Fin n → ℝ) → ℝ},
  ⋃ i, S i = Set.univ →
    (∀ (i : Fin N), ∀ x ∈ S i, f x = (eval x) (p i)) →
      ∀ (J : Fin N → ℕ) (K : (i : Fin N) → Fin (J i) → ℕ)
        (R : (i : Fin N) → (j : Fin (J i)) → Fin (K i j) → MvPolynomial (Fin n) ℝ),
        (∀ (i : Fin N), {x | f x ≤ (eval x) (p i)} = ⋃ j, ⋂ k, {x | 0 ≤ (eval x) (R i j k)}) → coeFun f ∈ C_bounded n
@t220_eq13 : ∀ {n N : ℕ} {S : Fin N → Set (Fin n → ℝ)} {P : Fin N → (Fin n → ℝ) → ℝ} {f : (Fin n → ℝ) → ℝ},
  LowerSemicontinuous f →
    (∀ (i : Fin N), Continuous (P i)) →
      ⋃ i, S i = Set.univ →
        (∀ (i : Fin N), ∀ x ∈ S i, f x = P i x) →
          ∀ (x : Fin n → ℝ), IsLeast {r | ∃ i, x ∈ closure (S i) ∧ r = P i x} (f x)
@t220_eq13_nonempty : ∀ {n N : ℕ} {S : Fin N → Set (Fin n → ℝ)},
  ⋃ i, S i = Set.univ → ∀ (x : Fin n → ℝ), ∃ i, x ∈ closure (S i)
```
