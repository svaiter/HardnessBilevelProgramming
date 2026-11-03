# W2-a API (HardnessBilevel.Smooth.Whitney, HardnessBilevel.Smooth.Thm11), namespace Bilevel

All public declarations: #print axioms = [propext, Classical.choice, Quot.sound]. Use `open scoped ContDiff` for `∞`.

```
@exists_contDiff_zeroSet_eq : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {C : Set E}, IsClosed C → ∃ g, ContDiff ℝ ∞ g ∧ ∀ (p : E), g p = 0 ↔ p ∈ C
@thm11P : {n : ℕ} → (Fin n → ℝ) → (Fin 3 → ℝ) → ℝ
@thm11Q : {n : ℕ} → ((Fin n → ℝ) × ℝ → ℝ) → ((Fin n → ℝ) → ℝ) → (Fin n → ℝ) → (Fin 3 → ℝ) → ℝ
@contDiff_thm11P : ∀ {n : ℕ}, ContDiff ℝ ∞ (Function.uncurry thm11P)
@contDiff_thm11Q : ∀ {n : ℕ} {h : (Fin n → ℝ) × ℝ → ℝ} {g : (Fin n → ℝ) → ℝ},
  ContDiff ℝ ∞ h → ContDiff ℝ ∞ g → ContDiff ℝ ∞ (Function.uncurry (thm11Q h g))
@thm11Q_nonneg : ∀ {n : ℕ} (h : (Fin n → ℝ) × ℝ → ℝ) (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (y : Fin 3 → ℝ),
  0 ≤ thm11Q h g x y
@argminSet_thm11Q_of_ne_top : ∀ {n : ℕ} {f : (Fin n → ℝ) → EReal} {h : (Fin n → ℝ) × ℝ → ℝ} {g : (Fin n → ℝ) → ℝ},
  (∀ (p : (Fin n → ℝ) × ℝ), h p = 0 ↔ f p.1 ≤ ↑p.2) →
    (∀ (x : Fin n → ℝ), g x = 0 ↔ f x ≠ ⊤) →
      ∀ {x : Fin n → ℝ}, f x ≠ ⊤ → argminSet (thm11Q h g) Set.univ x = {y | f x ≤ ↑(y 0) ∧ y 1 * y 2 = 1}
@valueFun_thm11_of_ne_top : ∀ {n : ℕ} {f : (Fin n → ℝ) → EReal} {h : (Fin n → ℝ) × ℝ → ℝ} {g : (Fin n → ℝ) → ℝ},
  (∀ (p : (Fin n → ℝ) × ℝ), h p = 0 ↔ f p.1 ≤ ↑p.2) →
    (∀ (x : Fin n → ℝ), g x = 0 ↔ f x ≠ ⊤) → ∀ {x : Fin n → ℝ}, f x ≠ ⊤ → valueFun thm11P (thm11Q h g) Set.univ x = f x
@argminSet_thm11Q_of_eq_top : ∀ {n : ℕ} {f : (Fin n → ℝ) → EReal} {h : (Fin n → ℝ) × ℝ → ℝ} {g : (Fin n → ℝ) → ℝ},
  (∀ (x : Fin n → ℝ), g x = 0 ↔ f x ≠ ⊤) → ∀ {x : Fin n → ℝ}, f x = ⊤ → argminSet (thm11Q h g) Set.univ x = ∅
@valueFun_thm11_of_eq_top : ∀ {n : ℕ} {f : (Fin n → ℝ) → EReal} {h : (Fin n → ℝ) × ℝ → ℝ} {g : (Fin n → ℝ) → ℝ},
  (∀ (x : Fin n → ℝ), g x = 0 ↔ f x ≠ ⊤) → ∀ {x : Fin n → ℝ}, f x = ⊤ → valueFun thm11P (thm11Q h g) Set.univ x = ⊤
@exists_smooth_of_lowerSemicontinuous : ∀ {n : ℕ} (f : (Fin n → ℝ) → EReal),
  LowerSemicontinuous f →
    IsClosed {x | f x ≠ ⊤} →
      ∃ P Q, ContDiff ℝ ∞ (Function.uncurry P) ∧ ContDiff ℝ ∞ (Function.uncurry Q) ∧ valueFun P Q Set.univ = f
@exists_smooth_of_lowerSemicontinuous_proper : ∀ {n : ℕ} (f : (Fin n → ℝ) → EReal),
  LowerSemicontinuous f →
    IsClosed {x | f x ≠ ⊤} →
      (∀ (x : Fin n → ℝ), f x ≠ ⊥) →
        (∃ x, f x ≠ ⊤) →
          ∃ P Q, ContDiff ℝ ∞ (Function.uncurry P) ∧ ContDiff ℝ ∞ (Function.uncurry Q) ∧ valueFun P Q Set.univ = f
@exists_smooth_of_upperSemicontinuous : ∀ {n : ℕ} (f : (Fin n → ℝ) → EReal),
  UpperSemicontinuous f →
    IsClosed {x | f x ≠ ⊥} →
      ∃ P Q, ContDiff ℝ ∞ (Function.uncurry P) ∧ ContDiff ℝ ∞ (Function.uncurry Q) ∧ pvalueFun P Q Set.univ = f
```
