# W2-b API (HardnessBilevel.Framework.Berge), namespace Bilevel

Imports: Framework.Basic, Framework.Value, Framework.Semicont. No [T2Space] anywhere.
All theorems: #print axioms = [propext, Classical.choice, Quot.sound]. Signatures from #check @Bilevel.<name> (printed with open Bilevel).

```
@continuous_section_of_uncurry : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X]
  [inst_1 : TopologicalSpace Y] {Q : X → Y → ℝ}, Continuous (Function.uncurry Q) → ∀ (x : X), Continuous (Q x)
@isClosed_argminSet_graph : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
  {Q : X → Y → ℝ} {S : Set Y}, Continuous (Function.uncurry Q) → IsClosed S → IsClosed {p | p.2 ∈ argminSet Q S p.1}
@argminSet_outer_semicont : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
  {Q : X → Y → ℝ} {S : Set Y},
  Continuous (Function.uncurry Q) →
    IsClosed S →
      ∀ {ι : Type u_5} {l : Filter ι} [l.NeBot] {xk : ι → X} {yk : ι → Y} {x : X} {y : Y},
        Tendsto xk l (𝓝 x) → Tendsto yk l (𝓝 y) → (∀ (k : ι), yk k ∈ argminSet Q S (xk k)) → y ∈ argminSet Q S x
@argminSet_nonempty_of_isCompact : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X]
  [inst_1 : TopologicalSpace Y] {Q : X → Y → ℝ} {S : Set Y},
  Continuous (Function.uncurry Q) → IsCompact S → S.Nonempty → ∀ (x : X), (argminSet Q S x).Nonempty
@argminSet_isCompact_of_continuous : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X]
  [inst_1 : TopologicalSpace Y] {Q : X → Y → ℝ} {S : Set Y},
  Continuous (Function.uncurry Q) → IsCompact S → ∀ (x : X), IsCompact (argminSet Q S x)
@exists_isMinOn_argminSet : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
  {P Q : X → Y → ℝ} {S : Set Y},
  Continuous (Function.uncurry P) →
    Continuous (Function.uncurry Q) →
      IsCompact S → S.Nonempty → ∀ (x : X), ∃ y₀ ∈ argminSet Q S x, IsMinOn (P x) (argminSet Q S x) y₀
@valueFun_attained : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
  {P Q : X → Y → ℝ} {S : Set Y},
  Continuous (Function.uncurry P) →
    Continuous (Function.uncurry Q) →
      IsCompact S → S.Nonempty → ∀ (x : X), ∃ y₀ ∈ argminSet Q S x, valueFun P Q S x = ↑(P x y₀)
@valueFun_ne_top_of_isCompact : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X]
  [inst_1 : TopologicalSpace Y] {P Q : X → Y → ℝ} {S : Set Y},
  Continuous (Function.uncurry P) →
    Continuous (Function.uncurry Q) → IsCompact S → S.Nonempty → ∀ (x : X), valueFun P Q S x ≠ ⊤
@valueFun_ne_bot_of_isCompact : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X]
  [inst_1 : TopologicalSpace Y] {P Q : X → Y → ℝ} {S : Set Y},
  Continuous (Function.uncurry P) → Continuous (Function.uncurry Q) → IsCompact S → ∀ (x : X), valueFun P Q S x ≠ ⊥
@isClosed_valueFun_sublevel : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
  {P Q : X → Y → ℝ} {S : Set Y},
  Continuous (Function.uncurry P) →
    Continuous (Function.uncurry Q) → IsCompact S → ∀ (r : ℝ), IsClosed {x | valueFun P Q S x ≤ ↑r}
@lowerSemicontinuous_valueFun : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X]
  [inst_1 : TopologicalSpace Y] {P Q : X → Y → ℝ} {S : Set Y},
  Continuous (Function.uncurry P) → Continuous (Function.uncurry Q) → IsCompact S → LowerSemicontinuous (valueFun P Q S)
@bddOn_compact_of_attained : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
  {P : X → Y → ℝ} {S : Set Y},
  Continuous (Function.uncurry P) →
    IsCompact S →
      ∀ {f : X → EReal},
        (∀ (x : X), ∃ y₀ ∈ S, f x = ↑(P x y₀)) → ∀ {K : Set X}, IsCompact K → ∃ M, ∀ x ∈ K, ↑(-M) ≤ f x ∧ f x ≤ ↑M
@valueFun_bddOn_compact : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
  {P Q : X → Y → ℝ} {S : Set Y},
  Continuous (Function.uncurry P) →
    Continuous (Function.uncurry Q) →
      IsCompact S →
        S.Nonempty → ∀ {K : Set X}, IsCompact K → ∃ M, ∀ x ∈ K, ↑(-M) ≤ valueFun P Q S x ∧ valueFun P Q S x ≤ ↑M
@cor29 : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {P Q : X → Y → ℝ}
  {S : Set Y},
  Continuous (Function.uncurry P) →
    Continuous (Function.uncurry Q) →
      IsCompact S →
        S.Nonempty →
          LowerSemicontinuous (valueFun P Q S) ∧
            (∀ (x : X), valueFun P Q S x ≠ ⊤ ∧ valueFun P Q S x ≠ ⊥) ∧
              ∀ (K : Set X), IsCompact K → ∃ M, ∀ x ∈ K, ↑(-M) ≤ valueFun P Q S x ∧ valueFun P Q S x ≤ ↑M
@continuous_uncurry_neg : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
  {P : X → Y → ℝ}, Continuous (Function.uncurry P) → Continuous (Function.uncurry fun x y => -P x y)
@upperSemicontinuous_pvalueFun : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X]
  [inst_1 : TopologicalSpace Y] {P Q : X → Y → ℝ} {S : Set Y},
  Continuous (Function.uncurry P) →
    Continuous (Function.uncurry Q) → IsCompact S → UpperSemicontinuous (pvalueFun P Q S)
@pvalueFun_attained : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
  {P Q : X → Y → ℝ} {S : Set Y},
  Continuous (Function.uncurry P) →
    Continuous (Function.uncurry Q) →
      IsCompact S → S.Nonempty → ∀ (x : X), ∃ y₀ ∈ argminSet Q S x, pvalueFun P Q S x = ↑(P x y₀)
@pvalueFun_ne_top_of_isCompact : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X]
  [inst_1 : TopologicalSpace Y] {P Q : X → Y → ℝ} {S : Set Y},
  Continuous (Function.uncurry P) → Continuous (Function.uncurry Q) → IsCompact S → ∀ (x : X), pvalueFun P Q S x ≠ ⊤
@pvalueFun_ne_bot_of_isCompact : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X]
  [inst_1 : TopologicalSpace Y] {P Q : X → Y → ℝ} {S : Set Y},
  Continuous (Function.uncurry P) →
    Continuous (Function.uncurry Q) → IsCompact S → S.Nonempty → ∀ (x : X), pvalueFun P Q S x ≠ ⊥
@pvalueFun_bddOn_compact : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
  {P Q : X → Y → ℝ} {S : Set Y},
  Continuous (Function.uncurry P) →
    Continuous (Function.uncurry Q) →
      IsCompact S →
        S.Nonempty → ∀ {K : Set X}, IsCompact K → ∃ M, ∀ x ∈ K, ↑(-M) ≤ pvalueFun P Q S x ∧ pvalueFun P Q S x ≤ ↑M
@cor29_pess : ∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
  {P Q : X → Y → ℝ} {S : Set Y},
  Continuous (Function.uncurry P) →
    Continuous (Function.uncurry Q) →
      IsCompact S →
        S.Nonempty →
          UpperSemicontinuous (pvalueFun P Q S) ∧
            (∀ (x : X), pvalueFun P Q S x ≠ ⊤ ∧ pvalueFun P Q S x ≠ ⊥) ∧
              ∀ (K : Set X), IsCompact K → ∃ M, ∀ x ∈ K, ↑(-M) ≤ pvalueFun P Q S x ∧ pvalueFun P Q S x ≤ ↑M
```
