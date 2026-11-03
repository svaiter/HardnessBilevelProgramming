# W1-cd API (HardnessBilevel.Framework.Box, HardnessBilevel.Framework.Semicont), namespace Bilevel

All theorems: #print axioms = [propext, Classical.choice, Quot.sound].

```
@boxSet : {ι : Type u_1} → (ι → EReal) → (ι → EReal) → Set (ι → ℝ)
@boundedBox : {ι : Type u_1} → (ι → ℝ) → (ι → ℝ) → Set (ι → ℝ)
@IsBoundedBox : {ι : Type u_1} → Set (ι → ℝ) → Prop
@IsUnboundedBox : {ι : Type u_1} → Set (ι → ℝ) → Prop
@IsBox : {ι : Type u_1} → Set (ι → ℝ) → Prop
@mem_boxSet : ∀ {ι : Type u_1} {lo hi : ι → EReal} {y : ι → ℝ},
  y ∈ boxSet lo hi ↔ ∀ (i : ι), lo i ≤ ↑(y i) ∧ ↑(y i) ≤ hi i
@mem_boundedBox : ∀ {ι : Type u_1} {lo hi y : ι → ℝ}, y ∈ boundedBox lo hi ↔ ∀ (i : ι), lo i ≤ y i ∧ y i ≤ hi i
@boxSet_pi : ∀ {ι : Type u_1} (lo hi : ι → EReal),
  boxSet lo hi = Set.univ.pi fun i => (fun t => ↑t) ⁻¹' Set.Icc (lo i) (hi i)
@boundedBox_eq_boxSet : ∀ {ι : Type u_1} (lo hi : ι → ℝ), boundedBox lo hi = boxSet (fun i => ↑(lo i)) fun i => ↑(hi i)
@IsBoundedBox.isBox : ∀ {ι : Type u_1} {S : Set (ι → ℝ)}, IsBoundedBox S → IsBox S
@isCompact_boundedBox : ∀ {ι : Type u_1} [Finite ι] (lo hi : ι → ℝ), IsCompact (boundedBox lo hi)
@IsBoundedBox.isCompact : ∀ {ι : Type u_1} [Finite ι] {S : Set (ι → ℝ)}, IsBoundedBox S → IsCompact S
@IsBoundedBox.nonempty : ∀ {ι : Type u_1} {S : Set (ι → ℝ)}, IsBoundedBox S → S.Nonempty
@convex_boundedBox : ∀ {ι : Type u_1} (lo hi : ι → ℝ), Convex ℝ (boundedBox lo hi)
@IsBoundedBox.convex : ∀ {ι : Type u_1} {S : Set (ι → ℝ)}, IsBoundedBox S → Convex ℝ S
@isClosed_boxSet : ∀ {ι : Type u_1} (lo hi : ι → EReal), IsClosed (boxSet lo hi)
@IsBox.isClosed : ∀ {ι : Type u_1} {S : Set (ι → ℝ)}, IsBox S → IsClosed S
@isClosed_boundedBox : ∀ {ι : Type u_1} (lo hi : ι → ℝ), IsClosed (boundedBox lo hi)
@IsBoundedBox.isClosed : ∀ {ι : Type u_1} {S : Set (ι → ℝ)}, IsBoundedBox S → IsClosed S
@convex_boxSet : ∀ {ι : Type u_1} (lo hi : ι → EReal), Convex ℝ (boxSet lo hi)
@IsBox.convex : ∀ {ι : Type u_1} {S : Set (ι → ℝ)}, IsBox S → Convex ℝ S
@boxSet_bot_top : ∀ {ι : Type u_1}, (boxSet (fun x => ⊥) fun x => ⊤) = Set.univ
@isBox_univ : ∀ {ι : Type u_1}, IsBox Set.univ
@isUnboundedBox_univ : ∀ {ι : Type u_1} [Nonempty ι], IsUnboundedBox Set.univ
@exists_real_mem_Icc : ∀ {a b : EReal}, a ≠ ⊤ → b ≠ ⊥ → a ≤ b → ∃ t, a ≤ ↑t ∧ ↑t ≤ b
@boxSet_nonempty : ∀ {ι : Type u_1} {lo hi : ι → EReal},
  (∀ (i : ι), lo i ≠ ⊤ ∧ hi i ≠ ⊥ ∧ lo i ≤ hi i) → (boxSet lo hi).Nonempty
@IsUnboundedBox.nonempty : ∀ {ι : Type u_1} {S : Set (ι → ℝ)}, IsUnboundedBox S → S.Nonempty
@IsUnboundedBox.isBox : ∀ {ι : Type u_1} {S : Set (ι → ℝ)}, IsUnboundedBox S → IsBox S
@IsUnboundedBox.isClosed : ∀ {ι : Type u_1} {S : Set (ι → ℝ)}, IsUnboundedBox S → IsClosed S
@IsUnboundedBox.convex : ∀ {ι : Type u_1} {S : Set (ι → ℝ)}, IsUnboundedBox S → Convex ℝ S
@isUnboundedBox_sum_univ_Ici : ∀ {α : Type u_1} {β : Type u_2} [Nonempty α],
  IsUnboundedBox (Set.univ.pi (Sum.elim (fun x => Set.univ) fun x => Set.Ici 0))
@lowerSemicontinuous_coe_iff : ∀ {X : Type u_1} [inst : TopologicalSpace X] (f : X → ℝ),
  (LowerSemicontinuous fun x => ↑(f x)) ↔ LowerSemicontinuous f
@upperSemicontinuous_coe_iff : ∀ {X : Type u_1} [inst : TopologicalSpace X] (f : X → ℝ),
  (UpperSemicontinuous fun x => ↑(f x)) ↔ UpperSemicontinuous f
@upperSemicontinuous_iff_lowerSemicontinuous_neg : ∀ {X : Type u_1} [inst : TopologicalSpace X] (h : X → EReal),
  UpperSemicontinuous h ↔ LowerSemicontinuous fun x => -h x
@lowerSemicontinuous_iff_upperSemicontinuous_neg : ∀ {X : Type u_1} [inst : TopologicalSpace X] (h : X → EReal),
  LowerSemicontinuous h ↔ UpperSemicontinuous fun x => -h x
@lowerSemicontinuous_neg_iff_real : ∀ {X : Type u_1} [inst : TopologicalSpace X] (f : X → ℝ),
  (LowerSemicontinuous fun x => -f x) ↔ UpperSemicontinuous f
@upperSemicontinuous_neg_iff_real : ∀ {X : Type u_1} [inst : TopologicalSpace X] (f : X → ℝ),
  (UpperSemicontinuous fun x => -f x) ↔ LowerSemicontinuous f
@isClosed_realEpigraph : ∀ {X : Type u_1} [inst : TopologicalSpace X] {f : X → EReal},
  LowerSemicontinuous f → IsClosed {p | f p.1 ≤ ↑p.2}
@isClosed_realHypograph : ∀ {X : Type u_1} [inst : TopologicalSpace X] {f : X → EReal},
  UpperSemicontinuous f → IsClosed {p | ↑p.2 ≤ f p.1}
```
