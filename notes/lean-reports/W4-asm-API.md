# W4-asm API: Bounded/Thm215.lean, Convex/Thm220.lean, Convex/Thm221.lean, Pessimistic.lean (namespace Bilevel)

Imports: Thm215 <- Bounded.Thm215Core, Semialgebraic.Value. Thm220 <- Convex.Thm220Core, Semialgebraic.Value.
Thm221 <- Bounded.Thm215, Convex.Hull, Semialgebraic.Hull. Pessimistic <- Convex.Thm220, Convex.Thm221, Smooth.Thm11.
All set `set_option linter.concreteInstances false`. No instance of A1–A3. Every declaration below:
#print axioms = [propext, Classical.choice, Quot.sound]. (A1 = HasSemialgebraicProjections, A2 = HasFinitenessTheorem,
A3 = HasGrowthBound.)

## Bounded/Thm215.lean
```
mem_boundedBox_of_sum_sq_le {n} {r} {x : Fin n → ℝ} : ∑ i, x i ^ 2 ≤ r → x ∈ boundedBox (fun _ => -(|r|+1)) (fun _ => |r|+1)
bdd_sum_sq_of_bdd_compact {n} {f} : (∀ K, IsCompact K → ∃ B, ∀ x ∈ K, |f x| ≤ B) → ∀ r, ∃ B, ∀ x, ∑ i, x i ^ 2 ≤ r → |f x| ≤ B
thm215_supset [A1] [A2] [A3] {n} (f : (Fin n → ℝ) → ℝ) (hsa : IsSemialgebraicMap f) (hlsc : LowerSemicontinuous f)
    (hcb : ∀ K : Set (Fin n → ℝ), IsCompact K → ∃ B, ∀ x ∈ K, |f x| ≤ B) :
    ∃ (ι : Type) (_ : Fintype ι) (P Q : (Fin n → ℝ) → (ι → ℝ) → ℝ) (a b : ι → ℝ),
      IsPolyFun P ∧ IsPolyFun Q ∧ (∀ k, a k ≤ b k) ∧ ∀ x, valueFun P Q (boundedBox a b) x = ((f x : ℝ) : EReal)
thm215_mem_P_bounded [A1] [A2] [A3] {n} (f) (hsa) (hlsc) (hcb) : coeFun f ∈ P_bounded n
eq_coeFun_toReal_of_mem_CB {n} {h} : h ∈ CB n → h = coeFun (fun x => (h x).toReal)
exists_real_of_mem_SA_LSC_CB {n} {h} : h ∈ SA n ∩ LSC n ∩ CB n →
    ∃ f, h = coeFun f ∧ IsSemialgebraicMap f ∧ LowerSemicontinuous f ∧ ∀ K, IsCompact K → ∃ B, ∀ x ∈ K, |f x| ≤ B
thm215_eq [A1] [A2] [A3] {n} : P_bounded n = SA n ∩ LSC n ∩ CB n
```
## Convex/Thm220.lean
```
thm220_supset [A2] {n} (f : (Fin n → ℝ) → ℝ) (hPP : f ∈ PP n) (hlsc : LowerSemicontinuous f) : coeFun f ∈ C_bounded n
thm220_main [A1] [A2] {n} : coeFun '' (PP n ∩ {f | LowerSemicontinuous f}) ⊆ C_bounded n ∧ C_bounded n ⊆ SA n ∩ LSC n ∩ CB n
```
## Convex/Thm221.lean
```
Msp_eq_eval {n} {ι : Type} [Fintype ι] (S : Finset (Fin n ⊕ ι →₀ ℕ)) (y) :
    Msp S y = fun d : S => eval y (∏ j, (X j : MvPolynomial ι ℝ) ^ (d.1 (Sum.inr j)))
thm221_hull_sa [A1] {n} {ι : Type} [Fintype ι] (S) {Y : Set (ι → ℝ)} : IsSemialgebraic Y →
    IsSemialgebraic (convexHull ℝ (Msp S '' Y))
thm221_compact_sa_incl [A1] {n} {ι : Type} [Fintype ι] {P Q} : IsPolyFun P → IsPolyFun Q → ∀ {Y}, IsCompact Y →
    Y.Nonempty → IsSemialgebraic Y → valueFun P Q Y ∈ C_cc n
thm221_compact_sa_incl_pess [A1] (same hypotheses) : pvalueFun P Q Y ∈ Cp_cc n
thm221_supset [A1] [A2] [A3] {n} : SA n ∩ LSC n ∩ CB n ⊆ C_cc n
thm221_eq [A1] [A2] [A3] {n} : C_cc n = SA n ∩ LSC n ∩ CB n
```
## Pessimistic.lean
```
neg_mem_PP {n} {f} : f ∈ PP n → (fun x => -f x) ∈ PP n
neg_mem_PP_iff {n} {f} : (fun x => -f x) ∈ PP n ↔ f ∈ PP n
coeFun_neg {n} (f) : coeFun (fun x => -f x) = fun x => -coeFun f x
neg_mem_SA_LSC_CB {n} {h} : h ∈ SA n ∩ USC n ∩ CB n → (fun x => -h x) ∈ SA n ∩ LSC n ∩ CB n
pess_thm11 {n} (f : (Fin n → ℝ) → EReal) : UpperSemicontinuous f → IsClosed {x | f x ≠ ⊥} →
    ∃ P Q : (Fin n → ℝ) → (Fin 3 → ℝ) → ℝ, ContDiff ℝ ∞ (uncurry P) ∧ ContDiff ℝ ∞ (uncurry Q) ∧ pvalueFun P Q univ = f
pess_cor29 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {P Q} {S} : Continuous (uncurry P) →
    Continuous (uncurry Q) → IsCompact S → S.Nonempty → (same conclusion as cor29_pess)
pess_thm212 [A1] {n} : Pp_unbound n = SA n
pess_thm218 [A1] {n} : PPe n ⊆ Cp_unbound n ∧ Cp_unbound n ⊆ SA n
pess_thm215 [A1] [A2] [A3] {n} : Pp_bounded n = SA n ∩ USC n ∩ CB n
pess_thm220 [A1] [A2] {n} : coeFun '' (PP n ∩ {f | UpperSemicontinuous f}) ⊆ Cp_bounded n ∧ Cp_bounded n ⊆ SA n ∩ USC n ∩ CB n
pess_thm221 [A1] [A2] [A3] {n} : Cp_cc n = SA n ∩ USC n ∩ CB n
```
