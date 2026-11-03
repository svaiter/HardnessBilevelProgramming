# W3-a AUDIT (Semialgebraic/Poly.lean, Semialgebraic/Ext.lean)

## 1. Verdict: ACCEPT
- Both modules build; no sorry/axiom/native_decide/unsafe/maxHeartbeats/open Classical/A1-A3 instance; all 48 public declarations have axioms within {propext, Classical.choice, Quot.sound}.
- `preimage_poly` has no finiteness hypothesis; `IsExtSemialgebraic` has exactly top/bot/graph (graph in `ι ⊕ Unit → ℝ`); `.neg` has no class binder; poly_bound/growth_shape statements match the blueprint.
- Only deviation: `[Finite _]` on box/singleton/ball/poly_graph lemmas (justified, and a strengthening of the brief's `[Fintype]`).

## 2. Build / hygiene / axioms
- `lake build HardnessBilevel.Semialgebraic.Poly HardnessBilevel.Semialgebraic.Ext` -> "Build completed successfully (18249 jobs)" (only the module-system lint warning from Framework/Box).
- grep for `sorry|axiom|native_decide|unsafe|admit|maxHeartbeats|open Classical|instance.*Has(...)` over both files: no hits.
- Scratch file `<SCRATCH>/lean/W3a.lean` (`#print axioms` on every theorem/def of both files, 48 entries): every line `[propext, Classical.choice, Quot.sound]`; output in `<SCRATCH>/lean/W3a.out`, `exit 0`.
- Scratch examples compile without error (same file):
  * `IsSemialgebraic {z : Fin 1 ⊕ Unit → ℝ | z (Sum.inr ()) = z (Sum.inl 0) ^ 2}` via `isSemialgebraicMap_eval (X 0 ^ 2)` + `of_eq`;
  * `IsExtSemialgebraic (fun x : Fin 1 → ℝ => ((x 0 ^ 2 : ℝ) : EReal))` via `rw [isExtSemialgebraic_coe_iff]` and the same map lemma.
  * `#check @IsExtSemialgebraic.neg` : `∀ {ι} {h}, IsExtSemialgebraic h → IsExtSemialgebraic fun x => -h x` (no instance binders).

## 3. Faithfulness
| blueprint id | Lean name | verdict | note |
|---|---|---|---|
| sa.preimage_poly (L4) | `IsSemialgebraic.preimage_poly` | IDENTICAL | `{ι κ : Type*} (F : κ → MvPolynomial ι ℝ) {S : Set (κ → ℝ)}`, no Finite/Fintype on either index. Extra pointwise form `preimage_of_poly` (strengthening/convenience). |
| sa.reindex | `IsSemialgebraic.reindex` | IDENTICAL | any `e : ι → κ`, `(fun x => x ∘ e) ⁻¹' S`; plus Equiv image forms and iff. |
| sa.cylinder | `isSemialgebraic_cylinder_inl/inr/cylinder` | IDENTICAL | no finiteness. |
| sa.poly_graph | `isSemialgebraic_poly_graph [Finite κ]`, `isSemialgebraicMap_eval` | IDENTICAL (see note) | `Finite κ` is needed (an infinite intersection of {z_j = G_j} is not in the generated algebra, which depends on finitely many coordinates) and the blueprint's use is `Fin`/finite. `isSemialgebraicMap_eval` (the used form) needs nothing. |
| sa.box | `isSemialgebraic_boxSet [Finite ι] (lo hi : ι → EReal)`, `IsBoundedBox.isSemialgebraic`, also `IsBox`/`IsUnboundedBox`/`boundedBox` | STRENGTHENED | EReal endpoints, `Finite` weaker than `Fintype`; finiteness necessary for infinite ι. |
| sa.singleton/finite_set | `isSemialgebraic_singleton`, `isSemialgebraic_of_finite` | IDENTICAL | renamed from `Set.Finite.isSemialgebraic` (declared, namespace reason). |
| sa.sup_ball, sa.euclid_ball | `isSemialgebraic_sup_ball`, `_closedBall`, `isSemialgebraic_euclid_ball (ρ)` (`∑ x i^2 ≤ ρ`), `_lt` | IDENTICAL | |
| sa.poly_bound (L17) | `exists_abs_eval_le` (alias `poly_bound`) | IDENTICAL | `∀ p, ∃ c M, ∀ x, |eval x p| ≤ c * (1 + ∑ i, x i ^ 2) ^ M`, `[Fintype ι]` (needed for the sum). Extra `0 ≤ c` variant. |
| sa.growth_shape | `growth_shape_iff` (alias `growth_shape`) + two directions | STRENGTHENED | stated as `Iff` between `∃ c M, |f x| ≤ c(1+∑x²)^M` and `∃ B M, |f x| ≤ B + (1+∑x²)^M`; blueprint only asks mul->add; add->mul is a bonus. No extra hypotheses beyond `Fintype ι`. |
| Def 2.2 | `structure IsExtSemialgebraic` | IDENTICAL | fields exactly `top`, `bot`, `graph`; graph set `{z : ι ⊕ Unit → ℝ | h (z ∘ inl) = ↑(z (inr ()))}`; `Prop`-structure over `{ι : Type*}`. |
| sa.ext_dom | `IsExtSemialgebraic.dom` | IDENTICAL | |
| sa.ext_coe | `isExtSemialgebraic_coe_iff`, `IsSemialgebraicMap.isExtSemialgebraic` | IDENTICAL | `↔ IsSemialgebraicMap f`. |
| sa.ext_neg | `IsExtSemialgebraic.neg`, `isExtSemialgebraic_neg_iff` | IDENTICAL | no TS/A1 binder; proof via polynomial preimage of graph. |
| sa.ext_graph_equiv (optional) | `extGraph`, `isExtSemialgebraic_iff_extGraph` | IDENTICAL | encoding as in blueprint. |
| (extra) | `IsExtSemialgebraic.const` | extra | constant EReal functions. |

## 4. Required fixes
None.

## 5. Optional improvements
1. `IsSemialgebraicMap.isExtSemialgebraic` and `isExtSemialgebraic_neg_iff` lack docstrings.
2. `poly_bound`/`growth_shape` aliases duplicate the primary names; fine, but later waves should pick one name (`exists_abs_eval_le`, `growth_shape_add_to_mul` is the form A3 consumers need).
3. Header says "Deviations: none" in Ext.lean (true); Poly.lean header correctly declares the `Finite`/`isSemialgebraic_of_finite` deviations.
4. Consumers needing the A3 conversion should use `growth_shape_mul_to_add`; interface matches blueprint §4.B.5.
