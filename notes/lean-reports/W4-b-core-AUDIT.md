# W4-b-core AUDIT — HardnessBilevel/Convex/Thm220Core.lean

## 1. Verdict: ACCEPT
- Build clean, no sorry/axiom/instances; all 28 public decls depend only on {propext, Classical.choice, Quot.sound}.
- `t220_core` is verbatim the blueprint statement; `t220_core_valueFun` gives `valueFun … = ↑(f x)`; the Steps 2-4 mathematics was re-derived and the Lean matches it; `ConvexLower Q` is on `univ`.
- The n=1 test instantiation elaborates and is proved (`#print axioms` clean). No required fixes.

## 2. Build / hygiene / axioms
- `lake build HardnessBilevel.Convex.Thm220Core` -> "Build completed successfully (18275 jobs)" (only the pre-existing `module` warnings from other files).
- grep for sorry|axiom|native_decide|unsafe|admit|Has(SemialgebraicProjections|FinitenessTheorem|GrowthBound)|maxHeartbeats|open Classical|instance: one hit, the header doc comment (line 31, mentions `HasFinitenessTheorem` in prose). No `instance`, no `set_option`, no `open Classical` (uses `classical` tactic). Deprecated names (`stdSimplex`, `Set.mem_setOf_eq`, ...) absent.
- Axioms: scratch `<SCRATCH>/lean/W4bcoreAx.lean` (`#print axioms` on all 28 public declarations incl. defs t220A/B/Q/P): 28/28 report `[propext, Classical.choice, Quot.sound]`.
- Check (5): no assumption class (`HasSemialgebraicProjections` etc.) is a binder or is used anywhere in the file (only `Framework.Classes` is imported for `C_bounded`/`coeFun`).

## 3. Faithfulness
| blueprint id | Lean name | verdict | note |
|---|---|---|---|
| t220.normalise | `t220_normalise`, `lowerSemicontinuous_sub_poly` | IDENTICAL / STRENGTHENED | `L : Type*` generalisation (declared); `g = C(1/4)+∑(p l)^2` as in blueprint |
| t220.core | `t220_core` | IDENTICAL | hypothesis `hf : ∀ x, IsLeast {r | ∃ l, (∀ k, 0 ≤ eval x (R l k)) ∧ r = eval x (p l)} (f x)`; conclusion `∃ (ι : Type) (_ : Fintype ι) P Q a b, IsPolyFun P ∧ IsPolyFun Q ∧ ConvexLower Q ∧ (∀ i, a i ≤ b i) ∧ ∀ x, IsLeast (P x '' argminSet Q (boundedBox a b) x) (f x)`; compared token by token; no lsc/sign/Nonempty hypotheses |
| t220.core (corollary) | `t220_core_valueFun` | IDENTICAL | `valueFun P Q (boundedBox a b) x = (f x : EReal)` via `valueFun_eq_of_isLeast`; `valueFun` is the literal `⨅ y ∈ argminSet…, ((P x y:ℝ):EReal)` (Framework/Basic.lean) |
| t220.D_closed | `t220_D_closed` | IDENTICAL | `LowerSemicontinuous f → IsClosed {x | f x ≤ eval x q}` for any polynomial q (more general than `p i`) |
| t220.D_sa | `t220_D_eq`, `t220_D_eq_of_poly`, `t220_D_sa` | IDENTICAL | `D_i = ⋃_k (S_k ∩ {p_k ≤ p_i})`; semialgebraic via `isSemialgebraic_iUnion`, `.inter`, `isSemialgebraic_eval_le` only (Boolean ops, no `Has…` binder, no projection) |
| t220.supset (c)-(e) | `t220_isLeast_of_presentation`, `t220_of_presentations`, `t220_mem_C_bounded_of_presentations` | IDENTICAL to spec (assumption-free part) | see below |
| t220.eq13 | `t220_eq13`, `t220_eq13_nonempty` | IDENTICAL | |
| t220.supset (A2 step), t220.subset, t220.main | — | NOT IN SCOPE | need A2/A1; assignment says so |

### Math re-derivation (D2)
- Variables y : L ⊕ Σ l,K l -> ℝ, box [0,1]^ι, `Q = (1-∑ s)^2 + ∑_{l,k} -R_lk(x) z_lk` (t220Q), `P = ∑_l p_l s_l ∏_k z_lk`.
- Argmin: `argminSet_sum_elim` splits the box and the separable objective into s-part and z-part. s-part (`mem_argminSet_t220A_iff`): min value 0 attained at a vertex (needs `Nonempty L`), so argmin = {s ≥ 0, ∑ s = 1} (the ≤1 bound follows from a single term ≤ sum). z-part via `argminSet_pi_sum`: each z_lk minimises `-R·v` over [0,1]. Correct, matches the weight-set description.
- Lower bound (`le_t220P_of_mem`), with p_l(x) ≤ 0: if x ∈ B_l then `0 ≤ ∏z ≤ 1` (prod_nonneg, prod_le_one₀) so `p_l ∏z ≥ p_l ≥ f(x)` (hf lower bound); else some R_lk(x)<0, so `z_lk = 0` (`eq_zero_of_isMin_Icc`), product 0 ≥ f(x) (f x ≤ 0 since f x = p_{l0}(x) ≤ 0). Then `P = ∑ s_l a_l ≥ ∑ s_l f(x) = f(x)`. Correct.
- Attainment (`exists_mem_argminSet_t220P_eq`): vertex at l0 with `z = 1_{R≥0}`; each coordinate is a 1-D minimiser (R≥0: z=1 minimises -R v; R<0: z=0 and -R v ≥ 0); `P = p_{l0}(x)·1·∏1`. Correct.
- Step 0: `p' = p - g`, `f' = f - g`, hf invariant; `P := P' + eval g` and `value_shift_attained` give the result; Q unchanged. Correct.
- Convexity (`convexLower_t220Q`): `ConvexOn ℝ Set.univ` for `(1-ℓ y)^2` (convexOn_sq_affine) plus linear sum: on `univ`, as required by the `ConvexLower` definition (`∀ x, ConvexOn ℝ univ …`).
- Polynomiality: built from `isPolyFun_const/y/of_upper_only` with add/sub/mul/pow/sum/prod closure; ι := L ⊕ Σ l, K l used directly (existential), no transport needed. `ι : Type` OK since L : Type, K l : Type.

### Presentation lemmas (D4)
Hypotheses of `t220_of_presentations` / `t220_mem_C_bounded_of_presentations`: `hcov : ⋃ i, S i = univ`, `hfS : ∀ i, ∀ x ∈ S i, f x = eval x (p i)`, `J K R`, `hB : ∀ i, {x | f x ≤ eval x (p i)} = ⋃ j, ⋂ k, {x | 0 ≤ eval x (R i j k)}`. Nothing else (no lsc, no semialgebraicity or disjointness of S i). Confirmed that these are unused: `t220_isLeast_of_presentation` only uses covering, `f = p_i0` on S_i0 and the presentation (blueprint step (d) says "needs no lsc"; lsc and semialgebraicity of S_i enter only for closedness/semialgebraicity of D_i to apply A2). Dropping them is a strengthening. `t220_mem_C_bounded_of_presentations` witnesses `C_bounded` with `IsBoundedBox (boundedBox a b) := ⟨a,b,hab,rfl⟩` and `ConvexLower Q`, `h = valueFun P Q S` by `funext`, matching `valueFunClass`/`coeFun` exactly. Remaining index shape `K : (i) → Fin (J i) → ℕ` is a mild generalisation of padded K (declared).

### Scratch instantiation (D test)
`<SCRATCH>/lean/W4bcoreInst.lean`: n=1, L=Fin 2, K _ = Fin 1, p 0 = X 0, p 1 = 0, R 0 0 = X 0, R 1 0 = -X 0; `t220_core` elaborates and the full theorem is proved with `#print axioms` clean. NOTE: the brief's suggested value `min (x 0) 0` is wrong for this data: the set is {x} for x>0, {0} for x<0, {0,0} at x=0, so f = `max (x 0) 0` (IsLeast with min is false for x>0). The test uses `max`; the hypothesis was proved by cases on sign of `x 0`. This is a mistake in the audit brief, not in the Lean.

## E. Interfaces
Names match blueprint ids (`t220_core`, `t220_D_closed`, `t220_D_sa`, `t220_eq13`, `t220_normalise`) and the writer's API file; signatures (L : Type, K : L -> Type, Fintype instances, explicit p R f hf) match the blueprint's.

## 4. Required fixes
None.

## 5. Optional improvements
- `t220_D_sa` etc. use `Fin N` for the pieces; fine for the Prop 2.4/A2 assembly, but the assembly unit will need `Fin N`-indexed `J`/`K` from A2 (writer's note: use `K := fun i _ => J' i`).
- Use of `Set.mem_ofPred_eq` in simps is Mathlib-version specific (fragile on bumps only).
- Helper defs t220A/B/Q/P and lemmas are public; consider `private`/namespacing if name clashes appear (low priority).
