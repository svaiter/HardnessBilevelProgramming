# Implementation plan: formalizing `blueprint.md` in Lean 4 + Mathlib

This is the execution plan for turning `blueprint.md` into a compiling Lean library `HardnessBilevel`.
It fixes the toolchain, the order of work, who does what, and the acceptance criteria for every unit.
Lemma ids (`fw.*`, `sa.*`, `gad.*`, `t11.*`, `berge.*`, `t212.*`, `t215.*`, `t219.*`, `t218.*`, `t220.*`,
`t221.*`, `s3.*`, `pess.*`, assumptions A1–A3) refer to `blueprint.md` §4.

## 0. Toolchain (pinned, matches the blueprint's name checks)

| item | value |
|---|---|
| Lean | `leanprover/lean4:v4.36.0-rc2` (`lean-toolchain`) |
| Mathlib | commit `1b1ccf4b088b32fa3f23f2de1127433254a81e1e` (`lakefile.toml`, `rev`; moved on 2026-11-09 from `1df8067a` to the pin of the `Semialgebraic` companion and of TauCeti), cache via `lake exe cache get` |
| Semialgebraic | `svaiter/Semialgebraic`, commit pinned in `lakefile.toml`; it pins TauCeti `2c9b12be` |
| library | `HardnessBilevel` (root module `HardnessBilevel.lean` re-exports every file) |
| options | `autoImplicit = false` project-wide |

Smoke test before any code: a file importing `Mathlib` builds with `lake build` in under a minute (cache hit).

## 1. Ground rules for every Lean file

1. **Header**: a doc comment naming the blueprint section it implements and the lemma ids it provides.
2. **Namespace** `Bilevel`; declaration names follow the blueprint (`argminSet`, `valueFun`, `pvalueFun`, `optVal`,
   `IsPolyFun`, `boxSet`, `IsBoundedBox`, `IsUnboundedBox`, `ConvexLower`, `IsSemialgebraic`, `IsExtSemialgebraic`,
   `HasSemialgebraicProjections`, `HasFinitenessTheorem`, `HasGrowthBound`, …). A lemma id `fw.value_eq_of_isLeast`
   becomes `Bilevel.valueFun_eq_of_isLeast` (section prefixes are dropped; the id is cited in the docstring).
3. **No `sorry`, no `axiom`, no `native_decide`, no `decide` on large goals, no `unsafe`.** `#print axioms` of every
   top-level theorem must show only `propext`, `Classical.choice`, `Quot.sound`.
4. **Assumptions A1–A3** live only in `HardnessBilevel/Assumptions/Classes.lean` as `class … : Prop`. **No unproved
   `instance` of them anywhere** (amended 2026-11-09; the original rule was "no instance"): the core library
   `HardnessBilevel` declares no instance at all and its consumers take `[HasSemialgebraicProjections]` etc. as explicit
   binders; the only instances are the three **proved** ones of `HardnessBilevelUnconditional/Instances.lean`, obtained
   from the `Semialgebraic` companion library (TauCeti-based), in a separate `lean_lib` that the core library does not
   import. A sorried or axiomatized instance is forbidden everywhere. `scripts/check.sh` enforces all of this and prints
   the axioms of the instances and of the assumption-free corollaries (§6).
5. **Statements are the blueprint's statements.** A theorem may be strengthened (weaker hypotheses, stronger
   conclusion) but never weakened or re-typed; definitions are the blueprint's (e.g. `valueFun` is the `⨅` in `EReal`,
   boxes have `EReal` endpoints). Any deviation is written in the file header with a reason and reported to the auditor.
6. **Deprecations**: never use `stdSimplex`, `isCompact_stdSimplex`, `Set.mem_setOf_eq`, `IsMinOn.on_subset`,
   `ContDiff ℝ ⊤` (analytic); smoothness is `ContDiff ℝ ∞` with `open scoped ContDiff`.
7. **Build discipline for parallel agents**: an agent type-checks its own files with
   `lake env lean HardnessBilevel/Path/File.lean` and builds its own modules with
   `lake build HardnessBilevel.Path.File`. Agents never run a bare `lake build`, never touch files outside their
   assignment, never edit `lakefile.toml`/`lean-toolchain`, and never import a file being written in the same wave by
   another agent. The orchestrator runs the full `lake build` between waves.
8. **Commits**: the orchestrator commits at the end of every wave after the full build and the audit pass.

## 2. Roles

* **Writers: Opus subagents.** One per unit below. Input: the blueprint section(s), this plan, the Mathlib checkout,
  the compiled project. Output: compiling files with no `sorry`, plus a short report (what was proved, every deviation
  from the blueprint, Mathlib names that had changed, anything left out).
* **Auditors: Sonnet subagents.** One per unit, after the wave's full build. They check: (a) the file builds in the
  project; (b) `#print axioms` of every public theorem; (c) no `sorry`/`axiom`/`native_decide`/`instance` of A1–A3;
  (d) **faithfulness**: every theorem/definition statement is compared against the blueprint's mathematical statement
  (hypotheses not silently added, conclusions not weakened, definitions not degenerate, classes not narrowed);
  (e) nothing is proved "by changing the definition". Output: an audit report with a verdict per declaration and a
  list of required fixes. Fixes go back to the original writer (same agent, by message) or to a fresh writer with the
  audit attached; the unit is re-audited until clean.
* **Orchestrator (this session)**: sequencing, full builds, merging the root module, commits, cross-unit interface
  conflicts (resolved by editing the earlier file, never by duplicating definitions).

## 3. Waves (dependency order; units within a wave run in parallel)

Effort tags are the blueprint's. "Imports" are project files; everything imports Mathlib.

### Wave 0 — setup (orchestrator)
`lakefile.toml`, `lean-toolchain`, cache, smoke test, this plan. Acceptance: `lake build` green on the empty library.

### Wave 1 — framework (blueprint §4.A; no assumptions)
| unit | files | provides | imports |
|---|---|---|---|
| W1-a | `Framework/Basic.lean`, `Framework/Value.lean`, `Framework/Separable.lean` | `argminSet`, `valueFun`, `pvalueFun`, `optVal`; F1–F8 (`mem_argmin_iff`, `argmin_subset`, `argmin_eq_empty_iff`, `argmin_eq_zeroSet`, `mem_argmin_of_nonneg_zero`, `argmin_prod_add`, `argmin_mul_pos`, `argmin_add_left`, `comp_equiv` ×3, `argmin_isClosed/isCompact`, `argmin_pi_sum`); V1–V5, V8, F0 (`value_eq_top_iff`, `value_eq_of_isMinOn`, `value_eq_of_isLeast`, `value_eq_coe_iff`, `value_eq_bot_iff`, `value_eq_of_const`, `value_unique`, `pvalue_eq_neg_value_neg`, `pvalue_class_neg` later), `mem_argmin_univ`, `argmin_empty_of_pos_inf`, `value_eq_bot_of_unbounded`, pessimistic twins | — |
| W1-b | `Framework/Poly.lean` | `IsPolyFun`, `polyFun`, closure lemmas (`isPolyFun_const/x/y/add/neg/sub/mul/pow/sum/prod`, substitution via `bind₁`, `rename`), `continuous_polyFun` | — |
| W1-c | `Framework/Box.lean` | `boxSet`, `boundedBox`, `IsBoundedBox`, `IsUnboundedBox`, `IsBox`, `box_lemmas` (compact, nonempty, convex, closed, `boxSet_bot_top`) | — |
| W1-d | `Framework/Semicont.lean` | `lsc_real_bridge`, `usc_neg`/`lsc_neg`, EReal negation helpers | — |
| W1-e | `Framework/Classes.lean` (after W1-a..d; written by the orchestrator or W1-a's agent) | `ConvexLower`, `valueFunClass`, `P_unbound`, `P_bounded`, `C_unbound`, `C_bounded`, `C_cc` (needs `IsSemialgebraic`: placed in Wave 3 instead — see W3-c), `LSC`, `USC`, `CB`, `class_incl`, `CB_real` | W1-a..d |

Acceptance: full build; audit of each unit; `#print axioms` clean.

### Wave 2 — assumption-free theorems and the semialgebraic base (parallel, 7 units)
| unit | files | provides | imports |
|---|---|---|---|
| W2-a | `Smooth/Whitney.lean`, `Smooth/Thm11.lean` | `t11.whitney`, `isClosed_realEpigraph`, `smooth`, `nonneg`, `case_finite`, `case_top`, `main` (`exists_smooth_of_lowerSemicontinuous`), `main_pess` | Basic, Value, Semicont |
| W2-b | `Framework/Berge.lean` | `berge.isClosed_graph`, `argmin_nonempty`, `argmin_isCompact`, `exists_isMinOn`, `value_attained`, `isClosed_sublevel`, `lsc`, `bdd_on_compact`, `cor29`, `pess` (`rem210` moves to Wave 3 with the classes) | Basic, Value, Separable, Semicont |
| W2-c | `Gadgets/Scalar.lean`, `Gadgets/ZeroLocus.lean`, `Unbounded/Thm212.lean` | `gad.G1`, `gad.G5`, `ZeroGadget` (+`mem_of_eval_eq_zero`, `mem_iff`), `gad.G2`, `gad.G3`; `t212.eval`, `a_lemma`, `case_real/top/bot`, `main` stated with `ZeroGadget (Γ h) τ_Γ` and `ZeroGadget {h = ⊥} τ₋` as hypotheses (the `IsSemialgebraic` version `t212.thm212_sup` and `gad.G4` come in Wave 3), `real_valued` | Basic, Value, Separable, Poly |
| W2-d | `Semialgebraic/Basic.lean` | `IsSemialgebraic`, `IsBasicSA`, `graphSet`, `IsSemialgebraicMap`; `sa.gen`, `sa.bool`, `sa.sign_sets`, `sa.sign_normal_form`, `sa.cell_basic`, `sa.finite_union_basic`, `sa.finite_union_basic_uniform`, `sa.disjoint_basic` | — |
| W2-e | `Hardness/SSI.lean`, `Hardness/Construction.lean`, `Hardness/Analysis.lean`, `Hardness/Reduction.lean` | `SSI`, `SSI.Yes`, polynomials over ℤ, `s3.L0`–`L8`, `lemma33`, `lemma33_no`, `BilevelInstance`, `reduce`, `reduce_correct`, `degree`, `integer_coeff` | Basic, Value, Separable, Poly |
| W2-f | `Convex/Toolkit.lean`, `Convex/Lemma219.lean`, `Convex/Thm218.lean` | `argmin_scalar`, `convex_toolkit` (`convexOn_sq_affine`, `convexOn_finset_sum`), `value_shift_attained`; `t219.main`; `t218.sum_indicator` (stated for a family of finite unions of basic sets given as data; `PP_sub_Cunbound`/`main` in Wave 3) | Basic, Value, Separable, Poly, Box |
| W2-g | `Gadgets/Box.lean` | `gad.G6`, `gad.G7` | Poly |

Acceptance: full build; audits; `#print axioms` clean on all of it (nothing here may mention A1–A3).

### Wave 3 — semialgebraic layer under A1, classes, Prop 2.6 (blueprint §4.B, §4.A classes)
| unit | files | provides | imports |
|---|---|---|---|
| W3-a | `Semialgebraic/Poly.lean`, `Semialgebraic/Ext.lean` | `sa.preimage_poly`, `sa.reindex`, `sa.cylinder`, `sa.poly_graph`, `sa.box`, `sa.singleton`, `sa.sup_ball`, `sa.euclid_ball`, `sa.poly_bound`, `sa.growth_shape`; `IsExtSemialgebraic`, `sa.ext_dom`, `sa.ext_coe`, `sa.ext_neg` | Sa/Basic, Poly, Box |
| W3-b | `Assumptions/Classes.lean`, `Semialgebraic/Projection.lean` | A1, A2, A3 classes (exact statements of blueprint §2.5); `sa.exists_sumElim`, `sa.forall_sumElim`, quantifier calculus helpers, optional `sa.closure` | Sa/Basic, Sa/Poly |
| W3-c | `Framework/Classes.lean` | `ConvexLower`, `valueFunClass`, the five classes and pessimistic twins, `LSC`, `USC`, `CB`, `SA`, `PP`, `class_incl`, `CB_real`, `pvalue_class_neg`, `berge.rem210` | W1, Berge, Sa/Ext |
| W3-d (after a–c) | `Semialgebraic/Value.lean`, `Semialgebraic/Hull.lean`, `Gadgets/Semialgebraic.lean`, `Unbounded/Thm212SA.lean`, `Convex/Thm218SA.lean` | `sa.value_semialgebraic` (Prop 2.6 for any semialgebraic `Y`, optimistic and pessimistic), `sa.class_sub_SA`, `sa.hull_semialgebraic`; `gad.G4`; `t212.thm212_sup`, `t212.eq_SA`; `t218.PP_sub_Cunbound`, `t218.Cunbound_sub_SA`, `t218.main` | W3-a..c, W2-c, W2-f |

Acceptance: full build; audits; `#print axioms` on A1-free results clean; A1-dependent results list no axiom beyond the
standard three (the class is a hypothesis, not an axiom).

### Wave 4 — the A2/A3 theorems (blueprint §4.F, §4.G.4, §4.H)
| unit | files | provides | imports |
|---|---|---|---|
| W4-a | `Bounded/Thm215.lean` | `t215.core`, `epi_closed`, `epi_sa`, `supset`, `subset`, `eq` | Gadgets/Box, Sa/Value, Berge, Classes |
| W4-b | `Convex/Thm220.lean` | `t220.normalise`, `D_closed`, `D_sa`, `core`, `supset`, `subset`, `main` (+ optional `eq13`) | Convex/Toolkit, Sa/Value, Classes |
| W4-c | `Convex/Linearize.lean`, `Convex/Hull.lean` | `t221.splitting`, `linearize` (both halves), `caratheodory_union`, `weights_compact`, `hull_compact`, `cc_data` | Basic, Value, Poly, Sa/Hull |
| W4-d (after a, c) | `Convex/Thm221.lean` | `t221.subset`, `supset`, `eq`, `compact_sa_incl` | W4-a, W4-c |

### Wave 5 — pessimistic counterparts, root module, final checks
| unit | files | provides |
|---|---|---|
| W5-a | `Pessimistic.lean` | `pess.class_neg`, `pess.target_neg`, `pess.t11`, `pess.berge`, `pess.t212`, `pess.t215`, `pess.t218`, `pess.t220`, `pess.t221` |
| W5-b (orchestrator) | `HardnessBilevel.lean`, `scripts/check_axioms.lean` | root imports; a file that `#print axioms` every main theorem; `grep` for `sorry`/`instance : Has…` |

Optional, after everything: `t220.euclid_remark`, `s3.coeff_bound`, `sa.closure`, `t212.reindex`, stretch `sa.growth_proof`.

## 4. Per-unit acceptance checklist (used by the auditors)

- [ ] file builds inside the project (`lake build HardnessBilevel.<Module>`)
- [ ] no `sorry`, `axiom`, `native_decide`, `unsafe`; no `instance` of A1–A3 in the core library (and no unproved one anywhere)
- [ ] `#print axioms` of each public theorem ⊆ {`propext`, `Classical.choice`, `Quot.sound`}
- [ ] every blueprint lemma id of the unit is present (or its absence is justified in the header)
- [ ] every statement matches the blueprint mathematically (hypotheses, conclusion, types, universes `Type`)
- [ ] definitions are the blueprint's; no helper definition silently changes the meaning of a theorem
- [ ] deprecated Mathlib names absent; `autoImplicit` off; no `open Classical` leaking into statements' decidability
      (prefer `classical` tactic inside proofs)

## 5. Milestones and reporting

| milestone | content |
|---|---|
| M0 | toolchain + empty build |
| M1 | framework compiled and audited |
| M2 | Thm 1.1, Cor 2.9, Lemma 3.3 end-to-end, Lemma 2.19, Thm 2.12 (gadget form), gadgets, semialgebraic base — all `#print axioms`-clean |
| M3 | semialgebraic layer under A1, Prop 2.6, `P_unbound = SA`, class inclusions |
| M4 | Thms 2.15, 2.20, 2.21 relative to A1–A3 |
| M5 | pessimistic counterparts; root module; check script; final commit |

After each milestone: full build, audits resolved, commit and push to `claude/elegant-maxwell-o2ppx8`, short status in
the session.

## 6. Discharging the assumptions (added 2026-11-09)

The three assumptions are proved over `ℝ` in the companion library `svaiter/Semialgebraic` (its own `PLAN.md` and
`notes/` document the routes, research and audits), which depends on TauCeti and not on this repository:

| id | interface theorem of the companion (namespace `Semialgebraic.Interface`) | source |
|---|---|---|
| A1 | `image_comp_inl` | TauCeti's Tarski–Seidenberg theorem (cylindrical algebraic decomposition) |
| A2 | `exists_eq_iUnion_iInter_nonneg` | weighted Łojasiewicz inequality on closed semialgebraic sets, finiteness theorem for open sets |
| A3 | `growth` | polynomial growth of fibrewise suprema of semialgebraic plane sets |

Integration (this repository):

* `lakefile.toml` requires the companion at a pinned commit and Mathlib at the companion's pin; a second `lean_lib`
  `HardnessBilevelUnconditional` is a default target next to the core library.
* `HardnessBilevelUnconditional/Instances.lean` declares the three proved instances (each is the interface theorem
  with no glue, because `Bilevel.IsSemialgebraic` and `TauCeti.IsSemialgebraic` have the same body);
  `HardnessBilevelUnconditional/Main.lean` restates Prop 2.6, Thms 2.12, 2.15, 2.18, 2.20, 2.21 and their pessimistic
  twins with no class binder, in namespace `Bilevel.Unconditional`.
* The core library is unchanged: binder-form statements, no instance.
* `scripts/check.sh`: build of both libraries, forbidden-token scan, no instance in the core library, exactly the
  three proved instances in the unconditional library, `#print axioms` of the core theorems
  (`scripts/CheckAxioms.lean`) and of the instances and corollaries (`scripts/CheckAxiomsUnconditional.lean`), all
  equal to `[propext, Classical.choice, Quot.sound]`.
