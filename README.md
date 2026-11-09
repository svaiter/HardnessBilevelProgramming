# HardnessBilevel

A Lean 4 + Mathlib formalization of the results of

> J. Bolte, T. Lê, E. Pauwels, S. Vaiter, *Geometric and computational hardness of bilevel programming*,
> Mathematical Programming, 2025 (arXiv:2407.12372).

The mathematical plan is `blueprint.md` (proof routes, Lean encoding, paper errata); the execution plan is `PLAN.md`.
The core library `HardnessBilevel` has 36 files, about 6950 lines and 700 declarations and builds with no `sorry`.
The library `HardnessBilevelUnconditional` adds proved instances of the three real-algebraic-geometry facts the core
library takes as hypotheses, and the main theorems with no hypothesis left. Every main theorem, in both forms, depends
only on `propext`, `Classical.choice`, `Quot.sound` (run `scripts/check.sh`).

NOTE: this is a work in progress, fully auto-formalized without human intervention on the Lean 4 code.

## Toolchain

Lean `leanprover/lean4:v4.36.0-rc2`. Pinned in `lakefile.toml` / `lake-manifest.json`:

| dependency | commit | role |
|---|---|---|
| Mathlib | `1b1ccf4b` | everything |
| [Semialgebraic](https://github.com/svaiter/Semialgebraic) | see `lakefile.toml` | proofs of A1, A2, A3 over `ℝ` |
| [TauCeti](https://github.com/TauCetiProject/TauCeti) | `2c9b12be` (through Semialgebraic) | semialgebraic sets, Tarski–Seidenberg |

```bash
scripts/setup.sh     # once: Mathlib oleans, and the mappings of TauCeti's olean cache
. scripts/env.sh     # in every shell: lets Lake fetch TauCeti modules instead of compiling them
lake build           # both libraries
scripts/check.sh     # build + hygiene + #print axioms of the main theorems, with and without assumptions
```

Without `scripts/env.sh` the build is still correct, but Lake compiles the imported part of TauCeti from source.
`lake build HardnessBilevel` builds the core library alone.

## Assumptions, and their proofs

Mathlib has no real algebraic geometry beyond the basics, so three facts are **quarantined as Prop-classes** in
`HardnessBilevel/Assumptions/Classes.lean` and taken as explicit instance-implicit hypotheses by the theorems of the
core library that need them. The core library declares **no instance** of them, so every dependency is visible in a
theorem's signature.

All three are now **proved**: the companion library `Semialgebraic` proves them over `ℝ` on top of TauCeti, and
`HardnessBilevelUnconditional/Instances.lean` declares the instances (each is the companion's interface theorem with
no glue, since `Bilevel.IsSemialgebraic` and `TauCeti.IsSemialgebraic` have the same body). No unproved instance
exists anywhere (`scripts/check.sh` enforces this).

| id | class | content | proved by (namespace `Semialgebraic.Interface`) |
|---|---|---|---|
| A1 | `HasSemialgebraicProjections` | Tarski–Seidenberg: projections of semialgebraic sets are semialgebraic | `image_comp_inl` (TauCeti's cylindrical algebraic decomposition) |
| A2 | `HasFinitenessTheorem` | closed semialgebraic sets are finite unions of finite intersections of `{p ≥ 0}` (paper Prop 2.4) | `exists_eq_iUnion_iInter_nonneg` (weighted Łojasiewicz inequality) |
| A3 | `HasGrowthBound` | a semialgebraic function bounded on bounded sets is polynomially bounded (corrected paper Prop 2.5) | `growth` (growth of fibrewise suprema) |

`HardnessBilevelUnconditional/Main.lean` restates, in namespace `Bilevel.Unconditional` and under the same names,
every theorem of the table below that has an entry in the "assumptions" column, with the class binders removed:
`valueFun_isExtSemialgebraic`, `pvalueFun_isExtSemialgebraic`, `thm212_eq_SA`, `thm215_supset`, `thm215_eq`,
`thm218_main`, `thm220_supset`, `thm220_main`, `thm221_compact_sa_incl` (and `_pess`), `thm221_eq`, `pess_thm212`,
`pess_thm215`, `pess_thm218`, `pess_thm220`, `pess_thm221`.

## Results

| paper | Lean (namespace `Bilevel`) | file | assumptions of the core statement (all proved, see above) |
|---|---|---|---|
| Thm 1.1 (C^∞ bilevel ⇒ any lsc function) | `exists_smooth_of_lowerSemicontinuous` | `Smooth/Thm11.lean` | none |
| Cor 2.9 (compact lower level: lsc, real, bounded) | `cor29`, `lowerSemicontinuous_valueFun` | `Framework/Berge.lean` | none |
| Prop 2.6 (value functions are semialgebraic, any semialgebraic Y) | `valueFun_isExtSemialgebraic` | `Semialgebraic/Value.lean` | A1 |
| Thm 2.12 construction | `exists_bilevel_valueFun_eq` | `Unbounded/Thm212.lean` | none |
| Thm 2.12, `P_unbound = SA` | `thm212_eq_SA` | `Semialgebraic/Value.lean` | A1 (⊆ only) |
| Thm 2.15 construction | `thm215_of_presentation`, `thm215_supset` | `Bounded/Thm215Core.lean`, `Bounded/Thm215.lean` | A1, A2, A3 |
| Thm 2.15, `P_bounded = SA ∩ LSC ∩ CB` | `thm215_eq` | `Bounded/Thm215.lean` | A1, A2, A3 |
| Lemma 2.19 (indicator of a basic set, convex lower level) | `lemma219` | `Convex/Lemma219.lean` | none |
| Thm 2.18, `PP ⊆ C_unbound ⊆ SA` | `thm218_PP_subset`, `thm218_main` | `Framework/Classes.lean`, `Semialgebraic/Value.lean` | none / A1 |
| Thm 2.20 construction | `t220_core`, `thm220_supset` | `Convex/Thm220Core.lean`, `Convex/Thm220.lean` | none / A2 |
| Thm 2.20, `PP ∩ LSC ⊆ C_bounded ⊆ SA ∩ LSC ∩ CB` | `thm220_main` | `Convex/Thm220.lean` | A1, A2 |
| Thm 2.21 linearization (any Y) | `t221_linearize` | `Convex/Linearize.lean` | none |
| Thm 2.21, `C_cc = SA ∩ LSC ∩ CB` | `thm221_eq`, `thm221_compact_sa_incl` | `Convex/Thm221.lean` | A1, A2, A3 / A1 |
| Lemma 3.3 (optimal value < 0 ⟺ YES instance), degree ≤ 5 | `SSI.lemma33`, `reduce_correct`, `SSI.totalDegree_Pp/Qp` | `Hardness/*.lean` | none |
| §2.4 pessimistic counterparts | `pess_thm11` … `pess_thm221` | `Pessimistic.lean` | as optimistic |

Theorem 3.2's Σ₂ᵖ-hardness statement is not formalized (Mathlib has no complexity classes); the reduction and its
correctness are. See `blueprint.md` §5 for the confirmed errata in the paper that the formalization works around
(notably: Prop 2.5 is false as stated for n ≥ 2; the §2.1 graph formula assumes attainment; eq. (18) needs Y ≠ ∅).

## Layout

- `Framework/`: argmin sets, value functions in `EReal`, polynomial functions, boxes, semicontinuity, Berge, classes
- `Semialgebraic/`: semialgebraic sets (generated set algebra), normal forms, preimages, extended-real functions,
  projection calculus (A1), Prop 2.6, hulls
- `Gadgets/`: zero-locus and escape gadgets, box gadgets
- `Smooth/`, `Unbounded/`, `Bounded/`, `Convex/`, `Hardness/`, `Pessimistic.lean`: the theorems
- `Assumptions/`: the three classes
- `HardnessBilevelUnconditional/`: proved instances of the three classes (`Instances.lean`) and assumption-free forms of
  the main theorems (`Main.lean`)
- `notes/`: research, audits and consolidation behind the blueprint; `notes/lean-reports/`: writer and audit reports per unit
