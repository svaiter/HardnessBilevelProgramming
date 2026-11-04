# HardnessBilevel

A Lean 4 + Mathlib formalization of the results of

> J. Bolte, T. Lê, E. Pauwels, S. Vaiter, *Geometric and computational hardness of bilevel programming*,
> Mathematical Programming, 2025 (arXiv:2407.12372).

The mathematical plan is `blueprint.md` (proof routes, Lean encoding, paper errata); the execution plan is `PLAN.md`.
The library has 36 files, about 6946 lines and 700 declarations, builds with no `sorry`, and every main theorem depends only on
`propext`, `Classical.choice`, `Quot.sound` (run `scripts/check.sh`).

NOTE: this is a work in progress, and relies on brutal axiomatization of semialgebraic sets.
It is also fully auto-formalized without human intervention on the Lean4 code.

## Toolchain

Lean `leanprover/lean4:v4.36.0-rc2`, Mathlib commit `1df8067a` (pinned in `lakefile.toml` / `lake-manifest.json`).

```bash
lake exe cache get   # Mathlib oleans
lake build
scripts/check.sh     # build + hygiene + #print axioms of the main theorems
```

## Assumptions

Mathlib has no real algebraic geometry beyond the basics, so three facts are **quarantined as Prop-classes** in
`HardnessBilevel/Assumptions/Classes.lean` and taken as explicit instance-implicit hypotheses by the theorems that need them.
**No instance of any of them is declared anywhere** (`scripts/check.sh` enforces this), so `#print axioms` stays clean and
every dependency is visible in a theorem's signature.

| id | class | content |
|---|---|---|
| A1 | `HasSemialgebraicProjections` | Tarski–Seidenberg: projections of semialgebraic sets are semialgebraic |
| A2 | `HasFinitenessTheorem` | closed semialgebraic sets are finite unions of finite intersections of `{p ≥ 0}` (paper Prop 2.4) |
| A3 | `HasGrowthBound` | a semialgebraic function bounded on bounded sets is polynomially bounded (corrected paper Prop 2.5) |

## Results

| paper | Lean (namespace `Bilevel`) | file | assumptions |
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
- `notes/`: research, audits and consolidation behind the blueprint; `notes/lean-reports/`: writer and audit reports per unit
