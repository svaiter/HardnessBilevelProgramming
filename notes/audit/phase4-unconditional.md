# Audit of Phase 4 (HardnessBilevelUnconditional) -- verdict: ACCEPT

Commit audited: 9012619 (range 84fba77..HEAD). Scratch files: /tmp/audit-p4/{A,B,C}.lean.

## 1. scripts/check.sh
Exit 0 (`exit=0`). Last lines: all 11 core `#print axioms` lines and then, for the unconditional file, the three
instances (`Bilevel.instHasSemialgebraicProjections`, `instHasFinitenessTheorem`, `instHasGrowthBound`) and the 16
`Bilevel.Unconditional.*` theorems, each `[propext, Classical.choice, Quot.sound]`, then
`OK: all listed theorems depend only on propext, Classical.choice, Quot.sound`.

Script review. `check_axioms`: every output line must be exactly the standard-axioms line or blank, so an error,
warning or different axiom list fails; the number of "depends on axioms" lines must equal the number of lines starting
with `#print axioms` in the file, so a missing report fails (an unknown constant gives an error line, also fails);
`set -o pipefail` makes a failing `lake lean | tee` abort. `2>/dev/null` only hides stderr (Lean messages are on stdout).
Gaps (non-blocking): (a) completeness of the `#print axioms` list w.r.t. Main.lean is not checked by the script (I checked:
19 lines = 3 instances + 16 theorems, all Main.lean theorems); (b) the token scan does not look for
`unsafe/implemented_by/extern/opaque` (I grepped manually: none); (c) the instance scans are line-start greps, so
`attribute [instance] ...` or `@[instance] theorem` would escape them; the real guard is the negative test in 6 below,
which is not in the script (optional: add it); (d) the "exactly three instances" test is sound (regex for the three
named lines plus a count of line-start `instance` == 3).

## 2. Core library unchanged
`git diff 84fba77..HEAD -- HardnessBilevel HardnessBilevel.lean`: one file, HardnessBilevel/Assumptions/Classes.lean,
17 lines (header doc comment only; hunk ends before `import`). The three `class` declarations and
`HasGrowthBound.growth'` are untouched (not in any hunk), hence byte-identical. Other changed files: see check 7.

## 3. Hygiene / instances
grep for sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque|set_option in HardnessBilevelUnconditional/,
HardnessBilevelUnconditional.lean, .lake/packages/Semialgebraic/Semialgebraic/ and Semialgebraic.lean: no hit.
`instance` declarations: HardnessBilevelUnconditional/Instances.lean:34,38,42 only (the three). Companion `Semialgebraic/`:
none (only a prose mention of TauCeti's instance in Interface/Projection.lean). The companion mentions `Bilevel` only in
doc comments and the SemialgebraicCheck/ shape files; it does not import HardnessBilevel and declares no HardnessBilevel class.
Companion pin 6a8030bd... = `git -C /home/user/Semialgebraic rev-parse HEAD` = tip of origin/claude/great-planck-pt0s0w.

## 4. Instances vs. interface theorems
Each instance is `⟨Semialgebraic.Interface.<thm>⟩` with no glue (image_comp_inl, exists_eq_iUnion_iInter_nonneg, growth).
Class fields (Classes.lean) vs. companion statements: binders `{α β : Type} [Fintype α] [Finite β] {S}` /
`{ι : Type} [Fintype ι] {s}` / `{n : ℕ} {f}`, hypotheses, and conclusions (`'' S` with `z ∘ Sum.inl`; `∃ I J P, s = ⋃ i, ⋂ j,
{x | 0 ≤ eval x (P i j)}`; `∃ B M, ∀ x, |f x| ≤ B + (1 + ∑ x_i^2)^M`) agree symbol by symbol; the only difference is
`Bilevel.IsSemialgebraic` vs `TauCeti.IsSemialgebraic`, and `isSemialgebraic_iff_tauCeti` is proved by `Iff.rfl`. The
instances elaborate, which also confirms the match.

## 5. Corollaries (statements copied in Main.lean; core types printed with `#check` in C.lean)
All 16 Main.lean theorems have a same-named core theorem. Verified mechanically (A.lean: telescope the core type, drop the
instance binders of the three classes, `isDefEq` with the Unconditional type: true for all 16) and by reading both texts:
only the class binders are removed; no hypothesis added or conclusion changed. Core vs. unconditional, abridged:
- valueFun_/pvalueFun_isExtSemialgebraic: `[A1] {n} {ι} [Fintype ι] {P Q} {Y}, IsPolyFun P → IsPolyFun Q → IsSemialgebraic Y → IsExtSemialgebraic (valueFun/pvalueFun P Q Y)` -- same without `[A1]`.
- thm212_eq_SA `[A1] {n}, P_unbound n = SA n`; pess_thm212 `Pp_unbound n = SA n` -- same.
- thm215_supset `[A1][A2][A3] {n} f, IsSemialgebraicMap f → LowerSemicontinuous f → (∀ K, IsCompact K → ∃ B, ∀ x ∈ K, |f x| ≤ B) → ∃ ι _ P Q a b, IsPolyFun P ∧ IsPolyFun Q ∧ (∀ k, a k ≤ b k) ∧ ∀ x, valueFun P Q (boundedBox a b) x = ↑(f x)` -- same.
- thm215_eq `P_bounded n = SA n ∩ LSC n ∩ CB n`; pess_thm215 `Pp_bounded n = SA n ∩ USC n ∩ CB n` -- same.
- thm218_main `[A1] PPe n ⊆ C_unbound n ∧ C_unbound n ⊆ SA n`; pess_thm218 with Cp_unbound -- same.
- thm220_supset `[A2] f ∈ PP n → LowerSemicontinuous f → coeFun f ∈ C_bounded n` -- same.
- thm220_main `[A1][A2] coeFun '' (PP n ∩ {f | LowerSemicontinuous f}) ⊆ C_bounded n ∧ C_bounded n ⊆ SA n ∩ LSC n ∩ CB n`; pess_thm220 (USC, Cp_bounded) -- same.
- thm221_compact_sa_incl / _pess `[A1] hP hQ {Y} IsCompact Y → Y.Nonempty → IsSemialgebraic Y → valueFun/pvalueFun P Q Y ∈ C_cc n / Cp_cc n` -- same.
- thm221_eq `C_cc n = SA n ∩ LSC n ∩ CB n`; pess_thm221 `Cp_cc n = ... ∩ USC n ∩ CB n` -- same.
Coverage: all 16 listed main theorems have a counterpart. The environment scan also shows other core theorems whose
type mentions a class (internal lemmas, not listed main theorems: thm215_subset(_pess), thm215_mem_P_bounded, thm218_main_pess,
thm220_subset(_pess), thm221_subset(_pess), thm221_supset, thm221_hull_sa, thm212_eq_SA_pess, the `*_subset_SA` family,
IsSemialgebraic.* closure lemmas, isSemialgebraic_* helpers). They are reachable with the instances in scope; no restatement
is required by the brief.

## 6. Axioms and instance search
A.lean (imports HardnessBilevelUnconditional): `#print axioms` of the three instances: each `[propext, Classical.choice,
Quot.sound]`; the 16 theorems are covered by check.sh output (same list). `example : Bilevel.Has... := inferInstance`
succeeds for all three. B.lean (imports only HardnessBilevel): `inferInstance` FAILS for all three (synthInstanceFailed),
so the core library has no instance in scope.

## 7. Pins and documentation
Pins correct: Mathlib 1b1ccf4b088b32fa3f23f2de1127433254a81e1e, Semialgebraic 6a8030bd1f9f53f5ad2128e073871655bad19495
(= companion HEAD = branch tip), TauCeti 2c9b12be26ca8efd0c54851aead7b7a6553f7f5c (manifest), lakefile and manifest agree.
README.md, PLAN.md §1 rule 4 and §6, the Classes.lean header describe the state truthfully (table, rule, commands).
Required fixes: none.
Optional fixes (stale or imprecise text):
1. blueprint.md lines ~305 and ~308 (§2.5 rules 3-4) still say "since no instance exists" and describe `Assumptions/Unsafe.lean`; the status
   paragraph above them qualifies this, but line 358 ("no instances"), 2047-2048 (Phase 0 history) are only historical.
2. PLAN.md line 124 checklist "no `instance` of A1-A3" and Classes.lean line 34 comment "No instance of these classes exists (by policy)"
   hold only for the core library; add "in the core library".
3. README.md: "about 6950 lines" -- the core library is 6997 lines now (36 files correct); blueprint.md line 6 and PLAN still cite Mathlib `1df8067a` as historical context (PLAN notes the move; blueprint line 6 does not).
4. scripts/lake-cache.toml (new file) is not mentioned in README/PLAN; add the inferInstance negative/positive tests to check.sh and a check that every Main.lean theorem appears in CheckAxiomsUnconditional.lean.
