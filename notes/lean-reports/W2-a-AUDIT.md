# W2-a AUDIT (Theorem 1.1) — Smooth/Whitney.lean, Smooth/Thm11.lean

## 1. Verdict: ACCEPT
- Build clean, no sorry/axiom/hygiene hits, all 13 public decls have axioms ⊆ {propext, Classical.choice, Quot.sound}.
- Main theorem, pessimistic twin, Whitney lemma match the blueprint exactly; smoothness is genuine C^∞ (not analytic).
- No undeclared deviations; no case lemma assumes `f x ≠ ⊥`.

## 2. Build / hygiene / axioms
- A: `lake build HardnessBilevel.Smooth.Whitney HardnessBilevel.Smooth.Thm11` -> "Build completed successfully" (only generic "consider adding `module`" warning).
- B: grep for sorry|axiom|native_decide|unsafe|admit|instance.*Has|maxHeartbeats|open Classical: no hits (only match: `ContDiff ℝ ⊤` inside a header comment saying "never"). No deprecated names in the unit files.
- C: scratch <SCRATCH>/lean/W2aAudit.lean, `#print axioms` on exists_contDiff_zeroSet_eq, thm11P, thm11Q, contDiff_thm11P/Q, thm11Q_nonneg, argminSet_thm11Q_of_ne_top/eq_top, valueFun_thm11_of_ne_top/eq_top, exists_smooth_of_lowerSemicontinuous(_proper), exists_smooth_of_upperSemicontinuous: all `[propext, Classical.choice, Quot.sound]`.
- D checks compiled in scratch (no errors):
  * `example : ∃ g, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ ∀ p, g p = 0 ↔ p ∈ C := exists_contDiff_zeroSet_eq hC` (E finite-dim, closed C) ok.
  * `(∞ : WithTop ℕ∞) = ((⊤:ℕ∞) : WithTop ℕ∞) := rfl` ok, and `(∞) ≠ (⊤ : WithTop ℕ∞)` by `decide` ok -> the `∞` in the statements is C^∞, not analytic.
  * Main theorem is accepted by `example : ∀ {n} f, LowerSemicontinuous f → IsClosed {x | f x ≠ ⊤} → ∃ P Q : (Fin n→ℝ)→(Fin 3→ℝ)→ℝ, ContDiff ℝ ∞ (uncurry P) ∧ ContDiff ℝ ∞ (uncurry Q) ∧ valueFun P Q Set.univ = f` (blueprint text verbatim).
  * `thm11P = fun _ y => y 0` and `thm11Q h g = fun x y => h (x,y 0)^2 + (g x * y 1)^2 + (1 - y 1 * y 2)^2` both by `rfl`.
  * Application to `f x = ((x 0:ℝ):EReal)` (n=1): lsc (continuous) and `{f ≠ ⊤} = univ` closed: typechecks, applies. Indicator `if x 0 ≤ 0 then 0 else 1`: hypotheses are the right shape; domain-closedness goal `{f ≠ ⊤}=univ` reduces to `¬(1:EReal)=⊤` (my scratch `simp` just did not close it; scratch-only, not a unit defect); lsc left as sorry in scratch (not needed for the faithfulness check).

## 3. Faithfulness
| blueprint id | Lean name | verdict | note |
|---|---|---|---|
| t11.whitney | exists_contDiff_zeroSet_eq | IDENTICAL | E: `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]`, closed C, `ContDiff ℝ ∞ g ∧ ∀ p, g p = 0 ↔ p ∈ C`. Proof via `exists_contDiff_support_eq (n := (⊤:ℕ∞))`. |
| t11.isClosed_realEpigraph | Bilevel.isClosed_realEpigraph (Framework/Semicont, W1-d) | reused | not audited here; used with `hf` giving `IsClosed {p | f p.1 ≤ ↑p.2}` as required by `hh`. |
| t11.T0 | thm11P, thm11Q | IDENTICAL | P x y = y 0; Q as blueprint (rfl-checked). |
| t11.smooth | contDiff_thm11P, contDiff_thm11Q | IDENTICAL | the latter takes `ContDiff ℝ ∞ h`, `ContDiff ℝ ∞ g` (needed, as in blueprint construction). |
| t11.nonneg | thm11Q_nonneg | IDENTICAL | |
| t11.case_finite | argminSet_thm11Q_of_ne_top, valueFun_thm11_of_ne_top | IDENTICAL/abstracted | hypotheses `hh : ∀ p, h p = 0 ↔ f p.1 ≤ ↑p.2`, `hg : ∀ x, g x = 0 ↔ f x ≠ ⊤`, `hx : f x ≠ ⊤` only; `⊥` case handled explicitly (no `≠ ⊥` assumption). |
| t11.case_top | argminSet_thm11Q_of_eq_top, valueFun_thm11_of_eq_top | IDENTICAL | uses only `hg`, `f x = ⊤`. |
| t11.main | exists_smooth_of_lowerSemicontinuous | IDENTICAL | exact blueprint statement, Y = Fin 3 → ℝ, `valueFun P Q Set.univ = f`, hypothesis `IsClosed {x | f x ≠ ⊤}`. |
| t11.main_paper | exists_smooth_of_lowerSemicontinuous_proper | IDENTICAL | only adds unused hypotheses `∀ x, f x ≠ ⊥`, `∃ x, f x ≠ ⊤`. |
| t11.main_pess | exists_smooth_of_upperSemicontinuous | IDENTICAL | `UpperSemicontinuous f`, `IsClosed {x | f x ≠ ⊥}`, `pvalueFun P Q Set.univ = f`. |
Definitions used: `valueFun = ⨅ y ∈ argminSet Q S x, ((P x y:ℝ):EReal)`, `pvalueFun` with `⨆` — as required; `argminSet Q S x = {y | y ∈ S ∧ ∀ y' ∈ S, Q x y ≤ Q x y'}`.

## 4. Required fixes
None.

## 5. Optional improvements
- E (interfaces): names match writer's API; blueprint ids map via docstrings. Fine.
- F: proofs use `nlinarith`/`positivity`/`linarith` on small goals (case_top), acceptable; `Set.mem_ofPred_eq` used in `simp only` (the current non-deprecated name) fine. No maxHeartbeats. The two `iInf₂_le (f := ...)` explicit-motive terms in valueFun_thm11_of_ne_top are verbose but robust.
- Header remark about `IsClosed {f ≠ ⊤}` vs `{f ∈ ℝ}` is present. 
