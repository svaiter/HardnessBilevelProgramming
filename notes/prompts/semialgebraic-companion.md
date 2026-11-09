# Prompt: semialgebraic companion library for HardnessBilevel

> Paste everything below the line into a new Claude Code session. Before starting it, fill in the two
> placeholders: `<COMPANION_REPO>` (an empty GitHub repository you created, e.g. `svaiter/SemialgebraicFiniteness`)
> and attach both `<COMPANION_REPO>` and `svaiter/HardnessBilevelProgramming` to the session.
> The last line of §6 makes the session stop after the A2 research; delete it if you want A2 implemented in the same run.

---

You are the orchestrator of a Lean 4 + Mathlib formalization project. Make a detailed plan file before writing
any Lean code, keep it updated, and run the work in phases with the gates below.

## 1. Context

`svaiter/HardnessBilevelProgramming` (branch `claude/elegant-maxwell-o2ppx8`, or `main` if it has been merged)
formalizes arXiv:2407.12372, "Geometric and computational hardness of bilevel programming" (Bolte, Lê, Pauwels,
Vaiter). Read its `README.md`, `blueprint.md` §2.5 and §4.B (the semialgebraic layer), and
`HardnessBilevel/Assumptions/Classes.lean`. That library builds with no `sorry`, but three real-algebraic-geometry
facts are taken as hypotheses through `Prop`-classes that have no instance anywhere:

```lean
namespace Bilevel
-- Bilevel.IsSemialgebraic {ι : Type*} (s : Set (ι → ℝ)) : Prop :=
--   s ∈ MeasureTheory.generateSetAlgebra
--     (Set.range (fun p : MvPolynomial ι ℝ => {x | MvPolynomial.eval x p = 0}) ∪
--      Set.range (fun p : MvPolynomial ι ℝ => {x | 0 < MvPolynomial.eval x p}))

class HasSemialgebraicProjections : Prop where            -- A1, Tarski–Seidenberg
  image_comp_inl {α β : Type} [Fintype α] [Finite β] {S : Set (α ⊕ β → ℝ)} :
    IsSemialgebraic S → IsSemialgebraic ((fun z : α ⊕ β → ℝ => z ∘ Sum.inl) '' S)

class HasFinitenessTheorem : Prop where                   -- A2, finiteness theorem (paper Prop 2.4, BCR 2.7.2)
  exists_eq_iUnion_iInter_nonneg {ι : Type} [Fintype ι] {s : Set (ι → ℝ)} :
    IsSemialgebraic s → IsClosed s →
    ∃ (I J : ℕ) (P : Fin I → Fin J → MvPolynomial ι ℝ),
      s = ⋃ i, ⋂ j, {x | 0 ≤ MvPolynomial.eval x (P i j)}

class HasGrowthBound : Prop where                         -- A3, corrected paper Prop 2.5
  growth {n : ℕ} {f : (Fin n → ℝ) → ℝ} :
    IsSemialgebraic {z : Fin n ⊕ Unit → ℝ | f (z ∘ Sum.inl) = z (Sum.inr ())} →
    (∀ r : ℝ, ∃ B : ℝ, ∀ x, ∑ i, x i ^ 2 ≤ r → |f x| ≤ B) →
    ∃ (B : ℝ) (M : ℕ), ∀ x, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M
end Bilevel
```

A1 is used by Prop 2.6 and every "⊆" half of the paper's theorems; A2 by the construction halves of Theorems 2.15,
2.20, 2.21; A3 by Theorem 2.15 (and so 2.21). The paper's Prop 2.5 is false as stated for `n ≥ 2`
(`1/(x₁ − x₂)` off the diagonal, `0` on it); A3 is the corrected statement, with local boundedness.

**Goal:** remove these assumptions, in a new companion library in `<COMPANION_REPO>`, built on TauCeti.

## 2. What is known about TauCeti (checked 2026-11-05; re-verify everything at the commit you pin)

`TauCetiProject/TauCeti` (Apache-2.0, AI-written, tracks Mathlib master hourly).
- At commit `e8758b7b` it used toolchain `leanprover/lean4:v4.36.0-rc2` and Mathlib `1b1ccf4b`.
  HardnessBilevel pins Mathlib `1df8067a` (one day newer). Its HEAD has moved since (`2c9b12be` on 2026-11-09).
- `TauCeti.IsSemialgebraic {σ R : Type*} [CommRing R] [LinearOrder R] (s : Set (σ → R))` has the same body as
  `Bilevel.IsSemialgebraic` with `R := ℝ`; the bridge should be `Iff.rfl` (to confirm by compiling).
- `instance : TauCeti.HasSemialgebraicProjections ℝ` is proved via cylindrical algebraic decomposition in
  `TauCeti/Geometry/RealAlgebraic/CAD/Existence.lean`. `TauCeti.IsSemialgebraic.image_comp_inl [Finite τ]` in
  `.../Semialgebraic/Image.lean` is exactly the field of A1. The import closure of the instance is 118 modules,
  about 23,600 lines, and a text scan found no `sorry`/`axiom`/`admit`/`native_decide`.
- Also available: closure, interior, frontier of semialgebraic sets (`Semialgebraic/Topology.lean`), quantifier
  elimination, semialgebraic maps `(σ → R) → (τ → R)` (`Semialgebraic/Function.lean`, a different shape from
  HardnessBilevel's real-valued `graphSet`), connected components, dimension, Thom encodings, sign determination,
  root counting in families (`Semialgebraic/RootCount.lean`, `FamilyRoots.lean`), Nash functions.
- Not available: the finiteness theorem, the Łojasiewicz inequality, any polynomial growth bound for semialgebraic
  functions. TauCeti's completed real-algebraic-geometry roadmap stops at CAD and quantifier elimination and lists
  triangulation and o-minimality as out of scope; no open roadmap mentions the finiteness theorem.
- TauCeti files use the Lean module system (`module`, `public import`). TauCeti publishes its own olean cache:
  `lake exe cache get` (Mathlib) then `bash scripts/lake-cache-get.sh .` (TauCeti). Check how a *downstream*
  project gets TauCeti's oleans; if it cannot, Lake builds only the imported closure.

## 3. Architecture (decided; deviate only with a written reason)

- `<COMPANION_REPO>` is a Lake project that depends on TauCeti at a pinned commit and uses TauCeti's pinned Mathlib,
  so both caches hit. It must NOT depend on HardnessBilevel.
- State results in TauCeti's vocabulary (`TauCeti.IsSemialgebraic`, `R := ℝ` where needed), so they can later be
  proposed upstream. For each of A1, A2, A3 provide an **interface theorem** whose statement, unfolded at `R := ℝ`,
  is exactly the class field above (same binders, same universe `Type`, same conclusion shape).
- Integration happens last, in HardnessBilevel: add the companion as a dependency, move HardnessBilevel's Mathlib pin
  to the companion's, and add a separate `lean_lib` target (e.g. `HardnessBilevelUnconditional`) that declares the
  three *proved* instances and assumption-free corollaries of the main theorems. The core `HardnessBilevel` library
  keeps its binder-form statements unchanged. Amend the no-instance rule in its `PLAN.md` to "no unproved instance".

## 4. Phases and gates

**Phase 0 — setup.** Install elan and the pinned toolchain, create the Lake project, fetch caches, smoke-test that a
file importing `TauCeti.Geometry.RealAlgebraic.CAD.Existence` builds. Write `PLAN.md`. Commit.

**Phase 1 — A1 bridge (small).** Prove `Bilevel`-shaped A1 from TauCeti: the definitional bridge between the two
`IsSemialgebraic` (or an explicit proof if not definitional), and the interface theorem for `image_comp_inl` over
`α β : Type`. Gate: `#print axioms` of the interface theorem is exactly `[propext, Classical.choice, Quot.sound]`.

**Phase 2 — A3 growth bound (medium-to-large, ~400–600 lines expected).** Follow HardnessBilevel `blueprint.md`
§4.B.5: `sa.thin_set` (a semialgebraic set whose fibres contain no open interval lies in the zero set of a polynomial
of positive degree in the isolated variable, from a sign-condition normal form), `sa.one_var_growth` (a semialgebraic
`G ⊆ ℝ²` with subsingleton fibres has its fibre values bounded by `c(1+ρ)^M` for large `ρ`; Mathlib has
`Polynomial.IsRoot.norm_lt_cauchyBound` and polynomial asymptotics in `Analysis/Polynomial/Basic.lean`),
`sa.growth_proof` (`g ρ := sSup (|f| '' {‖x‖² ≤ ρ})` is semialgebraic by quantifier elimination; carry nonemptiness
and boundedness explicitly because `Real.sSup` has junk values). Reuse TauCeti's root-counting and
quantifier-elimination API where it shortens this. Gate: interface theorem for A3, axioms clean.

**Phase 3a — A2 research (no Lean code).** Run parallel research agents, then independent audits, producing a report
that chooses a proof route for the finiteness theorem and decomposes it into lemmas with Lean-style statements,
Mathlib/TauCeti dependencies (verified by grep at the pinned commits) and effort estimates. Compare at least:
  1. the textbook route through Łojasiewicz (Schweighofer's lecture notes §6.2–6.3, Bochnak–Coste–Roy §2.6–2.7:
     one-variable growth, compact Łojasiewicz, weighted closed Łojasiewicz, finiteness);
  2. a route through TauCeti's cylindrical decomposition and Thom encodings (e.g. decompositions adapted to
     derivative-closed families, where closures of cells are obtained by relaxing strict sign conditions). This route
     is a hypothesis to be checked, not a known fact; establish whether it is correct and complete.
Also record: the weaker FT′ ("every closed semialgebraic `K` is `{x | ∃ z ∈ [0,1/2]^k, R(x,z) = 0}`") suffices
for Theorem 2.15 but not for Theorem 2.20, which needs the genuine `≥`-form (see HardnessBilevel `blueprint.md`
§4.B.4 and §4.G.4). Gate: audited report committed under `notes/`, with a recommendation and a risk assessment.

**Phase 3b — A2 implementation.** Implement the chosen route in waves with the same writer/auditor process.
Gate: interface theorem for A2, axioms clean.

**Phase 4 — integration into HardnessBilevel.** As in §3. Gate: HardnessBilevel's `scripts/check.sh` passes, and a
new check prints the axioms of the unconditional corollaries (Theorems 2.12, 2.15, 2.18, 2.20, 2.21, Prop 2.6 and
their pessimistic twins) as exactly `[propext, Classical.choice, Quot.sound]`. Update its `README.md` table.

## 5. Process and roles

- Research agents: Fable (high effort); research audits: Opus (high effort), adversarial, re-deriving every lemma.
- Lean writers: Opus; Lean auditors: Sonnet. One writer per unit, then one auditor per unit; fixes go back to the
  writer until the audit says ACCEPT. Units within a wave run in parallel; give each a standing brief (rules below)
  and the API summaries of the modules it imports.
- Auditors check: build of the unit's modules; no forbidden tokens; `#print axioms` of every public declaration;
  statement-by-statement faithfulness against the plan (no added hypotheses, no weakened conclusions, no changed
  definitions); and that interface theorems match the class fields character for character after unfolding.
- Commit and push after every audited unit, on the branch the session designates. Write reports to `notes/`.

## 6. Rules

- No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`. No instance of the HardnessBilevel classes unless proved.
- Never weaken a statement to make it provable; strengthening is fine and must be declared in the file header.
- Agents never run a bare `lake build` while others build; each builds its own modules with
  `lake build <Module>`; the orchestrator runs the full build between waves. Agents never edit files outside their
  assignment, `lakefile.toml`, `lean-toolchain` or the root module.
- Known traps at these Mathlib commits: `push_neg` is deprecated (use `push Not`), `if_pos`/`if_neg`/`if_true` and
  `Set.mem_setOf_eq` are deprecated, `stdSimplex` and its lemmas are deprecated, `ContDiff ℝ ⊤` means analytic,
  `continuous_finset_sum` is now `continuous_finsetSum`, a parameter-free `Prop`-class used as a binder triggers
  `linter.concreteInstances` (silence it locally). In a root module, `import` lines must precede the docstring.
- Do not open pull requests or issues on TauCeti or file TauCeti roadmaps; if upstreaming looks worthwhile, write a
  short proposal in `notes/` for the user.
- Stop after Phase 3a and report; do not start Phase 3b without the user's go-ahead.

## 7. Final report

State, for each of A1, A2, A3: done (interface theorem name and file), in progress, or not started, with reasons;
the pinned TauCeti and Mathlib commits; the exact commands that verify the result; and anything left for the user to
decide.
