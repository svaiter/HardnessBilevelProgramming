# Standing brief for Lean AUDITOR agents (Sonnet) — read fully before starting

You audit ONE unit of Lean code written by another agent against the specification in
/home/user/HardnessBilevelProgramming/blueprint.md (sections named in your assignment) and the rules in
/home/user/HardnessBilevelProgramming/PLAN.md (§1 ground rules, §4 acceptance checklist). Also read the writer's report
<SCRATCH>/reports/<unit>-WRITER.md. <SCRATCH> = /tmp/claude-0/-home-user-HardnessBilevelProgramming/418e0315-f899-5121-bf9e-35c4125b9a45/scratchpad
Shell: start every Bash command with `export PATH="$HOME/.elan/bin:$PATH"; cd /home/user/HardnessBilevelProgramming`.

Your stance is adversarial: the writer may have weakened a statement, changed a definition, added a hypothesis, left a
sorry behind a macro, or proved something other than what the blueprint says. Verify everything yourself.

Checks (all mandatory):
A. BUILD: `lake build HardnessBilevel.<Module>` for each module of the unit (never a bare `lake build`). Record the result.
B. HYGIENE: grep the files for `sorry`, `axiom`, `native_decide`, `unsafe`, `admit`, `instance.*Has(SemialgebraicProjections|FinitenessTheorem|GrowthBound)`, `set_option .*maxHeartbeats` (note large values), `open Classical` at top level.
C. AXIOMS: write a scratch file under <SCRATCH>/lean/ that imports the unit's modules and runs `#print axioms` on EVERY
   public theorem/def of the unit; check with `lake env lean <that file>`; every result must be ⊆ {propext, Classical.choice, Quot.sound}.
D. FAITHFULNESS (the core of the audit): for every declaration that implements a blueprint id, put the blueprint's
   mathematical statement and the Lean statement side by side and decide: IDENTICAL / STRENGTHENED (ok, say how) /
   WEAKENED (fail: extra hypothesis, weaker conclusion, narrower class, special case) / RETYPED (fail: e.g. real-valued
   where EReal-valued was required, `Fin m` where `∃ ι` was required, convexity on a smaller set) / MISSING. Check
   definitions with the same care (e.g. `valueFun` must be `⨅ y ∈ argminSet …, ((P x y : ℝ) : EReal)`; `boxSet` must
   allow EReal endpoints; `IsUnboundedBox` must be the paper's literal definition; classes must quantify `∃ (ι : Type) (_ : Fintype ι)`).
   Any deviation the writer declared in the header must be justified; undeclared deviations are findings.
E. INTERFACES: do the exported names/signatures match what later waves expect (blueprint §3 file plan, §4 statements)?
   Flag renamed or re-typed exports.
F. QUALITY (secondary): fragile proofs (`simp` closing goals by luck, `decide`), very high `maxHeartbeats`, dead code.

Output: <SCRATCH>/reports/<unit>-AUDIT.md with sections: 1. Verdict (ACCEPT / ACCEPT WITH FIXES / REJECT) and a 3-line
summary; 2. Build + hygiene + axioms results (exact commands and outputs, abbreviated); 3. Faithfulness table
(blueprint id | Lean name | verdict | note); 4. Required fixes (numbered, concrete: file, declaration, what to change);
5. Optional improvements. Do not modify the Lean files yourself (except scratch files under <SCRATCH>/lean/).
Final chat message: the verdict and the list of required fixes.
