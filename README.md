# gen-algo

An experiment in **specification-driven code generation**: I write the problem statement as a formal
specification in Lean 4, hand it to a coding agent, and require the agent to deliver both an
implementation *and* a machine-checked proof that the implementation meets the spec.

If the proof compiles, the solution is correct — no test cases, no eyeballing.

## Layout

Each problem is a Lean library named after its LeetCode number, split into three files:

| File | Author | Purpose |
| --- | --- | --- |
| `Spec.lean` | me | The problem statement: pure `Prop`-level definitions of what a correct answer *is*. No algorithm. |
| `Student.lean` | the agent | The implementation, plus the proofs of the theorems the grader demands. |
| `Grader.lean` | me | The contract: theorem statements the submission must discharge, followed by `#print axioms` to confirm nothing was smuggled in. |

Current problems:

- **`LC22Assignment`** — generate all valid parenthesis combinations.
  Contract: `s.length = 2 * n ∧ isValidParentheses s ↔ s ∈ generateAllValidParentheses n`
  (an iff, so it proves both soundness and completeness of the enumeration).
- **`LC3302Assignment`** — find the lexicographically valid index sequence for an almost-equal subsequence.
  Contract: the output, when present, is a valid solution; and `none` is returned *iff* no solution exists.

## Rules of the game

- `Spec.lean` and `Grader.lean` are fixed. The agent may only add to `Student.lean`.
- The agent may add its own helper lemmas, but the grader theorems must be closed by
  `exact`-ing something from `Student`, so the spec cannot be weakened.
- `#print axioms` must show only the standard axioms — no `sorryAx`.
- Some problems require not falling back to enumerating the entire solution space.

## Building

```sh
lake build                 # default target will be the problem I most recently worked on
lake build LC22Assignment
lake env lean LC3302Assignment.lean   # runs the #eval smoke tests
```

Toolchain: `leanprover/lean4:v4.32.2`, no external dependencies (no Mathlib). CI builds every push.

## Notes

Commit messages on agent-produced proofs record the model and its token usage, e.g.
`Opus 4.7 proof - 2.2k input, 223.9k output, 17.4m cache read, 655.8k cache write (.42)` —
a rough log of what it costs to get a nontrivial algorithm verified.
