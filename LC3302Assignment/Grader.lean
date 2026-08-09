import LC3302Assignment.Spec
import LC3302Assignment.Student

namespace LC3302.Grader

def noValidSolution (a b : List Char) : Prop :=
  ∀ i : List Nat, ¬ (
    monotonicIncreasing i ∧
    match subsequenceByIndex a i with
    | none => False
    | some s => almostEqual s b)


theorem no_output_iff_no_solution (a b : List Char) :
    (noValidSolution a b ↔ LC3302.Student.findValidSequence a b = none) := by
  exact LC3302.Student.no_output_iff_no_solution a b


theorem output_is_valid_solution (a b : List Char) :
    (LC3302.Student.findValidSequence a b = some indices) → isValidSolution a b indices := by
  exact LC3302.Student.output_is_valid_solution a b

#print axioms no_output_iff_no_solution
#print axioms output_is_valid_solution

end LC3302.Grader
