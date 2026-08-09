import LC3302Assignment.Spec
import LC3302Assignment.Student

namespace LC3302.Grader

theorem no_output_iff_no_solution (a b : List Char) :
    (LC3302.noValidSolution a b ↔ LC3302.Student.findValidSequence a b = none) := by
  exact LC3302.Student.no_output_iff_no_solution a b


theorem output_is_valid_solution (a b : List Char) (indices : List Nat) :
    (LC3302.Student.findValidSequence a b = some indices) → isValidSolution a b indices := by
  exact LC3302.Student.output_is_valid_solution a b

#print axioms no_output_iff_no_solution
#print axioms output_is_valid_solution

end LC3302.Grader
