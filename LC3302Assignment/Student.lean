import LC3302Assignment.Spec

namespace LC3302.Student

open LC3302

def findValidSequence (a b : List Char) : Option (List Nat) :=
  sorry


theorem no_output_iff_no_solution (a b : List Char) :
    (noValidSolution a b ↔ LC3302.Student.findValidSequence a b = none) := by
  sorry


theorem output_is_valid_solution (a b : List Char) :
    (findValidSequence a b = some indices) → isValidSolution a b indices := by
  sorry


end LC3302.Student
