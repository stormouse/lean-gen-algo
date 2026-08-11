import LC2996Assignment.Spec
import LC2996Assignment.Student

namespace LC2996.Grader

open LC2996

theorem solution_is_valid (a : List Nat) :
    let prefixSum := (longestSequentialPrefix a).sum
    let result := LC2996.Student.smallestMissingNatGtSequentialPrefixSum a
    result > prefixSum ∧ ∀ x : Nat, x > prefixSum → x ≥ result := by
  exact LC2996.Student.solution_is_valid a

#print axioms solution_is_valid

end LC2996.Grader
