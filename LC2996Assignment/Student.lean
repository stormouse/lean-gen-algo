import LC2996Assignment.Spec
namespace LC2996.Student

open LC2996

def smallestMissingNatGtSequentialPrefixSum (a : List Nat) : Nat :=
  sorry


theorem solution_is_valid (a : List Nat) :
    let prefixSum := (longestSequentialPrefix a).sum
    let result := smallestMissingNatGtSequentialPrefixSum a
    result > prefixSum ∧ ∀ x : Nat, x > prefixSum → x ≥ result := by
  sorry

end LC2996.Student
