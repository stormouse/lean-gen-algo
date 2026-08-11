import LC2996Assignment.Spec
namespace LC2996.Student

open LC2996

def smallestMissingNatGeSequentialPrefixSum (a : List Nat) : Nat :=
  sorry


theorem solution_is_valid (a : List Nat) :
    let prefixSum := (longestSequentialPrefix a).sum
    let result := smallestMissingNatGeSequentialPrefixSum a
    (result ≥ prefixSum ∧ result ∉ a) → ∀ x : Nat, (x ≥ prefixSum ∧ x ∉ a) → x ≥ result := by
  sorry

end LC2996.Student
