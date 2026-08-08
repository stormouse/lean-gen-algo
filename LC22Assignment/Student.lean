import LC22Assignment.Spec

namespace LC22.Student

open LC22

def generateAllValidParentheses (n : Nat) : List (List Char) := by
  sorry

theorem generated_is_valid :
    ∀ (n : Nat) (s : List Char),
      s ∈ generateAllValidParentheses n →
        s.length = 2 * n ∧ isValidParentheses s := by
  sorry

theorem valid_is_generated :
    ∀ (n : Nat) (s : List Char),
      s.length = 2 * n →
      isValidParentheses s →
      s ∈ generateAllValidParentheses n := by
  sorry

theorem algorithmSolvesLeetCode22 :
    ∀ (n : Nat) (s : List Char),
      (s.length = 2 * n ∧ isValidParentheses s) ↔
        s ∈ generateAllValidParentheses n := by
  intro n s
  constructor
  · intro h
    exact valid_is_generated n s h.1 h.2
  · intro h
    exact generated_is_valid n s h

end LC22.Student
