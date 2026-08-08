import LC22Assignment.Student

namespace LC22.Grader

theorem submission_has_exact_spec :
    ∀ (n : Nat) (s : List Char),
      (s.length = 2 * n ∧ LC22.isValidParentheses s) ↔
        s ∈ LC22.Student.generateAllValidParentheses n := by
  exact LC22.Student.algorithmSolvesLeetCode22

#print axioms submission_has_exact_spec

end LC22.Grader
