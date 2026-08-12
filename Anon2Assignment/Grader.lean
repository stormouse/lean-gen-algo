import Anon2Assignment.Student

namespace Anon2.Grader

open Anon2

theorem solution_is_valid (a : List Nat) (k : Nat) :
    let sol := Anon2.Student.solve a k
    isGood a sol k ∧ isSub a sol ∧
      ∀ alt, (isGood a alt k ∧ isSub a alt) → alt.length ≤ sol.length := by
  exact Anon2.Student.solution_is_valid a k

end Anon2.Grader
