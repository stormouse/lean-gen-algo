import Anon2Assignment.Spec

namespace Anon2.Student

open Anon2

def solve (a : List Nat) (k : Nat) : List Nat :=
  sorry

theorem solution_is_valid (a : List Nat) (k : Nat) :
    let sol := solve a k
    isGood a sol k ∧ isSub a sol ∧
      ∀ alt, (isGood a alt k ∧ isSub a alt) → alt.length ≤ sol.length := by
  sorry

end Anon2.Student
