import Anon4.Spec
import Anon4.Student

namespace Anon4

theorem solution_is_optimal' (l r : Nat) (xs : List Segment) :
    ∃ m : Nat,
        (∀ a b c d : Nat, runOperation a b c d xs = some ys ∧ score l r ys ≤ m) ∧
        (∃ a b c d : Nat, runOperation a b c d xs = some ys ∧ score l r ys = m) := by
  exact Anon4.solution_is_optimal l r xs

#print axioms solution_is_optimal'

end Anon4
