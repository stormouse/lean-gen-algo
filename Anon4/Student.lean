import Anon4.Spec

namespace Anon4


def query (l r : Nat) (a : List Segment) : Nat :=
  sorry


theorem solution_is_optimal (l r : Nat) (xs : List Segment) :
    ∃ m : Nat,
        (∀ a b c d : Nat, runOperation a b c d xs = some ys ∧ score l r ys ≤ m) ∧
        (∃ a b c d : Nat, runOperation a b c d xs = some ys ∧ score l r ys = m) := by
  sorry


end Anon4
