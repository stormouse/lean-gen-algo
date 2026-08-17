import Anon4.Spec

namespace Anon4


def query (l r : Nat) (a : List Segment) : Nat :=
  sorry


theorem solution_is_optimal (xs : List Segment) :
    ∀ l r : Nat, l ≤ r →
      let p := (xs.drop l).take (r - l + 1)
      let m := query l r xs
      (∀ a b c d : Nat, runOperation a b c d p = some ys → score ys ≤ m) ∧
      (∃ a b c d : Nat, runOperation a b c d p = some zs ∧ score zs = m) := by
  sorry


end Anon4
