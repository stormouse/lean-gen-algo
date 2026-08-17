import Anon4.Spec
import Anon4.Student

namespace Anon4


theorem solution_is_optimal' (xs : List Segment) :
    ∀ l r : Nat, l ≤ r →
      let p := (xs.drop l).take (r - l + 1)
      let m := query l r xs
      (∀ a b c d : Nat, ∀ ys : List Segment, runOperation a b c d p = some ys → score ys ≤ m) ∧
      (∃ a b c d : Nat, ∃ ys : List Segment, runOperation a b c d p = some ys ∧ score ys = m) := by
  exact solution_is_optimal xs

#print axioms solution_is_optimal'

end Anon4
