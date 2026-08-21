import Anon5.Spec
import Anon5.Student

namespace Anon5

theorem solution_is_valid'
    (ms : List Nat)
    (k : Nat)
    (hms : ms ≠ [])
    (hpos : ∀ m ∈ ms, 0 < m)
    (hk : 0 < k) :
    solution ms k = kthSmallest (multiples ms) k := by
  exact solution_is_valid ms k hms hpos hk

#print axioms solution_is_valid'

end Anon5
