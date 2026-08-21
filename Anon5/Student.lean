import Anon5.Spec

namespace Anon5

def solution (ms : List Nat) (k : Nat) : Nat :=
  sorry


theorem solution_is_valid
    (ms : List Nat)
    (k : Nat)
    (hms : ms ≠ [])
    (hpos : ∀ m ∈ ms, 0 < m)
    (hk : 0 < k) :
    solution ms k = kthSmallest (multiples ms) k := by
  sorry


end Anon5
