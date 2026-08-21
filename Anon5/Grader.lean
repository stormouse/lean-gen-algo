import Anon5.Spec
import Anon5.Student

namespace Anon5

theorem solution_is_valid' (ms : List Nat) (k : Nat) :
    solution ms k = kthSmallest (multiples ms) k := by
  exact solution_is_valid ms k

#print axioms solution_is_valid'

end Anon5
