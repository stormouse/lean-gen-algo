import Anon3Assignment.Spec
import Anon3Assignment.Student

namespace Anon3.Grader

open Anon3

theorem solution_is_correct
    (m k : Nat)
    (hm : 3 ≤ m)
    (hk : 2 * k < m)
    (ops : List Op) :
    runImplementation Anon3.Student.implementation m k ops =
      runBaseline m k ops := by
  exact Anon3.Student.solution_is_correct m k hm hk ops

end Anon3.Grader
