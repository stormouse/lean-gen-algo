import Anon3Assignment.Spec
import Anon3Assignment.Student

namespace Anon3.Grader

def runSolution
    (m k : Nat)
    (ops : List Anon3.Op) : List Int :=
  go (Anon3.Student.init m k) ops
where
  go (state : Anon3.Student.State) : List Anon3.Op → List Int
    | [] => []
    | .add n :: rest =>
        go (Anon3.Student.addElement state n) rest
    | .calc :: rest =>
        Anon3.Student.calculateMKAverage state ::
          go state rest

theorem solution_is_correct
    (m k : Nat)
    (hm : 3 ≤ m)
    (hk : 2 * k < m)
    (ops : List Op) :
    runSolution m k ops = run m k ops := by
  sorry

end Anon3.Grader
