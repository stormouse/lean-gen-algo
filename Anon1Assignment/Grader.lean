import Anon1Assignment.Student

namespace Anon1.Grader

open Anon1
open Anon1.Student

theorem solution_is_valid (t : List Nat) :
    solve t = true ↔ targetProperty t := by
  exact Anon1.Student.solution_is_valid t

end Anon1.Grader
