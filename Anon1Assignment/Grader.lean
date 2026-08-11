import Anon1Assignment.Student

namespace Anon1.Grader

open Anon1

theorem existsGeOddSequence_correctness (t : List Nat) :
    Anon1.Student.existsGeOddSequence t = true ↔
      ∃ s : List Bool, ∃ h : t.length = s.length,
        sumOddPositions (buildHeadAndTailSequence t s h) ≥
        sumEvenPositions (buildHeadAndTailSequence t s h) := by
  exact Anon1.Student.existsGeOddSequence_correctness t

end Anon1.Grader
