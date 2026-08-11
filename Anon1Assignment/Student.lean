import Anon1Assignment.Spec

namespace Anon1.Student

open Anon1

def existsGeOddSequence (t : List Nat) : Bool :=
  sorry


theorem existsGeOddSequence_correctness (t : List Nat) :
    existsGeOddSequence t = true ↔
      ∃ s : List Bool, ∃ h : t.length = s.length,
        sumOddPositions (buildHeadAndTailSequence t s h) ≥
        sumEvenPositions (buildHeadAndTailSequence t s h) := by
  sorry

end Anon1.Student
