import Anon3Assignment.Spec

namespace Anon3.Student

open Anon3

structure State where
  -- TODO: implementation

def init (m k : Nat) : State :=
  sorry

def addElement (s : State) (n : Nat) : State :=
  sorry

def calculateMKAverage (s : State) : Int :=
  sorry

def implementation : MKImplementation where
  State := State
  init := init
  addElement := addElement
  calculateMKAverage := calculateMKAverage

theorem solution_is_correct
    (m k : Nat)
    (hm : 3 ≤ m)
    (hk : 2 * k < m)
    (ops : List Op) :
    runImplementation implementation m k ops =
      runBaseline m k ops := by
  sorry

end Anon3.Student
