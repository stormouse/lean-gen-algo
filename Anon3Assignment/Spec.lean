namespace Anon3

inductive Op where
  | add : Nat → Op
  | calc : Op
  deriving Repr, DecidableEq

def lastN (xs : List Nat) (n : Nat) : List Nat :=
  xs.drop (xs.length - n)

def expectedAverage (stream : List Nat) (m k : Nat) : Int :=
  if stream.length < m then
    -1
  else
    let window := lastN stream m
    let sorted := window.mergeSort
    let middle := (sorted.drop k).take (m - 2 * k)
    Int.ofNat (middle.sum / (m - 2 * k))

def run
    (m k : Nat)
    (ops : List Op)
    (stream : List Nat := []) : List Int :=
  match ops with
  | [] => []
  | .add n :: rest =>
      run m k rest (stream ++ [n])
  | .calc :: rest =>
      expectedAverage stream m k ::
        run m k rest stream

end Anon3
