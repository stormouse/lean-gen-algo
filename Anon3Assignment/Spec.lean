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

def runBaseline
    (m k : Nat)
    (ops : List Op)
    (stream : List Nat := []) : List Int :=
  match ops with
  | [] => []
  | .add n :: rest =>
      runBaseline m k rest (stream ++ [n])
  | .calc :: rest =>
      expectedAverage stream m k ::
        runBaseline m k rest stream

structure MKImplementation where
  State : Type
  init : Nat → Nat → State
  addElement : State → Nat → State
  calculateMKAverage : State → Int

def runImplementation
    (impl : MKImplementation)
    (m k : Nat)
    (ops : List Op) : List Int :=
  go (impl.init m k) ops
where
  go (state : impl.State) : List Op → List Int
    | [] => []
    | .add x :: rest =>
        go (impl.addElement state x) rest
    | .calc :: rest =>
        impl.calculateMKAverage state ::
          go state rest

end Anon3
