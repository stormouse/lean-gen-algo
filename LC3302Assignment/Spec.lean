namespace LC3302

def countDiff (a b : List Char)
  (h : a.length = b.length): Nat :=
  match a, b with
  | [], [] => 0
  | x :: xs, y :: ys =>
      if x = y then
        countDiff xs ys (by simpa using h)
      else
        1 + countDiff xs ys (by simpa using h)


def almostEqual (a b : List Char) : Prop :=
  ∃ h : a.length = b.length, countDiff a b h ≤ 1


def subsequenceByIndex (s : List Char) (indices : List Nat) : Option (List Char) :=
  indices.mapM fun i => s[i]?


def monotonicIncreasing (a : List Nat) : Prop :=
  match a with
  | x1 :: (x2 :: xs) =>
      if x1 ≥ x2 then
        False
      else
        monotonicIncreasing (x2 :: xs)
  | _ => True


def isValidSolution (a b : List Char) (indices : List Nat) : Prop :=
  monotonicIncreasing indices ∧
    match subsequenceByIndex a indices with
    | none => False
    | some s => almostEqual s b


def noValidSolution (a b : List Char) : Prop :=
  ∀ indices : List Nat,
    ¬ isValidSolution a b indices


end LC3302
