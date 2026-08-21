namespace Anon4

inductive Segment where
  | Inactive
  | Active
  deriving Repr, BEq, DecidableEq


def isContiguous (s : Segment) (l r : Nat) (a : List Segment) : Bool :=
  a |>.drop l
    |>.take (r - l + 1)
    |>.all (fun x => x == s)


def isContiguousActive (l r : Nat) (a : List Segment) : Bool :=
  isContiguous Segment.Active l r a


def isContiguousInactive (l r : Nat) (a : List Segment) : Bool :=
  isContiguous Segment.Inactive l r a


def flip (l r : Nat) (a : List Segment) : List Segment :=
  List.zip (List.range a.length) a
    |>.map (fun (i, x) =>
        if l ≤ i && i ≤ r then
          match x with
          | Segment.Inactive => Segment.Active
          | Segment.Active => Segment.Inactive
        else
          x)


def flipFlap (l₁ r₁ l₂ r₂ : Nat) (a : List Segment) : List Segment :=
  flip l₂ r₂ (flip l₁ r₁ a)


def isValidFlipFlap (l₁ r₁ l₂ r₂ : Nat) (a : List Segment) : Bool :=
  l₁ ≤ r₂
    && l₂ ≤ r₂
    && isContiguousActive l₁ r₁ a
    && isContiguousInactive l₂ r₂ (flip l₁ r₁ a)


def runOperation (l₁ r₁ l₂ r₂ : Nat) (a : List Segment) : Option (List Segment) :=
  if isValidFlipFlap l₁ r₁ l₂ r₂ a then
    some (flipFlap l₁ r₁ l₂ r₂ a)
  else
    none


def score (a : List Segment) : Nat :=
    let rec go (xs : List Segment) (currStreak maxStreak : Nat) : Nat :=
    match xs with
    | [] => max currStreak maxStreak
    | Segment.Active :: rest => go rest (currStreak + 1) (max (currStreak + 1) maxStreak)
    | _ :: rest => go rest 0 maxStreak
  go a 0 0

end Anon4
