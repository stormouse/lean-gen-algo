namespace Anon1

inductive Side where
  | first
  | second
  deriving DecidableEq, Repr

def lastOf {α : Type} (x : α) (xs : List α) : α :=
  (x :: xs).getLast (by simp)

def dropLastOf {α : Type} (x : α) (xs : List α) : List α :=
  (x :: xs).dropLast

inductive ValidState :
    List Nat → Nat → Nat → Side → Prop where

  | done
      {a b : Nat}
      {side : Side}
      (h : a ≥ b) :
      ValidState [] a b side

  | firstLeft
      {x : Nat}
      {xs : List Nat}
      {a b : Nat}
      (h :
        ValidState xs (a + x) b .second) :
      ValidState (x :: xs) a b .first

  | firstRight
      {x : Nat}
      {xs : List Nat}
      {a b : Nat}
      (h :
        ValidState
          (dropLastOf x xs)
          (a + lastOf x xs)
          b
          .second) :
      ValidState (x :: xs) a b .first

  | secondBoth
      {x : Nat}
      {xs : List Nat}
      {a b : Nat}
      (left :
        ValidState xs a (b + x) .first)
      (right :
        ValidState
          (dropLastOf x xs)
          a
          (b + lastOf x xs)
          .first) :
      ValidState (x :: xs) a b .second

def targetProperty (t : List Nat) : Prop :=
  ValidState t 0 0 .first

end Anon1
