
namespace Anon1

def removeHeadOrTail {α : Type} (t : List α) (head : Bool) (h : t ≠ [])
    : α × List α :=
  if head then
    (t.head h, t.tail)
  else
    (t.getLast h, t.dropLast)


theorem removeHeadOrTail_length {α : Type}
    (t : List α) (head : Bool) (h : t ≠ []) :
    (removeHeadOrTail t head h).2.length + 1 = t.length := by
  cases t with
  | nil => contradiction
  | cons x xs =>
      cases head <;> simp [removeHeadOrTail]


def buildHeadAndTailSequence {α : Type} (t : List α) (operations : List Bool)
    (h : t.length = operations.length) : List α :=
  match t, operations with
  | [], [] => []
  | [], _ :: _ => by
      simp at h
  | _ :: _, [] => by
      simp at h
  | x :: xs, op :: ops =>
    have hne : x :: xs ≠ [] := by simp

    let result := removeHeadOrTail (x :: xs) op hne
    let element := result.1
    let seq := result.2

    have hseq : seq.length = ops.length := by
      have hremove : (removeHeadOrTail (x :: xs) op hne).2.length + 1 =
          (x :: xs).length := by exact removeHeadOrTail_length (x :: xs) op hne
      rw [h] at hremove
      simp only [List.length_cons] at hremove
      dsimp [seq, result]
      exact Nat.add_right_cancel hremove

    element :: buildHeadAndTailSequence seq ops hseq


def sumOddPositions (a : List Nat) : Nat :=
  a.zipIdx
    |>.filter (fun (_, i) => i % 2 = 1)
    |>.map (fun (x, _) => x)
    |>.sum


def sumEvenPositions (a : List Nat) : Nat :=
  a.zipIdx
    |>.filter (fun (_, i) => i % 2 = 0)
    |>.map (fun (x, _) => x)
    |>.sum


end Anon1
