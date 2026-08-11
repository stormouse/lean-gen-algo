namespace LC2996

def longestSequentialPrefix (a : List Nat) : List Nat :=
  match a with
  | [] => []
  | x :: [] => [x]
  | x :: y :: xs =>
      if x + 1 = y then
        x :: longestSequentialPrefix (y :: xs)
      else
        [x]

end LC2996
