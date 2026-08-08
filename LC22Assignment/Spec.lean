namespace LC22

def countOpenClose (s : List Char) : Int :=
  match s with
  | [] => 0
  | x :: xs =>
      if x = '(' then
        countOpenClose xs + 1
      else if x = ')' then
        countOpenClose xs - 1
      else
        countOpenClose xs


def containsOnlyParentheses (s : List Char) : Prop :=
  ∀ c ∈ s, (c = '(' ∨ c = ')')


-- def isPrefix (pre s : List Char) : Prop :=
--   match pre with
--   | [] => True
--   | p :: ps =>
--       match s with
--       | [] => False
--       | x :: xs =>
--           (p = x) ∧ isPrefix ps xs

def isPrefix (pre s : List Char) : Prop :=
  ∃ rest, s = pre ++ rest


def isValidParentheses (s : List Char) : Prop :=
  containsOnlyParentheses s
  ∧ countOpenClose s = 0
  ∧ ∀ p, isPrefix p s → countOpenClose p >= 0

end LC22
