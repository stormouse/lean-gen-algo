import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Nth

namespace Anon5

def multiples (ms : List Nat) : Set Nat :=
  { n : Nat | ∃ k : Nat, ∃ m ∈ ms, k ≥ 1 ∧ m * k = n }

noncomputable def kthSmallest (s : Set Nat) (k : Nat) : Nat :=
  Nat.nth (fun n => n ∈ s) (k - 1)

end Anon5
