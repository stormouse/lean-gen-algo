namespace Anon2

/-
  You are given an integer array nums and an integer k.

  The frequency of an element x is the number of times it occurs in an array.

  An array is called good if the frequency of each element in this array is less than or equal to k.

  Return the length of the longest good subarray of nums.

  A subarray is a contiguous non-empty sequence of elements within an array.
-/

def isGood (s : List Nat) (k : Nat) : Prop :=
  ∀ x : Nat, x ∈ s → s.count x ≤ k

def isSub (a s : List Nat) : Prop :=
  ∃ pre suf, a = pre ++ s ++ suf

end Anon2
