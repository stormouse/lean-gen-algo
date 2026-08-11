import LC2996Assignment.Spec
namespace LC2996.Student

open LC2996

/-! ### Counting helpers

The search below walks upward from a starting point, skipping every value that occurs
in `a`. It terminates because each skipped value strictly shrinks the number of list
entries that are `≥` the current candidate. -/

/-- Raising the threshold never increases the count of entries above it. -/
theorem countP_le_succ (a : List Nat) (k : Nat) :
    a.countP (fun x => decide (k + 1 ≤ x)) ≤ a.countP (fun x => decide (k ≤ x)) := by
  induction a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons, decide_eq_true_eq]
    split <;> split <;> omega

/-- If `k` occurs in `a`, raising the threshold past `k` strictly shrinks the count. -/
theorem countP_lt_of_mem (a : List Nat) (k : Nat) (h : k ∈ a) :
    a.countP (fun x => decide (k + 1 ≤ x)) < a.countP (fun x => decide (k ≤ x)) := by
  induction a with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with heq | h'
    · subst heq
      have hmono := countP_le_succ xs k
      simp only [List.countP_cons, decide_eq_true_eq]
      split <;> split <;> omega
    · have hlt := ih h'
      simp only [List.countP_cons, decide_eq_true_eq]
      split <;> split <;> omega

/-! ### The search -/

/-- The smallest natural number that is `≥ k` and does not occur in `a`. -/
def search (a : List Nat) (k : Nat) : Nat :=
  if k ∈ a then search a (k + 1) else k
termination_by a.countP (fun x => decide (k ≤ x))
decreasing_by exact countP_lt_of_mem a k ‹k ∈ a›

theorem search_ge (a : List Nat) (k : Nat) : k ≤ search a k := by
  fun_induction search a k with
  | case1 k hk ih => exact Nat.le_of_succ_le ih
  | case2 k hk => exact Nat.le_refl k

theorem search_not_mem (a : List Nat) (k : Nat) : search a k ∉ a := by
  fun_induction search a k with
  | case1 k hk ih => exact ih
  | case2 k hk => exact hk

/-- `search a k` is a lower bound on every value `≥ k` that avoids `a`. -/
theorem search_le (a : List Nat) (k : Nat) (x : Nat) (hx : k ≤ x) (hmem : x ∉ a) :
    search a k ≤ x := by
  fun_induction search a k with
  | case1 k hk ih =>
    apply ih
    rcases Nat.eq_or_lt_of_le hx with rfl | hlt
    · exact absurd hk hmem
    · exact hlt
  | case2 k hk => exact hx

/-! ### Solution -/

def smallestMissingNatGeSequentialPrefixSum (a : List Nat) : Nat :=
  search a (longestSequentialPrefix a).sum

/-- The answer is itself a valid candidate: at least the prefix sum, and absent from `a`. -/
theorem solution_is_candidate (a : List Nat) :
    smallestMissingNatGeSequentialPrefixSum a ≥ (longestSequentialPrefix a).sum ∧
      smallestMissingNatGeSequentialPrefixSum a ∉ a :=
  ⟨search_ge a _, search_not_mem a _⟩

theorem solution_is_valid (a : List Nat) :
    let prefixSum := (longestSequentialPrefix a).sum
    let result := smallestMissingNatGeSequentialPrefixSum a
    (result ≥ prefixSum ∧ result ∉ a) → ∀ x : Nat, (x ≥ prefixSum ∧ x ∉ a) → x ≥ result := by
  intro prefixSum result _ x hx
  exact search_le a prefixSum x hx.1 hx.2

end LC2996.Student
