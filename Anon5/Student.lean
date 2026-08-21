import Anon5.Spec

namespace Anon5

open scoped Classical

/-! ### Computable membership and counting

A natural number is in `multiples ms` when it is positive and divisible by some
element of `ms` (under the standing hypothesis that every element of `ms` is
positive). We implement this as a boolean test and count how many such numbers
lie below a bound. -/

/-- Boolean test: `n` is a positive multiple of some element of `ms`. -/
def isMultiple (ms : List Nat) (n : Nat) : Bool :=
  decide (0 < n) && ms.any (fun m => decide (m ∣ n))

/-- Number of multiples of `ms` that are `< x`. -/
def countMultiples (ms : List Nat) (x : Nat) : Nat :=
  (List.range x).countP (fun i => isMultiple ms i)

/-- An upper bound on the `k`-th smallest multiple of `ms`. -/
def bound (ms : List Nat) (k : Nat) : Nat :=
  k * ms.foldr max 1 + 1

/-! ### The `k`-th smallest multiple, by counting

`nth p (k - 1)` (with `p n := n ∈ multiples ms`) is the `k`-th smallest multiple.
Because `count` and `nth` form a Galois connection on the infinite set of
multiples, the `k`-th smallest multiple is one less than the least `x` whose
count reaches `k`. That least `x` is found by `Nat.find`, which linearly scans
`0, 1, 2, …` until `countMultiples ms x` reaches `k`; each count itself
enumerates `0, …, x-1` and tests `isMultiple`. -/

/-- `solution ms k` is the `k`-th smallest positive multiple of any element of
`ms` (1-indexed). -/
def solution (ms : List Nat) (k : Nat) : Nat :=
  if h : k ≤ countMultiples ms (bound ms k) then
    Nat.find (show ∃ x : Nat, k ≤ countMultiples ms x from ⟨bound ms k, h⟩) - 1
  else
    0

/-! ### Correctness -/

lemma isMultiple_iff (ms : List Nat) (n : Nat) (hpos : ∀ m ∈ ms, 0 < m) :
    isMultiple ms n = true ↔ n ∈ multiples ms := by
  unfold isMultiple
  rw [Bool.and_eq_true_iff]
  simp only [decide_eq_true_eq, List.any_eq_true, multiples, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hnpos, m, hmem, hdiv⟩
    rcases hdiv with ⟨c, hc⟩
    refine ⟨c, m, hmem, ?_, hc.symm⟩
    have hmpos : 0 < m := hpos m hmem
    have hcpos : 0 < c := by
      by_contra hc0
      have hc0' : c = 0 := by omega
      subst c
      simp at hc
      omega
    omega
  · rintro ⟨c, m, hmem, hc1, hmul⟩
    have hmpos : 0 < m := hpos m hmem
    refine ⟨?_, m, hmem, ⟨c, hmul.symm⟩⟩
    rw [← hmul]
    exact Nat.mul_pos hmpos (by omega : 0 < c)

lemma countMultiples_eq_count (ms : List Nat) (x : Nat) (hpos : ∀ m ∈ ms, 0 < m) :
    countMultiples ms x = Nat.count (fun n => n ∈ multiples ms) x := by
  classical
  unfold countMultiples
  rw [show Nat.count (fun n => n ∈ multiples ms) x =
      (List.range x).countP (fun i => decide (i ∈ multiples ms)) by rfl]
  exact List.countP_congr (fun i hi => by
    show isMultiple ms i = true ↔ decide (i ∈ multiples ms) = true
    rw [decide_eq_true_eq]
    exact isMultiple_iff ms i hpos)

lemma multiples_infinite (ms : List Nat) (hms : ms ≠ []) (hpos : ∀ m ∈ ms, 0 < m) :
    (setOf (fun n => n ∈ multiples ms)).Infinite := by
  rcases List.exists_mem_of_ne_nil ms hms with ⟨m, hmem⟩
  have hmpos : 0 < m := hpos m hmem
  refine Set.infinite_of_injective_forall_mem (f := fun c : Nat => m * (c + 1)) ?_ ?_
  · intro a b h
    have hsucc : a + 1 = b + 1 := Nat.mul_left_cancel hmpos h
    omega
  · intro c
    rw [Set.mem_setOf_eq, multiples]
    refine ⟨c + 1, m, hmem, ?_, rfl⟩
    omega

/-- Every element of `ms` is at most the fold of `max`. -/
lemma mem_le_foldr_max (ms : List Nat) {m : Nat} (hmem : m ∈ ms) :
    m ≤ ms.foldr max 1 := by
  induction ms with
  | nil => cases hmem
  | cons x xs ih =>
      simp only [List.foldr_cons, List.mem_cons] at hmem ⊢
      rcases hmem with h | h
      · subst h
        exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

/-- There are at least `k` positive multiples of `m` below `m * k + 1`. -/
lemma count_multiples_of_ge (m k : Nat) (hmpos : 0 < m) :
    k ≤ Nat.count (fun n => ∃ c : Nat, 1 ≤ c ∧ n = m * c) (m * k + 1) := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
      have hP : (∃ c : Nat, 1 ≤ c ∧ m * (k + 1) = m * c) := by
        use k + 1
        constructor
        · exact Nat.succ_le_succ (Nat.zero_le k)
        · rfl
      have hstep : Nat.count (fun n => ∃ c : Nat, 1 ≤ c ∧ n = m * c) (m * (k + 1) + 1)
          = Nat.count (fun n => ∃ c : Nat, 1 ≤ c ∧ n = m * c) (m * (k + 1)) + 1 := by
        rw [Nat.count_succ]
        rw [if_pos hP]
      rw [hstep]
      have hmono : Nat.count (fun n => ∃ c : Nat, 1 ≤ c ∧ n = m * c) (m * k + 1) ≤
          Nat.count (fun n => ∃ c : Nat, 1 ≤ c ∧ n = m * c) (m * (k + 1)) := by
        apply Nat.count_monotone
        rw [Nat.mul_succ]
        omega
      omega

/-- Under the hypotheses, `countMultiples ms (bound ms k)` reaches `k`, so the
search in `solution` is guaranteed to terminate inside the bound. -/
lemma countMultiples_ge_bound (ms : List Nat) (k : Nat)
    (hms : ms ≠ []) (hpos : ∀ m ∈ ms, 0 < m) :
    k ≤ countMultiples ms (bound ms k) := by
  classical
  rcases List.exists_mem_of_ne_nil ms hms with ⟨m, hmem⟩
  have hmpos : 0 < m := hpos m hmem
  have hmle : m ≤ ms.foldr max 1 := mem_le_foldr_max ms hmem
  let P : Nat → Prop := fun n => ∃ c : Nat, 1 ≤ c ∧ n = m * c
  have hkP : k ≤ Nat.count P (m * k + 1) := count_multiples_of_ge m k hmpos
  have hmono1 : Nat.count P (m * k + 1) ≤
      Nat.count (fun n => n ∈ multiples ms) (m * k + 1) := by
    apply Nat.count_mono_left
    intro n _ hPn
    rcases hPn with ⟨c, hc1, hc⟩
    unfold multiples
    exact ⟨c, m, hmem, hc1, hc.symm⟩
  have hmono2 : Nat.count (fun n => n ∈ multiples ms) (m * k + 1) ≤
      Nat.count (fun n => n ∈ multiples ms) (bound ms k) := by
    apply Nat.count_monotone
    unfold bound
    have hmulk : m * k ≤ ms.foldr max 1 * k := Nat.mul_le_mul_right k hmle
    rw [Nat.mul_comm (ms.foldr max 1) k] at hmulk
    omega
  have hk : k ≤ Nat.count (fun n => n ∈ multiples ms) (bound ms k) :=
    le_trans (le_trans hkP hmono1) hmono2
  rw [(countMultiples_eq_count ms (bound ms k) hpos).symm] at hk
  exact hk

theorem solution_is_valid
    (ms : List Nat)
    (k : Nat)
    (hms : ms ≠ [])
    (hpos : ∀ m ∈ ms, 0 < m)
    (hk : 0 < k) :
    solution ms k = kthSmallest (multiples ms) k := by
  unfold kthSmallest solution
  let p : Nat → Prop := fun n => n ∈ multiples ms
  let q : Nat → Prop := fun x => k ≤ countMultiples ms x
  have hpInf : (setOf p).Infinite := multiples_infinite ms hms hpos
  have hbound : k ≤ countMultiples ms (bound ms k) := countMultiples_ge_bound ms k hms hpos
  rw [dif_pos hbound]
  change Nat.find (p := q) ⟨bound ms k, hbound⟩ - 1 = Nat.nth p (k - 1)
  have hspec : k ≤ countMultiples ms (Nat.find (p := q) ⟨bound ms k, hbound⟩) :=
    Nat.find_spec (p := q) ⟨bound ms k, hbound⟩
  have hcount : k ≤ Nat.count p (Nat.find (p := q) ⟨bound ms k, hbound⟩) := by
    rwa [countMultiples_eq_count ms (Nat.find (p := q) ⟨bound ms k, hbound⟩) hpos] at hspec
  have hlt' : k - 1 < Nat.count p (Nat.find (p := q) ⟨bound ms k, hbound⟩) := by omega
  have hlt : Nat.nth p (k - 1) < Nat.find (p := q) ⟨bound ms k, hbound⟩ :=
    (Nat.lt_nth_iff_count_lt hpInf).mp hlt'
  have hge : Nat.nth p (k - 1) + 1 ≤ Nat.find (p := q) ⟨bound ms k, hbound⟩ :=
    Nat.succ_le_of_lt hlt
  have hle : Nat.find (p := q) ⟨bound ms k, hbound⟩ ≤ Nat.nth p (k - 1) + 1 := by
    apply Nat.find_min' (p := q)
    change k ≤ countMultiples ms (Nat.nth p (k - 1) + 1)
    rw [countMultiples_eq_count ms (Nat.nth p (k - 1) + 1) hpos]
    rw [Nat.count_nth_succ_of_infinite hpInf (k - 1)]
    omega
  have hfind : Nat.find (p := q) ⟨bound ms k, hbound⟩ = Nat.nth p (k - 1) + 1 :=
    le_antisymm hle hge
  rw [hfind]
  omega


end Anon5
