import Anon5.Spec

namespace Anon5

open scoped Classical

open Nat

/-! ### Counting multiples, fast

The `k`-th smallest amount formable with a *single* denomination is found by
binary search over the answer, using inclusion–exclusion to count, in `O(2ⁿ)`
per step, how many amounts `≤ X` are a multiple of at least one coin. -/

/-- Positive integers `≤ X` divisible by at least one `c ∈ cs`. -/
def mults (cs : List Nat) (X : Nat) : Finset Nat :=
  (Finset.range (X + 1)).filter (fun n => 0 < n ∧ ∃ c ∈ cs, c ∣ n)

/-- Number of multiples of `cs` that are `≤ X` (the specification-level count). -/
def countAtMost (cs : List Nat) (X : Nat) : Nat := (mults cs X).card

/-- Exactly `N / c` positive multiples of `c` are `≤ N`. -/
lemma card_multiples_pos (N c : Nat) :
    ((Finset.range (N + 1)).filter (fun n => 0 < n ∧ c ∣ n)).card = N / c := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases h : c ∣ N + 1
      · simp [h, Nat.succ_div_of_dvd h, ih]
      · simp [h, Nat.succ_div_of_not_dvd h, ih]

/-- The count for a single coin. -/
lemma card_single (c X : Nat) :
    (mults [c] X).card = X / c := by
  unfold mults
  rw [show (Finset.range (X + 1)).filter (fun n => 0 < n ∧ ∃ d ∈ [c], d ∣ n) =
      (Finset.range (X + 1)).filter (fun n => 0 < n ∧ c ∣ n) by
    refine Finset.ext ?_
    intro n
    simp only [Finset.mem_filter]
    simp]
  exact card_multiples_pos X c

/-- `mults` distributes over list cons as a union. -/
lemma mults_cons_union (c : Nat) (cs : List Nat) (X : Nat) :
    mults (c :: cs) X = mults [c] X ∪ mults cs X := by
  ext n
  simp only [mults, Finset.mem_filter, Finset.mem_union, Finset.mem_range]
  constructor
  · rintro ⟨hr, hnpos, d, hdmem, hdvd⟩
    simp only [List.mem_cons] at hdmem
    rcases hdmem with hdc | hdmem
    · exact Or.inl ⟨hr, hnpos, by simpa [hdc] using hdvd⟩
    · exact Or.inr ⟨hr, hnpos, d, hdmem, hdvd⟩
  · rintro (hleft | hright)
    · rcases hleft with ⟨hr, hnpos, d, hdmem, hdvd⟩
      simp only [List.mem_cons] at hdmem
      rcases hdmem with hdc | hdc
      · exact ⟨hr, hnpos, c, by simp, by simpa [hdc] using hdvd⟩
      · cases hdc
    · rcases hright with ⟨hr, hnpos, d, hdmem, hdvd⟩
      exact ⟨hr, hnpos, d, by simp [hdmem], hdvd⟩

/-- The intersection of "multiple of `c`" with the union for `cs` is the union
over `lcm c d` for `d ∈ cs`. -/
lemma mults_inter (c : Nat) (cs : List Nat) (X : Nat) :
    mults [c] X ∩ mults cs X = mults (cs.map (fun d => lcm c d)) X := by
  ext n
  simp only [mults, Finset.mem_filter, Finset.mem_inter, Finset.mem_range]
  constructor
  · rintro ⟨⟨hr, hnpos, hc_dvd⟩, ⟨_, _, d, hdmem, hdvd⟩⟩
    rcases hc_dvd with ⟨e, he_mem, he_dvd⟩
    simp only [List.mem_cons] at he_mem
    rcases he_mem with hec | hec
    · refine ⟨hr, hnpos, lcm c d, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨d, hdmem, rfl⟩
      · rw [hec] at he_dvd
        exact lcm_dvd_iff.mpr ⟨he_dvd, hdvd⟩
    · cases hec
  · rintro ⟨hr, hnpos, e, he_map, hdvd⟩
    rcases List.mem_map.mp he_map with ⟨d, hdmem, hle⟩
    rw [← hle] at hdvd
    have hcd := lcm_dvd_iff.mp hdvd
    exact ⟨⟨hr, hnpos, c, by simp, hcd.1⟩, hr, hnpos, d, hdmem, hcd.2⟩

/-- Recurrence: the count for `c :: cs` is `X/c` plus the count for `cs`, minus
the count for the pairwise lcms `lcm c d` (inclusion–exclusion on the list). -/
lemma countAtMost_cons (c : Nat) (cs : List Nat) (X : Nat) :
    countAtMost (c :: cs) X =
      X / c + countAtMost cs X - countAtMost (cs.map (fun d => lcm c d)) X := by
  unfold countAtMost
  rw [mults_cons_union c cs X]
  have hcard : (mults [c] X ∪ mults cs X).card =
      (mults [c] X).card + (mults cs X).card - (mults [c] X ∩ mults cs X).card := by
    have h := Finset.card_union_add_card_inter (mults [c] X) (mults cs X)
    omega
  rw [hcard, mults_inter c cs X, card_single c X]

/-- Fast, computable inclusion–exclusion count (the recursion tree has `2ⁿ`
nodes). -/
def countFast : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, X => X / c + countFast cs X - countFast (cs.map (fun d => lcm c d)) X
termination_by cs => cs.length
decreasing_by
  · simp
  · simp

/-- `countAtMost [] X = 0`. -/
lemma countAtMost_nil (X : Nat) : countAtMost [] X = 0 := by
  unfold countAtMost mults
  simp

/-- `countFast` agrees with the specification-level count. -/
lemma countFast_eq_countAtMost (cs : List Nat) (X : Nat) (hpos : ∀ c ∈ cs, 0 < c) :
    countFast cs X = countAtMost cs X := by
  classical
  have hmain : ∀ (m : Nat) (cs : List Nat), cs.length = m →
      (∀ c ∈ cs, 0 < c) → countFast cs X = countAtMost cs X := by
    intro m
    induction m using Nat.strong_induction_on with
    | h n ih =>
        intro cs hlen hpos
        cases cs with
        | nil =>
            rw [countFast.eq_1, countAtMost_nil]
        | cons c cs =>
            rw [countFast.eq_2]
            have hc : 0 < c := hpos c (by simp)
            have hposCs : ∀ d ∈ cs, 0 < d := by
              intro d hd
              exact hpos d (by simp [hd])
            have hposMap : ∀ d ∈ cs.map (fun d => lcm c d), 0 < d := by
              intro d hd
              rcases List.mem_map.mp hd with ⟨e, he, rfl⟩
              exact Nat.lcm_pos hc (hposCs e he)
            have ihCs := ih (cs.length) (by rw [← hlen]; simp) cs rfl hposCs
            have ihMap := ih ((cs.map (fun d => lcm c d)).length) (by rw [← hlen]; simp)
              (cs.map (fun d => lcm c d)) rfl hposMap
            rw [ihCs, ihMap]
            exact (countAtMost_cons c cs X).symm
  exact hmain cs.length cs rfl hpos

/-- `countFast ms 0 = 0`. -/
lemma countFast_zero (cs : List Nat) : countFast cs 0 = 0 := by
  have hmain : ∀ (m : Nat) (cs : List Nat), cs.length = m → countFast cs 0 = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h n ih =>
        intro cs hlen
        cases cs with
        | nil =>
            rw [countFast.eq_1]
        | cons c cs =>
            rw [countFast.eq_2]
            have ihCs := ih (cs.length) (by rw [← hlen]; simp) cs rfl
            have ihMap := ih ((cs.map (fun d => lcm c d)).length) (by rw [← hlen]; simp)
              (cs.map (fun d => lcm c d)) rfl
            rw [ihCs, ihMap]
            simp
  exact hmain cs.length cs rfl

/-- `countFast` is monotone in `X`. -/
lemma countFast_mono (cs : List Nat) (hpos : ∀ c ∈ cs, 0 < c) : Monotone (countFast cs) := by
  intro X Y hXY
  rw [countFast_eq_countAtMost cs X hpos, countFast_eq_countAtMost cs Y hpos]
  unfold countAtMost mults
  apply Finset.card_mono
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hn_range, hn_mult⟩
  refine Finset.mem_filter.mpr ⟨?_, hn_mult⟩
  have hnlt : n < X + 1 := Finset.mem_range.mp hn_range
  exact Finset.mem_range.mpr (by omega)

/-- Membership in `multiples cs` is "positive and divisible by some coin". -/
lemma mem_multiples_iff (cs : List Nat) (n : Nat) (hpos : ∀ c ∈ cs, 0 < c) :
    n ∈ multiples cs ↔ 0 < n ∧ ∃ c ∈ cs, c ∣ n := by
  unfold multiples
  constructor
  · rintro ⟨q, c, hmem, hq1, hmul⟩
    have hcpos : 0 < c := hpos c hmem
    refine ⟨?_, c, hmem, ⟨q, hmul.symm⟩⟩
    rw [← hmul]
    exact Nat.mul_pos hcpos (by omega : 0 < q)
  · rintro ⟨hnpos, c, hmem, hdiv⟩
    rcases hdiv with ⟨q, hq⟩
    refine ⟨q, c, hmem, ?_, hq.symm⟩
    have hcpos : 0 < c := hpos c hmem
    have hqpos : 0 < q := by
      by_contra hq0
      have : q = 0 := by omega
      subst q
      simp at hq
      omega
    omega

/-- `countAtMost cs X` equals `Nat.count` of membership in `multiples cs` at
`X + 1`. -/
lemma countAtMost_eq_count (cs : List Nat) (X : Nat) (hpos : ∀ c ∈ cs, 0 < c) :
    countAtMost cs X = Nat.count (fun n => n ∈ multiples cs) (X + 1) := by
  unfold countAtMost mults
  rw [Nat.count_eq_card_filter_range (n := X + 1)]
  congr 1
  refine Finset.ext ?_
  intro n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hn, hnpos, c, hmem, hdvd⟩
    rw [Finset.mem_range] at hn ⊢
    exact ⟨hn, (mem_multiples_iff cs n hpos).mpr ⟨hnpos, c, hmem, hdvd⟩⟩
  · rintro ⟨hn, hmult⟩
    rw [Finset.mem_range] at hn ⊢
    have hm := (mem_multiples_iff cs n hpos).mp hmult
    rcases hm with ⟨hnpos, c, hmem, hdvd⟩
    exact ⟨hn, hnpos, c, hmem, hdvd⟩

/-- The set of multiples is infinite. -/
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

/-- Under the hypotheses, `k ≤ Nat.count (· ∈ multiples ms) (k * M + 1)`. -/
lemma count_multiples_ge_bound (ms : List Nat) (k : Nat)
    (hms : ms ≠ []) (hpos : ∀ m ∈ ms, 0 < m) :
    k ≤ Nat.count (fun n => n ∈ multiples ms) (k * ms.foldr max 1 + 1) := by
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
      Nat.count (fun n => n ∈ multiples ms) (k * ms.foldr max 1 + 1) := by
    apply Nat.count_monotone
    have hmulk : m * k ≤ ms.foldr max 1 * k := Nat.mul_le_mul_right k hmle
    rw [Nat.mul_comm (ms.foldr max 1) k] at hmulk
    omega
  exact le_trans (le_trans hkP hmono1) hmono2

/-- Under the hypotheses, `countAtMost ms (k * M)` reaches `k`. -/
lemma countAtMost_ge (ms : List Nat) (k : Nat)
    (hms : ms ≠ []) (hpos : ∀ m ∈ ms, 0 < m) :
    k ≤ countAtMost ms (k * ms.foldr max 1) := by
  rw [countAtMost_eq_count ms (k * ms.foldr max 1) hpos]
  exact count_multiples_ge_bound ms k hms hpos

/-! ### Binary search -/

/-- Least `x ∈ (lo, hi]` with `k ≤ f x` for a monotone `f`, found by binary
search. -/
def bsearch (f : Nat → Nat) (k : Nat) (lo hi : Nat) : Nat :=
  if hi - lo ≤ 1 then
    hi
  else
    let mid := lo + (hi - lo) / 2
    if k ≤ f mid then
      bsearch f k lo mid
    else
      bsearch f k mid hi
termination_by hi - lo
decreasing_by
  · have h1 : (hi - lo) / 2 < hi - lo := Nat.div_lt_self (by omega) (by decide)
    have h2 : lo + (hi - lo) / 2 - lo < hi - lo := by
      rw [Nat.add_sub_cancel_left]
      exact h1
    exact h2
  · have hdiv : 0 < (hi - lo) / 2 := Nat.div_pos (by omega : 2 ≤ hi - lo) (by decide)
    have h2 : hi - (lo + (hi - lo) / 2) = hi - lo - ((hi - lo) / 2) := by omega
    rw [h2]
    omega

lemma bsearch_eq_base (f : Nat → Nat) (k lo hi : Nat) (h : hi - lo ≤ 1) :
    bsearch f k lo hi = hi := by
  rw [bsearch]
  simp [h]

lemma bsearch_eq_rec_lo (f : Nat → Nat) (k lo hi : Nat) (h : ¬ hi - lo ≤ 1)
    (hmid : k ≤ f (lo + (hi - lo) / 2)) :
    bsearch f k lo hi = bsearch f k lo (lo + (hi - lo) / 2) := by
  rw [bsearch]
  simp [h, hmid]

lemma bsearch_eq_rec_hi (f : Nat → Nat) (k lo hi : Nat) (h : ¬ hi - lo ≤ 1)
    (hmid : ¬ k ≤ f (lo + (hi - lo) / 2)) :
    bsearch f k lo hi = bsearch f k (lo + (hi - lo) / 2) hi := by
  rw [bsearch]
  simp [h, hmid]

/-- The result `r = bsearch f k lo hi` satisfies `lo < r ≤ hi`, `k ≤ f r`, and
`f (r - 1) < k` (i.e. `r` is the least index with `k ≤ f r`). -/
lemma bsearch_spec (f : Nat → Nat) (k : Nat) :
    ∀ lo hi, lo < hi → f lo < k → k ≤ f hi →
      lo < bsearch f k lo hi ∧ bsearch f k lo hi ≤ hi ∧
        k ≤ f (bsearch f k lo hi) ∧ f (bsearch f k lo hi - 1) < k := by
  intro lo hi hlt hlo hhi
  induction h : hi - lo using Nat.strong_induction_on generalizing lo hi with
  | h n ih =>
      by_cases hb : hi - lo ≤ 1
      · rw [bsearch_eq_base f k lo hi hb]
        have hhi' : hi - 1 = lo := by omega
        exact ⟨hlt, le_rfl, hhi, by rw [hhi']; exact hlo⟩
      · by_cases hmid : k ≤ f (lo + (hi - lo) / 2)
        · rw [bsearch_eq_rec_lo f k lo hi hb hmid]
          have hmid_lo : lo < lo + (hi - lo) / 2 := by
            have hdiv : 0 < (hi - lo) / 2 := Nat.div_pos (by omega : 2 ≤ hi - lo) (by decide)
            omega
          have hsub : (lo + (hi - lo) / 2) - lo < hi - lo := by
            rw [Nat.add_sub_cancel_left]
            exact Nat.div_lt_self (by omega : 0 < hi - lo) (by decide)
          have hrec := ih ((lo + (hi - lo) / 2) - lo) (h ▸ hsub) lo (lo + (hi - lo) / 2) hmid_lo hlo hmid rfl
          rcases hrec with ⟨rlo, rhi, rk, rprev⟩
          refine ⟨rlo, ?_, rk, rprev⟩
          have hmid_le : lo + (hi - lo) / 2 ≤ hi := by
            have hdiv : (hi - lo) / 2 < hi - lo := Nat.div_lt_self (by omega) (by decide)
            omega
          exact le_trans rhi hmid_le
        · rw [bsearch_eq_rec_hi f k lo hi hb hmid]
          have hlo_mid : lo < lo + (hi - lo) / 2 := by
            have hdiv : 0 < (hi - lo) / 2 := Nat.div_pos (by omega : 2 ≤ hi - lo) (by decide)
            omega
          have hmid_hi : lo + (hi - lo) / 2 < hi := by
            have hdiv : (hi - lo) / 2 < hi - lo := Nat.div_lt_self (by omega) (by decide)
            omega
          have hfmid : f (lo + (hi - lo) / 2) < k := by omega
          have hsub : hi - (lo + (hi - lo) / 2) < hi - lo := by
            have hdiv : 0 < (hi - lo) / 2 := Nat.div_pos (by omega : 2 ≤ hi - lo) (by decide)
            have h2 : hi - (lo + (hi - lo) / 2) = hi - lo - ((hi - lo) / 2) := by omega
            rw [h2]
            omega
          have hrec := ih (hi - (lo + (hi - lo) / 2)) (h ▸ hsub) (lo + (hi - lo) / 2) hi hmid_hi hfmid hhi rfl
          rcases hrec with ⟨rlo, rhi, rk, rprev⟩
          exact ⟨lt_trans hlo_mid rlo, rhi, rk, rprev⟩

/-! ### The submission -/

/-- `solution ms k` is the `k`-th smallest positive multiple of any element of
`ms` (1-indexed), found by binary search over the answer with an
inclusion–exclusion counting oracle. -/
def solution (ms : List Nat) (k : Nat) : Nat :=
  bsearch (countFast ms) k 0 (k * ms.foldr max 1)

theorem solution_is_valid
    (ms : List Nat)
    (k : Nat)
    (hms : ms ≠ [])
    (hpos : ∀ m ∈ ms, 0 < m)
    (hk : 0 < k) :
    solution ms k = kthSmallest (multiples ms) k := by
  classical
  unfold kthSmallest solution
  let p : Nat → Prop := fun n => n ∈ multiples ms
  let hi := k * ms.foldr max 1
  have hpInf : (setOf p).Infinite := multiples_infinite ms hms hpos
  have hzero : countFast ms 0 = 0 := countFast_zero ms
  have hlo : countFast ms 0 < k := by rw [hzero]; exact hk
  have hhi : k ≤ countFast ms hi := by
    change k ≤ countFast ms (k * ms.foldr max 1)
    rw [countFast_eq_countAtMost ms (k * ms.foldr max 1) hpos]
    exact countAtMost_ge ms k hms hpos
  have hMpos : 0 < ms.foldr max 1 := by
    rcases List.exists_mem_of_ne_nil ms hms with ⟨m, hmem⟩
    exact Nat.lt_of_lt_of_le (hpos m hmem) (mem_le_foldr_max ms hmem)
  have hlt : 0 < hi := by
    change 0 < k * ms.foldr max 1
    exact Nat.mul_pos hk hMpos
  have hspec := bsearch_spec (countFast ms) k 0 hi hlt hlo hhi
  set r : Nat := bsearch (countFast ms) k 0 hi
  rcases hspec with ⟨hrpos, hrhi, hrk, hrprev⟩
  have hf_r : countFast ms r = Nat.count p (r + 1) := by
    rw [countFast_eq_countAtMost ms r hpos, countAtMost_eq_count ms r hpos]
  have hf_r1 : countFast ms (r - 1) = Nat.count p r := by
    rw [countFast_eq_countAtMost ms (r - 1) hpos, countAtMost_eq_count ms (r - 1) hpos]
    have hb : 0 < r := hrpos
    have hsub : r - 1 + 1 = r := by omega
    rw [hsub]
  have hcount_lo : Nat.count p r < k := by
    rw [← hf_r1]
    exact hrprev
  have hcount_hi : k ≤ Nat.count p (r + 1) := by
    rw [← hf_r]
    exact hrk
  have hcount_succ : Nat.count p (r + 1) =
      Nat.count p r + (if p r then 1 else 0) := by
    rw [Nat.count_succ]
  have hpr : p r := by
    by_contra hnp
    rw [if_neg hnp] at hcount_succ
    omega
  have hcount_eq : Nat.count p r = k - 1 := by
    rw [if_pos hpr] at hcount_succ
    omega
  have hnth : Nat.nth p (k - 1) = r := by
    have hnth' : Nat.nth p (Nat.count p r) = r := Nat.nth_count hpr
    rw [hcount_eq] at hnth'
    exact hnth'
  exact hnth.symm


end Anon5
