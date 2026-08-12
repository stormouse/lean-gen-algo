import Anon2Assignment.Spec

namespace Anon2.Student

open Anon2

/-! ### Enumerating every contiguous sublist

`isSub a s` says `s` sits inside `a` as a contiguous block, i.e. `s` is a prefix of
some suffix of `a`.  Since `a` is finite there are only finitely many such blocks,
so we can simply list them all and pick the longest good one. -/

/-- Every prefix of `l`, shortest first. -/
def prefixes : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => [] :: (prefixes xs).map (fun p => x :: p)

/-- Every contiguous sublist of `a`: the prefixes of each of its suffixes. -/
def cands : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => prefixes (x :: xs) ++ cands xs

theorem nil_mem_prefixes : ∀ l : List Nat, [] ∈ prefixes l
  | [] => by simp [prefixes]
  | _ :: _ => by simp [prefixes]

theorem mem_prefixes_append : ∀ s suf : List Nat, s ∈ prefixes (s ++ suf)
  | [], suf => nil_mem_prefixes suf
  | x :: xs, suf => by
      simp only [List.cons_append, prefixes, List.mem_cons, List.mem_map]
      exact Or.inr ⟨xs, mem_prefixes_append xs suf, rfl⟩

theorem prefixes_spec : ∀ l s : List Nat, s ∈ prefixes l → ∃ suf, l = s ++ suf
  | [], s, h => by
      simp only [prefixes, List.mem_cons, List.not_mem_nil, or_false] at h
      exact ⟨[], by simp [h]⟩
  | x :: xs, s, h => by
      simp only [prefixes, List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨p, hp, rfl⟩
      · exact ⟨x :: xs, by simp [h]⟩
      · obtain ⟨suf, hsuf⟩ := prefixes_spec xs p hp
        exact ⟨suf, by simp [hsuf]⟩

theorem mem_cands_of_isSub (a : List Nat) : ∀ s : List Nat, isSub a s → s ∈ cands a := by
  induction a with
  | nil =>
      intro s h
      obtain ⟨pre, suf, h⟩ := h
      have hs : s = [] := by
        cases pre <;> cases s <;> simp_all
      subst hs
      simp [cands]
  | cons x xs ih =>
      intro s h
      obtain ⟨pre, suf, h⟩ := h
      simp only [cands, List.mem_append]
      cases pre with
      | nil =>
          simp only [List.nil_append] at h
          refine Or.inl ?_
          rw [h]
          exact mem_prefixes_append s suf
      | cons p ps =>
          simp only [List.cons_append] at h
          injection h with _ hxs
          exact Or.inr (ih s ⟨ps, suf, hxs⟩)

theorem isSub_of_mem_cands (a : List Nat) : ∀ s : List Nat, s ∈ cands a → isSub a s := by
  induction a with
  | nil =>
      intro s h
      simp only [cands, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      exact ⟨[], [], rfl⟩
  | cons x xs ih =>
      intro s h
      simp only [cands, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨suf, hsuf⟩ := prefixes_spec (x :: xs) s h
        exact ⟨[], suf, by simpa using hsuf⟩
      · obtain ⟨pre, suf, hp⟩ := ih s h
        exact ⟨x :: pre, suf, by simp [hp]⟩

/-! ### Deciding goodness -/

/-- Boolean version of `isGood`. -/
def goodB (s : List Nat) (k : Nat) : Bool :=
  s.all (fun x => decide (s.count x ≤ k))

theorem goodB_iff (s : List Nat) (k : Nat) : goodB s k = true ↔ isGood s k := by
  simp [goodB, isGood]

/-! ### Picking a longest element -/

/-- The longest list among `l`, defaulting to `acc` when nothing beats it. -/
def bestOf : List (List Nat) → List Nat → List Nat
  | [], acc => acc
  | s :: t, acc => bestOf t (if acc.length < s.length then s else acc)

theorem bestOf_eq_or_mem : ∀ (l : List (List Nat)) (acc : List Nat),
    bestOf l acc = acc ∨ bestOf l acc ∈ l := by
  intro l
  induction l with
  | nil => intro acc; exact Or.inl rfl
  | cons s t ih =>
      intro acc
      by_cases hlt : acc.length < s.length
      · rw [bestOf, if_pos hlt]
        rcases ih s with h | h
        · exact Or.inr (by simp [h])
        · exact Or.inr (by simp [h])
      · rw [bestOf, if_neg hlt]
        rcases ih acc with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])

theorem le_bestOf_acc : ∀ (l : List (List Nat)) (acc : List Nat),
    acc.length ≤ (bestOf l acc).length := by
  intro l
  induction l with
  | nil => intro acc; exact Nat.le_refl _
  | cons s t ih =>
      intro acc
      by_cases hlt : acc.length < s.length
      · rw [bestOf, if_pos hlt]
        exact Nat.le_trans (Nat.le_of_lt hlt) (ih s)
      · rw [bestOf, if_neg hlt]
        exact ih acc

theorem le_bestOf : ∀ (l : List (List Nat)) (acc s : List Nat),
    s ∈ l → s.length ≤ (bestOf l acc).length := by
  intro l
  induction l with
  | nil => intro acc s h; cases h
  | cons u t ih =>
      intro acc s h
      rcases List.mem_cons.mp h with rfl | h
      · by_cases hlt : acc.length < s.length
        · rw [bestOf, if_pos hlt]
          exact le_bestOf_acc t s
        · rw [bestOf, if_neg hlt]
          exact Nat.le_trans (Nat.le_of_not_lt hlt) (le_bestOf_acc t acc)
      · by_cases hlt : acc.length < u.length
        · rw [bestOf, if_pos hlt]
          exact ih u s h
        · rw [bestOf, if_neg hlt]
          exact ih acc s h

/-! ### The solution -/

def solve (a : List Nat) (k : Nat) : List Nat :=
  bestOf ((cands a).filter (fun s => goodB s k)) []

theorem solve_nil_or_mem (a : List Nat) (k : Nat) :
    solve a k = [] ∨ solve a k ∈ (cands a).filter (fun s => goodB s k) :=
  bestOf_eq_or_mem _ _

theorem solve_good (a : List Nat) (k : Nat) : isGood (solve a k) k := by
  rcases solve_nil_or_mem a k with h | h
  · rw [h]; intro x hx; cases hx
  · exact (goodB_iff _ _).mp (List.mem_filter.mp h).2

theorem solve_isSub (a : List Nat) (k : Nat) : isSub a (solve a k) := by
  rcases solve_nil_or_mem a k with h | h
  · exact ⟨a, [], by rw [h]; simp⟩
  · exact isSub_of_mem_cands a _ (List.mem_filter.mp h).1

theorem solve_max (a : List Nat) (k : Nat) (alt : List Nat)
    (hg : isGood alt k) (hs : isSub a alt) : alt.length ≤ (solve a k).length :=
  le_bestOf _ _ _ (List.mem_filter.mpr ⟨mem_cands_of_isSub a alt hs, (goodB_iff _ _).mpr hg⟩)

theorem solution_is_valid (a : List Nat) (k : Nat) :
    let sol := solve a k
    isGood sol k ∧ isSub a sol ∧
      ∀ alt, (isGood alt k ∧ isSub a alt) → alt.length ≤ sol.length :=
  ⟨solve_good a k, solve_isSub a k, fun alt h => solve_max a k alt h.1 h.2⟩

end Anon2.Student
