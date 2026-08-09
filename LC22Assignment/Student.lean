import LC22Assignment.Spec

namespace LC22.Student

open LC22

-- Backtracking generator.
-- gen op cl produces every string with exactly `op` '(' and `cl` ')',
-- such that every prefix has balance ≥ op - cl (so no cheap enumeration).
-- Only feasible partials are ever explored: from (op+1, cl+1) we place
-- '(' unconditionally, but '(' is only placed when there is room (op < cl).
def gen : Nat → Nat → List (List Char)
  | 0, 0 => [[]]
  | 0, cl+1 => (gen 0 cl).map (fun s => ')' :: s)
  | _+1, 0 => []
  | op+1, cl+1 =>
      (gen op (cl+1)).map (fun s => '(' :: s) ++
      (if op < cl then (gen (op+1) cl).map (fun s => ')' :: s) else [])
termination_by op cl => op + cl

def generateAllValidParentheses (n : Nat) : List (List Char) := gen n n

-- Basic char lemma
private theorem paren_open_ne_close : ('(' : Char) ≠ ')' := by decide

-- countOpenClose helpers
theorem countOC_open (xs : List Char) : countOpenClose ('(' :: xs) = countOpenClose xs + 1 := by
  simp [countOpenClose]

theorem countOC_close (xs : List Char) : countOpenClose (')' :: xs) = countOpenClose xs - 1 := by
  simp [countOpenClose]

-- containsOnlyParentheses helpers
theorem containsOnlyParens_nil : containsOnlyParentheses [] := by
  intro c hc; simp at hc

theorem containsOnlyParens_cons {c : Char} {xs : List Char} :
    containsOnlyParentheses (c :: xs) ↔
      (c = '(' ∨ c = ')') ∧ containsOnlyParentheses xs := by
  unfold containsOnlyParentheses
  constructor
  · intro h
    refine ⟨h c ?_, ?_⟩
    · rw [List.mem_cons]; left; rfl
    · intro c' hc'
      exact h c' (by rw [List.mem_cons]; right; exact hc')
  · rintro ⟨hc, hxs⟩ c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | h
    · exact hc
    · exact hxs c' h

-- isPrefix helpers
theorem isPrefix_cons_iff {p : List Char} {c : Char} {cs : List Char} :
    isPrefix p (c :: cs) ↔ p = [] ∨ ∃ p', p = c :: p' ∧ isPrefix p' cs := by
  unfold isPrefix
  constructor
  · rintro ⟨rest, hr⟩
    cases p with
    | nil => left; rfl
    | cons c' p' =>
      right
      simp at hr
      exact ⟨p', by rw [hr.1], rest, hr.2⟩
  · rintro (rfl | ⟨p', rfl, rest, hr⟩)
    · exact ⟨c :: cs, rfl⟩
    · exact ⟨rest, by simp [hr]⟩

theorem isPrefix_nil_iff {p : List Char} : isPrefix p [] ↔ p = [] := by
  unfold isPrefix
  constructor
  · rintro ⟨rest, hr⟩
    cases p with
    | nil => rfl
    | cons _ _ => simp at hr
  · rintro rfl; exact ⟨[], rfl⟩

-- countOpenClose is bounded by ±length when only parens
theorem count_bounds (s : List Char) (h : containsOnlyParentheses s) :
    -(s.length : Int) ≤ countOpenClose s ∧ countOpenClose s ≤ (s.length : Int) := by
  induction s with
  | nil => simp [countOpenClose]
  | cons c cs ih =>
    rw [containsOnlyParens_cons] at h
    obtain ⟨hc, hcs⟩ := h
    obtain ⟨ih1, ih2⟩ := ih hcs
    have hlen : (((c :: cs).length : Nat) : Int) = (cs.length : Int) + 1 := by
      simp only [List.length_cons]; omega
    rcases hc with rfl | rfl
    · rw [countOC_open]
      refine ⟨?_, ?_⟩ <;> (rw [hlen]; omega)
    · rw [countOC_close]
      refine ⟨?_, ?_⟩ <;> (rw [hlen]; omega)

-- Main equivalence for gen
theorem gen_iff : ∀ (N : Nat) (op cl : Nat), op + cl = N → op ≤ cl → ∀ (s : List Char),
    s ∈ gen op cl ↔
      s.length = op + cl ∧
      containsOnlyParentheses s ∧
      countOpenClose s = (op : Int) - (cl : Int) ∧
      (∀ p, isPrefix p s → countOpenClose p ≥ (op : Int) - (cl : Int)) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro op cl hN hle s
    match op, cl with
    | 0, 0 =>
      simp only [gen, List.mem_singleton]
      constructor
      · rintro rfl
        refine ⟨rfl, containsOnlyParens_nil, by simp [countOpenClose], ?_⟩
        intro p hp
        rw [isPrefix_nil_iff] at hp
        subst hp
        simp [countOpenClose]
      · rintro ⟨hlen, _, _, _⟩
        cases s with
        | nil => rfl
        | cons _ _ => simp at hlen
    | 0, cl+1 =>
      simp only [gen, List.mem_map]
      have ih' := ih cl (by omega) 0 cl (by omega) (Nat.zero_le _)
      constructor
      · rintro ⟨s', hs', rfl⟩
        obtain ⟨hlen, hcp, hcnt, hpre⟩ := (ih' s').mp hs'
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [hlen]
        · rw [containsOnlyParens_cons]; exact ⟨Or.inr rfl, hcp⟩
        · rw [countOC_close]; omega
        · intro p hp
          rw [isPrefix_cons_iff] at hp
          rcases hp with rfl | ⟨p', rfl, hpr⟩
          · simp only [countOpenClose]; omega
          · rw [countOC_close]
            have := hpre p' hpr
            omega
      · rintro ⟨hlen, hcp, hcnt, hpre⟩
        cases s with
        | nil => simp at hlen
        | cons c cs =>
          rw [containsOnlyParens_cons] at hcp
          obtain ⟨hc, hcs_cp⟩ := hcp
          have hcs_len : cs.length = cl := by simp at hlen; omega
          have hc_close : c = ')' := by
            rcases hc with h_open | h_close
            · exfalso
              subst h_open
              rw [countOC_open] at hcnt
              obtain ⟨hlb, _⟩ := count_bounds cs hcs_cp
              rw [hcs_len] at hlb
              omega
            · exact h_close
          subst hc_close
          rw [countOC_close] at hcnt
          have hcs_cnt : countOpenClose cs = (0 : Int) - (cl : Int) := by omega
          have hcs_pre : ∀ p', isPrefix p' cs → countOpenClose p' ≥ (0 : Int) - (cl : Int) := by
            intro p' hpr
            have hp : isPrefix (')' :: p') (')' :: cs) := by
              rw [isPrefix_cons_iff]; exact Or.inr ⟨p', rfl, hpr⟩
            have := hpre _ hp
            rw [countOC_close] at this
            omega
          refine ⟨cs, (ih' cs).mpr ⟨?_, hcs_cp, hcs_cnt, hcs_pre⟩, rfl⟩
          omega
    | op+1, 0 =>
      exact absurd hle (by omega)
    | op+1, cl+1 =>
      simp only [gen, List.mem_append]
      have ih_open := ih (op + (cl + 1)) (by omega) op (cl + 1) rfl (by omega)
      constructor
      · rintro (h1 | h2)
        · rw [List.mem_map] at h1
          obtain ⟨s', hs', rfl⟩ := h1
          obtain ⟨hlen', hcp', hcnt', hpre'⟩ := (ih_open s').mp hs'
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp [hlen']; omega
          · rw [containsOnlyParens_cons]; exact ⟨Or.inl rfl, hcp'⟩
          · rw [countOC_open]; omega
          · intro p hp
            rw [isPrefix_cons_iff] at hp
            rcases hp with rfl | ⟨p', rfl, hpr⟩
            · simp only [countOpenClose]; omega
            · rw [countOC_open]
              have := hpre' p' hpr
              omega
        · by_cases hlt : op < cl
          · rw [if_pos hlt, List.mem_map] at h2
            obtain ⟨s', hs', rfl⟩ := h2
            have ih_close := ih ((op + 1) + cl) (by omega) (op + 1) cl (by omega) (by omega)
            obtain ⟨hlen', hcp', hcnt', hpre'⟩ := (ih_close s').mp hs'
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp [hlen']; omega
            · rw [containsOnlyParens_cons]; exact ⟨Or.inr rfl, hcp'⟩
            · rw [countOC_close]; omega
            · intro p hp
              rw [isPrefix_cons_iff] at hp
              rcases hp with rfl | ⟨p', rfl, hpr⟩
              · simp only [countOpenClose]; omega
              · rw [countOC_close]
                have := hpre' p' hpr
                omega
          · rw [if_neg hlt] at h2
            cases h2
      · rintro ⟨hlen, hcp, hcnt, hpre⟩
        cases s with
        | nil => simp at hlen
        | cons c cs =>
          rw [containsOnlyParens_cons] at hcp
          obtain ⟨hc, hcs_cp⟩ := hcp
          have hcs_len : cs.length = op + 1 + cl := by simp at hlen; omega
          rcases hc with rfl | rfl
          · left
            rw [List.mem_map]
            rw [countOC_open] at hcnt
            have hcs_cnt : countOpenClose cs = (op : Int) - (cl + 1) := by omega
            have hcs_pre : ∀ p', isPrefix p' cs → countOpenClose p' ≥ (op : Int) - (cl + 1) := by
              intro p' hpr
              have hp : isPrefix ('(' :: p') ('(' :: cs) := by
                rw [isPrefix_cons_iff]; exact Or.inr ⟨p', rfl, hpr⟩
              have := hpre _ hp
              rw [countOC_open] at this
              omega
            have hcs_len' : cs.length = op + (cl + 1) := by omega
            exact ⟨cs, (ih_open cs).mpr ⟨hcs_len', hcs_cp, hcs_cnt, hcs_pre⟩, rfl⟩
          · right
            have hlt : op < cl := by
              have hp : isPrefix [')'] (')' :: cs) := ⟨cs, rfl⟩
              have := hpre [')'] hp
              simp [countOpenClose] at this
              omega
            rw [if_pos hlt, List.mem_map]
            rw [countOC_close] at hcnt
            have hcs_cnt : countOpenClose cs = (op + 1 : Int) - cl := by omega
            have hcs_pre : ∀ p', isPrefix p' cs → countOpenClose p' ≥ (op + 1 : Int) - cl := by
              intro p' hpr
              have hp : isPrefix (')' :: p') (')' :: cs) := by
                rw [isPrefix_cons_iff]; exact Or.inr ⟨p', rfl, hpr⟩
              have := hpre _ hp
              rw [countOC_close] at this
              omega
            have ih_close := ih ((op + 1) + cl) (by omega) (op + 1) cl (by omega) (by omega)
            have hcs_len' : cs.length = op + 1 + cl := by omega
            exact ⟨cs, (ih_close cs).mpr ⟨hcs_len', hcs_cp, hcs_cnt, hcs_pre⟩, rfl⟩

theorem generated_is_valid :
    ∀ (n : Nat) (s : List Char),
      s ∈ generateAllValidParentheses n →
        s.length = 2 * n ∧ isValidParentheses s := by
  intro n s hs
  unfold generateAllValidParentheses at hs
  obtain ⟨hlen, hcp, hcnt, hpre⟩ := (gen_iff (n + n) n n rfl (Nat.le_refl _) s).mp hs
  refine ⟨by omega, hcp, ?_, ?_⟩
  · omega
  · intro p hp
    have := hpre p hp
    omega

theorem valid_is_generated :
    ∀ (n : Nat) (s : List Char),
      s.length = 2 * n →
      isValidParentheses s →
      s ∈ generateAllValidParentheses n := by
  intro n s hlen ⟨hcp, hcnt, hpre⟩
  unfold generateAllValidParentheses
  apply (gen_iff (n + n) n n rfl (Nat.le_refl _) s).mpr
  refine ⟨by omega, hcp, ?_, ?_⟩
  · omega
  · intro p hp
    have := hpre p hp
    omega

theorem algorithmSolvesLeetCode22 :
    ∀ (n : Nat) (s : List Char),
      (s.length = 2 * n ∧ isValidParentheses s) ↔
        s ∈ generateAllValidParentheses n := by
  intro n s
  constructor
  · intro h
    exact valid_is_generated n s h.1 h.2
  · intro h
    exact generated_is_valid n s h

end LC22.Student
