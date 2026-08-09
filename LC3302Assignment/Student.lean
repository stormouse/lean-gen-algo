import LC3302Assignment.Spec

namespace LC3302.Student

open LC3302

-- Backtracking search with a mismatch budget.
-- solveDP a b e i j = try to match b[j..] using a[i..] with at most e mismatches.
def solveDP (a b : List Char) (e i j : Nat) : Option (List Nat) :=
  if hj : j ≥ b.length then some []
  else if hi : i ≥ a.length then none
  else
    have hi' : i < a.length := Nat.lt_of_not_le hi
    have hj' : j < b.length := Nat.lt_of_not_le hj
    let ac := a[i]
    let bc := b[j]
    let matchHere : Option (List Nat) :=
      if ac = bc then
        (solveDP a b e (i+1) (j+1)).map (fun rest => i :: rest)
      else if e > 0 then
        (solveDP a b (e-1) (i+1) (j+1)).map (fun rest => i :: rest)
      else none
    match matchHere with
    | some r => some r
    | none => solveDP a b e (i+1) j
termination_by a.length - i

def findValidSequence (a b : List Char) : Option (List Nat) :=
  solveDP a b 1 0 0

/-! ### Helper definitions and lemmas -/

/-- `matchesWith s t e`: `s` and `t` have equal length and differ in at most `e` positions. -/
def matchesWith (s t : List Char) (e : Nat) : Prop :=
  ∃ h : s.length = t.length, countDiff s t h ≤ e

theorem matchesWith_nil_nil (e : Nat) : matchesWith [] [] e := by
  refine ⟨rfl, ?_⟩
  unfold countDiff
  exact Nat.zero_le _

theorem matchesWith_cons_cons_same {x : Char} {xs ys : List Char} {e : Nat}
    (h : matchesWith xs ys e) : matchesWith (x :: xs) (x :: ys) e := by
  obtain ⟨hl, hc⟩ := h
  have hl' : (x :: xs).length = (x :: ys).length := by simp [hl]
  refine ⟨hl', ?_⟩
  unfold countDiff
  rw [if_pos rfl]
  exact hc

theorem matchesWith_cons_cons_diff {x y : Char} {xs ys : List Char} {e : Nat}
    (hxy : x ≠ y) (h : matchesWith xs ys e) : matchesWith (x :: xs) (y :: ys) (e + 1) := by
  obtain ⟨hl, hc⟩ := h
  have hl' : (x :: xs).length = (y :: ys).length := by simp [hl]
  refine ⟨hl', ?_⟩
  unfold countDiff
  simp only [if_neg hxy]
  omega

/-- Inverting a `matchesWith` where both sides start with same char. -/
theorem matchesWith_cons_cons_same_inv {x : Char} {xs ys : List Char} {e : Nat}
    (h : matchesWith (x :: xs) (x :: ys) e) : matchesWith xs ys e := by
  obtain ⟨hl, hc⟩ := h
  have hl' : xs.length = ys.length := by simpa using hl
  refine ⟨hl', ?_⟩
  have := hc
  unfold countDiff at this
  rw [if_pos rfl] at this
  exact this

/-- Inverting a `matchesWith` where sides differ in head. -/
theorem matchesWith_cons_cons_diff_inv {x y : Char} {xs ys : List Char} {e : Nat}
    (hxy : x ≠ y) (h : matchesWith (x :: xs) (y :: ys) e) :
    ∃ e', e = e' + 1 ∧ matchesWith xs ys e' := by
  obtain ⟨hl, hc⟩ := h
  have hl' : xs.length = ys.length := by simpa using hl
  have hc' := hc
  unfold countDiff at hc'
  simp only [if_neg hxy] at hc'
  -- 1 + countDiff xs ys hl' ≤ e
  have he : e ≥ 1 := by omega
  refine ⟨e - 1, by omega, hl', ?_⟩
  omega

/-- `matchesWith` is impossible with different lengths. -/
theorem matchesWith_length {s t : List Char} {e : Nat}
    (h : matchesWith s t e) : s.length = t.length := h.1

/-- If lengths differ, no `matchesWith`. -/
theorem not_matchesWith_of_length_ne {s t : List Char} {e : Nat}
    (h : s.length ≠ t.length) : ¬ matchesWith s t e := by
  intro hm
  exact h hm.1

theorem matchesWith_nil_cons_none {y : Char} {ys : List Char} {e : Nat} :
    ¬ matchesWith [] (y :: ys) e := by
  intro h
  have := h.1
  simp at this

theorem matchesWith_cons_nil_none {x : Char} {xs : List Char} {e : Nat} :
    ¬ matchesWith (x :: xs) [] e := by
  intro h
  have := h.1
  simp at this

/-- `almostEqual` in terms of `matchesWith`. -/
theorem almostEqual_iff_matchesWith (s t : List Char) :
    almostEqual s t ↔ matchesWith s t 1 := by
  unfold almostEqual matchesWith
  constructor
  · intro ⟨hl, hc⟩
    exact ⟨hl, hc⟩
  · intro ⟨hl, hc⟩
    exact ⟨hl, hc⟩

/-- monotonicIncreasing helper: adding a smaller element preserves it. -/
theorem monotonicIncreasing_cons {x : Nat} {xs : List Nat}
    (h : monotonicIncreasing xs)
    (hlt : ∀ y ∈ xs.head?, x < y) : monotonicIncreasing (x :: xs) := by
  cases xs with
  | nil => unfold monotonicIncreasing; trivial
  | cons y ys =>
      have hxy : x < y := hlt y (by simp)
      unfold monotonicIncreasing
      have : ¬ x ≥ y := by omega
      simp only [if_neg this]
      exact h

theorem monotonicIncreasing_cons_lt {x y : Nat} {ys : List Nat}
    (hxy : x < y) (h : monotonicIncreasing (y :: ys)) :
    monotonicIncreasing (x :: y :: ys) := by
  unfold monotonicIncreasing
  have hn : ¬ x ≥ y := by omega
  simp only [if_neg hn]
  exact h

theorem monotonicIncreasing_tail {x : Nat} {xs : List Nat}
    (h : monotonicIncreasing (x :: xs)) : monotonicIncreasing xs := by
  cases xs with
  | nil => unfold monotonicIncreasing; trivial
  | cons y ys =>
      unfold monotonicIncreasing at h
      by_cases hxy : x ≥ y
      · rw [if_pos hxy] at h; exact h.elim
      · rw [if_neg hxy] at h; exact h

theorem monotonicIncreasing_head_lt {x y : Nat} {ys : List Nat}
    (h : monotonicIncreasing (x :: y :: ys)) : x < y := by
  unfold monotonicIncreasing at h
  by_cases hxy : x ≥ y
  · rw [if_pos hxy] at h; exact h.elim
  · omega

/-- Members of an increasing sequence starting with x are all ≥ x. -/
theorem monotonicIncreasing_mem_ge {x : Nat} {xs : List Nat}
    (h : monotonicIncreasing (x :: xs)) : ∀ y ∈ xs, x < y := by
  induction xs generalizing x with
  | nil => intro y hy; cases hy
  | cons z zs ih =>
      intro y hy
      have hxz : x < z := monotonicIncreasing_head_lt h
      have htail : monotonicIncreasing (z :: zs) := monotonicIncreasing_tail h
      rw [List.mem_cons] at hy
      rcases hy with heq | hy
      · rw [heq]; exact hxz
      · have := ih htail y hy
        omega

/-- `subsequenceByIndex` unfolding for cons. -/
theorem subsequenceByIndex_cons (a : List Char) (i : Nat) (is : List Nat) :
    subsequenceByIndex a (i :: is) =
      match a[i]?, subsequenceByIndex a is with
      | some c, some rest => some (c :: rest)
      | _, _ => none := by
  unfold subsequenceByIndex
  rw [List.mapM_cons]
  simp only [Option.bind_eq_bind]
  -- (do let c ← a[i]?; let rest ← is.mapM (a[·]?); pure (c :: rest))
  cases hac : a[i]? with
  | none => simp
  | some c =>
      simp
      cases his : (is.mapM fun i => a[i]?) with
      | none => simp
      | some rest => simp

theorem subsequenceByIndex_nil (a : List Char) :
    subsequenceByIndex a [] = some [] := rfl

/-- Members of a subsequence: if the subsequence is `some s`, indices are valid. -/
theorem subsequenceByIndex_mem_valid (a : List Char) (indices : List Nat) (s : List Char)
    (h : subsequenceByIndex a indices = some s) :
    ∀ i ∈ indices, i < a.length := by
  induction indices generalizing s with
  | nil => intro i hi; cases hi
  | cons j js ih =>
      intro i hi
      rw [subsequenceByIndex_cons] at h
      rw [List.mem_cons] at hi
      rcases hi with heq | hi
      · subst heq
        cases hac : a[i]? with
        | none => rw [hac] at h; simp at h
        | some c =>
            have := List.getElem?_eq_some_iff.mp hac
            exact this.1
      · cases hac : a[j]? with
        | none => rw [hac] at h; simp at h
        | some c =>
            rw [hac] at h
            cases his : subsequenceByIndex a js with
            | none => rw [his] at h; simp at h
            | some rest =>
                exact ih rest his i hi

/-- Length of the resulting subsequence matches indices length. -/
theorem subsequenceByIndex_length (a : List Char) (indices : List Nat) (s : List Char)
    (h : subsequenceByIndex a indices = some s) :
    s.length = indices.length := by
  induction indices generalizing s with
  | nil =>
      rw [subsequenceByIndex_nil] at h
      injection h with h; subst h; rfl
  | cons j js ih =>
      rw [subsequenceByIndex_cons] at h
      cases hac : a[j]? with
      | none => rw [hac] at h; simp at h
      | some c =>
          rw [hac] at h
          cases his : subsequenceByIndex a js with
          | none => rw [his] at h; simp at h
          | some rest =>
              rw [his] at h
              simp at h
              subst h
              simp [ih rest his]

/-! ### Main soundness/completeness of solveDP -/

/-- Statement of the property for indices at level (e, i, j). -/
def validAt (a b : List Char) (e i j : Nat) (r : List Nat) : Prop :=
  monotonicIncreasing r ∧
    (∀ k ∈ r, i ≤ k ∧ k < a.length) ∧
    ∃ s, subsequenceByIndex a r = some s ∧ matchesWith s (b.drop j) e

/-- Helper: `(b.drop j).length = b.length - j`. -/
theorem length_drop_eq (b : List Char) (j : Nat) : (b.drop j).length = b.length - j :=
  List.length_drop

/-- When `j ≥ b.length`, `b.drop j = []`. -/
theorem drop_ge_nil {b : List Char} {j : Nat} (h : j ≥ b.length) : b.drop j = [] := by
  have : (b.drop j).length = 0 := by
    rw [length_drop_eq]; omega
  exact List.length_eq_zero_iff.mp this

/-- When `j < b.length`, `b.drop j = b[j] :: b.drop (j+1)`. -/
theorem drop_lt_cons {b : List Char} {j : Nat} (h : j < b.length) :
    b.drop j = b[j] :: b.drop (j+1) :=
  List.drop_eq_getElem_cons h

/-- Membership lemma. -/
theorem mem_head_cons {α : Type _} (x : α) (xs : List α) : x ∈ x :: xs := by
  exact List.mem_cons_self

/-- Unfolding lemma for solveDP when j ≥ b.length. -/
theorem solveDP_ge (a b : List Char) (e i j : Nat) (hj : j ≥ b.length) :
    solveDP a b e i j = some [] := by
  unfold solveDP
  simp [hj]

/-- Unfolding lemma for solveDP when j < b.length and i ≥ a.length. -/
theorem solveDP_no_a (a b : List Char) (e i j : Nat) (hj : ¬ j ≥ b.length) (hi : i ≥ a.length) :
    solveDP a b e i j = none := by
  unfold solveDP
  simp [hj, hi]

/-- Soundness: if solveDP returns `some r`, then `r` is a valid solution at level (e, i, j). -/
theorem solveDP_sound (a b : List Char) :
    ∀ e i j r, solveDP a b e i j = some r → validAt a b e i j r := by
  intro e i j
  induction e, i, j using solveDP.induct a b with
  | case1 e i j hj =>
      intro r hres
      rw [solveDP_ge a b e i j hj] at hres
      injection hres with hres; subst hres
      refine ⟨?_, ?_, ?_⟩
      · unfold monotonicIncreasing; trivial
      · intro k hk; cases hk
      · refine ⟨[], rfl, ?_⟩
        rw [drop_ge_nil hj]
        exact matchesWith_nil_nil _
  | case2 e i j hj hi =>
      intro r hres
      rw [solveDP_no_a a b e i j hj hi] at hres
      cases hres
  | case3 e i j hj hi hi' hj' ac bc mH r0 hmh ih2 ih1 =>
      intro r hres
      have hj_lt : j < b.length := hj'
      have hi_lt : i < a.length := hi'
      -- Generalize mH to a fresh variable to eliminate the let-binding issue
      have h_unfold : ∀ (mH' : Option (List Nat)),
          mH' = mH →
          solveDP a b e i j = (match mH' with | some res => some res | none => solveDP a b e (i+1) j) := by
        intro mH' hmH_eq
        subst hmH_eq
        conv => lhs; unfold solveDP
        rw [dif_neg hj, dif_neg hi]
        rfl
      have h1 := h_unfold mH rfl
      rw [hmh] at h1
      rw [hres] at h1
      injection h1 with heq; subst heq
      -- Now analyze mH = some r
      by_cases hab : ac = bc
      · have hmh_val : mH = Option.map (fun rest => i :: rest) (solveDP a b e (i+1) (j+1)) := by
          show (if h : ac = bc then _ else _) = _
          rw [dif_pos hab]
        rw [hmh_val] at hmh
        cases hsub : solveDP a b e (i+1) (j+1) with
        | none =>
            rw [hsub] at hmh
            simp at hmh
        | some rest =>
            rw [hsub] at hmh
            simp at hmh
            subst hmh
            have ⟨hmono, hbounds, s, hsub_s, hmatch⟩ := ih2 rest hsub
            refine ⟨?_, ?_, ?_⟩
            · apply monotonicIncreasing_cons hmono
              intro y hy
              cases rest with
              | nil => cases hy
              | cons k ks =>
                  simp at hy; subst hy
                  have := hbounds k (by exact List.mem_cons_self)
                  omega
            · intro k hk
              rw [List.mem_cons] at hk
              rcases hk with heq | hk
              · subst heq; exact ⟨Nat.le_refl _, hi_lt⟩
              · have := hbounds k hk; exact ⟨by omega, this.2⟩
            · refine ⟨ac :: s, ?_, ?_⟩
              · rw [subsequenceByIndex_cons]
                have hac : a[i]? = some a[i] := List.getElem?_eq_getElem hi_lt
                show (match a[i]?, subsequenceByIndex a rest with
                    | some c, some r => some (c :: r)
                    | _, _ => none) = some (ac :: s)
                rw [hac, hsub_s]
              · rw [drop_lt_cons hj_lt]
                show matchesWith (ac :: s) (b[j] :: b.drop (j+1)) e
                rw [hab]
                exact matchesWith_cons_cons_same hmatch
      · by_cases he : e > 0
        · have hmh_val : mH = Option.map (fun rest => i :: rest) (solveDP a b (e-1) (i+1) (j+1)) := by
            show (if h : ac = bc then _ else _) = _
            rw [dif_neg hab, dif_pos he]
          rw [hmh_val] at hmh
          cases hsub : solveDP a b (e-1) (i+1) (j+1) with
          | none =>
              rw [hsub] at hmh
              simp at hmh
          | some rest =>
              rw [hsub] at hmh
              simp at hmh
              subst hmh
              have ⟨hmono, hbounds, s, hsub_s, hmatch⟩ := ih1 rest hsub
              refine ⟨?_, ?_, ?_⟩
              · apply monotonicIncreasing_cons hmono
                intro y hy
                cases rest with
                | nil => cases hy
                | cons k ks =>
                    simp at hy; subst hy
                    have := hbounds k (by exact List.mem_cons_self)
                    omega
              · intro k hk
                rw [List.mem_cons] at hk
                rcases hk with heq | hk
                · subst heq; exact ⟨Nat.le_refl _, hi_lt⟩
                · have := hbounds k hk; exact ⟨by omega, this.2⟩
              · refine ⟨ac :: s, ?_, ?_⟩
                · show subsequenceByIndex a (i :: rest) = some (ac :: s)
                  rw [subsequenceByIndex_cons]
                  have hac : a[i]? = some a[i] := List.getElem?_eq_getElem hi_lt
                  show (match a[i]?, subsequenceByIndex a rest with
                      | some c, some r => some (c :: r)
                      | _, _ => none) = some (ac :: s)
                  rw [hac, hsub_s]
                · rw [drop_lt_cons hj_lt]
                  show matchesWith (ac :: s) (b[j] :: b.drop (j+1)) e
                  have h1 := matchesWith_cons_cons_diff hab hmatch
                  have : e - 1 + 1 = e := by omega
                  rw [this] at h1
                  exact h1
        · have hmh_val : mH = none := by
            show (if h : ac = bc then _ else _) = _
            rw [dif_neg hab, dif_neg he]
          rw [hmh_val] at hmh
          cases hmh
  | case4 e i j hj hi hi' hj' ac bc mH hmh_none ih2 ih1 ih3 =>
      intro r hres
      have hj_lt : j < b.length := hj'
      have hi_lt : i < a.length := hi'
      -- unfold solveDP: since mH = none, result = solveDP a b e (i+1) j
      have h_unfold : ∀ (mH' : Option (List Nat)),
          mH' = mH →
          solveDP a b e i j = (match mH' with | some res => some res | none => solveDP a b e (i+1) j) := by
        intro mH' hmH_eq
        subst hmH_eq
        conv => lhs; unfold solveDP
        rw [dif_neg hj, dif_neg hi]
        rfl
      have h1 := h_unfold mH rfl
      rw [hmh_none] at h1
      -- h1 : solveDP a b e i j = solveDP a b e (i+1) j
      rw [h1] at hres
      have ⟨hmono, hbounds, s, hsub_s, hmatch⟩ := ih3 r hres
      refine ⟨hmono, ?_, s, hsub_s, hmatch⟩
      intro k hk
      have := hbounds k hk
      exact ⟨by omega, this.2⟩

/-- Completeness: if solveDP returns none, no valid solution exists at level (e, i, j). -/
theorem solveDP_none_no_valid (a b : List Char) :
    ∀ e i j, solveDP a b e i j = none → ∀ r, ¬ validAt a b e i j r := by
  intro e i j
  induction e, i, j using solveDP.induct a b with
  | case1 e i j hj =>
      intro hres
      rw [solveDP_ge a b e i j hj] at hres
      cases hres
  | case2 e i j hj hi =>
      intro _hres r ⟨hmono, hbounds, s, hsub_s, hmatch⟩
      -- r must be empty since indices >= i >= a.length and indices < a.length
      cases r with
      | nil =>
          -- s = [] but b.drop j nonempty (j < b.length)
          rw [subsequenceByIndex_nil] at hsub_s
          injection hsub_s with hsub_s; subst hsub_s
          -- matchesWith [] (b.drop j) e: length 0 = length (b.drop j)
          have hlen := hmatch.1
          have : (b.drop j).length = 0 := hlen.symm
          rw [length_drop_eq] at this
          have hj_lt : j < b.length := Nat.lt_of_not_le hj
          omega
      | cons k ks =>
          have := hbounds k (by exact List.mem_cons_self)
          omega
  | case3 e i j hj hi hi' hj' ac bc mH r0 hmh _ih2 _ih1 =>
      intro hres
      -- solveDP = some r0 ≠ none: contradiction
      exfalso
      have h_unfold : ∀ (mH' : Option (List Nat)),
          mH' = mH →
          solveDP a b e i j = (match mH' with | some res => some res | none => solveDP a b e (i+1) j) := by
        intro mH' hmH_eq
        subst hmH_eq
        conv => lhs; unfold solveDP
        rw [dif_neg hj, dif_neg hi]
        rfl
      have h1 := h_unfold mH rfl
      rw [hmh] at h1
      rw [hres] at h1
      cases h1
  | case4 e i j hj hi hi' hj' ac bc mH hmh_none ih2 ih1 ih3 =>
      intro hres r ⟨hmono, hbounds, s, hsub_s, hmatch⟩
      have hj_lt : j < b.length := hj'
      have hi_lt : i < a.length := hi'
      -- solveDP a b e i j = solveDP a b e (i+1) j = none
      have h_unfold : ∀ (mH' : Option (List Nat)),
          mH' = mH →
          solveDP a b e i j = (match mH' with | some res => some res | none => solveDP a b e (i+1) j) := by
        intro mH' hmH_eq
        subst hmH_eq
        conv => lhs; unfold solveDP
        rw [dif_neg hj, dif_neg hi]
        rfl
      have h1 := h_unfold mH rfl
      rw [hmh_none] at h1
      rw [h1] at hres
      -- ih3 : solveDP a b e (i+1) j = none → ∀ r, ¬ validAt a b e (i+1) j r
      -- Also mH = none tells us: if ac = bc then solveDP e (i+1) (j+1) = none
      --                          else if e > 0 then solveDP (e-1) (i+1) (j+1) = none
      --                          else True
      -- Analyze r
      cases r with
      | nil =>
          rw [subsequenceByIndex_nil] at hsub_s
          injection hsub_s with hsub_s; subst hsub_s
          have hlen := hmatch.1
          have : (b.drop j).length = 0 := hlen.symm
          rw [length_drop_eq] at this
          omega
      | cons k ks =>
          rw [subsequenceByIndex_cons] at hsub_s
          cases hak : a[k]? with
          | none => rw [hak] at hsub_s; simp at hsub_s
          | some ck =>
              rw [hak] at hsub_s
              cases hks : subsequenceByIndex a ks with
              | none => rw [hks] at hsub_s; simp at hsub_s
              | some ss =>
                  rw [hks] at hsub_s
                  simp at hsub_s
                  -- hsub_s : ck :: ss = s
                  subst hsub_s
                  -- Now hbounds k : i ≤ k ∧ k < a.length
                  have hkbounds := hbounds k (by exact List.mem_cons_self)
                  have hki : i ≤ k := hkbounds.1
                  have hka : k < a.length := hkbounds.2
                  -- Case: k = i or k > i
                  by_cases hki_eq : k = i
                  · -- k = i: subsequence starts with a[i] = ck
                    subst hki_eq
                    have hck : ck = a[k] := by
                      have := List.getElem?_eq_some_iff.mp hak
                      exact this.2.symm
                    -- Split by whether ac (= a[k]) = bc (= b[j])
                    by_cases hab : ac = bc
                    · -- a[k] = b[j]. Then rest must be valid at (e, k+1, j+1)
                      -- But matchHere = none means Option.map (i :: ·) (solveDP e (k+1) (j+1)) = none
                      -- => solveDP e (k+1) (j+1) = none, use ih2
                      have hmH_val : mH = Option.map (fun rest => k :: rest) (solveDP a b e (k+1) (j+1)) := by
                        show (if h : ac = bc then _ else _) = _
                        rw [dif_pos hab]
                      rw [hmH_val] at hmh_none
                      have hsub_none : solveDP a b e (k+1) (j+1) = none := by
                        cases hh : solveDP a b e (k+1) (j+1) with
                        | none => rfl
                        | some x => rw [hh] at hmh_none; simp at hmh_none
                      -- Build a valid at (e, k+1, j+1) from ss
                      apply ih2 hsub_none ks
                      refine ⟨monotonicIncreasing_tail hmono, ?_, ss, hks, ?_⟩
                      · intro k' hk'
                        -- k' ∈ ks means k' > k (monotonicity)
                        have hkk' := monotonicIncreasing_mem_ge hmono k' hk'
                        have := hbounds k' (List.mem_cons_of_mem _ hk')
                        exact ⟨by omega, this.2⟩
                      · -- matchesWith ss (b.drop (j+1)) e
                        -- We have matchesWith (ck :: ss) (b.drop j) e with a[k] = ck, b[j] = bc = ac = a[k]
                        rw [drop_lt_cons hj_lt] at hmatch
                        -- ck :: ss vs b[j] :: b.drop (j+1)
                        -- and ck = a[k] = ac = bc = b[j]
                        have h_ck_eq : ck = b[j] := by
                          rw [hck]; exact hab
                        rw [h_ck_eq] at hmatch
                        exact matchesWith_cons_cons_same_inv hmatch
                    · -- a[k] ≠ b[j], so this must have used a mismatch
                      by_cases he : e > 0
                      · -- rest is valid at (e-1, k+1, j+1)
                        have hmH_val : mH = Option.map (fun rest => k :: rest) (solveDP a b (e-1) (k+1) (j+1)) := by
                          show (if h : ac = bc then _ else _) = _
                          rw [dif_neg hab, dif_pos he]
                        rw [hmH_val] at hmh_none
                        have hsub_none : solveDP a b (e-1) (k+1) (j+1) = none := by
                          cases hh : solveDP a b (e-1) (k+1) (j+1) with
                          | none => rfl
                          | some x => rw [hh] at hmh_none; simp at hmh_none
                        apply ih1 hsub_none ks
                        refine ⟨monotonicIncreasing_tail hmono, ?_, ss, hks, ?_⟩
                        · intro k' hk'
                          have hkk' := monotonicIncreasing_mem_ge hmono k' hk'
                          have := hbounds k' (List.mem_cons_of_mem _ hk')
                          exact ⟨by omega, this.2⟩
                        · rw [drop_lt_cons hj_lt] at hmatch
                          -- matchesWith (ck :: ss) (b[j] :: b.drop (j+1)) e
                          -- ck = a[k] = ac ≠ bc = b[j]
                          have h_ck_ne_bj : ck ≠ b[j] := by
                            rw [hck]; exact hab
                          have := matchesWith_cons_cons_diff_inv h_ck_ne_bj hmatch
                          obtain ⟨e', he_eq, hm⟩ := this
                          -- e = e' + 1, so e' = e - 1
                          have : e' = e - 1 := by omega
                          rw [this] at hm
                          exact hm
                      · -- e = 0. But we need at least one mismatch. Impossible.
                        have he_eq : e = 0 := by omega
                        subst he_eq
                        rw [drop_lt_cons hj_lt] at hmatch
                        -- matchesWith (ck :: ss) (b[j] :: b.drop (j+1)) 0
                        have h_ck_ne_bj : ck ≠ b[j] := by
                          rw [hck]; exact hab
                        have := matchesWith_cons_cons_diff_inv h_ck_ne_bj hmatch
                        obtain ⟨e', he_eq, _⟩ := this
                        omega
                  · -- k > i, so ks is valid at (e, i+1, j) since all indices are > k ≥ i+1... wait need k ≥ i+1
                    have hki_gt : k > i := by omega
                    -- Build valid at (e, i+1, j) from (k :: ks) itself
                    apply ih3 hres (k :: ks)
                    refine ⟨hmono, ?_, ck :: ss, ?_, hmatch⟩
                    · intro k' hk'
                      rw [List.mem_cons] at hk'
                      rcases hk' with heq | hk'
                      · subst heq; exact ⟨hki_gt, hka⟩
                      · have hkk' := monotonicIncreasing_mem_ge hmono k' hk'
                        have := hbounds k' (List.mem_cons_of_mem _ hk')
                        exact ⟨by omega, this.2⟩
                    · rw [subsequenceByIndex_cons]
                      show (match a[k]?, subsequenceByIndex a ks with
                          | some c, some r => some (c :: r)
                          | _, _ => none) = some (ck :: ss)
                      rw [hak, hks]

/-- Any valid solution at level (e, i, j) has all indices ≥ i and < a.length. -/
-- (Already inside validAt.)

theorem no_output_iff_no_solution (a b : List Char) :
    (noValidSolution a b ↔ LC3302.Student.findValidSequence a b = none) := by
  unfold findValidSequence noValidSolution isValidSolution
  constructor
  · intro h
    cases hres : solveDP a b 1 0 0 with
    | none => rfl
    | some r =>
        exfalso
        have ⟨hmono, hbounds, s, hsub_s, hmatch⟩ := solveDP_sound a b 1 0 0 r hres
        apply h r
        refine ⟨hmono, ?_⟩
        rw [hsub_s]
        show almostEqual s b
        rw [almostEqual_iff_matchesWith]
        have : b.drop 0 = b := List.drop_zero
        rw [this] at hmatch
        exact hmatch
  · intro hres r ⟨hmono, hrest⟩
    apply solveDP_none_no_valid a b 1 0 0 hres r
    refine ⟨hmono, ?_, ?_⟩
    · intro k hk
      constructor
      · exact Nat.zero_le _
      · cases hsub : subsequenceByIndex a r with
        | none =>
            rw [hsub] at hrest
            exact hrest.elim
        | some s => exact subsequenceByIndex_mem_valid a r s hsub k hk
    · cases hsub : subsequenceByIndex a r with
      | none => rw [hsub] at hrest; exact hrest.elim
      | some s =>
          rw [hsub] at hrest
          refine ⟨s, rfl, ?_⟩
          show matchesWith s (b.drop 0) 1
          have hae : almostEqual s b := hrest
          rw [almostEqual_iff_matchesWith] at hae
          have : b.drop 0 = b := List.drop_zero
          rw [this]
          exact hae

theorem output_is_valid_solution (a b : List Char) {indices : List Nat} :
    (findValidSequence a b = some indices) → isValidSolution a b indices := by
  intro hres
  unfold findValidSequence at hres
  have ⟨hmono, hbounds, s, hsub_s, hmatch⟩ := solveDP_sound a b 1 0 0 indices hres
  unfold isValidSolution
  refine ⟨hmono, ?_⟩
  rw [hsub_s]
  show almostEqual s b
  rw [almostEqual_iff_matchesWith]
  have : b.drop 0 = b := List.drop_zero
  rw [this] at hmatch
  exact hmatch

end LC3302.Student
