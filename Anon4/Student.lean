import Anon4.Spec

namespace Anon4

/-! ### Toggling helper -/

def toggle (x : Segment) : Segment :=
  match x with
  | Segment.Inactive => Segment.Active
  | Segment.Active => Segment.Inactive

/-! ### Basic facts about `flip` -/

theorem flip_length (l r : Nat) (a : List Segment) : (flip l r a).length = a.length := by
  unfold flip
  simp only [List.length_map, List.length_zip, List.length_range]
  simp

theorem flip_getElem (l r : Nat) (a : List Segment) (i : Nat) (hi : i < a.length) :
    (flip l r a)[i]'(by rw [flip_length]; exact hi) =
      if (decide (l ≤ i) && decide (i ≤ r)) then toggle a[i] else a[i] := by
  unfold flip
  simp only [List.getElem_map, List.getElem_zip, List.getElem_range]
  rfl

theorem flip_eq_self_of_le_length (l r : Nat) (a : List Segment) (hl : a.length ≤ l) :
    flip l r a = a := by
  apply List.ext_getElem
  · simp only [flip_length]
  · intro i hi hia
    rw [flip_getElem l r a i hia]
    have hnot : ¬ l ≤ i := by
      intro hli
      have hlt : i < l := Nat.lt_of_lt_of_le hia hl
      exact Nat.not_le_of_gt hlt hli
    simp [hnot]

theorem flip_self (a : List Segment) : flip a.length a.length a = a :=
  flip_eq_self_of_le_length a.length a.length a (Nat.le_refl _)

theorem drop_all (a : List Segment) : a.drop a.length = [] :=
  List.drop_eq_nil_of_le (Nat.le_refl _)

theorem flip_drop_self (l r : Nat) (a : List Segment) :
    (flip l r a).drop a.length = [] := by
  apply List.drop_eq_nil_of_le
  rw [flip_length]
  omega

/-! ### Clamping intervals to the list bounds -/

theorem mem_zip_fst {α β : Type} {l₁ : List α} {l₂ : List β} {i : α} {x : β} :
    (i, x) ∈ l₁.zip l₂ → i ∈ l₁ := by
  intro h
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons a as ih =>
      cases l₂ with
      | nil => simp at h
      | cons b bs =>
          simp only [List.zip_cons_cons, List.mem_cons] at h
          rcases h with h | h
          · simp only [List.mem_cons]
            left
            exact congrArg Prod.fst h
          · simp only [List.mem_cons]
            right
            exact ih h

theorem flip_clamp (l r : Nat) (a : List Segment) :
    flip l r a = flip (min l a.length) (min r a.length) a := by
  unfold flip
  apply List.map_congr_left
  intro p hp
  rcases p with ⟨i, x⟩
  have himem : i ∈ List.range a.length := mem_zip_fst hp
  have hi : i < a.length := List.mem_range.mp himem
  have hleft : (decide (l ≤ i)) = (decide (min l a.length ≤ i)) := by
    by_cases h1 : l ≤ i
    · have hmin : min l a.length ≤ i := Nat.le_trans (Nat.min_le_left _ _) h1
      rw [decide_eq_true h1, decide_eq_true hmin]
    · have hmin : ¬ min l a.length ≤ i := by
        intro hmi
        have hli : l ≤ i := by
          by_cases hln : l ≤ a.length
          · simpa [Nat.min_eq_left hln] using hmi
          · have hle : a.length ≤ l := Nat.le_of_not_le hln
            have : a.length ≤ i := by
              simpa [Nat.min_eq_right hle] using hmi
            omega
        exact h1 hli
      rw [decide_eq_false h1, decide_eq_false hmin]
  have hright : (decide (i ≤ r)) = (decide (i ≤ min r a.length)) := by
    by_cases h2 : i ≤ r
    · have hmin : i ≤ min r a.length := Nat.le_min.mpr ⟨h2, Nat.le_of_lt hi⟩
      rw [decide_eq_true h2, decide_eq_true hmin]
    · have hmin : ¬ i ≤ min r a.length := by
        intro hmi
        exact h2 (Nat.le_min.mp hmi).1
      rw [decide_eq_false h2, decide_eq_false hmin]
  simp only [hleft, hright]

theorem isContiguous_clamp (s : Segment) (l r : Nat) (a : List Segment) :
    isContiguous s l r a = isContiguous s (min l a.length) (min r a.length) a := by
  unfold isContiguous
  congr 1
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop]
    omega
  · intro i h1 h2
    simp only [List.length_take, List.length_drop] at h1 h2
    have hle : l ≤ a.length := by omega
    simp only [List.getElem_take, List.getElem_drop]
    simp [Nat.min_eq_left hle]

theorem min_le_min_of_le {a b c : Nat} (h : a ≤ b) : min a c ≤ min b c :=
  Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left _ _) h, Nat.min_le_right _ _⟩

theorem flipFlap_clamp (l₁ r₁ l₂ r₂ : Nat) (a : List Segment) :
    flipFlap l₁ r₁ l₂ r₂ a =
      flipFlap (min l₁ a.length) (min r₁ a.length) (min l₂ a.length) (min r₂ a.length) a := by
  unfold flipFlap
  rw [flip_clamp l₁ r₁ a]
  rw [flip_clamp l₂ r₂ (flip (min l₁ a.length) (min r₁ a.length) a)]
  simp only [flip_length]

theorem runOperation_clamp (l₁ r₁ l₂ r₂ : Nat) (a : List Segment) (ys : List Segment)
    (h : runOperation l₁ r₁ l₂ r₂ a = some ys) :
    runOperation (min l₁ a.length) (min r₁ a.length) (min l₂ a.length) (min r₂ a.length) a = some ys := by
  unfold runOperation at h
  by_cases hv : isValidFlipFlap l₁ r₁ l₂ r₂ a = true
  · have hys : flipFlap l₁ r₁ l₂ r₂ a = ys := by
      simpa [hv] using h
    have hv' : isValidFlipFlap (min l₁ a.length) (min r₁ a.length) (min l₂ a.length) (min r₂ a.length) a = true := by
      simp only [isValidFlipFlap, Bool.and_eq_true]
      have hv'' : ((l₁ ≤ r₂ ∧ l₂ ≤ r₂) ∧ isContiguousActive l₁ r₁ a = true) ∧
          isContiguousInactive l₂ r₂ (flip l₁ r₁ a) = true := by
        simpa [isValidFlipFlap, Bool.and_eq_true] using hv
      rcases hv'' with ⟨⟨⟨h12, h22⟩, hc1⟩, hc2⟩
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · exact decide_eq_true_eq.mpr (min_le_min_of_le h12)
      · exact decide_eq_true_eq.mpr (min_le_min_of_le h22)
      · unfold isContiguousActive
        rw [← isContiguous_clamp Segment.Active l₁ r₁ a]
        exact hc1
      · unfold isContiguousInactive
        unfold isContiguousInactive at hc2
        rw [isContiguous_clamp Segment.Inactive l₂ r₂ (flip l₁ r₁ a)] at hc2
        simpa [flip_clamp l₁ r₁ a, flip_length] using hc2
    simp [runOperation, hv', ← flipFlap_clamp l₁ r₁ l₂ r₂ a, hys]
  · simp only [hv] at h
    cases h

/-! ### A finite, exhaustive enumeration of the results -/

def idxs (n : Nat) : List Nat := List.range (n + 1)

def enumerateResults (a : List Segment) : List (List Segment) :=
  (idxs a.length).flatMap fun l₁ =>
    (idxs a.length).flatMap fun r₁ =>
      (idxs a.length).flatMap fun l₂ =>
        (idxs a.length).filterMap fun r₂ => runOperation l₁ r₁ l₂ r₂ a

def maxList : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxList xs)

theorem maxList_ge : ∀ (xs : List Nat), ∀ x : Nat, x ∈ xs → x ≤ maxList xs := by
  intro xs
  induction xs with
  | nil => intro x hx; cases hx
  | cons y ys ih =>
      intro x hx
      rw [maxList]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih x hx) (Nat.le_max_right _ _)

theorem exists_maxList (xs : List Nat) (h : xs ≠ []) :
    ∃ x : Nat, x ∈ xs ∧ x = maxList xs := by
  induction xs with
  | nil => exact False.elim (h rfl)
  | cons y ys ih =>
      rw [maxList]
      by_cases hys : ys = []
      · subst hys
        refine ⟨y, by simp, ?_⟩
        simp [maxList, Nat.max_eq_left (Nat.zero_le y)]
      · rcases ih hys with ⟨m, hm, hmeq⟩
        by_cases hle : y ≤ maxList ys
        · refine ⟨m, ?_, ?_⟩
          · simp [hm]
          · rw [Nat.max_eq_right hle, hmeq]
        · refine ⟨y, ?_, ?_⟩
          · simp
          · rw [Nat.max_eq_left (Nat.le_of_not_ge hle)]

theorem mem_enumerateResults_of (a : List Segment) (l₁ r₁ l₂ r₂ : Nat) (ys : List Segment)
    (hl₁ : l₁ ≤ a.length) (hr₁ : r₁ ≤ a.length) (hl₂ : l₂ ≤ a.length) (hr₂ : r₂ ≤ a.length)
    (h : runOperation l₁ r₁ l₂ r₂ a = some ys) :
    ys ∈ enumerateResults a := by
  simp only [enumerateResults, List.mem_filterMap, List.mem_flatMap, idxs, List.mem_range]
  refine ⟨l₁, by omega, ?_⟩
  refine ⟨r₁, by omega, ?_⟩
  refine ⟨l₂, by omega, ?_⟩
  refine ⟨r₂, by omega, ?_⟩
  exact h

theorem exists_runOperation_of_mem (a : List Segment) (ys : List Segment)
    (h : ys ∈ enumerateResults a) :
    ∃ l₁ r₁ l₂ r₂ : Nat, runOperation l₁ r₁ l₂ r₂ a = some ys := by
  simp only [enumerateResults, List.mem_filterMap, List.mem_flatMap, idxs, List.mem_range] at h
  rcases h with ⟨l₁, _, r₁, _, l₂, _, r₂, _, hrun⟩
  exact ⟨l₁, r₁, l₂, r₂, hrun⟩

theorem runOperation_self (a : List Segment) :
    runOperation a.length a.length a.length a.length a = some a := by
  have hv : isValidFlipFlap a.length a.length a.length a.length a = true := by
    simp only [isValidFlipFlap, Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact decide_eq_true (Nat.le_refl _)
    · exact decide_eq_true (Nat.le_refl _)
    · unfold isContiguousActive isContiguous
      simp
    · unfold isContiguousInactive isContiguous
      simp [flip_drop_self]
  simp [runOperation, hv, flipFlap, flip_self]

theorem enumerateResults_mem_self (a : List Segment) : a ∈ enumerateResults a := by
  exact mem_enumerateResults_of a a.length a.length a.length a.length a
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (runOperation_self a)

theorem scores_nonempty (a : List Segment) : (enumerateResults a).map score ≠ [] := by
  intro h
  have hmem : score a ∈ (enumerateResults a).map score :=
    List.mem_map.mpr ⟨a, enumerateResults_mem_self a, rfl⟩
  rw [h] at hmem
  cases hmem

/-! ### The submission -/

def query (l r : Nat) (xs : List Segment) : Nat :=
  maxList ((enumerateResults ((xs.drop l).take (r - l + 1))).map score)

theorem solution_is_optimal (xs : List Segment) :
    ∀ l r : Nat, l ≤ r →
      let p := (xs.drop l).take (r - l + 1)
      let m := query l r xs
      (∀ a b c d : Nat, ∀ ys : List Segment, runOperation a b c d p = some ys → score ys ≤ m) ∧
      (∃ a b c d : Nat, ∃ ys : List Segment, runOperation a b c d p = some ys ∧ score ys = m) := by
  intro l r hlr
  dsimp only
  let p := (xs.drop l).take (r - l + 1)
  change (∀ a b c d : Nat, ∀ ys : List Segment, runOperation a b c d p = some ys →
            score ys ≤ maxList ((enumerateResults p).map score)) ∧
         (∃ a b c d : Nat, ∃ ys : List Segment, runOperation a b c d p = some ys ∧
            score ys = maxList ((enumerateResults p).map score))
  constructor
  · intro a b c d ys hys
    have hclamp := runOperation_clamp a b c d p ys hys
    have hmem : ys ∈ enumerateResults p :=
      mem_enumerateResults_of p (min a p.length) (min b p.length) (min c p.length) (min d p.length) ys
        (Nat.min_le_right _ _) (Nat.min_le_right _ _) (Nat.min_le_right _ _) (Nat.min_le_right _ _)
        hclamp
    exact maxList_ge ((enumerateResults p).map score) (score ys)
      (List.mem_map.mpr ⟨ys, hmem, rfl⟩)
  · rcases exists_maxList ((enumerateResults p).map score) (scores_nonempty p) with ⟨s, hsmem, hseq⟩
    rcases List.mem_map.mp hsmem with ⟨zs, hzs, hzscore⟩
    rcases exists_runOperation_of_mem p zs hzs with ⟨a, b, c, d, hrun⟩
    refine ⟨a, b, c, d, zs, hrun, ?_⟩
    rw [hzscore, hseq]

end Anon4
