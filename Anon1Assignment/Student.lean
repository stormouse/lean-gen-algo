import Anon1Assignment.Spec

namespace Anon1.Student

open Anon1

/-! ### Reading `ValidState` as a two-player game -/

theorem nil_iff {a b : Nat} {s : Side} : ValidState [] a b s ↔ b ≤ a := by
  constructor
  · intro h; cases h with | done h => exact h
  · intro h; exact .done h

theorem first_iff {x : Nat} {xs : List Nat} {a b : Nat} :
    ValidState (x :: xs) a b .first ↔
      (ValidState xs (a + x) b .second ∨
        ValidState (dropLastOf x xs) (a + lastOf x xs) b .second) := by
  constructor
  · intro h
    cases h with
    | firstLeft h => exact Or.inl h
    | firstRight h => exact Or.inr h
  · rintro (h | h)
    · exact .firstLeft h
    · exact .firstRight h

theorem second_iff {x : Nat} {xs : List Nat} {a b : Nat} :
    ValidState (x :: xs) a b .second ↔
      (ValidState xs a (b + x) .first ∧
        ValidState (dropLastOf x xs) a (b + lastOf x xs) .first) := by
  constructor
  · intro h
    cases h with
    | secondBoth l r => exact ⟨l, r⟩
  · rintro ⟨l, r⟩
    exact .secondBoth l r

/-! ### The game value -/

def imax (p q : Int) : Int := if p ≤ q then q else p

def gameValue : List Nat → Int
  | [] => 0
  | x :: xs =>
      imax ((x : Int) - gameValue xs)
        (((lastOf x xs : Nat) : Int) - gameValue (dropLastOf x xs))
termination_by t => t.length
decreasing_by
  · simp
  · simp only [dropLastOf, List.length_dropLast, List.length_cons]
    omega

theorem gameValue_nil : gameValue [] = 0 := by
  rw [gameValue]

theorem gameValue_cons (x : Nat) (xs : List Nat) :
    gameValue (x :: xs) =
      imax ((x : Int) - gameValue xs)
        (((lastOf x xs : Nat) : Int) - gameValue (dropLastOf x xs)) := by
  rw [gameValue]

theorem valid_iff (n : Nat) :
    ∀ t : List Nat, t.length ≤ n → ∀ a b : Nat,
      (ValidState t a b .first ↔ 0 ≤ (a : Int) - (b : Int) + gameValue t) ∧
      (ValidState t a b .second ↔ 0 ≤ (a : Int) - (b : Int) - gameValue t) := by
  induction n with
  | zero =>
    intro t ht a b
    match t with
    | [] =>
      rw [gameValue_nil]
      exact ⟨by rw [nil_iff]; omega, by rw [nil_iff]; omega⟩
  | succ n ih =>
    intro t ht a b
    match t with
    | [] =>
      rw [gameValue_nil]
      exact ⟨by rw [nil_iff]; omega, by rw [nil_iff]; omega⟩
    | x :: xs =>
      have hxs : xs.length ≤ n := by
        simp only [List.length_cons] at ht; omega
      have hdl : (dropLastOf x xs).length ≤ n := by
        simp only [dropLastOf, List.length_dropLast, List.length_cons]; omega
      constructor
      · rw [first_iff, gameValue_cons,
          (ih xs hxs (a + x) b).2,
          (ih _ hdl (a + lastOf x xs) b).2]
        unfold imax; split <;> omega
      · rw [second_iff, gameValue_cons,
          (ih xs hxs a (b + x)).1,
          (ih _ hdl a (b + lastOf x xs)).1]
        unfold imax; split <;> omega

theorem targetProperty_iff (t : List Nat) : targetProperty t ↔ 0 ≤ gameValue t := by
  have h := (valid_iff t.length t (Nat.le_refl _) 0 0).1
  unfold targetProperty
  rw [h]
  omega

/-! ### Contiguous segments

`gameValue` as written re-explores subrows exponentially often, but every row it visits is
a *contiguous segment* of the original list, and there are only `O(n²)` of those. This
section re-phrases the recurrence in terms of `seg t i len`, the segment of length `len`
starting at index `i`, so the table can be filled bottom-up. -/

def seg (t : List Nat) (i len : Nat) : List Nat := (t.drop i).take len

theorem seg_length (t : List Nat) (i len : Nat) (h : i + len ≤ t.length) :
    (seg t i len).length = len := by
  simp only [seg, List.length_take, List.length_drop]
  omega

theorem seg_zero (t : List Nat) (i : Nat) : seg t i 0 = [] := by
  simp [seg]

theorem seg_full (t : List Nat) : seg t 0 t.length = t := by
  simp [seg]

/-- A nonempty segment, split at its left end. -/
theorem seg_succ_eq (t : List Nat) (i len : Nat) (h : i + len < t.length) :
    seg t i (len + 1) = t[i]! :: seg t (i + 1) len := by
  have hi : i < t.length := by omega
  simp only [seg]
  rw [List.drop_eq_getElem_cons hi, List.take_succ_cons, getElem!_pos t i hi]

/-- Trimming a segment on the right shortens it by one. -/
theorem dropLast_seg (t : List Nat) (i len : Nat) (h : i + len < t.length) :
    (seg t i (len + 1)).dropLast = seg t i len := by
  have hl : (seg t i (len + 1)).length = len + 1 := seg_length t i (len + 1) (by omega)
  rw [List.dropLast_eq_take, hl]
  show List.take (len + 1 - 1) (List.take (len + 1) (t.drop i)) = List.take len (t.drop i)
  rw [List.take_take]
  congr 1
  omega

/-- Rewriting `getLast` along an equality of lists. -/
theorem getLast_congr {l l' : List Nat} (h : l = l') (hne : l ≠ []) (hne' : l' ≠ []) :
    l.getLast hne = l'.getLast hne' := by
  subst h; rfl

theorem getLast_eq_getElem' (l : List Nat) (hne : l ≠ []) (k : Nat) (hk : k = l.length - 1)
    (hk2 : k < l.length) : l.getLast hne = l[k] := by
  subst hk; exact List.getLast_eq_getElem hne

/-- The last element of a segment. -/
theorem getLast_seg (t : List Nat) (i len : Nat) (h : i + len < t.length)
    (hne : seg t i (len + 1) ≠ []) :
    (seg t i (len + 1)).getLast hne = t[i + len]! := by
  have hl : (seg t i (len + 1)).length = len + 1 := seg_length t i (len + 1) (by omega)
  have hk : len < (seg t i (len + 1)).length := by omega
  rw [getLast_eq_getElem' _ hne len (by omega) hk]
  have hlen : i + len < t.length := h
  rw [getElem!_pos t (i + len) hlen]
  show (List.take (len + 1) (t.drop i))[len]'_ = _
  rw [List.getElem_take, List.getElem_drop]

/-- The `gameValue` recurrence, phrased on segments: taking the left end drops to
`seg t (i+1) len`, taking the right end drops to `seg t i len`. -/
theorem gameValue_seg_succ (t : List Nat) (i len : Nat) (h : i + len < t.length) :
    gameValue (seg t i (len + 1)) =
      imax ((t[i]! : Int) - gameValue (seg t (i + 1) len))
        ((t[i + len]! : Int) - gameValue (seg t i len)) := by
  have hcons := seg_succ_eq t i len h
  have hne : seg t i (len + 1) ≠ [] := by
    rw [hcons]; exact List.cons_ne_nil _ _
  have hne' : t[i]! :: seg t (i + 1) len ≠ [] := List.cons_ne_nil _ _
  have hlast : lastOf t[i]! (seg t (i + 1) len) = t[i + len]! := by
    show (t[i]! :: seg t (i + 1) len).getLast hne' = _
    rw [getLast_congr hcons.symm hne' hne]
    exact getLast_seg t i len h hne
  have hdrop : dropLastOf t[i]! (seg t (i + 1) len) = seg t i len := by
    show (t[i]! :: seg t (i + 1) len).dropLast = _
    rw [← hcons]
    exact dropLast_seg t i len h
  rw [hcons, gameValue_cons, hlast, hdrop]

/-! ### Filling the table bottom-up

`prev` holds `gameValue (seg t i len)` for every start `i`, at one fixed segment length
`len`. Each `stepRow` moves the whole table up one length in `O(n)`, so `buildRow` runs in
`O(n²)` with `O(n)` extra space. -/

def stepRow (t : Array Nat) (len : Nat) (prev : Array Int) : Array Int :=
  Array.ofFn (n := prev.size - 1) fun i =>
    imax (((t[i.1]! : Nat) : Int) - prev[i.1 + 1]!)
      (((t[i.1 + len]! : Nat) : Int) - prev[i.1]!)

def buildRow (t : Array Nat) (len : Nat) (prev : Array Int) : Array Int :=
  if 1 < prev.size then buildRow t (len + 1) (stepRow t len prev) else prev
termination_by prev.size
decreasing_by
  simp only [stepRow, Array.size_ofFn]
  omega

/-- `gameValue` computed by the bottom-up table. -/
def gameValueFast (t : List Nat) : Int :=
  (buildRow t.toArray 0 (Array.ofFn (n := t.length + 1) fun _ => (0 : Int)))[0]!

/-- The table invariant: `prev` lists the values of all segments of length `len`. -/
def RowOk (t : List Nat) (len : Nat) (prev : Array Int) : Prop :=
  prev.size = t.length + 1 - len ∧
    ∀ i, (h : i < prev.size) → prev[i] = gameValue (seg t i len)

theorem stepRow_ok (t : List Nat) (len : Nat) (prev : Array Int)
    (h : RowOk t len prev) (hpos : 1 < prev.size) :
    RowOk t (len + 1) (stepRow t.toArray len prev) := by
  obtain ⟨hsize, hval⟩ := h
  refine ⟨by simp only [stepRow, Array.size_ofFn]; omega, ?_⟩
  intro i hi
  simp only [stepRow, Array.size_ofFn] at hi
  have hil : i + len < t.length := by omega
  have h1 : i + 1 < prev.size := by omega
  have h2 : i < prev.size := by omega
  have ht1 : i < t.toArray.size := by simp; omega
  have ht2 : i + len < t.toArray.size := by simp; omega
  simp only [stepRow, Array.getElem_ofFn]
  rw [getElem!_pos t.toArray i ht1, getElem!_pos t.toArray (i + len) ht2,
    getElem!_pos prev (i + 1) h1, getElem!_pos prev i h2, hval (i + 1) h1, hval i h2,
    gameValue_seg_succ t i len hil, getElem!_pos t i (by omega),
    getElem!_pos t (i + len) (by omega)]
  simp

theorem buildRow_base (t : List Nat) (len : Nat) (prev : Array Int)
    (hpos : ¬ (1 < prev.size)) (hlen : len ≤ t.length) (hrow : RowOk t len prev) :
    (buildRow t.toArray len prev)[0]! = gameValue t := by
  obtain ⟨hs, hv⟩ := hrow
  have hlen' : len = t.length := by omega
  have h0 : 0 < prev.size := by omega
  rw [buildRow, if_neg hpos, getElem!_pos prev 0 h0, hv 0 h0, hlen', seg_full]

theorem buildRow_ok (t : List Nat) : ∀ (k len : Nat) (prev : Array Int),
    t.length - len ≤ k → len ≤ t.length → RowOk t len prev →
    (buildRow t.toArray len prev)[0]! = gameValue t := by
  intro k
  induction k with
  | zero =>
    intro len prev hk hlen hrow
    refine buildRow_base t len prev ?_ hlen hrow
    obtain ⟨hs, _⟩ := hrow
    omega
  | succ k ih =>
    intro len prev hk hlen hrow
    by_cases hpos : 1 < prev.size
    · have hs := hrow.1
      rw [buildRow, if_pos hpos]
      exact ih (len + 1) (stepRow t.toArray len prev) (by omega) (by omega)
        (stepRow_ok t len prev hrow hpos)
    · exact buildRow_base t len prev hpos hlen hrow

theorem gameValueFast_eq (t : List Nat) : gameValueFast t = gameValue t := by
  refine buildRow_ok t t.length 0 _ (by omega) (by omega) ⟨by simp, ?_⟩
  intro i hi
  simp only [Array.getElem_ofFn, seg_zero, gameValue_nil]

/-! ### The submission -/

def solve (t : List Nat) : Bool :=
  decide (0 ≤ gameValueFast t)

theorem solution_is_valid (t : List Nat) :
    solve t = true ↔ targetProperty t := by
  rw [targetProperty_iff, solve, gameValueFast_eq]
  simp

end Anon1.Student
