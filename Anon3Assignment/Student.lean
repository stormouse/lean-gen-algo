import Anon3Assignment.Spec

/-!
# Streaming MK average

`runBaseline` keeps the entire stream, appends to its end on every `add` (`O(n)` per element)
and, on every `calc`, re-derives and re-sorts the last `m` elements (`O(n + m log m)`).

This implementation keeps only the window, in two shapes at once:

* a banker's queue (`front ++ back.reverse`) giving the arrival order, so the element leaving
  the window is known in amortised `O(1)`;
* a weight-balanced binary search tree of the same elements, each node caching the size and
  the sum of its subtree, so the sum of the elements of rank `k..m-k` is read off in
  `O(log m)` without ever materialising the sorted window.

That is `O(log m)` per `add` and per `calc`, in `O(m)` space.

The proof keeps the two shapes tied to the specification by a single invariant (`Inv`): the
queue is `lastN stream m`, and the tree's in-order traversal is a sorted permutation of it.
Since a sorted list is the unique sorted representative of its multiset
(`List.Perm.eq_of_pairwise`), that traversal *is* `mergeSort` of the window, which is what the
specification queries.
-/

namespace Anon3.Student

open Anon3

/-! ## An order-statistic tree -/

/-- A weight-balanced binary search tree over a multiset of `Nat`s.  Every node caches the
size and the sum of its subtree, so a rank-slice sum costs `O(log n)`. -/
inductive Tree where
  | leaf : Tree
  | node (sz : Nat) (sm : Nat) (l : Tree) (v : Nat) (r : Tree) : Tree

namespace Tree

/-- Cached number of elements. -/
def size : Tree → Nat
  | leaf => 0
  | node sz _ _ _ _ => sz

/-- Cached sum of the elements. -/
def total : Tree → Nat
  | leaf => 0
  | node _ sm _ _ _ => sm

/-- The elements in order. -/
def toList : Tree → List Nat
  | leaf => []
  | node _ _ l v r => l.toList ++ v :: r.toList

/-- Smart constructor maintaining the cached fields. -/
def mk (l : Tree) (v : Nat) (r : Tree) : Tree :=
  node (l.size + 1 + r.size) (l.total + v + r.total) l v r

@[simp] theorem size_leaf : size leaf = 0 := rfl

@[simp] theorem total_leaf : total leaf = 0 := rfl

@[simp] theorem toList_leaf : toList leaf = [] := rfl

@[simp] theorem size_node (sz sm : Nat) (l : Tree) (v : Nat) (r : Tree) :
    (node sz sm l v r).size = sz := rfl

@[simp] theorem total_node (sz sm : Nat) (l : Tree) (v : Nat) (r : Tree) :
    (node sz sm l v r).total = sm := rfl

@[simp] theorem toList_node (sz sm : Nat) (l : Tree) (v : Nat) (r : Tree) :
    (node sz sm l v r).toList = l.toList ++ v :: r.toList := rfl

@[simp] theorem toList_mk (l : Tree) (v : Nat) (r : Tree) :
    (mk l v r).toList = l.toList ++ v :: r.toList := rfl

/-- The cached fields agree with the elements. -/
def Wf : Tree → Prop
  | leaf => True
  | node sz sm l v r =>
      sz = l.size + 1 + r.size ∧ sm = l.total + v + r.total ∧ Wf l ∧ Wf r

theorem wf_mk {l r : Tree} (v : Nat) (hl : Wf l) (hr : Wf r) : Wf (mk l v r) :=
  ⟨rfl, rfl, hl, hr⟩

theorem size_eq_length : ∀ {t : Tree}, Wf t → t.size = t.toList.length
  | leaf, _ => rfl
  | node sz sm l v r, ⟨hsz, _, hl, hr⟩ => by
    have hl' := size_eq_length hl
    have hr' := size_eq_length hr
    simp [hsz, hl', hr']
    omega

theorem total_eq_sum : ∀ {t : Tree}, Wf t → t.total = t.toList.sum
  | leaf, _ => rfl
  | node sz sm l v r, ⟨_, hsm, hl, hr⟩ => by
    have hl' := total_eq_sum hl
    have hr' := total_eq_sum hr
    simp [hsm, hl', hr']
    omega

/-! ### Rebalancing -/

def singleL (l : Tree) (v : Nat) (r : Tree) : Tree :=
  match r with
  | leaf => mk l v r
  | node _ _ rl rv rr => mk (mk l v rl) rv rr

def doubleL (l : Tree) (v : Nat) (r : Tree) : Tree :=
  match r with
  | node _ _ (node _ _ rll rlv rlr) rv rr => mk (mk l v rll) rlv (mk rlr rv rr)
  | _ => singleL l v r

def singleR (l : Tree) (v : Nat) (r : Tree) : Tree :=
  match l with
  | leaf => mk l v r
  | node _ _ ll lv lr => mk ll lv (mk lr v r)

def doubleR (l : Tree) (v : Nat) (r : Tree) : Tree :=
  match l with
  | node _ _ ll lv (node _ _ lrl lrv lrr) => mk (mk ll lv lrl) lrv (mk lrr v r)
  | _ => singleR l v r

/-- Size of the left/right child, `0` for a leaf. -/
def leftSize : Tree → Nat
  | leaf => 0
  | node _ _ l _ _ => l.size

def rightSize : Tree → Nat
  | leaf => 0
  | node _ _ _ _ r => r.size

/-- Rebuild a node whose children are each balanced but whose sizes may differ too much.
Weight-balanced (`delta = 3`, `ratio = 2`), so the tree stays `O(log n)` deep. -/
def balance (l : Tree) (v : Nat) (r : Tree) : Tree :=
  if 3 * l.size < r.size ∧ 2 ≤ r.size then
    (if r.leftSize < 2 * r.rightSize then singleL l v r else doubleL l v r)
  else if 3 * r.size < l.size ∧ 2 ≤ l.size then
    (if l.rightSize < 2 * l.leftSize then singleR l v r else doubleR l v r)
  else mk l v r

theorem toList_singleL (l : Tree) (v : Nat) (r : Tree) :
    (singleL l v r).toList = l.toList ++ v :: r.toList := by
  cases r <;> simp [singleL, toList]

theorem toList_doubleL (l : Tree) (v : Nat) (r : Tree) :
    (doubleL l v r).toList = l.toList ++ v :: r.toList := by
  match r with
  | leaf => simp [doubleL, toList_singleL]
  | node _ _ leaf _ _ => simp [doubleL, toList_singleL]
  | node _ _ (node _ _ _ _ _) _ _ => simp [doubleL, toList]

theorem toList_singleR (l : Tree) (v : Nat) (r : Tree) :
    (singleR l v r).toList = l.toList ++ v :: r.toList := by
  cases l <;> simp [singleR, toList]

theorem toList_doubleR (l : Tree) (v : Nat) (r : Tree) :
    (doubleR l v r).toList = l.toList ++ v :: r.toList := by
  match l with
  | leaf => simp [doubleR, toList_singleR]
  | node _ _ _ _ leaf => simp [doubleR, toList_singleR]
  | node _ _ _ _ (node _ _ _ _ _) => simp [doubleR, toList]

@[simp] theorem toList_balance (l : Tree) (v : Nat) (r : Tree) :
    (balance l v r).toList = l.toList ++ v :: r.toList := by
  unfold balance
  repeat' split
  all_goals simp [toList_singleL, toList_doubleL, toList_singleR, toList_doubleR]

theorem wf_singleL {l r : Tree} (v : Nat) (hl : Wf l) (hr : Wf r) : Wf (singleL l v r) := by
  cases r with
  | leaf => exact wf_mk v hl hr
  | node _ _ rl rv rr =>
    obtain ⟨_, _, hrl, hrr⟩ := hr
    exact wf_mk rv (wf_mk v hl hrl) hrr

theorem wf_doubleL {l r : Tree} (v : Nat) (hl : Wf l) (hr : Wf r) : Wf (doubleL l v r) := by
  match r, hr with
  | leaf, hr => exact wf_singleL v hl hr
  | node _ _ leaf _ _, hr => exact wf_singleL v hl hr
  | node _ _ (node _ _ rll rlv rlr) rv rr, ⟨_, _, ⟨_, _, hrll, hrlr⟩, hrr⟩ =>
    exact wf_mk rlv (wf_mk v hl hrll) (wf_mk rv hrlr hrr)

theorem wf_singleR {l r : Tree} (v : Nat) (hl : Wf l) (hr : Wf r) : Wf (singleR l v r) := by
  cases l with
  | leaf => exact wf_mk v hl hr
  | node _ _ ll lv lr =>
    obtain ⟨_, _, hll, hlr⟩ := hl
    exact wf_mk lv hll (wf_mk v hlr hr)

theorem wf_doubleR {l r : Tree} (v : Nat) (hl : Wf l) (hr : Wf r) : Wf (doubleR l v r) := by
  match l, hl with
  | leaf, hl => exact wf_singleR v hl hr
  | node _ _ _ _ leaf, hl => exact wf_singleR v hl hr
  | node _ _ ll lv (node _ _ lrl lrv lrr), ⟨_, _, hll, ⟨_, _, hlrl, hlrr⟩⟩ =>
    exact wf_mk lrv (wf_mk lv hll hlrl) (wf_mk v hlrr hr)

theorem wf_balance {l r : Tree} (v : Nat) (hl : Wf l) (hr : Wf r) : Wf (balance l v r) := by
  unfold balance
  repeat' split
  all_goals first
    | exact wf_mk v hl hr
    | exact wf_singleL v hl hr
    | exact wf_doubleL v hl hr
    | exact wf_singleR v hl hr
    | exact wf_doubleR v hl hr

/-! ### Prefix sums by rank -/

/-- Sum of the `n` smallest elements. -/
def sumFirst : Tree → Nat → Nat
  | leaf, _ => 0
  | node sz sm l v r, n =>
      if sz ≤ n then sm
      else if n ≤ l.size then sumFirst l n
      else l.total + v + sumFirst r (n - l.size - 1)

/-- Splitting a list of the shape produced by `toList` at a rank past the root. -/
theorem take_append_cons (A B : List Nat) (v j : Nat) :
    (A ++ v :: B).take (A.length + 1 + j) = (A ++ [v]) ++ B.take j := by
  rw [show A ++ v :: B = (A ++ [v]) ++ B by simp]
  rw [List.take_add, List.take_left' (by simp), List.drop_left' (by simp)]

theorem sumFirst_eq : ∀ {t : Tree}, Wf t → ∀ n, sumFirst t n = (t.toList.take n).sum
  | leaf, _, n => by simp [sumFirst]
  | node sz sm l v r, ⟨hsz, hsm, hl, hr⟩, n => by
    have hll : l.size = l.toList.length := size_eq_length hl
    have hrl : r.size = r.toList.length := size_eq_length hr
    have hlt : l.total = l.toList.sum := total_eq_sum hl
    have hrt : r.total = r.toList.sum := total_eq_sum hr
    have hlen : (toList (node sz sm l v r)).length = sz := by simp; omega
    rw [sumFirst]
    split
    · rw [List.take_of_length_le (by omega)]
      simp [hsm, hlt, hrt]
      omega
    · rename_i hsz'
      split
      · rename_i hn
        rw [sumFirst_eq hl, toList_node, List.take_append_of_le_length (by omega)]
      · rename_i hn
        have hn' : n = l.toList.length + 1 + (n - l.size - 1) := by omega
        rw [sumFirst_eq hr, toList_node, hn', take_append_cons]
        have : l.toList.length + 1 + (n - l.size - 1) - l.size - 1 = n - l.size - 1 := by omega
        rw [this]
        simp [hlt]
        omega


/-! ### Sorted lists -/

/-- Ascending order. -/
def Sorted (l : List Nat) : Prop := List.Pairwise (· ≤ ·) l

@[simp] theorem sorted_nil : Sorted [] := List.Pairwise.nil

@[simp] theorem sorted_singleton (x : Nat) : Sorted [x] := by
  simp [Sorted]

theorem sorted_append_cons_of {A B : List Nat} {v : Nat} (hA : Sorted A) (hB : Sorted B)
    (hAv : ∀ a ∈ A, a ≤ v) (hvB : ∀ b ∈ B, v ≤ b) : Sorted (A ++ v :: B) := by
  unfold Sorted at *
  rw [List.pairwise_append]
  refine ⟨hA, List.pairwise_cons.mpr ⟨hvB, hB⟩, ?_⟩
  intro a ha b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hAv a ha
  · exact Nat.le_trans (hAv a ha) (hvB b hb)

theorem sorted_append_cons {A B : List Nat} {v : Nat} (h : Sorted (A ++ v :: B)) :
    Sorted A ∧ Sorted B ∧ (∀ a ∈ A, a ≤ v) ∧ (∀ b ∈ B, v ≤ b) := by
  unfold Sorted at *
  rw [List.pairwise_append] at h
  obtain ⟨hA, hvB, hcross⟩ := h
  rw [List.pairwise_cons] at hvB
  exact ⟨hA, hvB.2, fun a ha => hcross a ha v List.mem_cons_self, hvB.1⟩

theorem sorted_append_of_cons {A B : List Nat} {v : Nat} (h : Sorted (A ++ v :: B)) :
    Sorted (A ++ B) := by
  obtain ⟨hA, hB, hAv, hvB⟩ := sorted_append_cons h
  unfold Sorted at *
  rw [List.pairwise_append]
  exact ⟨hA, hB, fun a ha b hb => Nat.le_trans (hAv a ha) (hvB b hb)⟩

/-! ### Insertion -/

def insert (x : Nat) : Tree → Tree
  | leaf => mk leaf x leaf
  | node _ _ l v r => if x ≤ v then balance (insert x l) v r else balance l v (insert x r)

theorem wf_insert (x : Nat) : ∀ {t : Tree}, Wf t → Wf (insert x t)
  | leaf, _ => wf_mk x trivial trivial
  | node _ _ l v r, ⟨_, _, hl, hr⟩ => by
    rw [insert]
    split
    · exact wf_balance v (wf_insert x hl) hr
    · exact wf_balance v hl (wf_insert x hr)

theorem toList_insert (x : Nat) : ∀ t : Tree, List.Perm (insert x t).toList (x :: t.toList)
  | leaf => by simp [insert]
  | node _ _ l v r => by
    rw [insert]
    split
    · rw [toList_balance, toList_node]
      exact List.Perm.append_right _ (toList_insert x l)
    · rw [toList_balance, toList_node]
      refine List.Perm.trans (List.Perm.append_left _ (List.Perm.cons v (toList_insert x r))) ?_
      rw [show l.toList ++ v :: x :: r.toList = (l.toList ++ [v]) ++ x :: r.toList by simp]
      refine List.Perm.trans List.perm_middle ?_
      simp

theorem sorted_insert (x : Nat) : ∀ {t : Tree}, Sorted t.toList → Sorted (insert x t).toList
  | leaf, _ => by simp [insert]
  | node _ _ l v r, h => by
    rw [toList_node] at h
    obtain ⟨hA, hB, hAv, hvB⟩ := sorted_append_cons h
    rw [insert]
    split
    · rename_i hx
      rw [toList_balance]
      refine sorted_append_cons_of (sorted_insert x hA) hB ?_ hvB
      intro a ha
      rcases List.mem_cons.mp ((toList_insert x l).mem_iff.mp ha) with rfl | ha
      · exact hx
      · exact hAv a ha
    · rename_i hx
      rw [toList_balance]
      refine sorted_append_cons_of hA (sorted_insert x hB) hAv ?_
      intro b hb
      rcases List.mem_cons.mp ((toList_insert x r).mem_iff.mp hb) with rfl | hb
      · omega
      · exact hvB b hb

/-! ### Deletion -/

/-- Remove the smallest element, returning it along with the rest of the tree. -/
def splitMin : Tree → Nat × Tree
  | leaf => (0, leaf)
  | node _ _ leaf v r => (v, r)
  | node _ _ (node a b c d e) v r =>
      let p := splitMin (node a b c d e)
      (p.1, balance p.2 v r)

theorem wf_splitMin : ∀ {t : Tree}, Wf t → Wf (splitMin t).2
  | leaf, _ => trivial
  | node _ _ leaf v r, ⟨_, _, _, hr⟩ => hr
  | node _ _ (node a b c d e) v r, ⟨_, _, hl, hr⟩ => by
    rw [splitMin]
    exact wf_balance v (wf_splitMin hl) hr

theorem toList_splitMin : ∀ {t : Tree}, t ≠ leaf →
    (splitMin t).1 :: (splitMin t).2.toList = t.toList
  | leaf, h => absurd rfl h
  | node _ _ leaf v r, _ => by simp [splitMin]
  | node _ _ (node a b c d e) v r, _ => by
    rw [splitMin]
    simp only [toList_balance, toList_node]
    rw [← List.cons_append, toList_splitMin (by simp)]
    simp

/-- Reunite the two subtrees of a node that is being removed. -/
def glue (l r : Tree) : Tree :=
  match r with
  | leaf => l
  | node a b c d e =>
      let p := splitMin (node a b c d e)
      balance l p.1 p.2

theorem wf_glue {l r : Tree} (hl : Wf l) (hr : Wf r) : Wf (glue l r) := by
  match r, hr with
  | leaf, _ => exact hl
  | node a b c d e, hr => exact wf_balance _ hl (wf_splitMin hr)

@[simp] theorem toList_glue (l r : Tree) : (glue l r).toList = l.toList ++ r.toList := by
  match r with
  | leaf => simp [glue]
  | node a b c d e =>
    show (balance l (splitMin (node a b c d e)).1 (splitMin (node a b c d e)).2).toList = _
    rw [toList_balance]
    congr 1
    exact toList_splitMin (by simp)

/-- Remove one occurrence of `x`. -/
def erase (x : Nat) : Tree → Tree
  | leaf => leaf
  | node _ _ l v r =>
      if x < v then balance (erase x l) v r
      else if v < x then balance l v (erase x r)
      else glue l r

theorem wf_erase (x : Nat) : ∀ {t : Tree}, Wf t → Wf (erase x t)
  | leaf, _ => trivial
  | node _ _ l v r, ⟨_, _, hl, hr⟩ => by
    rw [erase]
    split
    · exact wf_balance v (wf_erase x hl) hr
    · split
      · exact wf_balance v hl (wf_erase x hr)
      · exact wf_glue hl hr

theorem erase_append_cons_lt {A B : List Nat} {v x : Nat} (h : Sorted (A ++ v :: B))
    (hx : x < v) : (A ++ v :: B).erase x = A.erase x ++ v :: B := by
  obtain ⟨hA, hB, hAv, hvB⟩ := sorted_append_cons h
  by_cases hmem : x ∈ A
  · exact List.erase_append_left _ hmem
  · have hnot : x ∉ A ++ v :: B := by
      intro hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hmem hc
      · rcases List.mem_cons.mp hc with rfl | hc
        · omega
        · have := hvB x hc; omega
    rw [List.erase_of_not_mem hnot, List.erase_of_not_mem hmem]

theorem erase_append_cons_gt {A B : List Nat} {v x : Nat} (h : Sorted (A ++ v :: B))
    (hx : v < x) : (A ++ v :: B).erase x = A ++ v :: B.erase x := by
  obtain ⟨hA, hB, hAv, hvB⟩ := sorted_append_cons h
  have hmem : x ∉ A := fun hc => by have := hAv x hc; omega
  rw [List.erase_append_right _ hmem, List.erase_cons_tail (by simp; omega)]

theorem erase_append_cons_self {A B : List Nat} {v : Nat} :
    List.Perm (A ++ B) ((A ++ v :: B).erase v) := by
  by_cases hmem : v ∈ A
  · rw [List.erase_append_left _ hmem]
    refine List.Perm.trans (List.Perm.append_right _ (List.perm_cons_erase hmem)) ?_
    exact List.perm_middle.symm
  · rw [List.erase_append_right _ hmem, List.erase_cons_head]

theorem toList_erase (x : Nat) : ∀ {t : Tree}, Sorted t.toList →
    List.Perm (erase x t).toList (t.toList.erase x)
  | leaf, _ => by simp [erase]
  | node _ _ l v r, h => by
    rw [toList_node] at h
    obtain ⟨hA, hB, hAv, hvB⟩ := sorted_append_cons h
    rw [erase, toList_node]
    split
    · rename_i hx
      rw [toList_balance, erase_append_cons_lt h hx]
      exact List.Perm.append_right _ (toList_erase x hA)
    · split
      · rename_i hx
        rw [toList_balance, erase_append_cons_gt h hx]
        exact List.Perm.append_left _ (List.Perm.cons v (toList_erase x hB))
      · rename_i hx1 hx2
        have hxv : x = v := by omega
        subst hxv
        rw [toList_glue]
        exact erase_append_cons_self

theorem sorted_erase (x : Nat) : ∀ {t : Tree}, Sorted t.toList → Sorted (erase x t).toList
  | leaf, _ => by simp [erase]
  | node _ _ l v r, h => by
    rw [toList_node] at h
    obtain ⟨hA, hB, hAv, hvB⟩ := sorted_append_cons h
    rw [erase]
    split
    · rename_i hx
      rw [toList_balance]
      refine sorted_append_cons_of (sorted_erase x hA) hB ?_ hvB
      intro a ha
      exact hAv a (List.erase_subset ((toList_erase x hA).mem_iff.mp ha))
    · split
      · rename_i hx
        rw [toList_balance]
        refine sorted_append_cons_of hA (sorted_erase x hB) hAv ?_
        intro b hb
        exact hvB b (List.erase_subset ((toList_erase x hB).mem_iff.mp hb))
      · rw [toList_glue]
        exact sorted_append_of_cons h


/-! ### Reading off the sorted window

`mergeSort` is the sorted representative of a multiset, and so is the in-order traversal of
the tree, so the two agree.
-/

theorem pairwise_le_bool {l : List Nat} (h : Sorted l) :
    List.Pairwise (fun a b : Nat => (decide (a ≤ b)) = true) l :=
  List.Pairwise.imp (by simp) h

theorem mergeSort_toList {t : Tree} {w : List Nat} (hs : Sorted t.toList)
    (hp : List.Perm t.toList w) : w.mergeSort = t.toList := by
  refine List.Perm.eq_of_pairwise (le := fun a b : Nat => (decide (a ≤ b)) = true)
    (fun a b _ _ hab hba => Nat.le_antisymm (by simpa using hab) (by simpa using hba))
    (List.pairwise_mergeSort (by intro a b c; simp; omega) (by intro a b; simp; omega) w)
    (pairwise_le_bool hs)
    (List.Perm.trans (List.mergeSort_perm w _) hp.symm)

end Tree

/-! ## The state

The window is a banker's queue (amortised O(1) per element) and the order-statistic tree
carries the same elements sorted, so a query never has to sort anything.
-/

structure State where
  m : Nat
  k : Nat
  len : Nat
  front : List Nat
  back : List Nat
  tree : Tree

/-- The window the state represents, in arrival order. -/
def State.window (s : State) : List Nat := s.front ++ s.back.reverse

/-- Take the oldest element off a banker's queue. -/
def pop (f b : List Nat) : Option (Nat × List Nat × List Nat) :=
  match f with
  | y :: f' => some (y, f', b)
  | [] =>
    match b.reverse with
    | [] => none
    | y :: f' => some (y, f', [])

theorem pop_eq_none {f b : List Nat} (h : pop f b = none) : f ++ b.reverse = [] := by
  match f, h with
  | [], h =>
    simp only [pop] at h
    match hb : b.reverse, h with
    | [], _ => simp

theorem pop_eq_some {f b : List Nat} {y : Nat} {f' b' : List Nat}
    (h : pop f b = some (y, f', b')) : f ++ b.reverse = y :: (f' ++ b'.reverse) := by
  match f, h with
  | y₀ :: f₀, h =>
    simp only [pop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp
  | [], h =>
    simp only [pop] at h
    match hb : b.reverse, h with
    | y₀ :: f₀, h =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp

def init (m k : Nat) : State :=
  { m := m, k := k, len := 0, front := [], back := [], tree := Tree.leaf }

def addElement (s : State) (x : Nat) : State :=
  if s.len < s.m then
    { s with len := s.len + 1, back := x :: s.back, tree := s.tree.insert x }
  else
    match pop s.front s.back with
    | none => { s with back := [x], tree := s.tree.insert x }
    | some (y, f, b) =>
        { s with front := f, back := x :: b, tree := (s.tree.erase y).insert x }

def calculateMKAverage (s : State) : Int :=
  if s.len < s.m then
    -1
  else
    Int.ofNat ((s.tree.sumFirst (s.m - s.k) - s.tree.sumFirst s.k) / (s.m - 2 * s.k))

def implementation : MKImplementation where
  State := State
  init := init
  addElement := addElement
  calculateMKAverage := calculateMKAverage

/-! ## Correctness -/

theorem lastN_nil (m : Nat) : lastN [] m = [] := by
  simp [lastN]

theorem length_lastN (xs : List Nat) (m : Nat) :
    (lastN xs m).length = min xs.length m := by
  simp [lastN]
  omega

theorem lastN_append_one (xs : List Nat) (x m : Nat) (hm : 0 < m) :
    lastN (xs ++ [x]) m =
      if xs.length < m then lastN xs m ++ [x] else (lastN xs m).tail ++ [x] := by
  by_cases h : xs.length < m
  · simp only [h, if_pos]
    have h1 : xs.length + 1 - m = 0 := by omega
    have h2 : xs.length - m = 0 := by omega
    simp [lastN, h1, h2]
  · simp only [h, if_neg, not_false_iff]
    have hle : xs.length - m + 1 ≤ xs.length := by omega
    have h1 : (xs ++ [x]).length - m = xs.length - m + 1 := by
      simp; omega
    rw [lastN, h1, List.drop_append_of_le_length hle, lastN, List.tail_drop]

/-- The state invariant: the queue holds the last `m` elements of the stream in arrival
order, and the tree holds the very same elements in sorted order. -/
def Inv (m k : Nat) (s : State) (stream : List Nat) : Prop :=
  s.m = m ∧ s.k = k ∧ s.len = min stream.length m ∧ s.window = lastN stream m ∧
    s.tree.Wf ∧ Tree.Sorted s.tree.toList ∧ List.Perm s.tree.toList s.window

theorem inv_init (m k : Nat) : Inv m k (init m k) [] := by
  refine ⟨rfl, rfl, ?_, ?_, trivial, ?_, ?_⟩
  · simp [init]
  · simp [init, State.window, lastN_nil]
  · simp [init, Tree.Sorted]
  · simp [init, State.window]

theorem addElement_not_full (s : State) (x : Nat) (h : s.len < s.m) :
    addElement s x =
      { s with len := s.len + 1, back := x :: s.back, tree := s.tree.insert x } := by
  simp [addElement, h]

theorem addElement_pop (s : State) (x y : Nat) (f b : List Nat) (h : ¬ s.len < s.m)
    (hpop : pop s.front s.back = some (y, f, b)) :
    addElement s x =
      { s with front := f, back := x :: b, tree := (s.tree.erase y).insert x } := by
  simp [addElement, h, hpop]

/-- Field-by-field description of an insertion into a window that is not yet full. -/
theorem add_not_full (s : State) (x : Nat) (h : s.len < s.m) :
    (addElement s x).m = s.m ∧ (addElement s x).k = s.k ∧
      (addElement s x).len = s.len + 1 ∧ (addElement s x).window = s.window ++ [x] ∧
      (addElement s x).tree = s.tree.insert x := by
  rw [addElement_not_full s x h]
  refine ⟨rfl, rfl, rfl, ?_, rfl⟩
  simp [State.window]

/-- Field-by-field description of an insertion that also evicts the oldest element `y`. -/
theorem add_pop (s : State) (x y : Nat) (f b : List Nat) (h : ¬ s.len < s.m)
    (hpop : pop s.front s.back = some (y, f, b)) :
    (addElement s x).m = s.m ∧ (addElement s x).k = s.k ∧
      (addElement s x).len = s.len ∧ (addElement s x).window = s.window.tail ++ [x] ∧
      (addElement s x).tree = (s.tree.erase y).insert x := by
  have hsplit : s.window = y :: (f ++ b.reverse) := pop_eq_some hpop
  rw [addElement_pop s x y f b h hpop]
  refine ⟨rfl, rfl, rfl, ?_, rfl⟩
  show f ++ (x :: b).reverse = s.window.tail ++ [x]
  rw [hsplit]
  simp

theorem inv_add (m k : Nat) (hm : 0 < m) (s : State) (stream : List Nat) (x : Nat)
    (h : Inv m k s stream) : Inv m k (addElement s x) (stream ++ [x]) := by
  obtain ⟨hm', hk', hlen, hwin, hwf, hsorted, hperm⟩ := h
  subst hm'
  subst hk'
  by_cases hfull : s.len < s.m
  · have hlt : stream.length < s.m := by omega
    obtain ⟨e1, e2, e3, e4, e5⟩ := add_not_full s x hfull
    refine ⟨e1, e2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e3]; simp; omega
    · rw [e4, hwin, lastN_append_one _ _ _ hm, if_pos hlt]
    · rw [e5]; exact Tree.wf_insert x hwf
    · rw [e5]; exact Tree.sorted_insert x hsorted
    · rw [e5, e4]
      refine List.Perm.trans (Tree.toList_insert x s.tree) ?_
      exact List.Perm.trans (List.Perm.cons x hperm) (List.perm_append_singleton _ _).symm
  · have hge : ¬ stream.length < s.m := by omega
    have hwinlen : s.window.length = s.m := by
      rw [hwin, length_lastN]; omega
    cases hpop : pop s.front s.back with
    | none =>
      exfalso
      have hnil : s.window = [] := pop_eq_none hpop
      rw [hnil] at hwinlen
      simp at hwinlen
      omega
    | some p =>
      obtain ⟨y, f, b⟩ := p
      have hsplit : s.window = y :: (f ++ b.reverse) := pop_eq_some hpop
      obtain ⟨e1, e2, e3, e4, e5⟩ := add_pop s x y f b hfull hpop
      refine ⟨e1, e2, ?_, ?_, ?_, ?_, ?_⟩
      · rw [e3]; simp; omega
      · rw [e4, hwin, lastN_append_one _ _ _ hm, if_neg hge]
      · rw [e5]; exact Tree.wf_insert x (Tree.wf_erase y hwf)
      · rw [e5]; exact Tree.sorted_insert x (Tree.sorted_erase y hsorted)
      · rw [e5, e4, hsplit]
        refine List.Perm.trans (Tree.toList_insert x _) ?_
        refine List.Perm.trans (List.Perm.cons x ?_) (List.perm_append_singleton _ _).symm
        refine List.Perm.trans (Tree.toList_erase y hsorted) ?_
        have hpe := List.Perm.erase y hperm
        rw [hsplit, List.erase_cons_head] at hpe
        simpa using hpe

theorem calc_eq (m k : Nat) (hk : 2 * k < m) (s : State) (stream : List Nat)
    (h : Inv m k s stream) : calculateMKAverage s = expectedAverage stream m k := by
  obtain ⟨hm', hk', hlen, hwin, hwf, hsorted, hperm⟩ := h
  subst hm'
  subst hk'
  by_cases hshort : stream.length < s.m
  · have : s.len < s.m := by omega
    simp [calculateMKAverage, expectedAverage, this, hshort]
  · have hlen' : ¬ s.len < s.m := by omega
    have hsort : (lastN stream s.m).mergeSort = s.tree.toList := by
      rw [← hwin]; exact Tree.mergeSort_toList hsorted hperm
    have hsplit : (s.tree.toList.take (s.m - s.k)).sum
        = (s.tree.toList.take s.k).sum
          + ((s.tree.toList.drop s.k).take (s.m - 2 * s.k)).sum := by
      rw [show s.m - s.k = s.k + (s.m - 2 * s.k) by omega, List.take_add,
        List.sum_append_nat]
    have harith : (s.tree.toList.take (s.m - s.k)).sum - (s.tree.toList.take s.k).sum
        = ((s.tree.toList.drop s.k).take (s.m - 2 * s.k)).sum := by omega
    simp only [calculateMKAverage, expectedAverage, if_neg hlen', if_neg hshort, hsort,
      Tree.sumFirst_eq hwf, harith]

theorem go_eq (m k : Nat) (hm : 0 < m) (hk : 2 * k < m) :
    ∀ (ops : List Op) (s : State) (stream : List Nat), Inv m k s stream →
      runImplementation.go implementation s ops = runBaseline m k ops stream := by
  intro ops
  induction ops with
  | nil => intro s stream _; simp [runImplementation.go, runBaseline]
  | cons op rest ih =>
    intro s stream h
    cases op with
    | add x =>
      simp only [runImplementation.go, runBaseline]
      exact ih _ _ (inv_add m k hm s stream x h)
    | «calc» =>
      simp only [runImplementation.go, runBaseline, List.cons.injEq]
      exact ⟨calc_eq m k hk s stream h, ih s stream h⟩

theorem solution_is_correct
    (m k : Nat)
    (hm : 3 ≤ m)
    (hk : 2 * k < m)
    (ops : List Op) :
    runImplementation implementation m k ops =
      runBaseline m k ops := by
  have h := go_eq m k (by omega) hk ops (init m k) [] (inv_init m k)
  simpa [runImplementation, implementation] using h

end Anon3.Student
