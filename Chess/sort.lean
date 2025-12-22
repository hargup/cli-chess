import Mathlib.Data.List.Perm.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

open List

namespace SortTutorial

section PermHelpers
variable {α : Type _}

theorem Perm.append_right {l1 l2 : List α} (p : l1 ~ l2) (t : List α) :
    (l1 ++ t) ~ (l2 ++ t) := by
  induction p with
  | nil => rfl
  | cons a _ ih => exact Perm.cons a ih
  | swap a b l => exact Perm.swap a b (l ++ t)
  | trans _ _ ihp ihq => exact ihp.trans ihq

theorem Perm.append_left (t : List α) {l1 l2 : List α} (p : l1 ~ l2) :
    (t ++ l1) ~ (t ++ l2) := by
  induction t with
  | nil => exact p
  | cons x _ ih => exact Perm.cons x ih

theorem Perm.middle (l1 l2 : List α) (a : α) :
    (l1 ++ (a :: l2)) ~ (a :: (l1 ++ l2)) := by
  induction l1 with
  | nil => rfl
  | cons x xs ih => exact (Perm.cons x ih).trans (Perm.swap x a (xs ++ l2)).symm

end PermHelpers

section Sorting
variable {α : Type _} [LinearOrder α]

inductive Sorted : List α → Prop
  | nil : Sorted []
  | single (a : α) : Sorted [a]
  | cons {a b : α} {l : List α} : a ≤ b → Sorted (b :: l) → Sorted (a :: b :: l)

theorem Sorted.inv_cons {a b : α} {l : List α} (h : Sorted (a :: b :: l)) :
    a ≤ b ∧ Sorted (b :: l) := by
  cases h with
  | cons hab htail => exact ⟨hab, htail⟩

theorem Sorted.tail_sorted {x : α} {xs : List α} (h : Sorted (x :: xs)) : Sorted xs := by
  cases xs with
  | nil => exact Sorted.nil
  | cons y ys => exact (Sorted.inv_cons h).2

structure SortedPerm (l : List α) where
  out    : List α
  sorted : Sorted out
  perm   : out ~ l

/-! ### Insertion Sort -/

def insert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: insert a l

theorem perm_insert (a : α) (l : List α) : insert a l ~ (a :: l) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      unfold insert
      split
      · rfl
      · exact (Perm.cons b ih).trans (Perm.swap b a l).symm

theorem sorted_insert (x : α) : ∀ {l : List α}, Sorted l → Sorted (insert x l)
  | [], _ => Sorted.single x
  | [b], Sorted.single _ => by
      unfold insert
      split
      next hle => exact Sorted.cons hle (Sorted.single b)
      next hle => exact Sorted.cons (le_of_not_ge hle) (Sorted.single x)
  | a :: b :: t, hs => by
      have hab := (Sorted.inv_cons hs).1
      have htail := (Sorted.inv_cons hs).2
      unfold insert
      split
      next hxa => exact Sorted.cons hxa hs
      next hxa =>
        have hax : a ≤ x := le_of_not_ge hxa
        have ih := sorted_insert x htail
        simp only [insert] at ih ⊢
        split at ih <;> split
        · exact Sorted.cons hax ih  -- x ≤ b: insert puts x before b
        · contradiction  -- contradiction: ¬(x ≤ b) and x ≤ b
        · contradiction  -- contradiction: x ≤ b and ¬(x ≤ b)
        · exact Sorted.cons hab ih  -- ¬(x ≤ b): insert recurses

def insertSortList : List α → List α
  | [] => []
  | a :: l => insert a (insertSortList l)

theorem perm_insertSortList (l : List α) : insertSortList l ~ l := by
  induction l with
  | nil => rfl
  | cons a l ih => exact (perm_insert a _).trans (Perm.cons a ih)

theorem sorted_insertSortList (l : List α) : Sorted (insertSortList l) := by
  induction l with
  | nil => exact Sorted.nil
  | cons a l ih => exact sorted_insert a ih

def insertSort (l : List α) : SortedPerm l :=
  ⟨insertSortList l, sorted_insertSortList l, perm_insertSortList l⟩

/-! ### Merge Sort -/

def split : List α → List α × List α
  | [] => ([], [])
  | [a] => ([a], [])
  | a :: b :: t =>
      let (l1, l2) := split t
      (a :: l1, b :: l2)

theorem perm_split : ∀ (l : List α), (split l).1 ++ (split l).2 ~ l
  | [] => Perm.refl []
  | [a] => Perm.refl [a]
  | a :: b :: t => by
      simp only [split]
      -- Goal: (a :: (split t).1) ++ (b :: (split t).2) ~ a :: b :: t
      -- which is: a :: ((split t).1 ++ b :: (split t).2) ~ a :: b :: t
      have ih := perm_split t
      -- ih : (split t).1 ++ (split t).2 ~ t
      -- Need to show: (split t).1 ++ b :: (split t).2 ~ b :: t
      -- Use Perm.middle: (split t).1 ++ (b :: (split t).2) ~ b :: ((split t).1 ++ (split t).2)
      -- Then cons b ih: b :: ((split t).1 ++ (split t).2) ~ b :: t
      have step1 : ((split t).1 ++ (b :: (split t).2)) ~ (b :: ((split t).1 ++ (split t).2)) :=
        Perm.middle _ _ b
      have step2 : (b :: ((split t).1 ++ (split t).2)) ~ (b :: t) := Perm.cons b ih
      exact Perm.cons a (step1.trans step2)

def merge : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if x ≤ y then x :: merge xs (y :: ys)
      else y :: merge (x :: xs) ys

theorem perm_merge : ∀ (xs ys : List α), merge xs ys ~ (xs ++ ys)
  | [], ys => by simp [merge]
  | x :: xs, [] => by simp [merge]
  | x :: xs, y :: ys => by
      simp only [merge]
      split
      next hxy =>
        simp only [cons_append]
        exact Perm.cons x (perm_merge xs (y :: ys))
      next hxy =>
        simp only [cons_append]
        exact (Perm.cons y (perm_merge (x :: xs) ys)).trans (Perm.middle (x :: xs) ys y).symm

theorem sorted_merge {xs ys : List α} (hsx : Sorted xs) (hsy : Sorted ys) : Sorted (merge xs ys) := by
  induction xs generalizing ys with
  | nil => simp [merge]; exact hsy
  | cons x xs ih_xs =>
      induction ys with
      | nil => simp [merge]; exact hsx
      | cons y ys ih_ys =>
          simp only [merge]
          by_cases hxy : x ≤ y
          · simp only [hxy, ↓reduceIte]
            match xs with
            | [] => simp [merge]; exact Sorted.cons hxy hsy
            | x2 :: xs2 =>
                have hsx' : Sorted (x :: x2 :: xs2) := hsx
                have hxx2 := (Sorted.inv_cons hsx').1
                have ih := ih_xs (Sorted.tail_sorted hsx') hsy
                simp only [merge] at ih ⊢
                by_cases hx2y : x2 ≤ y
                · simp only [hx2y, ↓reduceIte] at ih ⊢; exact Sorted.cons hxx2 ih
                · simp only [hx2y, ↓reduceIte] at ih ⊢; exact Sorted.cons hxy ih
          · simp only [hxy, ↓reduceIte]
            match ys with
            | [] => simp [merge]; exact Sorted.cons (le_of_not_ge hxy) hsx
            | y2 :: ys2 =>
                have hsy' : Sorted (y :: y2 :: ys2) := hsy
                have hyy2 := (Sorted.inv_cons hsy').1
                have ih := ih_ys (Sorted.tail_sorted hsy')
                simp only [merge] at ih ⊢
                by_cases hxy2 : x ≤ y2
                · simp only [hxy2, ↓reduceIte] at ih ⊢; exact Sorted.cons (le_of_not_ge hxy) ih
                · simp only [hxy2, ↓reduceIte] at ih ⊢; exact Sorted.cons hyy2 ih

theorem split_len_fst : ∀ (l : List α), (split l).1.length ≤ l.length
  | [] => Nat.le_refl 0
  | [_] => Nat.le_refl 1
  | _ :: _ :: t => by
      simp only [split, length_cons]
      exact Nat.succ_le_succ (Nat.le_trans (split_len_fst t) (Nat.le_succ _))

theorem split_len_snd : ∀ (l : List α), (split l).2.length ≤ l.length
  | [] => Nat.le_refl 0
  | [_] => Nat.zero_le 1
  | _ :: _ :: t => by
      simp only [split, length_cons]
      exact Nat.succ_le_succ (Nat.le_trans (split_len_snd t) (Nat.le_succ _))

theorem split_len_fst_succ (a b : α) (t : List α) :
    (split (a :: b :: t)).1.length ≤ Nat.succ t.length := by
  simp only [split, length_cons]
  exact Nat.succ_le_succ (split_len_fst t)

theorem split_len_snd_succ (a b : α) (t : List α) :
    (split (a :: b :: t)).2.length ≤ Nat.succ t.length := by
  simp only [split, length_cons]
  exact Nat.succ_le_succ (split_len_snd t)

def mergeSortAux : Nat → List α → List α
  | 0, _ => []
  | _+1, [] => []
  | _+1, [a] => [a]
  | n+1, l =>
      let (l1, l2) := split l
      merge (mergeSortAux n l1) (mergeSortAux n l2)

theorem mergeSortAux_spec (fuel : Nat) (l : List α) (h : l.length ≤ fuel) :
    Sorted (mergeSortAux fuel l) ∧ (mergeSortAux fuel l ~ l) := by
  induction fuel generalizing l with
  | zero =>
      have : l.length = 0 := Nat.le_zero.mp h
      have : l = [] := List.eq_nil_of_length_eq_zero this
      simp [this, mergeSortAux, Sorted.nil]
  | succ n ih =>
      match l with
      | [] => simp [mergeSortAux, Sorted.nil]
      | [a] => simp [mergeSortAux, Sorted.single]
      | a :: b :: t =>
          simp only [mergeSortAux]
          -- h : (a :: b :: t).length ≤ n + 1, so t.length + 2 ≤ n + 1, so t.length + 1 ≤ n
          have ht : Nat.succ t.length ≤ n := by
            simp only [length_cons] at h
            exact Nat.lt_succ_iff.mp h
          have h1 : (split (a :: b :: t)).1.length ≤ n :=
            Nat.le_trans (split_len_fst_succ a b t) ht
          have h2 : (split (a :: b :: t)).2.length ≤ n :=
            Nat.le_trans (split_len_snd_succ a b t) ht
          have ⟨s1, p1⟩ := ih (split (a :: b :: t)).1 h1
          have ⟨s2, p2⟩ := ih (split (a :: b :: t)).2 h2
          refine ⟨sorted_merge s1 s2, ?_⟩
          have ps := perm_split (a :: b :: t)
          exact (perm_merge _ _).trans ((p1.append_right _).trans ((p2.append_left _).trans ps))

def mergeSort (l : List α) : SortedPerm l :=
  let ⟨s, p⟩ := mergeSortAux_spec l.length l (Nat.le_refl _)
  ⟨mergeSortAux l.length l, s, p⟩

end Sorting

#eval (insertSort [3,1,2,5,4]).out
#eval (mergeSort [3,1,2,5,4]).out

end SortTutorial
