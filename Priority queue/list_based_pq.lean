import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Order.Basic
import Mathlib.Data.Multiset.Lattice
import Mathlib.Order.Monotone.Basic


structure PriorityQueue where
  queue : List Nat

namespace PriorityQueue

def empty : PriorityQueue := {queue := []}

-- prob to bool
def leBool (a b : Nat) [Decidable (a ≤ b)] : Bool :=
  a ≤ b

def eqBool (a b : Nat) : Bool :=
  a = b

-- if is sorted
def invar (q : PriorityQueue) : Bool :=
  q.queue.Sorted (leBool · ·)

-- list to multiset
def mset (q : PriorityQueue) : Multiset Nat := Multiset.ofList q.queue


def insert (x : Nat) (q : PriorityQueue) : PriorityQueue :=
  {
    queue := List.mergeSort (x::q.queue)
  }


def get_min (q : PriorityQueue) : Option Nat := q.queue.head?

def del_min (q : PriorityQueue) : PriorityQueue :=
  match q.queue with
  | [] => q
  | _ :: x => {queue := x}


def merge (q1 q2 : PriorityQueue) : PriorityQueue :=
  {
    queue := List.merge q1.queue q2.queue
  }

def list_to_pq (l : List Nat) : PriorityQueue :=
  {
    queue := List.mergeSort l
  }

def optionToMultiset (x : Option Nat) : Multiset Nat :=
match x with
  | none => ∅
  | some v => {v}

open List Multiset

lemma mset_em (m : Multiset Nat) : (m ≠ ∅) = true ↔ m ≠ 0  := by
simp

-- Exercise 14.1. Give a list-based implementation of mergeable priority queues with
-- constant-time get_min and del_min. Verify the correctness of your implementation
-- w.r.t. Priority_Queue_Merge.

-- correctness prove
-- empty invariant
theorem empty_invar : invar (PriorityQueue.empty) = true := by simp [invar, empty]

-- empty mset
theorem empty_mset : mset (PriorityQueue.empty) = ∅ := by simp [mset, empty]

-- perm to prove is same
lemma mergeSort_multiset (l : List Nat) : ofList (List.mergeSort l) = ofList l := by
simp_all [List.Perm.merge]
apply mergeSort_perm


lemma mset_eq_ofList (q : PriorityQueue) : q.mset = ofList q.queue := by
simp_all [mset]

-- insert mset
theorem insert_mset (q : PriorityQueue) (x : Nat) : invar q → mset (insert x q) = {x} + (mset q)  := by
rw [insert]
rw [mset]
simp_all [mergeSort_multiset]
rw [mset_eq_ofList]
simp_all [cons_add]


-- insert invariant
theorem insert_invar (q : PriorityQueue) (x : Nat) : invar q → invar (insert x q) := by
  {
    rw [invar]
    rw [decide_eq_true_iff]
    simp [insert]
    rw [invar]
    rw [decide_eq_true_iff]
    intro h
    simp [h]
    rw [Sorted]
    apply sorted_mergeSort

    · simp_all [leBool]
      apply le_trans

    · simp_all [leBool]
      intro x y
      apply le_total

  }

-- prove mset del_min invariant
theorem del_min_mset (q : PriorityQueue) :
invar q ∧ mset q != ∅ → mset (del_min q) = mset q - optionToMultiset (get_min q) := by
 {
  simp_all
  rw [invar,del_min,mset]
  simp_all
  intro ha hb
  split

  ·contradiction

  ·rw [get_min]
   simp_all
   rw [optionToMultiset]
   simp_all
   rw [mset]

 }

-- del_min pq invariant
theorem del_min_invar (q : PriorityQueue) :
 invar q ∧ mset q ≠ ∅ → invar (del_min q) := by
 {
  simp [mset_em]
  rw [invar]
  simp [decide_eq_true_iff]
  intro ha hb
  simp [del_min]
  split

  ·simp_all [invar]

  ·rw [invar]
   simp_all

 }

-- merge mset
theorem merge_mset (q1 q2 : PriorityQueue) :
  invar q1 ∧ invar q2 → mset (merge q1 q2) = mset q1 + mset q2 := by
  simp [invar, merge, mset]
  intro h₁ h₂
  simp [List.merge_perm_append]

-- merge invariant
theorem merge_invar (q1 q2 : PriorityQueue):
  invar q1 ∧ invar q2 → invar (merge q1 q2) := by
  {
    simp_all [invar]
    simp [merge]
    simp [leBool]
    intros h₁ h₂
    rw [PriorityQueue.queue, PriorityQueue.queue]
    apply List.Sorted.merge

    · exact h₁

    · exact h₂

  }


-- multiset sort needs a complicated relation
instance : LinearOrder Nat := inferInstance
instance : IsTrans Nat (· ≤ ·) := inferInstance
instance : IsAntisymm Nat (· ≤ ·) := inferInstance
instance : IsTotal Nat (· ≤ ·) := inferInstance
noncomputable def min_mset (s : Multiset Nat) : Option Nat :=
  if s ≠ 0 then
    (s.sort (· ≤ ·)).head?
  else none

-- when l is sorted the mergesort is itself
lemma l_merge_eq_l_iff_sorted (l : PriorityQueue) :
Sorted (fun x1 x2 ↦ leBool x1 x2) l.queue → l.queue.mergeSort = l.queue := by
  intro h_sorted
  have h_eq : l.queue.mergeSort = l.queue := List.mergeSort_of_sorted h_sorted
  exact h_eq


theorem get_min_mset (q : PriorityQueue):
 invar q ∧ mset q != ∅ → (get_min q) = min_mset (mset q) := by
  simp_all
  intro h₁ h₂
  cases' q with queue
  simp_all [invar, mset, get_min, min_mset]
  rw [l_merge_eq_l_iff_sorted]
  simp_all
