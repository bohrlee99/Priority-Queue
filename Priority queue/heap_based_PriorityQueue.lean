import Mathlib.Data.Tree.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Tactic

-- Autor : Danyang Li
/-- Defines `PriorityQueue` as a wrapper around `Tree Nat` to implement a priority queue. -/
structure PriorityQueue  where
  queue : Tree Nat

namespace PriorityQueue

/-- Define an empty priority queue. -/
def empty : PriorityQueue := {queue := Tree.nil}

/-- Computes the boolean value for `a ≤ b`. -/
def leBool (a b : Nat) [Decidable (a ≤ b)]: Bool :=
  a ≤ b

/-- Retrieves the value of the root node, returning `none` if the tree is empty. -/
def get_value : Tree Nat → Option Nat
  | Tree.nil => none
  | Tree.node v _ _ => some v

/-- Converts a tree to a list using an in-order traversal (left-root-right). -/
def tree_to_list : Tree Nat → List Nat
  | Tree.nil => []
  | Tree.node v l r => tree_to_list l ++ [v] ++ tree_to_list r

/-- Checks whether `a` is less than or equal to all elements in tree `t`. -/
def le_tree (a : Nat) (t : Tree Nat) : Bool :=
  let ha := Multiset.ofList (tree_to_list t)
  ∀ x ∈ ha, a ≤ x

def le_subnode (v : Nat) (t : Tree Nat) : Bool :=
  match get_value t with
  | none => true
  | some x => v ≤ x

/-- Checks whether a tree satisfies the heap property (min-heap). -/
def is_heap_property : Tree Nat → Bool
  | Tree.nil => true
  | Tree.node _ Tree.nil Tree.nil => true
  | Tree.node v l r =>
    le_subnode v l && le_subnode v r && is_heap_property l && is_heap_property r
  -- | Tree.node v l r =>
  --   le_tree v l && le_tree v r &&
  --   is_heap_property l && is_heap_property r

/-- Returns the multiset representation of a priority queue. -/
def mset (q : PriorityQueue):  Multiset Nat :=
  Multiset.ofList (tree_to_list q.queue)

/-- Retrieves the minimum element (root node) of the priority queue, if any. -/
def get_min (q : PriorityQueue) : Option Nat :=
  match q.queue with
    | Tree.nil => none
    | Tree.node v _ _ => some v

/-- Computes that the number of nodes in the left subtree does not exceed the total tree size. -/
lemma tree_left_le (a : Tree Nat) : a.left.numNodes ≤ a.numNodes := by
  simp
  split
  {
    simp
  }
  {
    rw [Tree.numNodes]
    linarith
  }

/-- Computes that the number of nodes in the right subtree does not exceed the total tree size. -/
lemma tree_right_le (a : Tree Nat) : a.right.numNodes ≤ a.numNodes := by
  simp
  split
  {
    simp
  }
  {
    rw [Tree.numNodes]
    linarith
  }

/-- Merges two heap trees while maintaining the min-heap property. -/
def merge_tree  (q p: Tree Nat): Tree Nat :=
  match q, p with
  | Tree.nil, r => r
  | l, Tree.nil => l
  | Tree.node v1 l1 r1, Tree.node v2 l2 r2 =>
    if v1 ≤ v2 then
      Tree.node v1 l1 (merge_tree r1 (Tree.node v2 l2 r2))
    else
      Tree.node v2 l2 (merge_tree (Tree.node v1 l1 r1) r2)

/-- Merges two priority queues by merging their trees. -/
def merge (q p : PriorityQueue) : PriorityQueue :=
  {queue := merge_tree q.queue p.queue}

/-- Inserts a new value `v` into the priority queue by merging `{v}` with `q`. -/
def insert (q : PriorityQueue) (v : Nat) : PriorityQueue :=
  merge {queue := Tree.node v Tree.nil Tree.nil} q

/-- Deletes the minimum element (root node) from the priority queue. -/
def delete_min (q : PriorityQueue) : PriorityQueue :=
  match q.queue with
  | Tree.nil => {queue := Tree.nil}
  | Tree.node _ Tree.nil Tree.nil => {queue := Tree.nil}
  | Tree.node _ Tree.nil r => {queue := r}
  | Tree.node _ l Tree.nil =>{queue := l}
  | Tree.node _ l r => {queue := merge_tree l r}

/-- Checks whether a priority queue satisfies the heap invariant (min-heap property). -/
def invar (q : PriorityQueue) : Bool :=
  is_heap_property q.queue

/-- Proves that the number of nodes in `merge_tree` equals the sum of nodes in `q` and `p`. -/
lemma merge_numnode (q p: Tree Nat):
  Tree.numNodes q + Tree.numNodes p = Tree.numNodes (merge_tree q p) := by
  {
    induction q generalizing p with
    | nil => simp [merge_tree]
    | node v1 l1 r1 ih1 ih2 =>
      induction p with
      | nil => simp [merge_tree]
      | node v2 l2 r2 ih3 ih4 =>
        rw [merge_tree]
        by_cases h : v1 ≤ v2
        {
          simp_all only [Tree.numNodes, ite_true]
          rw [← ih1, ← ih1]
          rw [← ih2]
          simp
          linarith
        }
        {
          rw [if_neg h]
          simp_all [merge_tree, Tree.numNodes]
          linarith
        }
  }

/-- Recursively deletes `get_min` to construct a sorted list while ensuring termination. -/
def heap_to_list (q : PriorityQueue) : List Nat :=
  if q.queue = Tree.nil then []
  else
  let m := get_min q
  let newPQ : PriorityQueue := delete_min q
  match m with
  | none => []
  | some v => v :: heap_to_list newPQ
  termination_by Tree.numNodes q.queue
  decreasing_by
    simp_all
    rw [delete_min]
    split
    {
      contradiction
    }
    {
      rw [queue]
      simp_all
    }
    {
      rw [queue]
      simp_all
    }
    {
      simp_all
    }
    {
      rw [queue]
      simp_all
      rw [merge_numnode]
      linarith
    }

/-- Alternative method to retrieve a sorted list: convert the tree to a list and apply `mergeSort`. -/
def list (q : PriorityQueue) : List Nat :=
    let l := tree_to_list q.queue
    l.mergeSort

/-- Exercise 14.3
Proves that `list q` converted to a `Multiset` equals `mset q`. -/
theorem list_mset (q : PriorityQueue) :
Multiset.ofList (list q) = mset q := by
   {
    induction q.queue with
    | nil =>
      rw [list]
      rw [mset]
      simp_all
      apply List.mergeSort_perm
    | node v l r ih1 ih2 =>
      rw [list]
      rw [mset]
      simp_all
      apply List.mergeSort_perm
   }

/-- Proves that `list q` is sorted if `invar q = true`. -/
theorem list_sorted (q : PriorityQueue) :
 invar q → (list q).Sorted (leBool · ·) := by
 {
    intro h
    rw [list]
    rw [List.Sorted]
    apply List.sorted_mergeSort
    {
      intro ha hb hc ih1 ih2
      rw [leBool] at ih1 ih2
      rw [leBool]
      simp_all
      apply Nat.le_trans ih1 ih2
    }
    {
      intro ha hb
      simp
      rw [leBool,leBool]
      simp_all
      apply Nat.le_total
    }
 }

-- Exercise 14.2
-- Show functional correctness of the above definition of merge
lemma mset_list_add' (a b c: List Nat) :
  Multiset.ofList a + Multiset.ofList b + Multiset.ofList c= Multiset.ofList (a ++ b ++ c) := by
  {
    simp
  }

/-- Proves that merging two trees (`merge_tree`) results in a multiset equal to `t1 + t2`. -/
lemma merge_tree_mset (t1 t2 : Tree Nat) :
  Multiset.ofList (tree_to_list (merge_tree t1 t2)) = tree_to_list t1 + tree_to_list t2 := by
  {
    induction t1 generalizing t2 with
    | nil =>
      rw [merge_tree]
      simp
      rw [tree_to_list]
      simp
    | node v1 l1 r1 ih1 ih2 =>
      induction t2 with
      | nil =>
        rw [merge_tree]
        simp
        rw [tree_to_list]
        · simp
        · simp
      | node v2 l2 r2 ih3 ih4 =>
        rw [merge_tree]
        by_cases h : v1 ≤ v2
        {
          rw [if_pos h]
          rw [tree_to_list]
          rw [← mset_list_add']
          rw [ih2]
          rw [tree_to_list,tree_to_list]
          rw [← mset_list_add',← mset_list_add']
          rw [← add_assoc]
        }
        {
          rw [if_neg h]
          rw [tree_to_list]
          rw [← mset_list_add']
          rw [ih4]
          rw [tree_to_list,tree_to_list]
          rw (occs := .pos [1]) [add_comm]
          rw [← mset_list_add',← mset_list_add']
          rw [← add_assoc]
          rw (occs := .pos [2]) [add_assoc]
          rw (occs := .pos [5]) [add_comm]
          rw [← add_assoc]
          rw (occs := .pos [1]) [add_assoc]
          rw (occs := .pos [5]) [add_comm]
          rw [← add_assoc,← add_assoc,← add_assoc]
        }
  }

/-- Proves that merging two priority queues does not alter their combined multiset. -/
theorem merge_mset (q p : PriorityQueue) :
  invar q → invar p → mset (merge q p)  = mset q + mset p := by
  {
    intro ha hb
    rw [merge]
    rw [mset]
    simp
    rw [mset,mset]
    rw [merge_tree_mset]
  }

/-- Proves that if `Tree.node v l r` satisfies the heap property, then `l` does as well. -/
lemma left_tree_invar :
is_heap_property (Tree.node v l r) = true → is_heap_property l := by
  rw [is_heap_property.eq_def]
  aesop

/-- Proves that if `Tree.node v l r` satisfies the heap property, then `r` does as well. -/
lemma right_tree_invar :
is_heap_property (Tree.node v l r) = true → is_heap_property r := by
  rw [is_heap_property.eq_def]
  aesop

lemma ofList_add (a b c: List Nat) :
Multiset.ofList a + Multiset.ofList b + Multiset.ofList c = Multiset.ofList (a ++ b ++ c) := by
  simp


lemma add_multi_ex (a b c d: Multiset Nat) : a + b + c + d =  b + c + d + a := by
  rw (occs := .pos [4]) [add_comm]
  rw [← add_assoc,← add_assoc]

lemma merge_tree_eq (q p: Tree Nat) :
 Multiset.ofList (tree_to_list q ++ tree_to_list p) = Multiset.ofList (tree_to_list (merge_tree q p)) := by
 {
    induction q generalizing p with
    | nil =>
      rw [merge_tree]
      rw [tree_to_list]
      simp_all
    | node v1 l1 r1 ih1 ih2 =>
      induction p with
      | nil =>
        rw [merge_tree]
        rw [tree_to_list]
        · simp
        · simp
      | node v2 l2 r2 ih3 ih4 =>
        rw [merge_tree]
        rw [tree_to_list]
        by_cases h : v1 ≤ v2
        {
          rw [if_pos h]
          rw (occs := .pos [2]) [tree_to_list]
          rw [← ofList_add]
          rw [← Multiset.coe_add,← Multiset.coe_add]
          rw [← ih2]
          rw [← Multiset.coe_add,← Multiset.coe_add]
          rw [add_assoc]
        }
        {
          rw [if_neg h]
          rw (occs := .pos [2]) [tree_to_list]
          rw (occs := .pos [2]) [← ofList_add]
          rw [← ih4]
          rw [tree_to_list,tree_to_list]
          rw [← ofList_add,← ofList_add,← ofList_add]
          rw [← Multiset.coe_add]
          rw [← add_comm]
          rw [← add_assoc, ← add_assoc]
          rw (occs := .pos [4])[add_multi_ex]
          rw (occs := .pos [4])[add_multi_ex]
          rw (occs := .pos [4])[add_multi_ex]
          rw [← add_assoc,← add_assoc,← add_assoc]
        }
 }

lemma merge_tree_get_min (q p : Tree Nat) :
get_value q ≠ none ∧ get_value p ≠ none →
get_value (merge_tree q p) = min (get_value q) (get_value p) := by
{
  simp_all
  intro ha hb
  induction q generalizing p with
  | nil =>
    contradiction
  | node v1 l1 r1 ih1 ih2 =>
    induction p with
    | nil =>
      contradiction
    | node v2 l2 r2 ih3 ih4 =>
      rw [get_value,get_value]
      simp_all
      rw [merge_tree]
      by_cases h : v1 ≤ v2
      {
        rw [if_pos h]
        rw [get_value]
        simp_all
      }
      {
        rw [if_neg h]
        rw [get_value]
        simp_all
        exact Nat.le_of_lt h
      }
}


def optionToMultiset (x : Option Nat) : Multiset Nat :=
  match x with
  | none => ∅
  | some v => {v}

lemma emp_eq_zero (q : PriorityQueue) : q.mset = 0 ↔ 0 = q.mset := by
  {
    aesop
  }

lemma neq_to_neg (q : PriorityQueue) : ¬ q.mset = 0 ↔  q.mset ≠ 0  := by
  {
    aesop
  }

set_option diagnostics.threshold 100
lemma not_empty_mset_neq_nil (q : PriorityQueue) : ¬q.mset = 0 → q.queue ≠ Tree.nil := by
  {
    rw [mset]
    rw [queue]
    simp
    rw [tree_to_list.eq_def]
    simp
    split
    · simp
    · simp_all
  }

lemma list_append_mset (xs : List Nat) (x : Nat) : Multiset.ofList (xs ++ [x]) = Multiset.ofList xs + {x}:= by
{
  rw [← Multiset.coe_add]
  simp
}

lemma list_add_mset (xs : List Nat) (x : Nat) : Multiset.ofList (x :: xs) = {x} + Multiset.ofList xs := by
{
  simp
}

lemma mset_add (a : List Nat)(b : Nat) : Multiset.ofList a + {b} = Multiset.ofList (a ++ [b]) := by
{
  induction a generalizing b with
  |nil =>
    simp
  |cons x xs ih =>
    rw [list_add_mset]
    rw [list_append_mset]
    rw [list_add_mset]
}

lemma mset_add' (a b: List Nat)(c : Nat) :
Multiset.ofList a + {c} + Multiset.ofList b = Multiset.ofList (a ++ [c] ++ b) := by
{
  induction a generalizing b with
  |nil =>
    simp
  |cons x xs ih =>
    rw [list_add_mset]
    rw [← Multiset.coe_add,← Multiset.coe_add]
    rw [list_add_mset]
    simp
}

lemma mset_add'' (a b: List Nat) :
Multiset.ofList a + Multiset.ofList b = Multiset.ofList (a ++ b) := by
{
  induction a generalizing b with
  |nil =>
    simp
  |cons x xs ih =>
    rw [list_add_mset]
    rw [← Multiset.coe_add]
    rw [list_add_mset]
}

lemma mset_erase_eq_sub (a : List Nat)(b : Nat) : (Multiset.ofList a).erase b = Multiset.ofList a - {b} := by
{
  simp only [Multiset.coe_erase, Multiset.sub_singleton]
}

lemma mset_erase_eq_sub' (a b: List Nat)(c : Nat) :
Multiset.ofList ((a ++ [c] ++ b).erase c) = Multiset.ofList (a ++ [c] ++ b) - {c} := by
{
  simp only [Multiset.coe_erase, Multiset.sub_singleton]
}

lemma mset_list_erase_add (a : List Nat)(b : Nat) :
b ∈ a → Multiset.ofList ((a.erase b ++ [b])) = Multiset.ofList a := by
{
  intro ha
  rw [← mset_add]
  rw [← Multiset.coe_erase]
  rw [mset_erase_eq_sub]
  rw [Multiset.add_sub_cancel]
  simp_all
}

lemma tree_erase_eq_merge :
Multiset.ofList ((tree_to_list (Tree.node a l r)).erase a) =
Multiset.ofList (tree_to_list l) + Multiset.ofList (tree_to_list r) := by
{
  induction l generalizing r with
  | nil =>
    rw [tree_to_list]
    simp
    rw [tree_to_list, tree_to_list]
    simp
  | node x j k ih1 ih2 =>
    rw [tree_to_list]
    rw [mset_erase_eq_sub']
    rw [← mset_add']
    rw [add_comm]
    rw [← add_assoc]
    simp only [Multiset.coe_add, add_tsub_cancel_right]
    {
      rw [← mset_add'', ← mset_add'']
      rw [add_comm]
    }
}

-- Proves that `delete_min q` removes exactly `get_min q` from the multiset.
set_option diagnostics.threshold 50
theorem delete_min_mset (q : PriorityQueue) :
  invar q ∧ mset q != ∅ → mset (delete_min q) = mset q - optionToMultiset (get_min q) := by
  {
    simp
    intro ha hb
    have hq : q.queue ≠ Tree.nil := not_empty_mset_neq_nil q hb
    rw [mset]
    rw [delete_min]
    rw [queue]
    rw [mset,get_min]
    rw [queue]
    rw [optionToMultiset.eq_def]
    simp_all
    aesop
    {
      rw [tree_to_list,tree_to_list,tree_to_list]
      simp
    }
    {
      rw [tree_to_list,tree_to_list]
      simp
    }
    {
      rw [tree_to_list,tree_to_list]
      simp_all
      rw [List.erase_append]
      simp
      split
      {
        rw [← Multiset.coe_eq_coe]
        rw [mset_list_erase_add]
        assumption
      }
      {
        simp
      }
    }
    {
      rw [tree_to_list]
      rw [← Multiset.coe_eq_coe]
      rw [← merge_tree_eq]
      rw [mset_erase_eq_sub']
      rw [← mset_add']
      rw [add_comm]
      rw [← add_assoc]
      simp only [Multiset.coe_add, add_tsub_cancel_right]
      rw [← mset_add'', ← mset_add'']
      rw [add_comm]
    }
  }

/-- Proves that `insert v q` does not change the multiset except adding `v`. -/
theorem insert_mset (q : PriorityQueue) (v : Nat) :
is_heap_property q.queue → mset q + {v}= mset (insert q v) := by
  {
    intro ha
    rw [insert]
    rw [merge]
    rw [mset]
    rw [queue,queue]
    simp_all
    rw [mset]
    rw [queue]
    simp_all
    rw [merge_tree_mset]
    rw [tree_to_list]
    rw [tree_to_list]
    rw [List.nil_append,List.append_nil]
    simp only [Multiset.coe_singleton]
    rw [add_comm]
  }


-- TODO: correctness proving incomplete part
lemma get_value_node : get_value (Tree.node v l r) = some v := by
{
  rw [get_value]
}

/-- Proves that `merge_tree` preserves the heap property (partially incomplete). -/
lemma merge_tree_invar (q p : Tree Nat) :
is_heap_property q → is_heap_property p → is_heap_property (merge_tree q p) := by
  {
    intro ha hb
    induction q generalizing p with
    | nil =>
      rw [merge_tree]
      simp_all
    | node v1 l1 r1 ih1 ih2 =>
      induction p with
      | nil =>
        rw [merge_tree]
        exact ha
        simp
      | node v2 l2 r2 ih3 ih4 =>
          sorry
        -- rw [left_tree_invar] at ih1
        -- rw [left_tree_invar] at ih3
        -- rw [right_tree_invar] at ih2
        -- rw [right_tree_invar] at ih4
        -- rw [merge_tree]
        -- simp_all
        -- by_cases h : v1 ≤ v2
        -- {
        --   rw [if_pos h]
        --   unfold is_heap_property
        --   split
        --   · simp
        --   · simp
        --   {
        --     have x := ih2 (Tree.node v2 l2 r2)
        --     simp_all
        --     rw [is_heap_property] at ha
        --     simp_all
        --     rename_i h1 h2
        --     rcases h2 with ⟨h3,⟨h4,h5⟩⟩
        --     rw [← h5]
        --     rw [le_subnode]
        --     split
        --     · simp only
        --     {
        --       rename_i h1 h2
        --       rw [merge_tree_get_min] at h2
        --       rw [get_value] at h2
        --       simp
        --       rw [get_value.eq_def] at h2
        --       split at h2
        --       {
        --         simp_all
        --       }
        --       {
        --         simp_all
        --         rw [← h3]
        --         rw [← h3] at h
        --         rw [← h2]
        --         rw [Nat.le_min]
        --         simp_all
        --         rcases ha with ⟨⟨⟨h3,h4⟩,h5⟩,h6⟩
        --         rw [le_subnode] at h4
        --         rw [get_value] at h4
        --         simp_all
        --       }
        --       {
        --         rw [get_value]
        --         simp_all
        --         sorry
        --       }
        --     }
        --     sorry
        -- }
        -- }
  }

lemma merge_nil (q : Tree Nat) : merge_tree Tree.nil q= q := by
{
  rw [merge_tree]
}

theorem merge_invar (q p : PriorityQueue) :
  invar q → invar p → invar (merge q p) := by
  {
    sorry
  }

/-- Proves that `insert v q` maintains `invar` (partially incomplete). -/
theorem insert_invar (q : PriorityQueue) (v : Nat) : invar q → invar (insert q v) := by
  {
    intro ha
    rw [invar] at ha
    rw [is_heap_property.eq_def] at ha
    rw [invar,insert,merge]
    simp_all
    rw [merge_tree.eq_def]
    split
    · simp_all
    · rw [is_heap_property.eq_def]
    {
      split
      {
        simp_all
        sorry
      }
      sorry
    }
  }


/-- Proves that `delete_min q` maintains `invar` (partially incomplete). -/
theorem delete_min_invar (q : PriorityQueue) :
invar q ∧ mset q ≠ ∅ → invar (delete_min q) := by
  {
    simp_all
    intro ha hb
    rw [delete_min]
    split
    {
      rw [invar]
      aesop
    }
    {
      rw [invar]
      aesop
    }
    {
      rw [invar] at ha
      simp_all
      rw [invar]
      apply right_tree_invar at ha
      rw [queue]
      simp_all
    }
    {
      rw [invar] at ha
      simp_all
      rw [invar]
      apply left_tree_invar at ha
      rw [queue]
      simp_all
    }
    {
      rw [invar] at ha
      simp_all
      rw [invar]
      rw [queue]
      simp_all
      -- merge_tree_invar
      sorry
    }
  }
