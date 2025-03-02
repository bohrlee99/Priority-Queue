import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- Define a Binomial Tree structure with:
-- - `rank`: The rank of the tree (order)
-- - `value`: The root value
-- - `children`: A list of child trees
structure BinomialTree (α : Type) where
  rank : Nat
  value : α
  children : List (BinomialTree α)
  deriving Repr

namespace BinomialHeap

-- Provide a default instance for BinomialTree (empty tree)
instance [Inhabited α] : Inhabited (BinomialTree α) where
  default := ⟨0, default, []⟩

-- Provide a default instance for (BinomialTree × List of trees)
instance [Inhabited α] : Inhabited (BinomialTree α × List (BinomialTree α)) where
  default := (default, [])

-- **Link two binomial trees of the same rank**
-- The tree with the smaller root becomes the parent, increasing the rank.
def link {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (t1 t2 : BinomialTree α) : BinomialTree α :=
  if t1.value ≤ t2.value then
    { rank := t1.rank + 1, value := t1.value, children := t2 :: t1.children }
  else
    { rank := t2.rank + 1, value := t2.value, children := t1 :: t2.children }

-- **Merge two binomial heaps (lists of trees)**
-- The merge function recursively processes both lists and maintains the binomial heap properties.
def merge {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (h1 h2 : List (BinomialTree α)) : List (BinomialTree α) :=

  -- Helper function to handle carrying trees of the same rank
  let rec mergeCarry (carry : BinomialTree α) (ts : List (BinomialTree α)) : List (BinomialTree α) :=
    match ts with
    | [] => [carry]  -- If no trees left, return the carry
    | t :: ts' =>
      if carry.rank < t.rank then
        carry :: t :: ts'  -- Insert carry before `t`
      else
        let newCarry := link carry t  -- Merge carry and `t`
        mergeCarry newCarry ts'  -- Continue merging

  match h1, h2 with
  | [], _ => h2  -- If `h1` is empty, return `h2`
  | _, [] => h1  -- If `h2` is empty, return `h1`
  | t1 :: ts1, t2 :: ts2 =>
    if t1.rank < t2.rank then
      t1 :: merge ts1 (t2 :: ts2)
    else if t2.rank < t1.rank then
      t2 :: merge (t1 :: ts1) ts2
    else
      let carry := link t1 t2  -- Merge two trees of the same rank
      mergeCarry carry (merge ts1 ts2)

-- **Recursive termination proof**
termination_by h1.length + h2.length
decreasing_by
  simp  -- Simplify the length comparison
  {
    simp only [List.length]
    rw [← Nat.add_assoc]
    linarith  -- Use `linarith` to resolve the inequality
  }
  {
    simp only [List.length]
    rw [← Nat.add_assoc]
    linarith
  }

-- **Insert a new element into the heap**
-- Creates a singleton tree and merges it into the existing heap.
def insert {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (x : α) (h : List (BinomialTree α)) : List (BinomialTree α) :=
  merge [ { rank := 0, value := x, children := [] } ] h

-- **Find the minimum value in the heap**
-- Recursively traverses all tree roots to find the smallest value.
def findMin {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (h : List (BinomialTree α)) : Option α :=
  match h with
  | [] => none  -- If the heap is empty, return `none`
  | t :: ts =>
    match findMin ts with
    | none => some t.value
    | some x => if t.value ≤ x then some t.value else some x  -- Compare root values

-- **Delete the minimum element from the heap**
-- Finds the tree with the smallest root, removes it, and merges its children back.
def deleteMin {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] [Inhabited α] (h : List (BinomialTree α)) : List (BinomialTree α) :=
  match h with
  | [] => []  -- If heap is empty, return an empty list
  | _ =>
    let rec extractMin : List (BinomialTree α) → BinomialTree α × List (BinomialTree α)
      | [] => (default, [])  -- If empty, return the default tree
      | [t] => (t, [])  -- If only one tree, return it and an empty list
      | t :: ts =>
        let (minT, rest) := extractMin ts
        if t.value ≤ minT.value then
          (t, ts)  -- If `t` is smaller, return it and the rest
        else
          (minT, t :: rest)

    let (minTree, rest) := extractMin h  -- Extract the minimum tree
    let reversedChildren := minTree.children.reverse  -- Reverse children for correct order
    merge rest reversedChildren  -- Merge remaining heap with children

-- **Compute the total size of the heap (number of elements)**
-- The size is calculated as the sum of `2^rank` for all trees.
def size {α : Type} (h : List (BinomialTree α)) : Nat :=
  h.foldl (fun acc t => acc + (2 ^ t.rank)) 0

-- **Compute the total rank of all trees in the heap**
-- Used for analyzing runtime complexity.
def totalRank {α : Type} (h : List (BinomialTree α)) : Nat :=
  h.foldl (fun acc t => acc + t.rank) 0

end BinomialHeap

-- **Test cases**
#eval BinomialHeap.insert 5 []  -- Insert element 5 into an empty heap
#eval BinomialHeap.findMin [BinomialTree.mk 0 2 []]  -- Find minimum (should return `some 2`)
#eval BinomialHeap.deleteMin [BinomialTree.mk 0 2 []]  -- Delete the only element (should return `[]`)
#eval BinomialHeap.size [BinomialTree.mk 1 3 [BinomialTree.mk 0 5 []]]  -- Compute heap size
#eval BinomialHeap.totalRank [BinomialTree.mk 2 4 [BinomialTree.mk 1 7 [BinomialTree.mk 0 9 []], BinomialTree.mk 0 10 []]]  -- Compute total rank
