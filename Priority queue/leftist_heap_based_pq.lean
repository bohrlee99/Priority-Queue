import Mathlib.Data.Real.Basic
import Mathlib.Tactic

inductive Lheap (α : Type) where
 | nil : Lheap α
 | node : α → Nat → Lheap α → Lheap α → Lheap α


namespace Lheap

def mh : Lheap Nat → Nat
 | Lheap.nil => 0
 | Lheap.node _ h _ _ => h

def numNodes {α : Type} [Ord α] : Lheap α → Nat
 | Lheap.nil => 0
 | Lheap.node _ _ l r => 1 + numNodes l + numNodes r

def merge (q p : Lheap Nat) : Lheap Nat:=
match q, p with
| Lheap.nil, _ => p
| _, Lheap.nil => q
| Lheap.node k1 npl1 l1 r1, Lheap.node k2 npl2 l2 r2 =>
  if k1 ≤ k2 then
    if (mh (merge r1 (Lheap.node k2 npl2 l2 r2))) ≥ (mh l1) then
      Lheap.node k1 (mh l1 + 1) (merge r1 (Lheap.node k2 npl2 l2 r2)) l1
    else
      Lheap.node k1 (mh (merge r1 (Lheap.node k2 npl2 l2 r2)) + 1) l1 (merge r1 (Lheap.node k2 npl2 l2 r2))
  else
    if (mh (merge (Lheap.node k1 npl1 l1 r1) r2)) ≥ (mh l2) then
      Lheap.node k2 (mh l2 + 1) (merge (Lheap.node k1 npl1 l1 r1) r2) l2
    else
      Lheap.node k2 (mh (merge (Lheap.node k1 npl1 l1 r1) r2) + 1) l2 (merge (Lheap.node k1 npl1 l1 r1) r2)
 termination_by numNodes q + numNodes p
 decreasing_by
  rw [numNodes,numNodes]
  simp_all
  rw [numNodes,numNodes]
  simp_all

def insert (x : Nat) (q : Lheap Nat) : Lheap Nat :=
 merge q (Lheap.node x 1 Lheap.nil Lheap.nil)

def get_min (q : Lheap Nat) : Option Nat :=
 match q with
 | Lheap.nil => none
 | Lheap.node k _ _ _ => k

def delete_min (q : Lheap Nat) : Lheap Nat :=
 match q with
 | Lheap.nil => Lheap.nil
 | Lheap.node _ _ l r => merge l r

def Lheap_to_list : Lheap Nat → List Nat
 | Lheap.nil => []
 | Lheap.node v _ l r => [v] ++ Lheap_to_list l ++ Lheap_to_list r

def le_tree (a : Nat) (t : Lheap Nat) : Bool :=
 let ha := Multiset.ofList (Lheap_to_list t)
 ∀ x ∈ ha, a ≤ x

def is_heap_property : Lheap Nat → Bool
 | Lheap.nil => true
 | Lheap.node _ _ Lheap.nil Lheap.nil => true
 | Lheap.node v _ l r =>
  le_tree v l ∧ le_tree v r ∧
  is_heap_property l ∧ is_heap_property r

def list_to_lheap (l : List Nat) : Lheap Nat :=
 l.foldr insert Lheap.nil

def is_ltree : Lheap Nat → Bool
 | Lheap.nil => true
 | Lheap.node _ h l r =>
  mh r ≤ mh l ∧ h = mh r + 1 ∧ is_ltree l ∧ is_ltree r

def invar (q : Lheap Nat) : Bool :=
 is_ltree q ∧ is_heap_property q

def mset (q : Lheap Nat) : Multiset Nat :=
 Multiset.ofList (Lheap_to_list q)

def examplepq1 : Lheap Nat := list_to_lheap [1,2,3]

def examplepq2 : Lheap Nat := list_to_lheap [4,5,6,7]

def examplepq3 : Lheap Nat := list_to_lheap [8,9,10,11]

#eval examplepq1
#eval examplepq2
#eval get_min examplepq1
#eval invar examplepq1
#eval invar (merge (merge examplepq1 examplepq2) examplepq3)

-- Exercise 15.1. An alternative definition of leftist tree is via the length of the right
-- spine of the tree:

def rank : Lheap Nat → Nat
 | Lheap.nil => 0
 | Lheap.node _ _ _ r => rank r + 1

def is_ltree_by : (Lheap Nat → Nat) → Lheap Nat → Bool
 | _, Lheap.nil => true
 | f, Lheap.node _ _ l r => f r ≤ f l ∧ is_ltree_by f l ∧ is_ltree_by f r

-- Prove that the definition by rank and by mh define the same trees:

theorem rank_eq_mh (q : Lheap Nat) : is_ltree_by rank q = is_ltree_by mh q := by
 sorry

#eval is_ltree_by numNodes examplepq1

lemma sqr_mul_two (x : Nat) : 2 ^ (x + 1) = 2 ^ x + 2 ^ x := by
{
 omega
}

-- It turns out that we can also consider leftist trees by size rather than height and
-- obtain the crucial logarithmic bound for the length of the right spine.
theorem numNodes_uplimit (q : Lheap Nat) :
is_ltree_by numNodes q → 2 ^ (rank q) ≤ numNodes q + 1 := by
{
 intro h₁
 induction q with
 | nil =>
  rw [rank]
  rw [numNodes]
  simp
 | node v h l r ih1 ih2 =>
  rw [rank]
  rw [numNodes]
  rw [is_ltree_by] at h₁
  simp_all
  rw [sqr_mul_two]
  rcases h₁ with ⟨h1,⟨h2,h3⟩⟩
  linarith
}
lemma ltree_mset (l r : Lheap Nat) :
is_ltree l ∧ is_ltree r → is_ltree (merge l r) := by
{
 simp
 intro h₁ h₂
 induction l generalizing r with
 | nil =>
  rw [merge]
  exact h₂
 | node k1 h1 l1 r1 ih1 ih2=>
  induction r with
  | nil =>
   rw [merge]
   exact h₁
   simp
  | node k2 h2 l2 r2 ih3 ih4 =>
   rw [is_ltree] at h₁ h₂
   simp_all
   rcases h₁ with ⟨h1,⟨h2,⟨h3,h4⟩⟩⟩
   rcases h₂ with ⟨h5,⟨h6,⟨h7,h8⟩⟩⟩

   sorry
}

lemma mset_list_add' (a b c: List Nat) :
  Multiset.ofList a + Multiset.ofList b + Multiset.ofList c= Multiset.ofList (a ++ b ++ c) := by
  {
    simp
  }

lemma add_ex (a b c: Multiset Nat) :
  a + b + c = b + c + a := by
  {
    rw (occs := .pos [3]) [add_comm]
    rw [← add_assoc]
  }

lemma mset_eq_of_list (a : Nat) :
  Multiset.ofList [a] = {a} := by
  {
    simp
  }

-- autor: Danyang Li
/-- Proves that merging two priority queues does not alter their combined multiset. -/
lemma merge_mset (q p : Lheap Nat) :
Multiset.ofList (Lheap_to_list (merge q p)) = Lheap_to_list q + Lheap_to_list p:= by
{
  induction q generalizing p with
  | nil =>
    rw [merge]
    simp
    rw [Lheap_to_list]
    simp
  | node k1 npl1 l1 r1 ih1 ih2 =>
    induction p with
    | nil =>
      rw [merge]
      simp
      rw [Lheap_to_list]
      · simp
      · simp
    | node k2 npl2 l2 r2 ih3 ih4 =>
      rw [merge]
      by_cases h : k1 ≤ k2
      {
        rw [if_pos h]
        rw [Lheap_to_list]
        rw [← mset_list_add']
        split
        {
          rw [Lheap_to_list, Lheap_to_list]
          rw [← mset_list_add']
          rw [ih2]
          rw [Lheap_to_list]
          rw [← mset_list_add']
          rw (occs := .pos [1]) [add_comm]
          simp only [← add_assoc]
          rw (occs := .pos [5]) [add_comm]
        }
        {
          rw [Lheap_to_list, Lheap_to_list]
          rw [← mset_list_add']
          rw [ih2]
          rw [Lheap_to_list]
          rw [← mset_list_add']
          rw [← add_assoc,← add_assoc,← add_assoc]
        }
      }
      {
        rw [if_neg h]
        rw [Lheap_to_list]
        rw [← mset_list_add']
        split
        {
          rw [Lheap_to_list, Lheap_to_list]
          rw [← mset_list_add']
          rw [ih4]
          rw [Lheap_to_list]
          rw [← mset_list_add',← mset_list_add']
          rw (occs := .pos [2]) [add_comm]
          rw (occs := .pos [7]) [add_ex]
          rw (occs := .pos [7]) [add_ex]
          rw [←add_assoc,←add_assoc]
        }
        {
          rw [Lheap_to_list, Lheap_to_list]
          rw [← mset_list_add']
          rw [ih4]
          rw [Lheap_to_list]
          rw [← mset_list_add',← mset_list_add']
          rw [← add_assoc]
          rw (occs := .pos [2])[← add_comm]
          rw (occs := .pos [2])[← add_assoc]
        }
      }
}

lemma add_emp_mset (a : Multiset Nat) :
a + Multiset.ofList [] = a:= by
{
  simp
}

-- autor: Danyang Li
/-- Proves that `insert v q` does not change the multiset except adding `v`. -/
theorem insert_mset (q : Lheap Nat) (x : Nat) : mset (insert x q) = {x} + mset q := by
  {
    rw [insert]
    rw [mset]
    rw [merge_mset]
    rw [Lheap_to_list]
    rw [← mset_list_add']
    rw [Lheap_to_list]
    simp only [add_emp_mset]
    rw [mset_eq_of_list]
    rw [mset]
    rw [add_comm]
  }

def optionToMultiset (x : Option Nat) : Multiset Nat :=
  match x with
  | none => ∅
  | some v => {v}

set_option diagnostics.threshold 100
lemma not_empty_mset_neq_nil (q : Lheap Nat) : ¬q.mset = 0 → q ≠ Lheap.nil := by
  {
    rw [mset]
    simp
    rw [Lheap_to_list.eq_def]
    simp
    split
    · simp
    · simp_all
  }

lemma get_min' :
invar (Lheap.node v h l r) =true → get_min (Lheap.node v h l r) = v := by
  {
    rw [invar]
    simp
    intro ha hb
    rw [get_min]
  }

-- autor: Danyang Li
-- Proves that `delete_min q` removes exactly `get_min q` from the multiset.
set_option diagnostics.threshold 50
theorem delete_min_mset (q : Lheap Nat) :
  invar q ∧ mset q != ∅ → mset (delete_min q) = mset q - optionToMultiset (get_min q) := by
  {
    simp
    intro ha hb
    have hq : q ≠ Lheap.nil := not_empty_mset_neq_nil q hb
    rw [mset]
    rw [delete_min.eq_def]
    split
    {
      contradiction
    }
    {
      rename_i h1 h2 h3 h4 h5
      rw [merge_mset]
      rw [optionToMultiset.eq_def]
      simp only [Multiset.empty_eq_zero]
      aesop
      {
        contradiction
      }
      {
        rw [mset]
        rw [get_min'] at heq
        simp at heq
        rw [heq]
        rw [Lheap_to_list]
        rw [← mset_list_add']
        simp
        exact ha
      }
    }
  }

-- For any leftist heap q and any natural number x
-- if q is a valid leftist heap, then inserting x into q results in a valid leftist heap:
theorem ltree_insert (q : Lheap Nat) (x : Nat) :
is_ltree q → is_ltree (insert x q) := by
  {
    induction q with
    | nil =>
      rw [insert]
      rw [merge]
      rw [is_ltree]
      simp
      rw [is_ltree]
      simp_all
      rw [mh]
      rw [is_ltree]
      simp
    | node k h l r ih1 ih2 =>
      intro ha
      rw [insert]
      rw [merge]
      rw [is_ltree] at ha
      simp_all
      rw [insert] at ih1 ih2
      aesop
      {
        rw [is_ltree]
        simp_all
      }
      {
        rw [is_ltree]
        simp_all
        exact Nat.le_of_lt h_1
      }
      {
        rw [is_ltree]
        simp_all
        simp [is_ltree]
        rw [merge]
        rw [is_ltree]
        simp_all
        simp
      }
      {
        rw [is_ltree]
        simp_all
        contradiction
      }
  }
