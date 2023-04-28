import PnP2023.Labs.Lab02.SelectionSort

/-!
# Selection Sort (continued)

In this lab you will show that `selectionSort` defined in the previous lab is correct, i.e. the result is sorted and preserves membership.

__Note:__ If the list has duplicates the sorted list will erase these. For example, `[1, 1, 2, 3]` will be sorted to `[1, 2, 3]`. For the purposes of this exercise, this is fine.


We first define recursively when a list is sorted. -/

/-- A direct definition of an element being below all members of a list. -/
def List.le_all (a : ℕ) (l : List ℕ) : Prop := ∀ b: ℕ, b ∈ l → a ≤ b

/-- Whether a given list is sorted. -/
def List.sorted: List ℕ →  Prop 
| [] => True 
| h :: t => (t.le_all h) ∧ (t.sorted)

-- For your convenience, here are some definitions/theorems that may be useful in the two labs. Clicking on them takes you to the source, where you may find other useful results.
#check List.remove -- {α : Type u_1} → [inst : DecidableEq α] → α → List α → List α
#check List.length_cons -- ∀ {α : Type u_1} (a : α) (as : List α), List.length (a :: as) = Nat.succ (List.length as)
#check List.mem_cons -- ∀ {α : Type u_1} {a b : α} {l : List α}, a ∈ b :: l ↔ a = b ∨ a ∈ l
#check List.mem_of_mem_remove -- ∀ {α : Type u_1} [inst : DecidableEq α] {a b : α} {as : List α}, b ∈ List.remove a as → b ∈ as
#check List.remove_eq_of_not_mem -- ∀ {α : Type u_1} [inst : DecidableEq α] {a : α} {as : List α}, ¬a ∈ as → List.remove a as = as
#check List.mem_remove_iff -- ∀ {α : Type u_1} [inst : DecidableEq α] {a b : α} {as : List α}, b ∈ List.remove a as ↔ b ∈ as ∧ b ≠ a

/-!
- Problem 1: show that members of the given list are members of the sorted list(remove sorry). 
-/

/-- Members of a list are members of the given sorted list -/
theorem selectionSort_mem_of_mem {a : ℕ} {l : List ℕ} (hyp : a ∈ l) : a ∈ selectionSort l := by
by_cases c: l = []
·simp[c] at hyp
·match l with
| head :: tail =>
  by_cases c: tail = []
  ·rw[selectionSort]
   ·simp[c]
    ·apply Or.elim (List.mem_cons.1 hyp)
     ·intro hyp_
      rw[hyp_]
      apply Or.inl rfl
     ·intro hyp_
      apply Or.inr
      simp[hyp_,c] at hyp_
 ·have result1: head::tail = [] := 
  by 
   intro contradict    
   simp[hyp, contradict] at hyp
 by_cases d: a = smallest (head::tail) result1
 ·simp[d]
  rw[selectionSort]
  simp[c]
 ·rw[selectionSort]    
  simp [c,d]
 apply selectionSort_mem_of_mem
 apply List.mem_remove_iff.2
 simp[d]
 apply List.mem_cons.1 hyp
 sorry       
  
    
      

/-!
- Problem 2: show that members of the sorted list are members of the given list(remove sorry). 
-/

/-- Members of the sorted list are members of the given list -/
theorem selectionSort_mem_mem {a : ℕ} {l : List ℕ} (hyp : a ∈ selectionSort l) : a ∈ l := by 
   rw[selectionSort] at hyp
   by_cases c: l = []
   ·simp[c] at hyp
   ·by_cases d: a = smallest l c
    ·simp[d]
     apply smallest_in_list
    ·simp[c,d] at hyp
     have result1: a ∈ List.remove (smallest l (c: l ≠ [])) l := by
      apply selectionSort_mem_of_mem hyp
     apply List.mem_of_mem_remove result1
  termination_by _ _ => l.length
  decreasing_by  sorry
      
 

theorem selectionSort_mem (l : List ℕ) (a : ℕ) : a ∈ l ↔ a ∈ selectionSort l := by 
  apply Iff.intro
  · apply selectionSort_mem_of_mem
  · apply selectionSort_mem_mem

/-!
- Problems 3: Prove that the results of `selectionSort` is sorted (remove the sorry).
-/


/-- The result of `selectionSort` is sorted -/
theorem selectionSort_sorted (l : List ℕ) : (selectionSort l).sorted := 
    by 
    by_cases c: l = []
    ·simp[List.sorted, c]
    ·rw[selectionSort]
     have result: l≠[] := by
      simp[c]
     simp[result]
     simp[List.sorted]
     simp[List.le_all]
     intro b h 
     apply smallest_le
     have result2: b ∈ List.remove (smallest (l) (result)) (l) := by
      apply selectionSort_mem_mem
     simp[h]
     apply List.mem_of_mem_remove result2
     simp[c, result, List.sorted]
     apply selectionSort_sorted
termination_by _ _ => l.length
decreasing_by
 apply remove_mem_length
 apply smallest_in_list
sorry
      
-- No correct solutions, 2/30