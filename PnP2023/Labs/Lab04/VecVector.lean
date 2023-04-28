import Mathlib
import PnP2023.Lec_02_03.InductiveTypes

/-!
Vectors, i.e., lists of a fixed length, can be defined in (at least) two ways. One way is as an indexed inductive type `Vec`, as we saw in lecture and is in the file `InductiveTypes.lean`. 

A different definition is as a subtype `Vector` of lists consisting of those of a fixed length. This is the definition used in `mathlib` and is recalled below.

```lean
/-- `Vector α n` is the type of lists of length `n` with elements of type `α`. -/
def Vector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }
```

In this lab, you will relate the two definitions by constructing functions that convert between the two definitions and prove that these functions are inverses of each other.
-/
universe u

/-- Convert a `Vector` to a `Vec` -/
def Vec.ofVector {α : Type u}: (n : ℕ) →  Vector α n → Vec α n 
| 0, _ => .nil
|n+1, ⟨.cons head tail, h⟩ => Vec.cons head (Vec.ofVector n ⟨tail, Nat.succ.inj h⟩ ) 

--Nat.succ.inj h⟩ ) 
/-- Convert a `Vec` to a `Vector` -/
def Vec.toVector {α : Type u}: (n : ℕ) →  Vec α n → Vector α n
|0, .nil => ⟨[], rfl⟩
|n+1, .cons head tail => 
  let ⟨l,h⟩ := Vec.toVector n tail 
  ⟨head::l, by simp only[List.length_cons,h]⟩    

/-- Mapping a `Vec` to a `Vector` and back gives the original `Vec` -/
theorem Vec.ofVector.toVector {α : Type u} (n : ℕ) (v : Vec α n) :
  Vec.ofVector n (Vec.toVector n v) = v := by
  induction v 
  case nil => rfl 
  case cons n head tail h_ => 
   rw[toVector]
   cases h:Vec.toVector n tail
   rw[ofVector, ←h, h_ ]  
    
  

/-- Mapping a `Vector` to a `Vec` and back gives the original `Vector` -/
theorem Vec.toVector.ofVector {α : Type u} (n : ℕ) (v : Vector α n) :
  Vec.toVector n (Vec.ofVector n v) = v := 
  induction n with 
  sorry

-- 3 of 4 correct, but late submission; 25/40