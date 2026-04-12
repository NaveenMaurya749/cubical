import HoTT.Equiv
/-
-- This is a demonstration that we cannot have an inductive type of the following form,
which if we did, we'd have Russell's Paradox in Type Theory.

inductive T where
| intro : (T → 2) → T

A way to formalize this in lean would be to show that the corresponding induction principle
will lead to a contradiction.

-/ 

inductive Two where
| Zero : Two 
| One  : Two 

def swap : Two → Two :=
  fun x ↦ match x with
  | Two.Zero => Two.One
  | Two.One  => Two.Zero

-- In fact, we can produce a contradiction with just the recursion principle,
-- no need to involve the full induction principle
/-
def Russell {α : Type} 
  (intro : (α → Two) → α)                                             -- introduction rule 
  (ind : (γ : Type) → ((f : α → Two) → γ) → ((t : α) → γ))            -- induction principle
  (rule : (f : α → Two) → (ind (α → Two) (fun x ↦ x)) (intro f) = f)  -- computation rule 
 : Empty
:= by
  let γ := α → Two
  have inverse := ind γ (fun x ↦ x)
  have η : α → Two := fun t ↦ swap ((inverse t) (t))
   
  sorry
-/

/-- 
## W-Types
One can formlaize W-Types as an inudctive type
--/

inductive W (α : Type) (β : α → Type) where
| sup : (a : α) → (β a → W α β) → W α β

variable {α : Type}

--inductive FinTree where
--| leaf : α → FinTree 
--| node : (n : Nat) → (Fin n → Fin (2*n) → FinTree → FinTree → FinTree) → FinTree

inductive FinTree' where
| leaf : α → FinTree'
| node : (n : Nat) → (Fin n ⊕ Fin (2*n) → FinTree') → FinTree'

--#print FinTree
#print FinTree'

--def N_w := W Two 
--  (fun x ↦ match x with
--    | Two.Zero => 0
--    | Two.one  => 1
--  )

open Equiv

notation:50 "One" => Unit

/-
def h₀ {α : Type}: α ≃ (One → α) := by
  rw [Equiv] 
  have f : α → One → α := (fun x y ↦ x)
  have h : isEquiv f := by
    unfold isEquiv
  sorry
  -/
