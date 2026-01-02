/-
## Chapter 2: Homotopy Type Theory
-/

/-
We restate some notions used in Chapter 1 exercises.
-/

import HoTT.MyEq
import HoTT.Equiv

open MyEq

/-
 Here we show reflexivity, symmetry and transitivity of paths.
-/

def constant_path {α : Type} (a : α) : a =' a :=
  MyEq.refl a

def inverse_path {α : Type} {x y : α} (p : x =' y) : y =' x :=
  ind (fun x y _ ↦ y =' x) (fun a ↦ MyEq.refl a) x y p

def concat_path {α : Type} {x y z : α} (p : x =' y) (q : y =' z) : x =' z :=
  ind (fun x y _ ↦ (z : α) → (y =' z) → (x =' z))
    (fun x ↦ (fun z q ↦ ind (fun x z _ ↦ x =' z) (fun a ↦ MyEq.refl a) x z q))
    x y p z q

def reflexivity {α : Type} (a : α) : a =' a :=
  constant_path a

def symmetry {α : Type} {x y : α} (p : x =' y) : y =' x :=
  inverse_path p

def transitivity {α : Type} {x y z : α} (p : x =' y) (q : y =' z) : x =' z :=
  concat_path p q

notation:10 p " ◾ " q => concat_path p q

/-
## Exercise 2.1
Show that the three obvious proofs of Lemma 2.1.2 are equal.
-/

-- We first list the three proofs here
def concat_path_1 {α : Type} {x y z: α} (p : x =' y) (q : y =' z) : x =' z :=
  ind (fun x y _ ↦ (z : α) → (y =' z) → (x =' z))
    (fun _ ↦ (fun _ q ↦ q)) x y p z q

def concat_path_2 {α : Type} {x y z: α} (p : x =' y) (q : y =' z) : x =' z :=
  ind (fun x y _ ↦ (z : α) → (y =' z) → (x =' z))
    (fun _ ↦ (fun _ q ↦ q)) x y p z q

def concat_path_3 {α : Type} {x y z: α} (p : x =' y) (q : y =' z) : x =' z :=
  ind (fun x y _ ↦ (z : α) → (y =' z) → (x =' z))
    (fun x ↦ (fun z q ↦ ind (fun x z _ ↦ x =' z) (fun a ↦ MyEq.refl a) x z q))
    x y p z q

-- #print concat_path_1 (MyEq.refl (0 : Nat)) (MyEq.refl (0 : Nat))

-- Now we prove that `concat_path_1` and `concat_path_2` are all equal to `concat_path_3`

-- def concat_path_eq_1 {α : Type} {x y z: α} (p : x =' y) (q : y =' z) :
--   concat_path_1 p q =' concat_path_3 p q :=
--   by
--   unfold concat_path_1 concat_path_3


-- def concat_path_eq_2 {α : Type} {x y z: α} (p : x =' y) (q : y =' z) :
--   concat_path_2 p q =' concat_path_3 p q :=
--   by
--   pathind (concat_path_2 p q) =' (concat_path_3 p q)

/-
# Exercise 2.4
Define, by induction on `n`, a general notion of `n`**-dimnensional path** in a type `α`,
simultaneously with the type of boundaries for such paths.
-/

def Ω (α : Type) (n : Nat) : Type :=
  Nat.rec α (fun _ Ωn ↦ Σ (x y : Ωn), x =' y) n

def boundary (α : Type) (n : Nat) : Type :=
  match n with
  | Nat.zero => Empty
  | Nat.succ m => Ω α m

-- One can also define based loop spaces

def Ω' (α : Type) (a : α) (n : Nat) : Type × α :=
  Nat.rec (α, a) (fun _ (Ωn, a) ↦ (Σ (x y : Ωn), x =' y, a)) n

/-
# Exercise 2.5
Prove that the natural functions
  `(f x =' f y) → (p⁎(f x)) =' p⁎(f y))`
  `(p⁎(f x)) =' p⁎(f y)) → (f x =' f y)`
are equivalences.
-/

section
open Equiv

-- def transport_equiv {α β : Type} (f : α → β) (x y : α) (p : x =' y) :
--   Equiv.isEquiv lift p (fx) :=
--   sorry

/-
# Exercise 2.6
Prove that if `p : x =' y`, then the function `(p · -) : (y =' z) → (x =' z)` is an equivalence.
-/

def concat_along {x y : α} (p : x =' y) (z : α) : (y =' z) → (x =' z) :=
  fun q ↦ p ◾ q

-- def pathsEquiv (x y z : α) (p : x =' y) : isEquiv (concat_along p z) :=
--   by
--   let f   := concat_along p
--   have g  := concat_along (inverse_path p)
--   unfold isEquiv
--   constructor
--   · constructor
--     · unfold homotopic concat_along
--       simp
--       intro q
--       unfold Equiv.id
--   · constructor
--     ·
--       sorry
--     · exact g z

end
