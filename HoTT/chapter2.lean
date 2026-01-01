/-
## Chapter 2: Homotopy Type Theory
-/

/-
We restate some notions used in Chapter 1 exercises.
-/

import HoTT.chapter1

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

notation:50 p " ⬝ " q => concat_path p q

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

--#print concat_path_1 (MyEq.refl (0 : Nat)) (MyEq.refl (0 : Nat))

-- Now we prove that `concat_path_1` and `concat_path_2` are all equal to `concat_path_3`

def concat_path_eq_1 {α : Type} {x y z: α} (p : x =' y) (q : y =' z) :
  concat_path_1 p q =' concat_path_3 p q :=
  by
  unfold concat_path_1 concat_path_3
  unfold ind

def concat_path_eq_2 {α : Type} {x y z: α} (p : x =' y) (q : y =' z) :
  concat_path_2 p q =' concat_path_3 p q :=
  by
  pathind (concat_path_2 p q) =' (concat_path_3 p q)
