namespace MyEq

inductive MyEq : α → α → Type where
| refl (a : α) : MyEq a a

notation:0 a " =' " b => MyEq a b

def id (α : Type) : α → α := fun x ↦ x

-- Path induction
def ind  (f : (x : α) → (y : α) → (p : x =' y) → Type)
  : ((a : α) → f a a (MyEq.refl a))
  → (x : α) → (y : α) → (p : x =' y) → f x y p :=
  fun c x _ p ↦
  match p with
  | MyEq.refl x => c x

theorem ind_def_eq {f : (x : α) → (y : α) → (p : x =' y) → Type}
  (c : (a : α) → f a a (MyEq.refl a))
  (z : α) : ind f c z z (MyEq.refl z) = c z := rfl

def application (f : α → β) : (p : x =' y) → f x =' f y :=
  ind (fun x y _ ↦ f x =' f y) (fun a ↦ MyEq.refl (f a)) x y

theorem application_def_eq (f : α → β) :
  application f (MyEq.refl x) = MyEq.refl (f x) := rfl

-- Based Path Induction
def ind' (a : α) (f : (x : α) → (p : a =' x) → Type)
  : (c : f a (MyEq.refl a))
  → (x : α) → (p : a =' x) → f x p := 
 fun c _ p ↦ 
 match p with 
 | MyEq.refl a => c 

theorem ind'_def_eq {a : α} {f : (x : α) → (p : a =' x) → Type}
  (c : f a (MyEq.refl a))
  : ind' a f c a (MyEq.refl a) = c := 
  rfl 

def transport (π : α → Type) {x y : α} (p : x =' y) : π x → π y :=
  ind (fun x y _ ↦ π x → π y) (fun a ↦ id (π a) ) x y p

def transport_def_eq (π : α → Type) (x : α) (y : π x)
  : transport π (MyEq.refl x) y = y := rfl 

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
  
notation:50 p " ⁎ " u => transport _ p u
notation:100 p "⁻¹"    => inverse_path p
notation:60 p " ▪ " q => concat_path p q

def refl_inverse_refl (a : α) : (MyEq.refl a)⁻¹ =' MyEq.refl a :=
  MyEq.refl (MyEq.refl a) 

--def constant_path_constant (x y : α) (p : x =' y)
--  : (p ▪ (MyEq.refl y)) =' p :=
--  ind (fun x y p ↦ (p ▪ (MyEq.refl y)) =' p) (fun a ↦ MyEq.refl (MyEq.refl a)) x y p
--
--def inverse_path_inverse (x y : α) (p : x =' y)
--  : (p ▪ p⁻¹) =' MyEq.refl x :=
--  ind (fun x y p ↦ (p ▪ p⁻¹) =' MyEq.refl x) (fun a ↦ refl_inverse_refl a) x y p

def isContr (α : Type) := Σ a : α, ((x : α) → a ='x)

def freePathSpace (α : Type) := Σ (x y : α), x =' y

def basedPathSpace {α : Type} (a : α) := Σ (x : α), a =' x

--def based_path_contr {α : Type} (a : α) : isContr (basedPathSpace a) := by
--  unfold isContr
--  let fst := Sigma.mk a (MyEq.refl a)
  --ind' (fun x _ ↦ fst × (fun x ↦ fst =' x))
--  sorry
  
-- Incomplete
end MyEq
