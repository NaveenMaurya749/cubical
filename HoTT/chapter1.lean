/-

# Chapter 1 : Type Theory

## Product Types

-/
-- Recursor of the product type

namespace MyProd

-- Defining rec primitively and pr1 and pr2 from it
def rec {α β} (γ : Type) : (α → β → γ) → α × β → γ :=
  fun g (a, b) ↦ g a b

def pr1 {α β : Type} : α × β → α := rec α (fun a _ ↦ a)

def pr2 {α β : Type} : α × β → β := rec β (fun _ b ↦ b)

#check rec Nat Nat.add (1,4)

#print pr1

-- Induction on α × β
def ind : (γ : α × β → Type)
  → ((x : α) → (y : β) → γ (x, y))
  → ((z : α × β) → γ z)
  :=
  fun _ g z ↦ g (pr1 z) (pr2 z)

-- This allows us to prove uniq
def uniq : (z : α × β) → ((pr1 z), (pr2 z)) = z
  := by
  intro z
  constructor

end MyProd

/-
# Exercises
-/

/-
## Problem 1.1
-- Given functions f : α → β and g : α → γ, define their composite g ∘ f : α → γ. Show that h ∘ (g ∘ f) = (h ∘ g) ∘ f.
-/

def compose (f : α → β) (g : β → γ) : α → γ :=
  fun x ↦ g (f x)

theorem compose_assoc (f : α → β) (g : β → γ) (h : γ → δ) :
  (compose f (compose g h)) = (compose (compose f g) h) :=
  by
  unfold compose
  rfl

/-
## Problem 1.2
-- Derive the recursion principle for products rec α β
-/

namespace MyProd

-- Here, let's define pr1 and pr2 primitively and rec from them

def pr1' {α β : Type} : α × β → α :=
  fun z ↦ z.1

def pr2' {α β : Type} : α × β → β :=
  fun z ↦ z.2

def rec' {α β} (γ : Type) : (α → β → γ) → α × β → γ :=
  fun g z ↦ g (pr1' z) (pr2' z)

theorem rec_eq_rec' {α β} (γ : Type) (g : α → β → γ) :
  rec γ g = rec' γ g :=
  by
  unfold rec rec'
  rfl

theorem rec'_def_eq {α β} (γ : Type) (g : α → β → γ) (a : α) (b : β) :
  rec' γ g (a, b) = g a b :=
  by
  unfold rec'
  rfl

end MyProd

namespace MySigma

-- Again, projections are primitive, while rec is defined from them

def pr1 {α : Type} {β : α → Type} : (Σ x : α, β x) → α :=
  fun ⟨ x, _ ⟩ ↦ x

def pr2 {α : Type} {β : α → Type} : (z : Σ x : α, β x) → β (pr1 z) :=
  fun ⟨ _, y ⟩ ↦ y

def rec {α : Type} {β : α → Type} (γ : Type) :
  ((x : α) → (y : β x) → γ) → (Σ x : α, β x) → γ :=
  fun g z ↦ g (pr1 z) (pr2 z)

theorem def_equaliy_valid {α : Type} {β : α → Type} (γ : Type)
  (g : (x : α) → (y : β x) → γ) (a : α) (b : β a) :
  rec γ g ⟨ a, b ⟩ = g a b :=
  by
  unfold rec
  simp only [pr1, pr2]

end MySigma

/-
## Problem 1.3
-- Derive the induction principle for products ind (α × β) using only the projections,
-- and the propositional uniqueness principle uniq (α × β) and verify that
-- the definitional equalities are valid. Generalize uniq to Σ-types,
-- and do the same for Σ-types.

-/

namespace MyProd

#print uniq
/-
def MyProd.uniq :
  ∀ {α β : Type} (z : α × β), (pr1 z, pr2 z) = z :=
  fun {α β} z => Eq.refl (pr1 z, pr2 z)
-/

#print ind
/-
def MyProd.ind : {α β : Type}
  → (γ : α × β → Type) → ((x : α) → (y : β) → γ (x, y))
  → (z : α × β) → γ z :=
  fun {α β} x g z => g (pr1 z) (pr2 z)
-/

theorem pr1_eq {α β : Type} (a : α) (b : β) :
  pr1 (a, b) = a
  := by
  unfold pr1
  rfl

theorem pr2_eq {α β : Type} (a : α) (b : β) :
  pr2 (a, b) = b
  := by
  unfold pr2
  rfl

theorem ind_def_eq {α β : Type} (γ : α × β → Type)
  (g : (x : α) → (y : β) → γ (x, y)) (a : α) (b : β) :
  ind γ g (a, b) = g a b :=
  by
  unfold ind
  rfl

end MyProd

-- Sigma type version of uniq and ind

namespace MySigma

#print MySigma.rec

/-
def MySigma.rec : {α : Type} → {β : α → Type}
  → (γ : Type) → ((x : α) → β x → γ)
  → (x : α) × β x → γ
:= fun {α} {β} γ g z => g (pr1 z) (pr2 z)
-/

def uniq {α : Type} {β : α → Type} (z : Σ x : α, β x) :
  ⟨ pr1 z, pr2 z ⟩ = z :=
  by
  cases z with
  | mk a b =>
    rfl

def ind {α : Type} {β : α → Type} :
  (γ : (Σ x : α, β x) → Type)
  → ((x : α) → (y : β x) → γ ⟨ x, y ⟩)
  → (z : Σ x : α, β x) → γ z :=
  fun _ g z ↦ g (pr1 z) (pr2 z)

theorem ind_def_eq {α : Type} {β : α → Type}
  (γ : (Σ x : α, β x) → Type)
  (g : (x : α) → (y : β x) → γ ⟨ x, y ⟩)
  (a : α) (b : β a) :
  ind γ g ⟨ a, b ⟩ = g a b :=
  by
  unfold ind
  rfl

end MySigma

/-
## Problem 1.4
-- Assuming as given only the iterator for natural numbers,
  iter : ∀ (γ : Type), γ → (γ → γ) → ℕ → γ,
-- with the defining equations
  iter γ c0 f 0 = c0
  iter γ c0 f (succ n) = f (iter γ c0 f n)
-- derive a function having the type of the recursor rec_ℕ. Show that the defining equations of the recursor hold propositionally for this function, using the induction principle for ℕ.
-/

namespace MyNat

#print Nat.rec
/-
recursor Nat.rec.{u} : {motive : Nat → Sort u} →
  motive Nat.zero → ((n : Nat) → motive n → motive n.succ) → (t : Nat) → motive t
-/

-- Defining iter in terms of Nat.rec
def iter (γ : Sort u) (c0 : γ) (f : γ → γ) : (n : Nat) → γ :=
  Nat.rec c0 (fun _ cn ↦ f cn)

#print iter
/-
def MyNat.iter.{u} :
  (γ : Sort u) → γ → (γ → γ) → Nat → γ
  := fun γ c0 f t => Nat.rec c0 (fun x ih => f ih) t
-/

-- We define rec from iter via a construction

#check Sigma (fun _ ↦ Nat)
#check Sigma.mk 0 0
#check Nat × Nat

-- We use the product type Nat × γ to keep track of the current number and the computed value so that data is not lost.
def rec (γ : Type) (c0 : γ) (cs : (n : Nat) → γ → γ) : Nat → γ :=
  fun n ↦ (iter (Nat × γ) (0, c0) (fun z ↦ (Nat.succ z.fst, cs z.fst z.snd))) n|>.snd

#print MyNat.rec

theorem iter_succ (γ : Type) (c0 : γ) (f : γ → γ) (n : Nat) :
  iter γ c0 f (Nat.succ n) = f (iter γ c0 f n) :=
  by
  unfold iter
  rfl

-- We verify the defining equations propositionally
theorem rec_def_eq (γ : Type) (c0 : γ) (cs : (n : Nat) → γ → γ) :
  (MyNat.rec γ c0 cs 0 = c0) ∧ (∀ n : Nat, MyNat.rec γ c0 cs (Nat.succ n) = cs n (rec γ c0 cs n)) :=
  by
  constructor
  · -- base case
    unfold MyNat.rec iter
    rfl
  · -- successor case
    intro n
    unfold MyNat.rec

    have h (n : Nat) : iter (Nat × γ) (0, c0) (fun z ↦ (Nat.succ z.fst, cs z.fst z.snd)) (Nat.succ n) = (fun z ↦ (Nat.succ z.fst, cs z.fst z.snd)) (iter (Nat × γ) (0, c0) (fun z ↦ (Nat.succ z.fst, cs z.fst z.snd)) n)
    := by
      exact iter_succ (Nat × γ) (0, c0) (fun z ↦ (Nat.succ z.fst, cs z.fst z.snd)) n
    simp only [h]

    have h1 : (iter (Nat × γ) (0, c0) (fun z ↦ (Nat.succ z.fst, cs z.fst z.snd)) n).fst = n
    := by
      unfold iter
      simp
      induction n with
      | zero => rfl
      | succ k ih =>
        simp only [ih]

    rw [h1]

  -- This completes the proof.

end MyNat

/-
## Problem 1.5
-- Show that if we define A + B := Σ x:2, rec_2 (Type) A B x,
-- then we can give a definition of ind_{A+B} for which the definitional equalities hold.
-/

namespace MySum

#print Bool.rec
/-
  recursor Bool.rec.{u} : {motive : Bool → Sort u}
  → motive false → motive true → (t : Bool) → motive t
-/

#print Sigma
/-
structure Sigma.{u, v} {α : Type u} (β : α → Type v) : Type (max u v)
number of parameters: 2
fields:
  Sigma.fst : α
  Sigma.snd : β self.fst
constructor:
  Sigma.mk.{u, v} {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) : Sigma β
-/

def MySum (α β : Type) : Type :=
  Σ (x : Bool), Bool.rec α β x

def inl {α β : Type} (a : α) : MySum α β :=
  ⟨ false, a ⟩

def inr {α β : Type} (b : β) : MySum α β :=
  ⟨ true, b ⟩

def ind {α β : Type} {γ : MySum α β → Type}
  (f : (a : α) → γ (inl a))
  (g : (b : β) → γ (inr b))
  : (s : MySum α β) → γ s :=
  fun s ↦
  match s with
  | ⟨ false, a ⟩ => f a
  | ⟨ true, b ⟩  => g b

theorem ind_def_eq {α β : Type} {γ : MySum α β → Type}
  (f : (a : α) → γ (inl a))
  (g : (b : β) → γ (inr b))
  (a : α) (b : β) :
  (ind f g (inl a) = f a) ∧ (ind f g (inr b) = g b) :=
  by
  constructor
  · -- inl case
    unfold ind
    rfl
  · -- inr case
    unfold ind
    rfl

-- This completes the definition which hold propositionally.

end MySum

/-
## Problem 1.6
-- Show that if we define A × B := Π (x : 2), rec_2 (Type) A B x,
-- then we can give a definition of ind_{A×B} for which the definitional equalities hold
-- propositionally.
-/

namespace MyBoolProd

def MyBoolProd (α β : Type) : Type :=
  (x : Bool) → Bool.rec α β x

def pr1 (p : MyBoolProd α β) : α :=
  p false

def pr2 (p : MyBoolProd α β) : β :=
  p true

def pair (a : α) (b : β) : MyBoolProd α β :=
  fun x ↦ match x with
  | false => a
  | true  => b

def abs : (b : Bool) → Nat :=
fun b ↦ match b with
| true => 1
| false => 0

#check pair (abs false) (abs true)
#check abs

#print funext
/-
theorem funext.{u, v} : ∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α), f x = g x) → f = g :=
fun {α} {β} {f g} h =>
  let eqv := fun f g => ∀ (x : α), f x = g x;
  let extfunApp := fun f x => f.liftOn (fun f => f x) fun x_1 x_2 h => h x;
  id (congrArg extfunApp (Quot.sound h))
-/

theorem pairwise (g : MyBoolProd α β) : pair (g false) (g true) = g
  := by
  apply funext
  intro x
  unfold pair
  match x with
  | false => rfl
  | true => rfl

def ind {α β : Type} {γ : MyBoolProd α β → Type}
  (f : (a : α) → (b : β) → γ (pair a b))
  : (z : MyBoolProd α β) → γ z :=
  fun z ↦ by
    rw [←pairwise z]
    exact f (z false) (z true)

theorem ind_def_eq {α β : Type} {γ : MyBoolProd α β → Type}
  (g : (x : α) → (y : β) → γ (pair x y)) (a : α) (b : β) :
  ind g (pair a b) = g a b :=
  by
  unfold ind
  have h : g (pair a b false) (pair a b true) = g a b := by rfl
  rw [h]
  rw [Eq.mpr]

-- This is the definition which follows the propositional equalities.

end MyBoolProd

/-
## Problem 1.7
-- Give an alternative derivation of ind'_{=_A} from ind_{=_A} which avoids the use of universes.

-/
