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

#check MyBoolProd

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
theorem funext.{u, v} : ∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x},
(∀ (x : α), f x = g x) → f = g :=
fun {α} {β} {f g} h =>
  let eqv := fun f g => ∀ (x : α), f x = g x;
  let extfunApp := fun f x => f.liftOn (fun f => f x) fun x_1 x_2 h => h x;
  id (congrArg extfunApp (Quot.sound h))
-/

-- This is the part of the proof that requires function extentionality,
-- since otherwise there is no introduction rule for the equality of functions
-- that are not definitionaly equal.
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

namespace MyEq

inductive MyEq : α → α → Type where
| refl (a : α) : MyEq a a

notation:100 a " =' " b => MyEq a b

def ind  (f : ((x : α) → (y : α) → (p : x =' y) → Type))
  : ((a : α) → f a a (MyEq.refl a))
  → (x : α) → (y : α) → (p : x =' y) → f x y p :=
  fun c x _ p ↦
  match p with
  | MyEq.refl x => c x

theorem ind_def_eq (f : (x : α) → (y : α) → (p : x =' y) → Type)
  (c : (a : α) → f a a (MyEq.refl a))
  (z : α) : ind f c z z (MyEq.refl z) = c z := rfl

def application (f : α → β) : (p : x =' y) → f x =' f y :=
  ind (fun x y _ ↦ f x =' f y) (fun a ↦ MyEq.refl (f a)) x y

theorem application_def_eq (f : α → β) :
  application f (MyEq.refl x) = MyEq.refl (f x) := rfl

def transport (π : α → Type) {x y : α} (p : x =' y) : π x → π y :=
  ind (fun x y _ ↦ π x → π y) (fun _ ↦ id) x y p

-- theorem lift_def_eq : lift π u p

def isContr (α : Type) := Σ a : α, ((x : α) → a ='x)

def freePathSpace (α : Type) := Σ (x y : α), x =' y

def basedPathSpace {α : Type} (a : α) := Σ (x : α), a =' x

def based_path_contr {α : Type} (a : α) : isContr (basedPathSpace a) := by
  unfold isContr
  let fst := Sigma.mk a (MyEq.refl a)
  constructor
  · intro z
    let ⟨u, v⟩ := z
    -- let π : (a : α) → basedPathSpace a := fun a ↦ ⟨a, MyEq.refl a⟩
    -- let π : α → Type := basedPathSpace
    -- let tr : π u := transport π v ⟨a, MyEq.refl a⟩
    -- apply transport
    -- ·
    -- have cheat : fst =' ⟨u, v⟩ := sorry
    -- let β := MyEq.transport π v fst
    -- let ⟨u', v'⟩ := β
    -- have h : a =' u' := transitive v v'
    -- exact cheat
    sorry
  · exact fst
-- Incomplete
end MyEq

/-
## Problem 1.8
-- Define multiplication and exponentiation using rec_ℕ. Verify that (ℕ, +, 0, ×, 1)
-- is a semiring using only $ind_ℕ$. You will probably also need to use symmetry and
-- transitivity fo equality.

-/

section MyNat

#print Nat
/-
inductive Nat : Type
number of parameters: 0
constructors:
Nat.zero : Nat
Nat.succ : Nat → Nat
-/

#print Nat.rec
/-
recursor Nat.rec.{u} : {motive : Nat → Sort u} →
  motive Nat.zero → ((n : Nat) → motive n → motive n.succ) → (t : Nat) → motive t
-/

/-
### Note:
This `Nat.rec` is more powerful than our indepedendent type eliminator `rec_ℕ`. In fact, this is as powerful as our depdendent eliminator, `ind_ℕ`.
Though, we will only be using the independent type family in our use case.
-/

def add : Nat → Nat → Nat :=
  Nat.rec (fun n ↦ n) (fun _ f ↦ (fun n ↦ Nat.succ (f n)))

#eval add 2 3   --5
#eval add 53 47 --100

def mul : Nat → Nat → Nat :=
  Nat.rec (fun _ ↦ 0) (fun _ f ↦ (fun n ↦ (f n) + n))
  -- Not using `add` but rather the internal, much more optimized `+`

#eval mul 2 4   --8
#eval mul 37 3  --111
#eval mul 24 25 --600

-- exp a b := b^a
def exp : Nat → Nat → Nat :=
  Nat.rec (fun _ ↦ 1) (fun _ f ↦ (fun n ↦ mul (f n) n))

-- exp' a b := a^b
def exp' : Nat → Nat → Nat :=
  fun a b ↦ (exp) b a

#eval exp  4 6 --6^4 = 1296
#eval exp' 4 6 --4^6 = 4096

-- -- Verfying $Nat$ is a semiring
-- theorem add_assoc : (a b c : Nat) → (a + b) + c = a + (b + c) := by
--   intro a b c
--   induction a with
--   | zero =>

-- theorem nat_semiring :

end MyNat

/-
## Problem 1.9
-- Define the type family `Fin : ℕ → Type`, and the dependent function
-- `fmax : (n : ℕ) → Fin (n+1)`.
-/

namespace MyFin

-- We will use Sum types to construct Fin.
-- Note that `Fin (n+1) := Fin(n) + 1`, where `1` is the Unit type.
notation:50 α "+" β => Sum α β

def Fin : Nat → Type := Nat.rec Empty (fun _ α ↦ α + Unit)

-- Some example Fin elements
def zero_one : Fin 1 := Sum.inr Unit.unit
def zero_two : Fin 2 := Sum.inl (Sum.inr Unit.unit)
def one_two  : Fin 2 := Sum.inr Unit.unit

#check Fin 19
#print Fin

def fmax : (n : Nat) → Fin (n + 1) :=
  Nat.rec (Sum.inr Unit.unit) (fun _ _ ↦ Sum.inr Unit.unit)

#check fmax 0
#check fmax 5

end MyFin
-- This completes our construction.`
