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

-- Problem 1
-- Given functions f : α → β and g : α → γ, define their composite g ∘ f : α → γ. Show that h ∘ (g ∘ f) = (h ∘ g) ∘ f.

def compose (f : α → β) (g : β → γ) : α → γ :=
  fun x ↦ g (f x)

theorem compose_assoc (f : α → β) (g : β → γ) (h : γ → δ) :
  (compose f (compose g h)) = (compose (compose f g) h) :=
  by
  unfold compose
  rfl

-- Problem 2
-- Derive the recursion principle for products rec α β

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

def def_equaliy_valid {α : Type} {β : α → Type} (γ : Type)
  (g : (x : α) → (y : β x) → γ) (a : α) (b : β a) :
  rec γ g ⟨ a, b ⟩ = g a b :=
  by
  unfold rec
  rfl

end MySigma

-- Problem 3
-- Derive the induction principle for products ind (α × β) using only the projections,
-- and the propositional uniqueness principle uniq (α × β) and verify that
-- the definitional equalities are valid. Generalize uniq to Σ-types,
-- and do the same for Σ-types.

namespace MyProd

#print uniq

theorem ind_def_eq (γ : α × β → Type)
  (g : (x : α) → (y : β) → γ (x, y)) (a : α) (b : β) :
  ind γ g (a, b) = g a b :=
  by
  -- use uniqueness: ((pr1 (a,b)), (pr2 (a,b))) = (a,b)
  let p := uniq (a, b)
  -- from the equality of pairs we get equalities of components
  have ⟨h1, h2⟩ := Prod.mk.inj p
  -- ind on a pair computes to g (pr1 _) (pr2 _), then rewrite components
  calc
    ind γ g (a, b) = g (pr1 (a, b)) (pr2 (a, b)) := rfl
    _ = g a b := by rw [h1, h2]

end MyProd
