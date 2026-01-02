import HoTT.MyEq

namespace Equiv

def id.{u} (α : Sort u) : α → α := fun x ↦ x

def homotopic.{u} {α : Sort u} {β : Sort v} (f g : α → β) :=
  (x : α) → f x =' g x

notation:50 f " ~ " g => homotopic f g

-- def Equiv.{u} (α : Sort u) (β : Sort u) :=
--   fun α β ↦ Σ (f : α → β), (Σ (g : β → α), ((f ∘ g) ~ id β)) × (Σ (h : β → α), ((h ∘ f) ~ id α))

def isEquiv {α : Type u} {β : Type v} : (f : α → β) → Type (max u v) :=
fun f ↦ (Σ (g : β → α), ((f ∘ g) ~ id β)) × (Σ (h : β → α), ((h ∘ f) ~ id α))

#check isEquiv

def Equiv (α : Type u) (β : Type v) := Σ (f : α → β), isEquiv f

end Equiv
