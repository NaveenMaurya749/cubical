namespace MyEq

inductive MyEq : α → α → Type where
| refl (a : α) : MyEq a a

notation:20 a " =' " b => MyEq a b

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
