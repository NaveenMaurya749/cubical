import Lean
import HoTT.MyEq -- Importing depedency `MyEq` and `ind`

/-

# Tactic for Path Induction - pathind

I'm writing this tactic to more conveniently work with path induction `ind`.

Path induction says that to define a function out of a path type `x =' y`,
it suffices to assume define it on reflexivity paths `MyEq.refl a`.

-/

open MyEq

#print MyEq.MyEq
#print MyEq.ind

def reflexive (a : Nat) : a =' a :=
  MyEq.refl a

/-

# Tactic for Path Induction - pathind

I'm writing this tactic to more conveniently work with path induction `ind`.

Path induction says that to define a function out of a path type `x =' y`,
it suffices to assume define it on reflexivity paths `MyEq.refl a`.

-/

open Lean Meta Elab Tactic Term MyEq

#print Level

elab "pathind" : tactic => do
  -- let goal ← getMainGoal
  -- let target ← goal.getType
  -- let lctx ← getLCtx

  -- -- let pExpr ← Term.elabTerm p none
  -- -- let pType ← inferType pExpr

  -- -- IO.println s!"p: {pExpr}"
  -- -- IO.println s!"pType: {pType}"
  -- -- IO.println s!""
  -- IO.println s!"target: {target}"

  -- -- Match `p` with type `x =' y`
  -- match target with
  -- | Expr.app (Expr.app (Expr.app (Expr.const ``MyEq.MyEq _) x ) y) γ =>
  --   -- We have found that `p : x =' y` and determined `x` and `y`
  --   -- Now we need to find a dependent function `f` of type
  --   -- (x y : α) → (p : x =' y) → Type
  --   IO.println s!"Detected path type: {x} =' {y}"
  --   pure ()
  -- | _ =>
  --   -- pure ()
  --   throwError "Error:  is not a path of type MyEq α α for some α : Type"
  --   pure ()

  let goal ← getMainGoal
  let target ← whnf (← goal.getType)

  IO.println s!"target: {target}"

  -- Expect: ∀ x, ∀ y, ∀ p : x = y, D x y p
  let Expr.forallE xName A body _ := target
    | throwError "expected ∀ x, ..."
  let Expr.forallE yName A' body _ := body
    | throwError "expected ∀ y, ..."
  let Expr.forallE pName pType body _ := body
    | throwError "expected ∀ p : x = y, ..."

  -- Check p : x = y
  let Expr.app (Expr.app (Expr.const ``MyEq.MyEq _) x) y := pType
    | throwError "expected p : x = y"

  -- body is D x y p
  let D := mkLambda xName BinderInfo.default A $
           mkLambda yName BinderInfo.default A' $
           mkLambda pName BinderInfo.default pType body

  -- Construct the new goal: ∀ a, D a a rfl
  let aName := Name.mkSimple "a"
  let rflExpr := Lean.mkConst ``MyEq.refl
  let newGoal :=
    mkForall aName BinderInfo.default A $
      mkAppN D #[mkBVar 0, mkBVar 0, rflExpr]

  -- Replace the goal
  let newGoalMVar ← mkFreshExprMVar newGoal
  goal.assign newGoalMVar
  replaceMainGoal [newGoalMVar.mvarId!]


def concat_path {α : Type} {x y z : α} (p : x =' y) (q : y =' z) : x =' z :=
  ind (fun x y _ ↦ (z : α) → (y =' z) → (x =' z))
    (fun x ↦ (fun z q ↦ ind (fun x z _ ↦ x =' z) (fun a ↦ MyEq.refl a) x z q))
    x y p z q

/-
  pType: MyEq.MyEq.{1} _uniq.2720 _uniq.2721 _uniq.2722
-/
