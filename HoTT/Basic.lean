import Lean
import HoTT.chapter1 -- Importing depedency `MyEq` and `ind`

macro x:ident ":" t:term " ↦ " y:term : term => do
  `(fun $x : $t => $y)

#eval (x : Nat ↦ x + 2) 2 -- 4

macro x:ident " ↦ " y:term : term => do
  `(fun $x  => $y)

#eval (x ↦  x + 2) 2 -- 4

#print MyEq.ind

/-

# Tactic for Path Induction - pathind

I'm writing this tactic to more conveniently work with path induction `ind`.

Path induction says that to define a function out of a path type `x =' y`,
it suffices to assume define it on reflexivity paths `MyEq.refl a`.

-/

open Lean Meta Elab Tactic Term in
elab "suppose " n:ident " : " t:term : tactic => do
  let n : Name := n.getId
  let mvarId ← getMainGoal
  mvarId.withContext do
    let t ← elabType t
    let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque n
    let (_, mvarIdNew) ← MVarId.intro1P $ ← mvarId.assert n t p
    replaceMainGoal [p.mvarId!, mvarIdNew]
  evalTactic $ ← `(tactic|rotate_left)

example (a : Nat) : a = a := by
  suppose add_comm : a = a + 0
  rw [add_comm]; rfl     -- closes the initial main goal

open Lean Meta Elab Tactic Term in
elab "pathind " fx:term fy:term : tactic => do
  let mvarId ← getMainGoal
  let ctx ← Lean.MonadLCtx.getLCtx -- get the local context
