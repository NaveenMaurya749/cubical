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

-- open Lean Meta Elab Tactic Term in
-- elab "pathind" t:term : tactic => do
--   let goal ← getMainGoal
--   let target ← goal.getType
--   let target ← whnf target
--   match target with
--   | Expr.forallE x y t body => sorry
--   | _ =>
--     throwError "pathind tactic: expected a function type `∏ (x y : A) (p : x =' y) D(x,y,p)` in the goal, got {target}"

--   goal.withContext do
--     let t ← elabType t
--     let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque
--     let (_, mvarIdNew) ← MVarId.intro1P $ ← goal.assert
--     replaceMainGoal [p.mvarId!, mvarIdNew]
--   evalTactic $ ← `(tactic|rotate_left)
