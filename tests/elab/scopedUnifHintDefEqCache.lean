import Lean

open Lean Meta

structure Magma where
  α   : Type
  mul : α → α → α

def Nat.Magma : Magma := ⟨Nat, Nat.mul⟩

class K2 (α β : Type) where

instance (α : Type) : K2 α α := ⟨⟩

namespace Algebra
scoped unif_hint (s : Magma) where
  s =?= Nat.Magma |- s.α =?= Nat
end Algebra

/-- Resolves `K2 Nat.Magma.α Nat` only with the scoped hint. -/
def hintQuery : Expr :=
  mkApp2 (mkConst ``K2) (mkApp (mkConst ``Magma.α) (mkConst ``Nat.Magma)) (mkConst ``Nat)

/-- info: false true false -/
#guard_msgs in
run_meta do
  let before := (← synthInstance? hintQuery).isSome
  (pushScope : CoreM Unit)
  (activateScoped `Algebra : CoreM Unit)
  resetSynthInstanceCache
  let active := (← synthInstance? hintQuery).isSome
  (popScope : CoreM Unit)
  resetSynthInstanceCache
  let after := (← synthInstance? hintQuery).isSome
  logInfo m!"{before} {active} {after}"
