import SyntheticBench.Base

namespace SyntheticBench.S2

open SyntheticBench

class TopAlg (α : Type u) where
  baseOp : α → α → α

class LeftPath (α : Type u) extends TopAlg α where
  leftTag : Nat

class RightPath (α : Type u) extends TopAlg α where
  rightTag : Nat

class DiamondAlg (α : Type u) extends LeftPath α, RightPath α where
  merge : α → α → α

class DeepBridge (α : Type u) (β : outParam (Type v)) (γ : outParam (Type w)) where
  lift : α → β
  proj : β → γ

instance : TopAlg Nat where baseOp := (· + ·)
instance : LeftPath Nat where leftTag := 1
instance : RightPath Nat where rightTag := 2
instance : DiamondAlg Nat where merge a b := a + b + 1

instance (tag : Nat) [TopAlg α] : TopAlg (Tagged tag α) where
  baseOp a b := ⟨TopAlg.baseOp a.val b.val⟩
instance (tag : Nat) [LeftPath α] : LeftPath (Tagged tag α) where
  leftTag := LeftPath.leftTag α + tag
instance (tag : Nat) [RightPath α] : RightPath (Tagged tag α) where
  rightTag := RightPath.rightTag α + tag
instance (tag : Nat) [DiamondAlg α] : DiamondAlg (Tagged tag α) where
  merge a b := ⟨DiamondAlg.merge a.val b.val⟩

instance [DiamondAlg α] [DiamondAlg β] : TopAlg (α × β) where
  baseOp x y := (TopAlg.baseOp x.1 y.1, TopAlg.baseOp x.2 y.2)
instance [DiamondAlg α] [DiamondAlg β] : LeftPath (α × β) where
  leftTag := LeftPath.leftTag α + LeftPath.leftTag β
instance [DiamondAlg α] [DiamondAlg β] : RightPath (α × β) where
  rightTag := RightPath.rightTag α + RightPath.rightTag β
instance [DiamondAlg α] [DiamondAlg β] : DiamondAlg (α × β) where
  merge x y := (DiamondAlg.merge x.1 y.1, DiamondAlg.merge x.2 y.2)

instance : DeepBridge Nat (Vec2 Nat) Nat where
  lift n := ⟨n, n + 1⟩
  proj v := v.x + v.y

instance [DeepBridge α β γ] (tag : Nat) : DeepBridge (Tagged tag α) β γ where
  lift x := DeepBridge.lift x.val
  proj y := DeepBridge.proj (α := α) y

def evalDiamond [DiamondAlg α] (a b : α) : α :=
  TopAlg.baseOp (DiamondAlg.merge a b) a

def bridgeApply {α : Type} {β γ : Type} [DeepBridge α β γ] (x : α) : γ :=
  DeepBridge.proj (α := α) (DeepBridge.lift x)

theorem s2_diamond_comm_001 (x y : Tagged 1 (Tagged 11 (Tagged 21 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_001 : (evalDiamond (α := Tagged 1 (Tagged 11 Nat × Tagged 21 Nat)) ⟨(⟨1⟩, ⟨2⟩)⟩ ⟨(⟨3⟩, ⟨4⟩)⟩).val.1.val = 6 := rfl
theorem s2_outparam_bridge_001 : bridgeApply (⟨⟨1⟩⟩ : Tagged 1 (Tagged 11 Nat)) = 3 ∧ Normed.norm (⟨⟨1⟩⟩ : Tagged 1 (Tagged 11 Nat)) = 1 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_002 (x y : Tagged 2 (Tagged 12 (Tagged 22 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_002 : (evalDiamond (α := Tagged 2 (Tagged 12 Nat × Tagged 22 Nat)) ⟨(⟨2⟩, ⟨3⟩)⟩ ⟨(⟨4⟩, ⟨5⟩)⟩).val.1.val = 9 := rfl
theorem s2_outparam_bridge_002 : bridgeApply (⟨⟨2⟩⟩ : Tagged 2 (Tagged 12 Nat)) = 5 ∧ Normed.norm (⟨⟨2⟩⟩ : Tagged 2 (Tagged 12 Nat)) = 2 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_003 (x y : Tagged 3 (Tagged 13 (Tagged 23 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_003 : (evalDiamond (α := Tagged 3 (Tagged 13 Nat × Tagged 23 Nat)) ⟨(⟨3⟩, ⟨4⟩)⟩ ⟨(⟨5⟩, ⟨6⟩)⟩).val.1.val = 12 := rfl
theorem s2_outparam_bridge_003 : bridgeApply (⟨⟨3⟩⟩ : Tagged 3 (Tagged 13 Nat)) = 7 ∧ Normed.norm (⟨⟨3⟩⟩ : Tagged 3 (Tagged 13 Nat)) = 3 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_004 (x y : Tagged 4 (Tagged 14 (Tagged 24 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_004 : (evalDiamond (α := Tagged 4 (Tagged 14 Nat × Tagged 24 Nat)) ⟨(⟨4⟩, ⟨5⟩)⟩ ⟨(⟨6⟩, ⟨7⟩)⟩).val.1.val = 15 := rfl
theorem s2_outparam_bridge_004 : bridgeApply (⟨⟨4⟩⟩ : Tagged 4 (Tagged 14 Nat)) = 9 ∧ Normed.norm (⟨⟨4⟩⟩ : Tagged 4 (Tagged 14 Nat)) = 4 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_005 (x y : Tagged 5 (Tagged 15 (Tagged 25 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_005 : (evalDiamond (α := Tagged 5 (Tagged 15 Nat × Tagged 25 Nat)) ⟨(⟨5⟩, ⟨6⟩)⟩ ⟨(⟨7⟩, ⟨8⟩)⟩).val.1.val = 18 := rfl
theorem s2_outparam_bridge_005 : bridgeApply (⟨⟨5⟩⟩ : Tagged 5 (Tagged 15 Nat)) = 11 ∧ Normed.norm (⟨⟨5⟩⟩ : Tagged 5 (Tagged 15 Nat)) = 5 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_006 (x y : Tagged 6 (Tagged 16 (Tagged 26 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_006 : (evalDiamond (α := Tagged 6 (Tagged 16 Nat × Tagged 26 Nat)) ⟨(⟨6⟩, ⟨7⟩)⟩ ⟨(⟨8⟩, ⟨9⟩)⟩).val.1.val = 21 := rfl
theorem s2_outparam_bridge_006 : bridgeApply (⟨⟨6⟩⟩ : Tagged 6 (Tagged 16 Nat)) = 13 ∧ Normed.norm (⟨⟨6⟩⟩ : Tagged 6 (Tagged 16 Nat)) = 6 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_007 (x y : Tagged 7 (Tagged 17 (Tagged 27 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_007 : (evalDiamond (α := Tagged 7 (Tagged 17 Nat × Tagged 27 Nat)) ⟨(⟨7⟩, ⟨8⟩)⟩ ⟨(⟨9⟩, ⟨10⟩)⟩).val.1.val = 24 := rfl
theorem s2_outparam_bridge_007 : bridgeApply (⟨⟨7⟩⟩ : Tagged 7 (Tagged 17 Nat)) = 15 ∧ Normed.norm (⟨⟨7⟩⟩ : Tagged 7 (Tagged 17 Nat)) = 7 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_008 (x y : Tagged 8 (Tagged 18 (Tagged 28 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_008 : (evalDiamond (α := Tagged 8 (Tagged 18 Nat × Tagged 28 Nat)) ⟨(⟨8⟩, ⟨9⟩)⟩ ⟨(⟨10⟩, ⟨11⟩)⟩).val.1.val = 27 := rfl
theorem s2_outparam_bridge_008 : bridgeApply (⟨⟨8⟩⟩ : Tagged 8 (Tagged 18 Nat)) = 17 ∧ Normed.norm (⟨⟨8⟩⟩ : Tagged 8 (Tagged 18 Nat)) = 8 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_009 (x y : Tagged 9 (Tagged 19 (Tagged 29 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_009 : (evalDiamond (α := Tagged 9 (Tagged 19 Nat × Tagged 29 Nat)) ⟨(⟨9⟩, ⟨10⟩)⟩ ⟨(⟨11⟩, ⟨12⟩)⟩).val.1.val = 30 := rfl
theorem s2_outparam_bridge_009 : bridgeApply (⟨⟨9⟩⟩ : Tagged 9 (Tagged 19 Nat)) = 19 ∧ Normed.norm (⟨⟨9⟩⟩ : Tagged 9 (Tagged 19 Nat)) = 9 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_010 (x y : Tagged 10 (Tagged 20 (Tagged 30 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_010 : (evalDiamond (α := Tagged 10 (Tagged 20 Nat × Tagged 30 Nat)) ⟨(⟨10⟩, ⟨11⟩)⟩ ⟨(⟨12⟩, ⟨13⟩)⟩).val.1.val = 33 := rfl
theorem s2_outparam_bridge_010 : bridgeApply (⟨⟨10⟩⟩ : Tagged 10 (Tagged 20 Nat)) = 21 ∧ Normed.norm (⟨⟨10⟩⟩ : Tagged 10 (Tagged 20 Nat)) = 10 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_011 (x y : Tagged 11 (Tagged 21 (Tagged 31 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_011 : (evalDiamond (α := Tagged 11 (Tagged 21 Nat × Tagged 31 Nat)) ⟨(⟨11⟩, ⟨12⟩)⟩ ⟨(⟨13⟩, ⟨14⟩)⟩).val.1.val = 36 := rfl
theorem s2_outparam_bridge_011 : bridgeApply (⟨⟨11⟩⟩ : Tagged 11 (Tagged 21 Nat)) = 23 ∧ Normed.norm (⟨⟨11⟩⟩ : Tagged 11 (Tagged 21 Nat)) = 11 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_012 (x y : Tagged 12 (Tagged 22 (Tagged 32 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_012 : (evalDiamond (α := Tagged 12 (Tagged 22 Nat × Tagged 32 Nat)) ⟨(⟨12⟩, ⟨13⟩)⟩ ⟨(⟨14⟩, ⟨15⟩)⟩).val.1.val = 39 := rfl
theorem s2_outparam_bridge_012 : bridgeApply (⟨⟨12⟩⟩ : Tagged 12 (Tagged 22 Nat)) = 25 ∧ Normed.norm (⟨⟨12⟩⟩ : Tagged 12 (Tagged 22 Nat)) = 12 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_013 (x y : Tagged 13 (Tagged 23 (Tagged 33 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_013 : (evalDiamond (α := Tagged 13 (Tagged 23 Nat × Tagged 33 Nat)) ⟨(⟨13⟩, ⟨14⟩)⟩ ⟨(⟨15⟩, ⟨16⟩)⟩).val.1.val = 42 := rfl
theorem s2_outparam_bridge_013 : bridgeApply (⟨⟨13⟩⟩ : Tagged 13 (Tagged 23 Nat)) = 27 ∧ Normed.norm (⟨⟨13⟩⟩ : Tagged 13 (Tagged 23 Nat)) = 13 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_014 (x y : Tagged 14 (Tagged 24 (Tagged 34 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_014 : (evalDiamond (α := Tagged 14 (Tagged 24 Nat × Tagged 34 Nat)) ⟨(⟨14⟩, ⟨15⟩)⟩ ⟨(⟨16⟩, ⟨17⟩)⟩).val.1.val = 45 := rfl
theorem s2_outparam_bridge_014 : bridgeApply (⟨⟨14⟩⟩ : Tagged 14 (Tagged 24 Nat)) = 29 ∧ Normed.norm (⟨⟨14⟩⟩ : Tagged 14 (Tagged 24 Nat)) = 14 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_015 (x y : Tagged 15 (Tagged 25 (Tagged 35 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_015 : (evalDiamond (α := Tagged 15 (Tagged 25 Nat × Tagged 35 Nat)) ⟨(⟨15⟩, ⟨16⟩)⟩ ⟨(⟨17⟩, ⟨18⟩)⟩).val.1.val = 48 := rfl
theorem s2_outparam_bridge_015 : bridgeApply (⟨⟨15⟩⟩ : Tagged 15 (Tagged 25 Nat)) = 31 ∧ Normed.norm (⟨⟨15⟩⟩ : Tagged 15 (Tagged 25 Nat)) = 15 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_016 (x y : Tagged 16 (Tagged 26 (Tagged 36 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_016 : (evalDiamond (α := Tagged 16 (Tagged 26 Nat × Tagged 36 Nat)) ⟨(⟨16⟩, ⟨17⟩)⟩ ⟨(⟨18⟩, ⟨19⟩)⟩).val.1.val = 51 := rfl
theorem s2_outparam_bridge_016 : bridgeApply (⟨⟨16⟩⟩ : Tagged 16 (Tagged 26 Nat)) = 33 ∧ Normed.norm (⟨⟨16⟩⟩ : Tagged 16 (Tagged 26 Nat)) = 16 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_017 (x y : Tagged 17 (Tagged 27 (Tagged 37 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_017 : (evalDiamond (α := Tagged 17 (Tagged 27 Nat × Tagged 37 Nat)) ⟨(⟨17⟩, ⟨18⟩)⟩ ⟨(⟨19⟩, ⟨20⟩)⟩).val.1.val = 54 := rfl
theorem s2_outparam_bridge_017 : bridgeApply (⟨⟨17⟩⟩ : Tagged 17 (Tagged 27 Nat)) = 35 ∧ Normed.norm (⟨⟨17⟩⟩ : Tagged 17 (Tagged 27 Nat)) = 17 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_018 (x y : Tagged 18 (Tagged 28 (Tagged 38 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_018 : (evalDiamond (α := Tagged 18 (Tagged 28 Nat × Tagged 38 Nat)) ⟨(⟨18⟩, ⟨19⟩)⟩ ⟨(⟨20⟩, ⟨21⟩)⟩).val.1.val = 57 := rfl
theorem s2_outparam_bridge_018 : bridgeApply (⟨⟨18⟩⟩ : Tagged 18 (Tagged 28 Nat)) = 37 ∧ Normed.norm (⟨⟨18⟩⟩ : Tagged 18 (Tagged 28 Nat)) = 18 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_019 (x y : Tagged 19 (Tagged 29 (Tagged 39 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_019 : (evalDiamond (α := Tagged 19 (Tagged 29 Nat × Tagged 39 Nat)) ⟨(⟨19⟩, ⟨20⟩)⟩ ⟨(⟨21⟩, ⟨22⟩)⟩).val.1.val = 60 := rfl
theorem s2_outparam_bridge_019 : bridgeApply (⟨⟨19⟩⟩ : Tagged 19 (Tagged 29 Nat)) = 39 ∧ Normed.norm (⟨⟨19⟩⟩ : Tagged 19 (Tagged 29 Nat)) = 19 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_020 (x y : Tagged 20 (Tagged 30 (Tagged 40 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_020 : (evalDiamond (α := Tagged 20 (Tagged 30 Nat × Tagged 40 Nat)) ⟨(⟨20⟩, ⟨21⟩)⟩ ⟨(⟨22⟩, ⟨23⟩)⟩).val.1.val = 63 := rfl
theorem s2_outparam_bridge_020 : bridgeApply (⟨⟨20⟩⟩ : Tagged 20 (Tagged 30 Nat)) = 41 ∧ Normed.norm (⟨⟨20⟩⟩ : Tagged 20 (Tagged 30 Nat)) = 20 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_021 (x y : Tagged 21 (Tagged 31 (Tagged 41 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_021 : (evalDiamond (α := Tagged 21 (Tagged 31 Nat × Tagged 41 Nat)) ⟨(⟨21⟩, ⟨22⟩)⟩ ⟨(⟨23⟩, ⟨24⟩)⟩).val.1.val = 66 := rfl
theorem s2_outparam_bridge_021 : bridgeApply (⟨⟨21⟩⟩ : Tagged 21 (Tagged 31 Nat)) = 43 ∧ Normed.norm (⟨⟨21⟩⟩ : Tagged 21 (Tagged 31 Nat)) = 21 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_022 (x y : Tagged 22 (Tagged 32 (Tagged 42 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_022 : (evalDiamond (α := Tagged 22 (Tagged 32 Nat × Tagged 42 Nat)) ⟨(⟨22⟩, ⟨23⟩)⟩ ⟨(⟨24⟩, ⟨25⟩)⟩).val.1.val = 69 := rfl
theorem s2_outparam_bridge_022 : bridgeApply (⟨⟨22⟩⟩ : Tagged 22 (Tagged 32 Nat)) = 45 ∧ Normed.norm (⟨⟨22⟩⟩ : Tagged 22 (Tagged 32 Nat)) = 22 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_023 (x y : Tagged 23 (Tagged 33 (Tagged 43 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_023 : (evalDiamond (α := Tagged 23 (Tagged 33 Nat × Tagged 43 Nat)) ⟨(⟨23⟩, ⟨24⟩)⟩ ⟨(⟨25⟩, ⟨26⟩)⟩).val.1.val = 72 := rfl
theorem s2_outparam_bridge_023 : bridgeApply (⟨⟨23⟩⟩ : Tagged 23 (Tagged 33 Nat)) = 47 ∧ Normed.norm (⟨⟨23⟩⟩ : Tagged 23 (Tagged 33 Nat)) = 23 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_024 (x y : Tagged 24 (Tagged 34 (Tagged 44 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_024 : (evalDiamond (α := Tagged 24 (Tagged 34 Nat × Tagged 44 Nat)) ⟨(⟨24⟩, ⟨25⟩)⟩ ⟨(⟨26⟩, ⟨27⟩)⟩).val.1.val = 75 := rfl
theorem s2_outparam_bridge_024 : bridgeApply (⟨⟨24⟩⟩ : Tagged 24 (Tagged 34 Nat)) = 49 ∧ Normed.norm (⟨⟨24⟩⟩ : Tagged 24 (Tagged 34 Nat)) = 24 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_025 (x y : Tagged 25 (Tagged 35 (Tagged 45 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_025 : (evalDiamond (α := Tagged 25 (Tagged 35 Nat × Tagged 45 Nat)) ⟨(⟨25⟩, ⟨26⟩)⟩ ⟨(⟨27⟩, ⟨28⟩)⟩).val.1.val = 78 := rfl
theorem s2_outparam_bridge_025 : bridgeApply (⟨⟨25⟩⟩ : Tagged 25 (Tagged 35 Nat)) = 51 ∧ Normed.norm (⟨⟨25⟩⟩ : Tagged 25 (Tagged 35 Nat)) = 25 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_026 (x y : Tagged 26 (Tagged 36 (Tagged 46 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_026 : (evalDiamond (α := Tagged 26 (Tagged 36 Nat × Tagged 46 Nat)) ⟨(⟨26⟩, ⟨27⟩)⟩ ⟨(⟨28⟩, ⟨29⟩)⟩).val.1.val = 81 := rfl
theorem s2_outparam_bridge_026 : bridgeApply (⟨⟨26⟩⟩ : Tagged 26 (Tagged 36 Nat)) = 53 ∧ Normed.norm (⟨⟨26⟩⟩ : Tagged 26 (Tagged 36 Nat)) = 26 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_027 (x y : Tagged 27 (Tagged 37 (Tagged 47 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_027 : (evalDiamond (α := Tagged 27 (Tagged 37 Nat × Tagged 47 Nat)) ⟨(⟨27⟩, ⟨28⟩)⟩ ⟨(⟨29⟩, ⟨30⟩)⟩).val.1.val = 84 := rfl
theorem s2_outparam_bridge_027 : bridgeApply (⟨⟨27⟩⟩ : Tagged 27 (Tagged 37 Nat)) = 55 ∧ Normed.norm (⟨⟨27⟩⟩ : Tagged 27 (Tagged 37 Nat)) = 27 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_028 (x y : Tagged 28 (Tagged 38 (Tagged 48 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_028 : (evalDiamond (α := Tagged 28 (Tagged 38 Nat × Tagged 48 Nat)) ⟨(⟨28⟩, ⟨29⟩)⟩ ⟨(⟨30⟩, ⟨31⟩)⟩).val.1.val = 87 := rfl
theorem s2_outparam_bridge_028 : bridgeApply (⟨⟨28⟩⟩ : Tagged 28 (Tagged 38 Nat)) = 57 ∧ Normed.norm (⟨⟨28⟩⟩ : Tagged 28 (Tagged 38 Nat)) = 28 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_029 (x y : Tagged 29 (Tagged 39 (Tagged 49 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_029 : (evalDiamond (α := Tagged 29 (Tagged 39 Nat × Tagged 49 Nat)) ⟨(⟨29⟩, ⟨30⟩)⟩ ⟨(⟨31⟩, ⟨32⟩)⟩).val.1.val = 90 := rfl
theorem s2_outparam_bridge_029 : bridgeApply (⟨⟨29⟩⟩ : Tagged 29 (Tagged 39 Nat)) = 59 ∧ Normed.norm (⟨⟨29⟩⟩ : Tagged 29 (Tagged 39 Nat)) = 29 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_030 (x y : Tagged 30 (Tagged 40 (Tagged 50 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_030 : (evalDiamond (α := Tagged 30 (Tagged 40 Nat × Tagged 50 Nat)) ⟨(⟨30⟩, ⟨31⟩)⟩ ⟨(⟨32⟩, ⟨33⟩)⟩).val.1.val = 93 := rfl
theorem s2_outparam_bridge_030 : bridgeApply (⟨⟨30⟩⟩ : Tagged 30 (Tagged 40 Nat)) = 61 ∧ Normed.norm (⟨⟨30⟩⟩ : Tagged 30 (Tagged 40 Nat)) = 30 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_031 (x y : Tagged 31 (Tagged 41 (Tagged 51 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_031 : (evalDiamond (α := Tagged 31 (Tagged 41 Nat × Tagged 51 Nat)) ⟨(⟨31⟩, ⟨32⟩)⟩ ⟨(⟨33⟩, ⟨34⟩)⟩).val.1.val = 96 := rfl
theorem s2_outparam_bridge_031 : bridgeApply (⟨⟨31⟩⟩ : Tagged 31 (Tagged 41 Nat)) = 63 ∧ Normed.norm (⟨⟨31⟩⟩ : Tagged 31 (Tagged 41 Nat)) = 31 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_032 (x y : Tagged 32 (Tagged 42 (Tagged 52 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_032 : (evalDiamond (α := Tagged 32 (Tagged 42 Nat × Tagged 52 Nat)) ⟨(⟨32⟩, ⟨33⟩)⟩ ⟨(⟨34⟩, ⟨35⟩)⟩).val.1.val = 99 := rfl
theorem s2_outparam_bridge_032 : bridgeApply (⟨⟨32⟩⟩ : Tagged 32 (Tagged 42 Nat)) = 65 ∧ Normed.norm (⟨⟨32⟩⟩ : Tagged 32 (Tagged 42 Nat)) = 32 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_033 (x y : Tagged 33 (Tagged 43 (Tagged 53 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_033 : (evalDiamond (α := Tagged 33 (Tagged 43 Nat × Tagged 53 Nat)) ⟨(⟨33⟩, ⟨34⟩)⟩ ⟨(⟨35⟩, ⟨36⟩)⟩).val.1.val = 102 := rfl
theorem s2_outparam_bridge_033 : bridgeApply (⟨⟨33⟩⟩ : Tagged 33 (Tagged 43 Nat)) = 67 ∧ Normed.norm (⟨⟨33⟩⟩ : Tagged 33 (Tagged 43 Nat)) = 33 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_034 (x y : Tagged 34 (Tagged 44 (Tagged 54 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_034 : (evalDiamond (α := Tagged 34 (Tagged 44 Nat × Tagged 54 Nat)) ⟨(⟨34⟩, ⟨35⟩)⟩ ⟨(⟨36⟩, ⟨37⟩)⟩).val.1.val = 105 := rfl
theorem s2_outparam_bridge_034 : bridgeApply (⟨⟨34⟩⟩ : Tagged 34 (Tagged 44 Nat)) = 69 ∧ Normed.norm (⟨⟨34⟩⟩ : Tagged 34 (Tagged 44 Nat)) = 34 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_035 (x y : Tagged 35 (Tagged 45 (Tagged 55 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_035 : (evalDiamond (α := Tagged 35 (Tagged 45 Nat × Tagged 55 Nat)) ⟨(⟨35⟩, ⟨36⟩)⟩ ⟨(⟨37⟩, ⟨38⟩)⟩).val.1.val = 108 := rfl
theorem s2_outparam_bridge_035 : bridgeApply (⟨⟨35⟩⟩ : Tagged 35 (Tagged 45 Nat)) = 71 ∧ Normed.norm (⟨⟨35⟩⟩ : Tagged 35 (Tagged 45 Nat)) = 35 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_036 (x y : Tagged 36 (Tagged 46 (Tagged 56 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_036 : (evalDiamond (α := Tagged 36 (Tagged 46 Nat × Tagged 56 Nat)) ⟨(⟨36⟩, ⟨37⟩)⟩ ⟨(⟨38⟩, ⟨39⟩)⟩).val.1.val = 111 := rfl
theorem s2_outparam_bridge_036 : bridgeApply (⟨⟨36⟩⟩ : Tagged 36 (Tagged 46 Nat)) = 73 ∧ Normed.norm (⟨⟨36⟩⟩ : Tagged 36 (Tagged 46 Nat)) = 36 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_037 (x y : Tagged 37 (Tagged 47 (Tagged 57 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_037 : (evalDiamond (α := Tagged 37 (Tagged 47 Nat × Tagged 57 Nat)) ⟨(⟨37⟩, ⟨38⟩)⟩ ⟨(⟨39⟩, ⟨40⟩)⟩).val.1.val = 114 := rfl
theorem s2_outparam_bridge_037 : bridgeApply (⟨⟨37⟩⟩ : Tagged 37 (Tagged 47 Nat)) = 75 ∧ Normed.norm (⟨⟨37⟩⟩ : Tagged 37 (Tagged 47 Nat)) = 37 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_038 (x y : Tagged 38 (Tagged 48 (Tagged 58 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_038 : (evalDiamond (α := Tagged 38 (Tagged 48 Nat × Tagged 58 Nat)) ⟨(⟨38⟩, ⟨39⟩)⟩ ⟨(⟨40⟩, ⟨41⟩)⟩).val.1.val = 117 := rfl
theorem s2_outparam_bridge_038 : bridgeApply (⟨⟨38⟩⟩ : Tagged 38 (Tagged 48 Nat)) = 77 ∧ Normed.norm (⟨⟨38⟩⟩ : Tagged 38 (Tagged 48 Nat)) = 38 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_039 (x y : Tagged 39 (Tagged 49 (Tagged 59 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_039 : (evalDiamond (α := Tagged 39 (Tagged 49 Nat × Tagged 59 Nat)) ⟨(⟨39⟩, ⟨40⟩)⟩ ⟨(⟨41⟩, ⟨42⟩)⟩).val.1.val = 120 := rfl
theorem s2_outparam_bridge_039 : bridgeApply (⟨⟨39⟩⟩ : Tagged 39 (Tagged 49 Nat)) = 79 ∧ Normed.norm (⟨⟨39⟩⟩ : Tagged 39 (Tagged 49 Nat)) = 39 := ⟨rfl, rfl⟩
theorem s2_diamond_comm_040 (x y : Tagged 40 (Tagged 50 (Tagged 60 Nat))) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem s2_diamond_ground_040 : (evalDiamond (α := Tagged 40 (Tagged 50 Nat × Tagged 60 Nat)) ⟨(⟨40⟩, ⟨41⟩)⟩ ⟨(⟨42⟩, ⟨43⟩)⟩).val.1.val = 123 := rfl
theorem s2_outparam_bridge_040 : bridgeApply (⟨⟨40⟩⟩ : Tagged 40 (Tagged 50 Nat)) = 81 ∧ Normed.norm (⟨⟨40⟩⟩ : Tagged 40 (Tagged 50 Nat)) = 40 := ⟨rfl, rfl⟩

end SyntheticBench.S2
