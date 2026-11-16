import Std

theorem badGrind (a b : Nat) (f : Nat → Nat) (h : a = b) : f a = f b + 1 := by
  grind
