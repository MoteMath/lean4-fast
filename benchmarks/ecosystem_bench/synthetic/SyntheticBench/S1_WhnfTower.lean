import SyntheticBench.Base

namespace SyntheticBench.S1

def tower0 (x : Nat) : Nat := x + 1
def tower1 (x : Nat) : Nat := tower0 (tower0 x) + 2
def tower2 (x : Nat) : Nat := tower1 (tower1 x) + 3
def tower3 (x : Nat) : Nat := tower2 (tower2 x) + 5
def tower4 (x : Nat) : Nat := tower3 (tower3 x) + 7

def depVec : (n : Nat) → Type
  | 0 => Unit
  | n + 1 => Nat × depVec n

def depSum : (n : Nat) → depVec n → Nat
  | 0, () => 0
  | n + 1, (a, rest) => a + depSum n rest

def churchMul (f : Nat → Nat) (n x : Nat) : Nat :=
  match n with
  | 0 => x
  | k + 1 => churchMul f k (f x)

def openBetaStep (k : Nat) (f : Nat → Nat) (x : Nat) : Nat :=
  (fun g a => g (g a + k)) f (x + 1)

theorem s1_tower4_001 : tower4 10 = 71 := rfl
theorem s1_tower4_002 : tower4 17 = 78 := rfl
theorem s1_tower4_003 : tower4 24 = 85 := rfl
theorem s1_tower4_004 : tower4 31 = 92 := rfl
theorem s1_tower4_005 : tower4 38 = 99 := rfl
theorem s1_tower4_006 : tower4 4 = 65 := rfl
theorem s1_tower4_007 : tower4 11 = 72 := rfl
theorem s1_tower4_008 : tower4 18 = 79 := rfl
theorem s1_tower4_009 : tower4 25 = 86 := rfl
theorem s1_tower4_010 : tower4 32 = 93 := rfl
theorem s1_tower4_011 : tower4 39 = 100 := rfl
theorem s1_tower4_012 : tower4 5 = 66 := rfl
theorem s1_tower4_013 : tower4 12 = 73 := rfl
theorem s1_tower4_014 : tower4 19 = 80 := rfl
theorem s1_tower4_015 : tower4 26 = 87 := rfl
theorem s1_tower4_016 : tower4 33 = 94 := rfl
theorem s1_tower4_017 : tower4 40 = 101 := rfl
theorem s1_tower4_018 : tower4 6 = 67 := rfl
theorem s1_tower4_019 : tower4 13 = 74 := rfl
theorem s1_tower4_020 : tower4 20 = 81 := rfl
theorem s1_tower4_021 : tower4 27 = 88 := rfl
theorem s1_tower4_022 : tower4 34 = 95 := rfl
theorem s1_tower4_023 : tower4 0 = 61 := rfl
theorem s1_tower4_024 : tower4 7 = 68 := rfl
theorem s1_tower4_025 : tower4 14 = 75 := rfl
theorem s1_tower4_026 : tower4 21 = 82 := rfl
theorem s1_tower4_027 : tower4 28 = 89 := rfl
theorem s1_tower4_028 : tower4 35 = 96 := rfl
theorem s1_tower4_029 : tower4 1 = 62 := rfl
theorem s1_tower4_030 : tower4 8 = 69 := rfl
theorem s1_tower4_031 : tower4 15 = 76 := rfl
theorem s1_tower4_032 : tower4 22 = 83 := rfl
theorem s1_tower4_033 : tower4 29 = 90 := rfl
theorem s1_tower4_034 : tower4 36 = 97 := rfl
theorem s1_tower4_035 : tower4 2 = 63 := rfl
theorem s1_tower4_036 : tower4 9 = 70 := rfl
theorem s1_tower4_037 : tower4 16 = 77 := rfl
theorem s1_tower4_038 : tower4 23 = 84 := rfl
theorem s1_tower4_039 : tower4 30 = 91 := rfl
theorem s1_tower4_040 : tower4 37 = 98 := rfl
theorem s1_tower4_041 : tower4 3 = 64 := rfl
theorem s1_tower4_042 : tower4 10 = 71 := rfl
theorem s1_tower4_043 : tower4 17 = 78 := rfl
theorem s1_tower4_044 : tower4 24 = 85 := rfl
theorem s1_tower4_045 : tower4 31 = 92 := rfl
theorem s1_tower4_046 : tower4 38 = 99 := rfl
theorem s1_tower4_047 : tower4 4 = 65 := rfl
theorem s1_tower4_048 : tower4 11 = 72 := rfl
theorem s1_tower4_049 : tower4 18 = 79 := rfl
theorem s1_tower4_050 : tower4 25 = 86 := rfl
theorem s1_tower4_051 : tower4 32 = 93 := rfl
theorem s1_tower4_052 : tower4 39 = 100 := rfl
theorem s1_tower4_053 : tower4 5 = 66 := rfl
theorem s1_tower4_054 : tower4 12 = 73 := rfl
theorem s1_tower4_055 : tower4 19 = 80 := rfl
theorem s1_church_001 : churchMul (fun z => z + 2) 3 4 = 10 := rfl
theorem s1_church_002 : churchMul (fun z => z + 3) 4 7 = 19 := rfl
theorem s1_church_003 : churchMul (fun z => z + 4) 5 10 = 30 := rfl
theorem s1_church_004 : churchMul (fun z => z + 5) 6 13 = 43 := rfl
theorem s1_church_005 : churchMul (fun z => z + 1) 7 16 = 23 := rfl
theorem s1_church_006 : churchMul (fun z => z + 2) 8 19 = 35 := rfl
theorem s1_church_007 : churchMul (fun z => z + 3) 9 22 = 49 := rfl
theorem s1_church_008 : churchMul (fun z => z + 4) 10 25 = 65 := rfl
theorem s1_church_009 : churchMul (fun z => z + 5) 11 28 = 83 := rfl
theorem s1_church_010 : churchMul (fun z => z + 1) 12 1 = 13 := rfl
theorem s1_church_011 : churchMul (fun z => z + 2) 13 4 = 30 := rfl
theorem s1_church_012 : churchMul (fun z => z + 3) 2 7 = 13 := rfl
theorem s1_church_013 : churchMul (fun z => z + 4) 3 10 = 22 := rfl
theorem s1_church_014 : churchMul (fun z => z + 5) 4 13 = 33 := rfl
theorem s1_church_015 : churchMul (fun z => z + 1) 5 16 = 21 := rfl
theorem s1_church_016 : churchMul (fun z => z + 2) 6 19 = 31 := rfl
theorem s1_church_017 : churchMul (fun z => z + 3) 7 22 = 43 := rfl
theorem s1_church_018 : churchMul (fun z => z + 4) 8 25 = 57 := rfl
theorem s1_church_019 : churchMul (fun z => z + 5) 9 28 = 73 := rfl
theorem s1_church_020 : churchMul (fun z => z + 1) 10 1 = 11 := rfl
theorem s1_church_021 : churchMul (fun z => z + 2) 11 4 = 26 := rfl
theorem s1_church_022 : churchMul (fun z => z + 3) 12 7 = 43 := rfl
theorem s1_church_023 : churchMul (fun z => z + 4) 13 10 = 62 := rfl
theorem s1_church_024 : churchMul (fun z => z + 5) 2 13 = 23 := rfl
theorem s1_church_025 : churchMul (fun z => z + 1) 3 16 = 19 := rfl
theorem s1_church_026 : churchMul (fun z => z + 2) 4 19 = 27 := rfl
theorem s1_church_027 : churchMul (fun z => z + 3) 5 22 = 37 := rfl
theorem s1_church_028 : churchMul (fun z => z + 4) 6 25 = 49 := rfl
theorem s1_church_029 : churchMul (fun z => z + 5) 7 28 = 63 := rfl
theorem s1_church_030 : churchMul (fun z => z + 1) 8 1 = 9 := rfl
theorem s1_church_031 : churchMul (fun z => z + 2) 9 4 = 22 := rfl
theorem s1_church_032 : churchMul (fun z => z + 3) 10 7 = 37 := rfl
theorem s1_church_033 : churchMul (fun z => z + 4) 11 10 = 54 := rfl
theorem s1_church_034 : churchMul (fun z => z + 5) 12 13 = 73 := rfl
theorem s1_church_035 : churchMul (fun z => z + 1) 13 16 = 29 := rfl
theorem s1_church_036 : churchMul (fun z => z + 2) 2 19 = 23 := rfl
theorem s1_church_037 : churchMul (fun z => z + 3) 3 22 = 31 := rfl
theorem s1_church_038 : churchMul (fun z => z + 4) 4 25 = 41 := rfl
theorem s1_church_039 : churchMul (fun z => z + 5) 5 28 = 53 := rfl
theorem s1_church_040 : churchMul (fun z => z + 1) 6 1 = 7 := rfl
theorem s1_church_041 : churchMul (fun z => z + 2) 7 4 = 18 := rfl
theorem s1_church_042 : churchMul (fun z => z + 3) 8 7 = 31 := rfl
theorem s1_church_043 : churchMul (fun z => z + 4) 9 10 = 46 := rfl
theorem s1_church_044 : churchMul (fun z => z + 5) 10 13 = 63 := rfl
theorem s1_church_045 : churchMul (fun z => z + 1) 11 16 = 27 := rfl
theorem s1_church_046 : churchMul (fun z => z + 2) 12 19 = 43 := rfl
theorem s1_church_047 : churchMul (fun z => z + 3) 13 22 = 61 := rfl
theorem s1_church_048 : churchMul (fun z => z + 4) 2 25 = 33 := rfl
theorem s1_church_049 : churchMul (fun z => z + 5) 3 28 = 43 := rfl
theorem s1_church_050 : churchMul (fun z => z + 1) 4 1 = 5 := rfl
theorem s1_church_051 : churchMul (fun z => z + 2) 5 4 = 14 := rfl
theorem s1_church_052 : churchMul (fun z => z + 3) 6 7 = 25 := rfl
theorem s1_church_053 : churchMul (fun z => z + 4) 7 10 = 38 := rfl
theorem s1_church_054 : churchMul (fun z => z + 5) 8 13 = 53 := rfl
theorem s1_church_055 : churchMul (fun z => z + 1) 9 16 = 25 := rfl
theorem s1_open_beta_001 (f : Nat → Nat) (x : Nat) : openBetaStep 2 f x = f (f (x + 1) + 2) := rfl
theorem s1_open_beta_002 (f : Nat → Nat) (x : Nat) : openBetaStep 3 f x = f (f (x + 1) + 3) := rfl
theorem s1_open_beta_003 (f : Nat → Nat) (x : Nat) : openBetaStep 4 f x = f (f (x + 1) + 4) := rfl
theorem s1_open_beta_004 (f : Nat → Nat) (x : Nat) : openBetaStep 5 f x = f (f (x + 1) + 5) := rfl
theorem s1_open_beta_005 (f : Nat → Nat) (x : Nat) : openBetaStep 6 f x = f (f (x + 1) + 6) := rfl
theorem s1_open_beta_006 (f : Nat → Nat) (x : Nat) : openBetaStep 7 f x = f (f (x + 1) + 7) := rfl
theorem s1_open_beta_007 (f : Nat → Nat) (x : Nat) : openBetaStep 8 f x = f (f (x + 1) + 8) := rfl
theorem s1_open_beta_008 (f : Nat → Nat) (x : Nat) : openBetaStep 9 f x = f (f (x + 1) + 9) := rfl
theorem s1_open_beta_009 (f : Nat → Nat) (x : Nat) : openBetaStep 1 f x = f (f (x + 1) + 1) := rfl
theorem s1_open_beta_010 (f : Nat → Nat) (x : Nat) : openBetaStep 2 f x = f (f (x + 1) + 2) := rfl
theorem s1_open_beta_011 (f : Nat → Nat) (x : Nat) : openBetaStep 3 f x = f (f (x + 1) + 3) := rfl
theorem s1_open_beta_012 (f : Nat → Nat) (x : Nat) : openBetaStep 4 f x = f (f (x + 1) + 4) := rfl
theorem s1_open_beta_013 (f : Nat → Nat) (x : Nat) : openBetaStep 5 f x = f (f (x + 1) + 5) := rfl
theorem s1_open_beta_014 (f : Nat → Nat) (x : Nat) : openBetaStep 6 f x = f (f (x + 1) + 6) := rfl
theorem s1_open_beta_015 (f : Nat → Nat) (x : Nat) : openBetaStep 7 f x = f (f (x + 1) + 7) := rfl
theorem s1_open_beta_016 (f : Nat → Nat) (x : Nat) : openBetaStep 8 f x = f (f (x + 1) + 8) := rfl
theorem s1_open_beta_017 (f : Nat → Nat) (x : Nat) : openBetaStep 9 f x = f (f (x + 1) + 9) := rfl
theorem s1_open_beta_018 (f : Nat → Nat) (x : Nat) : openBetaStep 1 f x = f (f (x + 1) + 1) := rfl
theorem s1_open_beta_019 (f : Nat → Nat) (x : Nat) : openBetaStep 2 f x = f (f (x + 1) + 2) := rfl
theorem s1_open_beta_020 (f : Nat → Nat) (x : Nat) : openBetaStep 3 f x = f (f (x + 1) + 3) := rfl
theorem s1_open_beta_021 (f : Nat → Nat) (x : Nat) : openBetaStep 4 f x = f (f (x + 1) + 4) := rfl
theorem s1_open_beta_022 (f : Nat → Nat) (x : Nat) : openBetaStep 5 f x = f (f (x + 1) + 5) := rfl
theorem s1_open_beta_023 (f : Nat → Nat) (x : Nat) : openBetaStep 6 f x = f (f (x + 1) + 6) := rfl
theorem s1_open_beta_024 (f : Nat → Nat) (x : Nat) : openBetaStep 7 f x = f (f (x + 1) + 7) := rfl
theorem s1_open_beta_025 (f : Nat → Nat) (x : Nat) : openBetaStep 8 f x = f (f (x + 1) + 8) := rfl
theorem s1_dep_tree_001 (g : Nat → Nat) : depSum 3 (1, (3, (5, ()))) + 0 = 9 ∧ (ExprTree.leaf (1 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_002 (g : Nat → Nat) : depSum 3 (2, (4, (6, ()))) + 0 = 12 ∧ (ExprTree.leaf (2 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_003 (g : Nat → Nat) : depSum 3 (3, (5, (7, ()))) + 0 = 15 ∧ (ExprTree.leaf (3 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_004 (g : Nat → Nat) : depSum 3 (4, (6, (8, ()))) + 0 = 18 ∧ (ExprTree.leaf (4 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_005 (g : Nat → Nat) : depSum 3 (5, (7, (9, ()))) + 0 = 21 ∧ (ExprTree.leaf (5 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_006 (g : Nat → Nat) : depSum 3 (6, (8, (10, ()))) + 0 = 24 ∧ (ExprTree.leaf (6 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_007 (g : Nat → Nat) : depSum 3 (7, (9, (11, ()))) + 0 = 27 ∧ (ExprTree.leaf (7 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_008 (g : Nat → Nat) : depSum 3 (8, (10, (12, ()))) + 0 = 30 ∧ (ExprTree.leaf (8 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_009 (g : Nat → Nat) : depSum 3 (9, (11, (13, ()))) + 0 = 33 ∧ (ExprTree.leaf (9 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_010 (g : Nat → Nat) : depSum 3 (10, (12, (14, ()))) + 0 = 36 ∧ (ExprTree.leaf (10 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_011 (g : Nat → Nat) : depSum 3 (11, (13, (15, ()))) + 0 = 39 ∧ (ExprTree.leaf (11 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_012 (g : Nat → Nat) : depSum 3 (12, (14, (16, ()))) + 0 = 42 ∧ (ExprTree.leaf (12 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_013 (g : Nat → Nat) : depSum 3 (13, (15, (17, ()))) + 0 = 45 ∧ (ExprTree.leaf (13 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_014 (g : Nat → Nat) : depSum 3 (14, (16, (18, ()))) + 0 = 48 ∧ (ExprTree.leaf (14 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_015 (g : Nat → Nat) : depSum 3 (15, (17, (19, ()))) + 0 = 51 ∧ (ExprTree.leaf (15 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_016 (g : Nat → Nat) : depSum 3 (16, (18, (20, ()))) + 0 = 54 ∧ (ExprTree.leaf (16 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_017 (g : Nat → Nat) : depSum 3 (17, (19, (21, ()))) + 0 = 57 ∧ (ExprTree.leaf (17 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_018 (g : Nat → Nat) : depSum 3 (18, (20, (22, ()))) + 0 = 60 ∧ (ExprTree.leaf (18 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_019 (g : Nat → Nat) : depSum 3 (19, (21, (23, ()))) + 0 = 63 ∧ (ExprTree.leaf (19 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_020 (g : Nat → Nat) : depSum 3 (20, (22, (24, ()))) + 0 = 66 ∧ (ExprTree.leaf (20 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_021 (g : Nat → Nat) : depSum 3 (21, (23, (25, ()))) + 0 = 69 ∧ (ExprTree.leaf (21 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_022 (g : Nat → Nat) : depSum 3 (22, (24, (26, ()))) + 0 = 72 ∧ (ExprTree.leaf (22 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_023 (g : Nat → Nat) : depSum 3 (23, (25, (27, ()))) + 0 = 75 ∧ (ExprTree.leaf (23 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_024 (g : Nat → Nat) : depSum 3 (24, (26, (28, ()))) + 0 = 78 ∧ (ExprTree.leaf (24 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩
theorem s1_dep_tree_025 (g : Nat → Nat) : depSum 3 (25, (27, (29, ()))) + 0 = 81 ∧ (ExprTree.leaf (25 : Nat) |> ExprTree.map g |> ExprTree.size) = 1 := ⟨rfl, rfl⟩

end SyntheticBench.S1
