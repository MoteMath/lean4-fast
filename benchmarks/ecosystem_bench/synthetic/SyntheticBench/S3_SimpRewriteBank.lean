import SyntheticBench.Base

namespace SyntheticBench.S3

def tagAdd0 (k x : Nat) : Nat := x + k
def tagMul1 (k x : Nat) : Nat := x * k
def wrapId (x : Nat) : Nat := x
def pairWrap (a b : Nat) : Nat × Nat := (a, b)

@[simp] theorem wrapId_eq (x : Nat) : wrapId x = x := rfl
@[simp] theorem pairWrap_fst (a b : Nat) : (pairWrap a b).1 = a := rfl
@[simp] theorem pairWrap_snd (a b : Nat) : (pairWrap a b).2 = b := rfl
@[simp] theorem tagAdd0_zero (x : Nat) : tagAdd0 0 x = x := Nat.add_zero x
@[simp] theorem tagMul1_one (x : Nat) : tagMul1 1 x = x := Nat.mul_one x

def bankOp001 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp001_spec (x : Nat) : bankOp001 x = x + 1 := rfl
def bankOp002 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp002_spec (x : Nat) : bankOp002 x = x + 2 := rfl
def bankOp003 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp003_spec (x : Nat) : bankOp003 x = x + 3 := rfl
def bankOp004 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp004_spec (x : Nat) : bankOp004 x = x + 4 := rfl
def bankOp005 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp005_spec (x : Nat) : bankOp005 x = x + 5 := rfl
def bankOp006 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp006_spec (x : Nat) : bankOp006 x = x + 6 := rfl
def bankOp007 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp007_spec (x : Nat) : bankOp007 x = x + 7 := rfl
def bankOp008 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp008_spec (x : Nat) : bankOp008 x = x + 8 := rfl
def bankOp009 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp009_spec (x : Nat) : bankOp009 x = x + 9 := rfl
def bankOp010 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp010_spec (x : Nat) : bankOp010 x = x + 10 := rfl
def bankOp011 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp011_spec (x : Nat) : bankOp011 x = x + 11 := rfl
def bankOp012 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp012_spec (x : Nat) : bankOp012 x = x + 12 := rfl
def bankOp013 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp013_spec (x : Nat) : bankOp013 x = x + 13 := rfl
def bankOp014 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp014_spec (x : Nat) : bankOp014 x = x + 14 := rfl
def bankOp015 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp015_spec (x : Nat) : bankOp015 x = x + 15 := rfl
def bankOp016 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp016_spec (x : Nat) : bankOp016 x = x + 16 := rfl
def bankOp017 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp017_spec (x : Nat) : bankOp017 x = x + 0 := rfl
def bankOp018 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp018_spec (x : Nat) : bankOp018 x = x + 1 := rfl
def bankOp019 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp019_spec (x : Nat) : bankOp019 x = x + 2 := rfl
def bankOp020 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp020_spec (x : Nat) : bankOp020 x = x + 3 := rfl
def bankOp021 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp021_spec (x : Nat) : bankOp021 x = x + 4 := rfl
def bankOp022 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp022_spec (x : Nat) : bankOp022 x = x + 5 := rfl
def bankOp023 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp023_spec (x : Nat) : bankOp023 x = x + 6 := rfl
def bankOp024 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp024_spec (x : Nat) : bankOp024 x = x + 7 := rfl
def bankOp025 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp025_spec (x : Nat) : bankOp025 x = x + 8 := rfl
def bankOp026 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp026_spec (x : Nat) : bankOp026 x = x + 9 := rfl
def bankOp027 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp027_spec (x : Nat) : bankOp027 x = x + 10 := rfl
def bankOp028 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp028_spec (x : Nat) : bankOp028 x = x + 11 := rfl
def bankOp029 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp029_spec (x : Nat) : bankOp029 x = x + 12 := rfl
def bankOp030 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp030_spec (x : Nat) : bankOp030 x = x + 13 := rfl
def bankOp031 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp031_spec (x : Nat) : bankOp031 x = x + 14 := rfl
def bankOp032 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp032_spec (x : Nat) : bankOp032 x = x + 15 := rfl
def bankOp033 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp033_spec (x : Nat) : bankOp033 x = x + 16 := rfl
def bankOp034 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp034_spec (x : Nat) : bankOp034 x = x + 0 := rfl
def bankOp035 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp035_spec (x : Nat) : bankOp035 x = x + 1 := rfl
def bankOp036 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp036_spec (x : Nat) : bankOp036 x = x + 2 := rfl
def bankOp037 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp037_spec (x : Nat) : bankOp037 x = x + 3 := rfl
def bankOp038 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp038_spec (x : Nat) : bankOp038 x = x + 4 := rfl
def bankOp039 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp039_spec (x : Nat) : bankOp039 x = x + 5 := rfl
def bankOp040 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp040_spec (x : Nat) : bankOp040 x = x + 6 := rfl
def bankOp041 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp041_spec (x : Nat) : bankOp041 x = x + 7 := rfl
def bankOp042 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp042_spec (x : Nat) : bankOp042 x = x + 8 := rfl
def bankOp043 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp043_spec (x : Nat) : bankOp043 x = x + 9 := rfl
def bankOp044 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp044_spec (x : Nat) : bankOp044 x = x + 10 := rfl
def bankOp045 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp045_spec (x : Nat) : bankOp045 x = x + 11 := rfl
def bankOp046 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp046_spec (x : Nat) : bankOp046 x = x + 12 := rfl
def bankOp047 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp047_spec (x : Nat) : bankOp047 x = x + 13 := rfl
def bankOp048 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp048_spec (x : Nat) : bankOp048 x = x + 14 := rfl
def bankOp049 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp049_spec (x : Nat) : bankOp049 x = x + 15 := rfl
def bankOp050 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp050_spec (x : Nat) : bankOp050 x = x + 16 := rfl
def bankOp051 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp051_spec (x : Nat) : bankOp051 x = x + 0 := rfl
def bankOp052 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp052_spec (x : Nat) : bankOp052 x = x + 1 := rfl
def bankOp053 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp053_spec (x : Nat) : bankOp053 x = x + 2 := rfl
def bankOp054 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp054_spec (x : Nat) : bankOp054 x = x + 3 := rfl
def bankOp055 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp055_spec (x : Nat) : bankOp055 x = x + 4 := rfl
def bankOp056 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp056_spec (x : Nat) : bankOp056 x = x + 5 := rfl
def bankOp057 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp057_spec (x : Nat) : bankOp057 x = x + 6 := rfl
def bankOp058 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp058_spec (x : Nat) : bankOp058 x = x + 7 := rfl
def bankOp059 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp059_spec (x : Nat) : bankOp059 x = x + 8 := rfl
def bankOp060 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp060_spec (x : Nat) : bankOp060 x = x + 9 := rfl
def bankOp061 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp061_spec (x : Nat) : bankOp061 x = x + 10 := rfl
def bankOp062 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp062_spec (x : Nat) : bankOp062 x = x + 11 := rfl
def bankOp063 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp063_spec (x : Nat) : bankOp063 x = x + 12 := rfl
def bankOp064 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp064_spec (x : Nat) : bankOp064 x = x + 13 := rfl
def bankOp065 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp065_spec (x : Nat) : bankOp065 x = x + 14 := rfl
def bankOp066 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp066_spec (x : Nat) : bankOp066 x = x + 15 := rfl
def bankOp067 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp067_spec (x : Nat) : bankOp067 x = x + 16 := rfl
def bankOp068 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp068_spec (x : Nat) : bankOp068 x = x + 0 := rfl
def bankOp069 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp069_spec (x : Nat) : bankOp069 x = x + 1 := rfl
def bankOp070 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp070_spec (x : Nat) : bankOp070 x = x + 2 := rfl
def bankOp071 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp071_spec (x : Nat) : bankOp071 x = x + 3 := rfl
def bankOp072 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp072_spec (x : Nat) : bankOp072 x = x + 4 := rfl
def bankOp073 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp073_spec (x : Nat) : bankOp073 x = x + 5 := rfl
def bankOp074 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp074_spec (x : Nat) : bankOp074 x = x + 6 := rfl
def bankOp075 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp075_spec (x : Nat) : bankOp075 x = x + 7 := rfl
def bankOp076 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp076_spec (x : Nat) : bankOp076 x = x + 8 := rfl
def bankOp077 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp077_spec (x : Nat) : bankOp077 x = x + 9 := rfl
def bankOp078 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp078_spec (x : Nat) : bankOp078 x = x + 10 := rfl
def bankOp079 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp079_spec (x : Nat) : bankOp079 x = x + 11 := rfl
def bankOp080 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp080_spec (x : Nat) : bankOp080 x = x + 12 := rfl
def bankOp081 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp081_spec (x : Nat) : bankOp081 x = x + 13 := rfl
def bankOp082 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp082_spec (x : Nat) : bankOp082 x = x + 14 := rfl
def bankOp083 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp083_spec (x : Nat) : bankOp083 x = x + 15 := rfl
def bankOp084 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp084_spec (x : Nat) : bankOp084 x = x + 16 := rfl
def bankOp085 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp085_spec (x : Nat) : bankOp085 x = x + 0 := rfl
def bankOp086 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp086_spec (x : Nat) : bankOp086 x = x + 1 := rfl
def bankOp087 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp087_spec (x : Nat) : bankOp087 x = x + 2 := rfl
def bankOp088 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp088_spec (x : Nat) : bankOp088 x = x + 3 := rfl
def bankOp089 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp089_spec (x : Nat) : bankOp089 x = x + 4 := rfl
def bankOp090 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp090_spec (x : Nat) : bankOp090 x = x + 5 := rfl
def bankOp091 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp091_spec (x : Nat) : bankOp091 x = x + 6 := rfl
def bankOp092 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp092_spec (x : Nat) : bankOp092 x = x + 7 := rfl
def bankOp093 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp093_spec (x : Nat) : bankOp093 x = x + 8 := rfl
def bankOp094 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp094_spec (x : Nat) : bankOp094 x = x + 9 := rfl
def bankOp095 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp095_spec (x : Nat) : bankOp095 x = x + 10 := rfl
def bankOp096 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp096_spec (x : Nat) : bankOp096 x = x + 11 := rfl
def bankOp097 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp097_spec (x : Nat) : bankOp097 x = x + 12 := rfl
def bankOp098 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp098_spec (x : Nat) : bankOp098 x = x + 13 := rfl
def bankOp099 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp099_spec (x : Nat) : bankOp099 x = x + 14 := rfl
def bankOp100 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp100_spec (x : Nat) : bankOp100 x = x + 15 := rfl
def bankOp101 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp101_spec (x : Nat) : bankOp101 x = x + 16 := rfl
def bankOp102 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp102_spec (x : Nat) : bankOp102 x = x + 0 := rfl
def bankOp103 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp103_spec (x : Nat) : bankOp103 x = x + 1 := rfl
def bankOp104 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp104_spec (x : Nat) : bankOp104 x = x + 2 := rfl
def bankOp105 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp105_spec (x : Nat) : bankOp105 x = x + 3 := rfl
def bankOp106 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp106_spec (x : Nat) : bankOp106 x = x + 4 := rfl
def bankOp107 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp107_spec (x : Nat) : bankOp107 x = x + 5 := rfl
def bankOp108 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp108_spec (x : Nat) : bankOp108 x = x + 6 := rfl
def bankOp109 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp109_spec (x : Nat) : bankOp109 x = x + 7 := rfl
def bankOp110 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp110_spec (x : Nat) : bankOp110 x = x + 8 := rfl
def bankOp111 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp111_spec (x : Nat) : bankOp111 x = x + 9 := rfl
def bankOp112 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp112_spec (x : Nat) : bankOp112 x = x + 10 := rfl
def bankOp113 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp113_spec (x : Nat) : bankOp113 x = x + 11 := rfl
def bankOp114 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp114_spec (x : Nat) : bankOp114 x = x + 12 := rfl
def bankOp115 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp115_spec (x : Nat) : bankOp115 x = x + 13 := rfl
def bankOp116 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp116_spec (x : Nat) : bankOp116 x = x + 14 := rfl
def bankOp117 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp117_spec (x : Nat) : bankOp117 x = x + 15 := rfl
def bankOp118 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp118_spec (x : Nat) : bankOp118 x = x + 16 := rfl
def bankOp119 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp119_spec (x : Nat) : bankOp119 x = x + 0 := rfl
def bankOp120 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp120_spec (x : Nat) : bankOp120 x = x + 1 := rfl
def bankOp121 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp121_spec (x : Nat) : bankOp121 x = x + 2 := rfl
def bankOp122 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp122_spec (x : Nat) : bankOp122 x = x + 3 := rfl
def bankOp123 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp123_spec (x : Nat) : bankOp123 x = x + 4 := rfl
def bankOp124 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp124_spec (x : Nat) : bankOp124 x = x + 5 := rfl
def bankOp125 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp125_spec (x : Nat) : bankOp125 x = x + 6 := rfl
def bankOp126 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp126_spec (x : Nat) : bankOp126 x = x + 7 := rfl
def bankOp127 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp127_spec (x : Nat) : bankOp127 x = x + 8 := rfl
def bankOp128 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp128_spec (x : Nat) : bankOp128 x = x + 9 := rfl
def bankOp129 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp129_spec (x : Nat) : bankOp129 x = x + 10 := rfl
def bankOp130 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp130_spec (x : Nat) : bankOp130 x = x + 11 := rfl
def bankOp131 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp131_spec (x : Nat) : bankOp131 x = x + 12 := rfl
def bankOp132 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp132_spec (x : Nat) : bankOp132 x = x + 13 := rfl
def bankOp133 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp133_spec (x : Nat) : bankOp133 x = x + 14 := rfl
def bankOp134 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp134_spec (x : Nat) : bankOp134 x = x + 15 := rfl
def bankOp135 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp135_spec (x : Nat) : bankOp135 x = x + 16 := rfl
def bankOp136 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp136_spec (x : Nat) : bankOp136 x = x + 0 := rfl
def bankOp137 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp137_spec (x : Nat) : bankOp137 x = x + 1 := rfl
def bankOp138 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp138_spec (x : Nat) : bankOp138 x = x + 2 := rfl
def bankOp139 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp139_spec (x : Nat) : bankOp139 x = x + 3 := rfl
def bankOp140 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp140_spec (x : Nat) : bankOp140 x = x + 4 := rfl
def bankOp141 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp141_spec (x : Nat) : bankOp141 x = x + 5 := rfl
def bankOp142 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp142_spec (x : Nat) : bankOp142 x = x + 6 := rfl
def bankOp143 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp143_spec (x : Nat) : bankOp143 x = x + 7 := rfl
def bankOp144 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp144_spec (x : Nat) : bankOp144 x = x + 8 := rfl
def bankOp145 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp145_spec (x : Nat) : bankOp145 x = x + 9 := rfl
def bankOp146 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp146_spec (x : Nat) : bankOp146 x = x + 10 := rfl
def bankOp147 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp147_spec (x : Nat) : bankOp147 x = x + 11 := rfl
def bankOp148 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp148_spec (x : Nat) : bankOp148 x = x + 12 := rfl
def bankOp149 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp149_spec (x : Nat) : bankOp149 x = x + 13 := rfl
def bankOp150 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp150_spec (x : Nat) : bankOp150 x = x + 14 := rfl
def bankOp151 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp151_spec (x : Nat) : bankOp151 x = x + 15 := rfl
def bankOp152 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp152_spec (x : Nat) : bankOp152 x = x + 16 := rfl
def bankOp153 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp153_spec (x : Nat) : bankOp153 x = x + 0 := rfl
def bankOp154 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp154_spec (x : Nat) : bankOp154 x = x + 1 := rfl
def bankOp155 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp155_spec (x : Nat) : bankOp155 x = x + 2 := rfl
def bankOp156 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp156_spec (x : Nat) : bankOp156 x = x + 3 := rfl
def bankOp157 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp157_spec (x : Nat) : bankOp157 x = x + 4 := rfl
def bankOp158 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp158_spec (x : Nat) : bankOp158 x = x + 5 := rfl
def bankOp159 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp159_spec (x : Nat) : bankOp159 x = x + 6 := rfl
def bankOp160 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp160_spec (x : Nat) : bankOp160 x = x + 7 := rfl
def bankOp161 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp161_spec (x : Nat) : bankOp161 x = x + 8 := rfl
def bankOp162 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp162_spec (x : Nat) : bankOp162 x = x + 9 := rfl
def bankOp163 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp163_spec (x : Nat) : bankOp163 x = x + 10 := rfl
def bankOp164 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp164_spec (x : Nat) : bankOp164 x = x + 11 := rfl
def bankOp165 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp165_spec (x : Nat) : bankOp165 x = x + 12 := rfl
def bankOp166 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp166_spec (x : Nat) : bankOp166 x = x + 13 := rfl
def bankOp167 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp167_spec (x : Nat) : bankOp167 x = x + 14 := rfl
def bankOp168 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp168_spec (x : Nat) : bankOp168 x = x + 15 := rfl
def bankOp169 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp169_spec (x : Nat) : bankOp169 x = x + 16 := rfl
def bankOp170 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp170_spec (x : Nat) : bankOp170 x = x + 0 := rfl
def bankOp171 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp171_spec (x : Nat) : bankOp171 x = x + 1 := rfl
def bankOp172 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp172_spec (x : Nat) : bankOp172 x = x + 2 := rfl
def bankOp173 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp173_spec (x : Nat) : bankOp173 x = x + 3 := rfl
def bankOp174 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp174_spec (x : Nat) : bankOp174 x = x + 4 := rfl
def bankOp175 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp175_spec (x : Nat) : bankOp175 x = x + 5 := rfl
def bankOp176 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp176_spec (x : Nat) : bankOp176 x = x + 6 := rfl
def bankOp177 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp177_spec (x : Nat) : bankOp177 x = x + 7 := rfl
def bankOp178 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp178_spec (x : Nat) : bankOp178 x = x + 8 := rfl
def bankOp179 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp179_spec (x : Nat) : bankOp179 x = x + 9 := rfl
def bankOp180 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp180_spec (x : Nat) : bankOp180 x = x + 10 := rfl
def bankOp181 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp181_spec (x : Nat) : bankOp181 x = x + 11 := rfl
def bankOp182 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp182_spec (x : Nat) : bankOp182 x = x + 12 := rfl
def bankOp183 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp183_spec (x : Nat) : bankOp183 x = x + 13 := rfl
def bankOp184 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp184_spec (x : Nat) : bankOp184 x = x + 14 := rfl
def bankOp185 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp185_spec (x : Nat) : bankOp185 x = x + 15 := rfl
def bankOp186 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp186_spec (x : Nat) : bankOp186 x = x + 16 := rfl
def bankOp187 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp187_spec (x : Nat) : bankOp187 x = x + 0 := rfl
def bankOp188 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp188_spec (x : Nat) : bankOp188 x = x + 1 := rfl
def bankOp189 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp189_spec (x : Nat) : bankOp189 x = x + 2 := rfl
def bankOp190 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp190_spec (x : Nat) : bankOp190 x = x + 3 := rfl
def bankOp191 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp191_spec (x : Nat) : bankOp191 x = x + 4 := rfl
def bankOp192 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp192_spec (x : Nat) : bankOp192 x = x + 5 := rfl
def bankOp193 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp193_spec (x : Nat) : bankOp193 x = x + 6 := rfl
def bankOp194 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp194_spec (x : Nat) : bankOp194 x = x + 7 := rfl
def bankOp195 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp195_spec (x : Nat) : bankOp195 x = x + 8 := rfl
def bankOp196 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp196_spec (x : Nat) : bankOp196 x = x + 9 := rfl
def bankOp197 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp197_spec (x : Nat) : bankOp197 x = x + 10 := rfl
def bankOp198 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp198_spec (x : Nat) : bankOp198 x = x + 11 := rfl
def bankOp199 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp199_spec (x : Nat) : bankOp199 x = x + 12 := rfl
def bankOp200 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp200_spec (x : Nat) : bankOp200 x = x + 13 := rfl
def bankOp201 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp201_spec (x : Nat) : bankOp201 x = x + 14 := rfl
def bankOp202 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp202_spec (x : Nat) : bankOp202 x = x + 15 := rfl
def bankOp203 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp203_spec (x : Nat) : bankOp203 x = x + 16 := rfl
def bankOp204 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp204_spec (x : Nat) : bankOp204 x = x + 0 := rfl
def bankOp205 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp205_spec (x : Nat) : bankOp205 x = x + 1 := rfl
def bankOp206 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp206_spec (x : Nat) : bankOp206 x = x + 2 := rfl
def bankOp207 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp207_spec (x : Nat) : bankOp207 x = x + 3 := rfl
def bankOp208 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp208_spec (x : Nat) : bankOp208 x = x + 4 := rfl
def bankOp209 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp209_spec (x : Nat) : bankOp209 x = x + 5 := rfl
def bankOp210 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp210_spec (x : Nat) : bankOp210 x = x + 6 := rfl
def bankOp211 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp211_spec (x : Nat) : bankOp211 x = x + 7 := rfl
def bankOp212 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp212_spec (x : Nat) : bankOp212 x = x + 8 := rfl
def bankOp213 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp213_spec (x : Nat) : bankOp213 x = x + 9 := rfl
def bankOp214 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp214_spec (x : Nat) : bankOp214 x = x + 10 := rfl
def bankOp215 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp215_spec (x : Nat) : bankOp215 x = x + 11 := rfl
def bankOp216 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp216_spec (x : Nat) : bankOp216 x = x + 12 := rfl
def bankOp217 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp217_spec (x : Nat) : bankOp217 x = x + 13 := rfl
def bankOp218 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp218_spec (x : Nat) : bankOp218 x = x + 14 := rfl
def bankOp219 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp219_spec (x : Nat) : bankOp219 x = x + 15 := rfl
def bankOp220 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp220_spec (x : Nat) : bankOp220 x = x + 16 := rfl
def bankOp221 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp221_spec (x : Nat) : bankOp221 x = x + 0 := rfl
def bankOp222 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp222_spec (x : Nat) : bankOp222 x = x + 1 := rfl
def bankOp223 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp223_spec (x : Nat) : bankOp223 x = x + 2 := rfl
def bankOp224 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp224_spec (x : Nat) : bankOp224 x = x + 3 := rfl
def bankOp225 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp225_spec (x : Nat) : bankOp225 x = x + 4 := rfl
def bankOp226 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp226_spec (x : Nat) : bankOp226 x = x + 5 := rfl
def bankOp227 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp227_spec (x : Nat) : bankOp227 x = x + 6 := rfl
def bankOp228 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp228_spec (x : Nat) : bankOp228 x = x + 7 := rfl
def bankOp229 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp229_spec (x : Nat) : bankOp229 x = x + 8 := rfl
def bankOp230 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp230_spec (x : Nat) : bankOp230 x = x + 9 := rfl
def bankOp231 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp231_spec (x : Nat) : bankOp231 x = x + 10 := rfl
def bankOp232 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp232_spec (x : Nat) : bankOp232 x = x + 11 := rfl
def bankOp233 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp233_spec (x : Nat) : bankOp233 x = x + 12 := rfl
def bankOp234 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp234_spec (x : Nat) : bankOp234 x = x + 13 := rfl
def bankOp235 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp235_spec (x : Nat) : bankOp235 x = x + 14 := rfl
def bankOp236 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp236_spec (x : Nat) : bankOp236 x = x + 15 := rfl
def bankOp237 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp237_spec (x : Nat) : bankOp237 x = x + 16 := rfl
def bankOp238 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp238_spec (x : Nat) : bankOp238 x = x + 0 := rfl
def bankOp239 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp239_spec (x : Nat) : bankOp239 x = x + 1 := rfl
def bankOp240 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp240_spec (x : Nat) : bankOp240 x = x + 2 := rfl
def bankOp241 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp241_spec (x : Nat) : bankOp241 x = x + 3 := rfl
def bankOp242 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp242_spec (x : Nat) : bankOp242 x = x + 4 := rfl
def bankOp243 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp243_spec (x : Nat) : bankOp243 x = x + 5 := rfl
def bankOp244 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp244_spec (x : Nat) : bankOp244 x = x + 6 := rfl
def bankOp245 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp245_spec (x : Nat) : bankOp245 x = x + 7 := rfl
def bankOp246 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp246_spec (x : Nat) : bankOp246 x = x + 8 := rfl
def bankOp247 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp247_spec (x : Nat) : bankOp247 x = x + 9 := rfl
def bankOp248 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp248_spec (x : Nat) : bankOp248 x = x + 10 := rfl
def bankOp249 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp249_spec (x : Nat) : bankOp249 x = x + 11 := rfl
def bankOp250 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp250_spec (x : Nat) : bankOp250 x = x + 12 := rfl
def bankOp251 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp251_spec (x : Nat) : bankOp251 x = x + 13 := rfl
def bankOp252 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp252_spec (x : Nat) : bankOp252 x = x + 14 := rfl
def bankOp253 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp253_spec (x : Nat) : bankOp253 x = x + 15 := rfl
def bankOp254 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp254_spec (x : Nat) : bankOp254 x = x + 16 := rfl
def bankOp255 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp255_spec (x : Nat) : bankOp255 x = x + 0 := rfl
def bankOp256 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp256_spec (x : Nat) : bankOp256 x = x + 1 := rfl
def bankOp257 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp257_spec (x : Nat) : bankOp257 x = x + 2 := rfl
def bankOp258 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp258_spec (x : Nat) : bankOp258 x = x + 3 := rfl
def bankOp259 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp259_spec (x : Nat) : bankOp259 x = x + 4 := rfl
def bankOp260 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp260_spec (x : Nat) : bankOp260 x = x + 5 := rfl
def bankOp261 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp261_spec (x : Nat) : bankOp261 x = x + 6 := rfl
def bankOp262 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp262_spec (x : Nat) : bankOp262 x = x + 7 := rfl
def bankOp263 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp263_spec (x : Nat) : bankOp263 x = x + 8 := rfl
def bankOp264 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp264_spec (x : Nat) : bankOp264 x = x + 9 := rfl
def bankOp265 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp265_spec (x : Nat) : bankOp265 x = x + 10 := rfl
def bankOp266 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp266_spec (x : Nat) : bankOp266 x = x + 11 := rfl
def bankOp267 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp267_spec (x : Nat) : bankOp267 x = x + 12 := rfl
def bankOp268 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp268_spec (x : Nat) : bankOp268 x = x + 13 := rfl
def bankOp269 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp269_spec (x : Nat) : bankOp269 x = x + 14 := rfl
def bankOp270 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp270_spec (x : Nat) : bankOp270 x = x + 15 := rfl
def bankOp271 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp271_spec (x : Nat) : bankOp271 x = x + 16 := rfl
def bankOp272 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp272_spec (x : Nat) : bankOp272 x = x + 0 := rfl
def bankOp273 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp273_spec (x : Nat) : bankOp273 x = x + 1 := rfl
def bankOp274 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp274_spec (x : Nat) : bankOp274 x = x + 2 := rfl
def bankOp275 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp275_spec (x : Nat) : bankOp275 x = x + 3 := rfl
def bankOp276 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp276_spec (x : Nat) : bankOp276 x = x + 4 := rfl
def bankOp277 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp277_spec (x : Nat) : bankOp277 x = x + 5 := rfl
def bankOp278 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp278_spec (x : Nat) : bankOp278 x = x + 6 := rfl
def bankOp279 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp279_spec (x : Nat) : bankOp279 x = x + 7 := rfl
def bankOp280 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp280_spec (x : Nat) : bankOp280 x = x + 8 := rfl
def bankOp281 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp281_spec (x : Nat) : bankOp281 x = x + 9 := rfl
def bankOp282 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp282_spec (x : Nat) : bankOp282 x = x + 10 := rfl
def bankOp283 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp283_spec (x : Nat) : bankOp283 x = x + 11 := rfl
def bankOp284 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp284_spec (x : Nat) : bankOp284 x = x + 12 := rfl
def bankOp285 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp285_spec (x : Nat) : bankOp285 x = x + 13 := rfl
def bankOp286 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp286_spec (x : Nat) : bankOp286 x = x + 14 := rfl
def bankOp287 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp287_spec (x : Nat) : bankOp287 x = x + 15 := rfl
def bankOp288 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp288_spec (x : Nat) : bankOp288 x = x + 16 := rfl
def bankOp289 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp289_spec (x : Nat) : bankOp289 x = x + 0 := rfl
def bankOp290 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp290_spec (x : Nat) : bankOp290 x = x + 1 := rfl
def bankOp291 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp291_spec (x : Nat) : bankOp291 x = x + 2 := rfl
def bankOp292 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp292_spec (x : Nat) : bankOp292 x = x + 3 := rfl
def bankOp293 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp293_spec (x : Nat) : bankOp293 x = x + 4 := rfl
def bankOp294 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp294_spec (x : Nat) : bankOp294 x = x + 5 := rfl
def bankOp295 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp295_spec (x : Nat) : bankOp295 x = x + 6 := rfl
def bankOp296 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp296_spec (x : Nat) : bankOp296 x = x + 7 := rfl
def bankOp297 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp297_spec (x : Nat) : bankOp297 x = x + 8 := rfl
def bankOp298 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp298_spec (x : Nat) : bankOp298 x = x + 9 := rfl
def bankOp299 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp299_spec (x : Nat) : bankOp299 x = x + 10 := rfl
def bankOp300 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp300_spec (x : Nat) : bankOp300 x = x + 11 := rfl
def bankOp301 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp301_spec (x : Nat) : bankOp301 x = x + 12 := rfl
def bankOp302 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp302_spec (x : Nat) : bankOp302 x = x + 13 := rfl
def bankOp303 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp303_spec (x : Nat) : bankOp303 x = x + 14 := rfl
def bankOp304 (x : Nat) : Nat := x + 15
@[simp] theorem bankOp304_spec (x : Nat) : bankOp304 x = x + 15 := rfl
def bankOp305 (x : Nat) : Nat := x + 16
@[simp] theorem bankOp305_spec (x : Nat) : bankOp305 x = x + 16 := rfl
def bankOp306 (x : Nat) : Nat := x + 0
@[simp] theorem bankOp306_spec (x : Nat) : bankOp306 x = x + 0 := rfl
def bankOp307 (x : Nat) : Nat := x + 1
@[simp] theorem bankOp307_spec (x : Nat) : bankOp307 x = x + 1 := rfl
def bankOp308 (x : Nat) : Nat := x + 2
@[simp] theorem bankOp308_spec (x : Nat) : bankOp308 x = x + 2 := rfl
def bankOp309 (x : Nat) : Nat := x + 3
@[simp] theorem bankOp309_spec (x : Nat) : bankOp309 x = x + 3 := rfl
def bankOp310 (x : Nat) : Nat := x + 4
@[simp] theorem bankOp310_spec (x : Nat) : bankOp310 x = x + 4 := rfl
def bankOp311 (x : Nat) : Nat := x + 5
@[simp] theorem bankOp311_spec (x : Nat) : bankOp311 x = x + 5 := rfl
def bankOp312 (x : Nat) : Nat := x + 6
@[simp] theorem bankOp312_spec (x : Nat) : bankOp312 x = x + 6 := rfl
def bankOp313 (x : Nat) : Nat := x + 7
@[simp] theorem bankOp313_spec (x : Nat) : bankOp313 x = x + 7 := rfl
def bankOp314 (x : Nat) : Nat := x + 8
@[simp] theorem bankOp314_spec (x : Nat) : bankOp314 x = x + 8 := rfl
def bankOp315 (x : Nat) : Nat := x + 9
@[simp] theorem bankOp315_spec (x : Nat) : bankOp315 x = x + 9 := rfl
def bankOp316 (x : Nat) : Nat := x + 10
@[simp] theorem bankOp316_spec (x : Nat) : bankOp316 x = x + 10 := rfl
def bankOp317 (x : Nat) : Nat := x + 11
@[simp] theorem bankOp317_spec (x : Nat) : bankOp317 x = x + 11 := rfl
def bankOp318 (x : Nat) : Nat := x + 12
@[simp] theorem bankOp318_spec (x : Nat) : bankOp318 x = x + 12 := rfl
def bankOp319 (x : Nat) : Nat := x + 13
@[simp] theorem bankOp319_spec (x : Nat) : bankOp319 x = x + 13 := rfl
def bankOp320 (x : Nat) : Nat := x + 14
@[simp] theorem bankOp320_spec (x : Nat) : bankOp320 x = x + 14 := rfl
theorem s3_simp_chain_01 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp008 (bankOp019 (bankOp041 x))))) = x + 17 := by simp [Nat.add_assoc]
theorem s3_simp_chain_02 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp015 (bankOp032 (bankOp070 x))))) = x + 32 := by simp [Nat.add_assoc]
theorem s3_simp_chain_03 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp022 (bankOp045 (bankOp099 x))))) = x + 30 := by simp [Nat.add_assoc]
theorem s3_simp_chain_04 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp029 (bankOp058 (bankOp128 x))))) = x + 28 := by simp [Nat.add_assoc]
theorem s3_simp_chain_05 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp036 (bankOp071 (bankOp157 x))))) = x + 9 := by simp [Nat.add_assoc]
theorem s3_simp_chain_06 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp043 (bankOp084 (bankOp186 x))))) = x + 41 := by simp [Nat.add_assoc]
theorem s3_simp_chain_07 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp050 (bankOp097 (bankOp215 x))))) = x + 39 := by simp [Nat.add_assoc]
theorem s3_simp_chain_08 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp057 (bankOp110 (bankOp244 x))))) = x + 20 := by simp [Nat.add_assoc]
theorem s3_simp_chain_09 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp064 (bankOp123 (bankOp273 x))))) = x + 18 := by simp [Nat.add_assoc]
theorem s3_simp_chain_10 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp071 (bankOp136 (bankOp302 x))))) = x + 16 := by simp [Nat.add_assoc]
theorem s3_simp_chain_11 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp078 (bankOp149 (bankOp011 x))))) = x + 34 := by simp [Nat.add_assoc]
theorem s3_simp_chain_12 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp085 (bankOp162 (bankOp040 x))))) = x + 15 := by simp [Nat.add_assoc]
theorem s3_simp_chain_13 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp092 (bankOp175 (bankOp069 x))))) = x + 13 := by simp [Nat.add_assoc]
theorem s3_simp_chain_14 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp099 (bankOp188 (bankOp098 x))))) = x + 28 := by simp [Nat.add_assoc]
theorem s3_simp_chain_15 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp106 (bankOp201 (bankOp127 x))))) = x + 26 := by simp [Nat.add_assoc]
theorem s3_simp_chain_16 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp113 (bankOp214 (bankOp156 x))))) = x + 24 := by simp [Nat.add_assoc]
theorem s3_simp_chain_17 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp120 (bankOp227 (bankOp185 x))))) = x + 22 := by simp [Nat.add_assoc]
theorem s3_simp_chain_18 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp127 (bankOp240 (bankOp214 x))))) = x + 20 := by simp [Nat.add_assoc]
theorem s3_simp_chain_19 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp134 (bankOp253 (bankOp243 x))))) = x + 35 := by simp [Nat.add_assoc]
theorem s3_simp_chain_20 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp141 (bankOp266 (bankOp272 x))))) = x + 16 := by simp [Nat.add_assoc]
theorem s3_simp_chain_21 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp148 (bankOp279 (bankOp301 x))))) = x + 31 := by simp [Nat.add_assoc]
theorem s3_simp_chain_22 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp155 (bankOp292 (bankOp010 x))))) = x + 15 := by simp [Nat.add_assoc]
theorem s3_simp_chain_23 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp162 (bankOp305 (bankOp039 x))))) = x + 30 := by simp [Nat.add_assoc]
theorem s3_simp_chain_24 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp169 (bankOp318 (bankOp068 x))))) = x + 28 := by simp [Nat.add_assoc]
theorem s3_simp_chain_25 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp176 (bankOp011 (bankOp097 x))))) = x + 29 := by simp [Nat.add_assoc]
theorem s3_simp_chain_26 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp183 (bankOp024 (bankOp126 x))))) = x + 27 := by simp [Nat.add_assoc]
theorem s3_simp_chain_27 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp190 (bankOp037 (bankOp155 x))))) = x + 8 := by simp [Nat.add_assoc]
theorem s3_simp_chain_28 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp197 (bankOp050 (bankOp184 x))))) = x + 40 := by simp [Nat.add_assoc]
theorem s3_simp_chain_29 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp204 (bankOp063 (bankOp213 x))))) = x + 21 := by simp [Nat.add_assoc]
theorem s3_simp_chain_30 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp211 (bankOp076 (bankOp242 x))))) = x + 19 := by simp [Nat.add_assoc]
theorem s3_simp_chain_31 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp218 (bankOp089 (bankOp271 x))))) = x + 34 := by simp [Nat.add_assoc]
theorem s3_simp_chain_32 (x : Nat) : wrapId (tagAdd0 0 (tagMul1 1 (bankOp225 (bankOp102 (bankOp300 x))))) = x + 15 := by simp [Nat.add_assoc]

end SyntheticBench.S3
