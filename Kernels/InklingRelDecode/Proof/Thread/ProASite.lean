-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProADefs

@[expose] public section

/-! # The event instructions of the default partition's prologue

The 185 sites of pc 27 to 573: every event instruction of the `Flow.Sites` of that region
(157 of them), with the elements of a vector store told apart (the four `st.shared.v4.b32`
elements of each of the eight stores, and the two of the `st.shared.v2.b32`: one event each). -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section


inductive Site where
  /-- `setmaxnreg.inc` (pc 27). -/
  | sMax
  /-- `cu_seqlens_q[req]` (pc 34). -/
  | ldCu0
  /-- `cu_seqlens_q[req + 1]` (pc 37). -/
  | ldCu1
  /-- `seq_lens[req]` (pc 41). -/
  | ldSk
  | el0
  | in0
  | el1
  | in1
  | el2
  | in2
  | el3
  | in3
  | el4
  | in4
  | el5
  | in5
  | el6
  | in6
  | el7
  | in7
  | el8
  | in8
  | el9
  | in9
  | el10
  | in10
  | el11
  | in11
  /-- `fence.proxy.async` after the mbarrier initializations (pc 179). -/
  | fnc0
  /-- The partition's barrier `bar.sync 0, 128` (pc 180). -/
  | bar2
  | pbA0
  | arr0
  | lbA0
  | pbB0
  | psh0
  | pel0_0
  | ptc0_0
  | pbC0
  | pel0_1
  | ptc0_1
  | lbB0
  | pbD0
  | pel0_2
  | ptc0_2
  | pbE0
  | pel0_3
  | ptc0_3
  | pbA1
  | arr1
  | lbA1
  | pbB1
  | psh1
  | pel1_0
  | ptc1_0
  | pbC1
  | pel1_1
  | ptc1_1
  | lbB1
  | pbD1
  | pel1_2
  | ptc1_2
  | pbE1
  | pel1_3
  | ptc1_3
  | pbA2
  | arr2
  | lbA2
  | pbB2
  | psh2
  | pel2_0
  | ptc2_0
  | pbC2
  | pel2_1
  | ptc2_1
  | lbB2
  | pbD2
  | pel2_2
  | ptc2_2
  | pbE2
  | pel2_3
  | ptc2_3
  | ldq0
  | ldq1
  | ldq2
  | ldq3
  | ldq4
  | ldq5
  | ldq6
  | ldq7
  | ldq8
  | ldq9
  | ldq10
  | ldq11
  | ldq12
  | ldq13
  | ldq14
  | ldq15
  | ldq16
  | ldq17
  | ldq18
  | ldq19
  | ldq20
  | ldq21
  | ldq22
  | ldq23
  | ldq24
  | ldq25
  | ldq26
  | ldq27
  | ldq28
  | ldq29
  | ldq30
  | ldq31
  | ldq32
  | ldq33
  | ldq34
  | ldq35
  | ldq36
  | ldq37
  | ldq38
  | ldq39
  | ldq40
  | ldq41
  | ldq42
  | ldq43
  | ldq44
  | ldq45
  | ldq46
  | ldq47
  | ldq48
  | ldq49
  | ldq50
  | ldq51
  | ldq52
  | ldq53
  | ldq54
  | ldq55
  | ldq56
  | ldq57
  | ldq58
  | ldq59
  | ldq60
  | ldq61
  | ldq62
  | ldq63
  | stq0_0
  | stq0_1
  | stq0_2
  | stq0_3
  | stq1_0
  | stq1_1
  | stq1_2
  | stq1_3
  | stq2_0
  | stq2_1
  | stq2_2
  | stq2_3
  | stq3_0
  | stq3_1
  | stq3_2
  | stq3_3
  | stq4_0
  | stq4_1
  | stq4_2
  | stq4_3
  | stq5_0
  | stq5_1
  | stq5_2
  | stq5_3
  | stq6_0
  | stq6_1
  | stq6_2
  | stq6_3
  | stq7_0
  | stq7_1
  | stq7_2
  | stq7_3
  /-- `fence.proxy.async` after the Q stores (pc 569). -/
  | fnc1
  /-- The role table store (pc 570). -/
  | st8
  /-- Element 0 of the `(num_pre, num_iters)` store (pc 571). -/
  | st9_0
  /-- Element 1 of the `(num_pre, num_iters)` store (pc 571). -/
  | st9_1
  /-- `barrier.sync 1` (pc 573), the last event of the region. -/
  | bar18
  deriving DecidableEq, Repr

/-- The program counter of a site. -/
def Site.pc : Site → Nat
  | .sMax => Flow.setMaxReg_0
  | .ldCu0 => Flow.load_1
  | .ldCu1 => Flow.load_2
  | .ldSk => Flow.load_3
  | .el0 => Flow.elect_0
  | .in0 => Flow.mbarInit_0
  | .el1 => Flow.elect_1
  | .in1 => Flow.mbarInit_1
  | .el2 => Flow.elect_2
  | .in2 => Flow.mbarInit_2
  | .el3 => Flow.elect_3
  | .in3 => Flow.mbarInit_3
  | .el4 => Flow.elect_4
  | .in4 => Flow.mbarInit_4
  | .el5 => Flow.elect_5
  | .in5 => Flow.mbarInit_5
  | .el6 => Flow.elect_6
  | .in6 => Flow.mbarInit_6
  | .el7 => Flow.elect_7
  | .in7 => Flow.mbarInit_7
  | .el8 => Flow.elect_8
  | .in8 => Flow.mbarInit_8
  | .el9 => Flow.elect_9
  | .in9 => Flow.mbarInit_9
  | .el10 => Flow.elect_10
  | .in10 => Flow.mbarInit_10
  | .el11 => Flow.elect_11
  | .in11 => Flow.mbarInit_11
  | .fnc0 => Flow.fenceProxy_0
  | .bar2 => Flow.bar_2
  | .pbA0 => Flow.bar_3
  | .arr0 => Flow.mbarArrive_0
  | .lbA0 => Flow.load_4
  | .pbB0 => Flow.bar_4
  | .psh0 => Flow.shfl_1
  | .pel0_0 => Flow.elect_12
  | .ptc0_0 => Flow.tensorCopy_0
  | .pbC0 => Flow.bar_5
  | .pel0_1 => Flow.elect_13
  | .ptc0_1 => Flow.tensorCopy_1
  | .lbB0 => Flow.load_5
  | .pbD0 => Flow.bar_6
  | .pel0_2 => Flow.elect_14
  | .ptc0_2 => Flow.tensorCopy_2
  | .pbE0 => Flow.bar_7
  | .pel0_3 => Flow.elect_15
  | .ptc0_3 => Flow.tensorCopy_3
  | .pbA1 => Flow.bar_8
  | .arr1 => Flow.mbarArrive_1
  | .lbA1 => Flow.load_6
  | .pbB1 => Flow.bar_9
  | .psh1 => Flow.shfl_2
  | .pel1_0 => Flow.elect_16
  | .ptc1_0 => Flow.tensorCopy_4
  | .pbC1 => Flow.bar_10
  | .pel1_1 => Flow.elect_17
  | .ptc1_1 => Flow.tensorCopy_5
  | .lbB1 => Flow.load_7
  | .pbD1 => Flow.bar_11
  | .pel1_2 => Flow.elect_18
  | .ptc1_2 => Flow.tensorCopy_6
  | .pbE1 => Flow.bar_12
  | .pel1_3 => Flow.elect_19
  | .ptc1_3 => Flow.tensorCopy_7
  | .pbA2 => Flow.bar_13
  | .arr2 => Flow.mbarArrive_2
  | .lbA2 => Flow.load_8
  | .pbB2 => Flow.bar_14
  | .psh2 => Flow.shfl_3
  | .pel2_0 => Flow.elect_20
  | .ptc2_0 => Flow.tensorCopy_8
  | .pbC2 => Flow.bar_15
  | .pel2_1 => Flow.elect_21
  | .ptc2_1 => Flow.tensorCopy_9
  | .lbB2 => Flow.load_9
  | .pbD2 => Flow.bar_16
  | .pel2_2 => Flow.elect_22
  | .ptc2_2 => Flow.tensorCopy_10
  | .pbE2 => Flow.bar_17
  | .pel2_3 => Flow.elect_23
  | .ptc2_3 => Flow.tensorCopy_11
  | .ldq0 => Flow.load_10
  | .ldq1 => Flow.load_11
  | .ldq2 => Flow.load_12
  | .ldq3 => Flow.load_13
  | .ldq4 => Flow.load_14
  | .ldq5 => Flow.load_15
  | .ldq6 => Flow.load_16
  | .ldq7 => Flow.load_17
  | .ldq8 => Flow.load_18
  | .ldq9 => Flow.load_19
  | .ldq10 => Flow.load_20
  | .ldq11 => Flow.load_21
  | .ldq12 => Flow.load_22
  | .ldq13 => Flow.load_23
  | .ldq14 => Flow.load_24
  | .ldq15 => Flow.load_25
  | .ldq16 => Flow.load_26
  | .ldq17 => Flow.load_27
  | .ldq18 => Flow.load_28
  | .ldq19 => Flow.load_29
  | .ldq20 => Flow.load_30
  | .ldq21 => Flow.load_31
  | .ldq22 => Flow.load_32
  | .ldq23 => Flow.load_33
  | .ldq24 => Flow.load_34
  | .ldq25 => Flow.load_35
  | .ldq26 => Flow.load_36
  | .ldq27 => Flow.load_37
  | .ldq28 => Flow.load_38
  | .ldq29 => Flow.load_39
  | .ldq30 => Flow.load_40
  | .ldq31 => Flow.load_41
  | .ldq32 => Flow.load_42
  | .ldq33 => Flow.load_43
  | .ldq34 => Flow.load_44
  | .ldq35 => Flow.load_45
  | .ldq36 => Flow.load_46
  | .ldq37 => Flow.load_47
  | .ldq38 => Flow.load_48
  | .ldq39 => Flow.load_49
  | .ldq40 => Flow.load_50
  | .ldq41 => Flow.load_51
  | .ldq42 => Flow.load_52
  | .ldq43 => Flow.load_53
  | .ldq44 => Flow.load_54
  | .ldq45 => Flow.load_55
  | .ldq46 => Flow.load_56
  | .ldq47 => Flow.load_57
  | .ldq48 => Flow.load_58
  | .ldq49 => Flow.load_59
  | .ldq50 => Flow.load_60
  | .ldq51 => Flow.load_61
  | .ldq52 => Flow.load_62
  | .ldq53 => Flow.load_63
  | .ldq54 => Flow.load_64
  | .ldq55 => Flow.load_65
  | .ldq56 => Flow.load_66
  | .ldq57 => Flow.load_67
  | .ldq58 => Flow.load_68
  | .ldq59 => Flow.load_69
  | .ldq60 => Flow.load_70
  | .ldq61 => Flow.load_71
  | .ldq62 => Flow.load_72
  | .ldq63 => Flow.load_73
  | .stq0_0 => Flow.store_0
  | .stq0_1 => Flow.store_0
  | .stq0_2 => Flow.store_0
  | .stq0_3 => Flow.store_0
  | .stq1_0 => Flow.store_1
  | .stq1_1 => Flow.store_1
  | .stq1_2 => Flow.store_1
  | .stq1_3 => Flow.store_1
  | .stq2_0 => Flow.store_2
  | .stq2_1 => Flow.store_2
  | .stq2_2 => Flow.store_2
  | .stq2_3 => Flow.store_2
  | .stq3_0 => Flow.store_3
  | .stq3_1 => Flow.store_3
  | .stq3_2 => Flow.store_3
  | .stq3_3 => Flow.store_3
  | .stq4_0 => Flow.store_4
  | .stq4_1 => Flow.store_4
  | .stq4_2 => Flow.store_4
  | .stq4_3 => Flow.store_4
  | .stq5_0 => Flow.store_5
  | .stq5_1 => Flow.store_5
  | .stq5_2 => Flow.store_5
  | .stq5_3 => Flow.store_5
  | .stq6_0 => Flow.store_6
  | .stq6_1 => Flow.store_6
  | .stq6_2 => Flow.store_6
  | .stq6_3 => Flow.store_6
  | .stq7_0 => Flow.store_7
  | .stq7_1 => Flow.store_7
  | .stq7_2 => Flow.store_7
  | .stq7_3 => Flow.store_7
  | .fnc1 => Flow.fenceProxy_1
  | .st8 => Flow.store_8
  | .st9_0 => Flow.store_9
  | .st9_1 => Flow.store_9
  | .bar18 => Flow.bar_18

/-- The element of a vector store at a site (`sub`), zero elsewhere. -/
def Site.sub : Site → Nat
  | .stq0_1 => 1
  | .stq0_2 => 2
  | .stq0_3 => 3
  | .stq1_1 => 1
  | .stq1_2 => 2
  | .stq1_3 => 3
  | .stq2_1 => 1
  | .stq2_2 => 2
  | .stq2_3 => 3
  | .stq3_1 => 1
  | .stq3_2 => 2
  | .stq3_3 => 3
  | .stq4_1 => 1
  | .stq4_2 => 2
  | .stq4_3 => 3
  | .stq5_1 => 1
  | .stq5_2 => 2
  | .stq5_3 => 3
  | .stq6_1 => 1
  | .stq6_2 => 2
  | .stq6_3 => 3
  | .stq7_1 => 1
  | .stq7_2 => 2
  | .stq7_3 => 3
  | .st9_1 => 1
  | _ => 0

/-- The sites after the third load (`seq_lens`): the request's words are loaded. -/
def Site.afterSk : Site → Bool
  | .sMax | .ldCu0 | .ldCu1 | .ldSk => false
  | _ => true

/-- The index of the next query load: the sites before the loads are at 0, the sites after
them at 64. -/
def Site.qIdx : Site → Nat
  | .ldq0 => 0
  | .ldq1 => 1
  | .ldq2 => 2
  | .ldq3 => 3
  | .ldq4 => 4
  | .ldq5 => 5
  | .ldq6 => 6
  | .ldq7 => 7
  | .ldq8 => 8
  | .ldq9 => 9
  | .ldq10 => 10
  | .ldq11 => 11
  | .ldq12 => 12
  | .ldq13 => 13
  | .ldq14 => 14
  | .ldq15 => 15
  | .ldq16 => 16
  | .ldq17 => 17
  | .ldq18 => 18
  | .ldq19 => 19
  | .ldq20 => 20
  | .ldq21 => 21
  | .ldq22 => 22
  | .ldq23 => 23
  | .ldq24 => 24
  | .ldq25 => 25
  | .ldq26 => 26
  | .ldq27 => 27
  | .ldq28 => 28
  | .ldq29 => 29
  | .ldq30 => 30
  | .ldq31 => 31
  | .ldq32 => 32
  | .ldq33 => 33
  | .ldq34 => 34
  | .ldq35 => 35
  | .ldq36 => 36
  | .ldq37 => 37
  | .ldq38 => 38
  | .ldq39 => 39
  | .ldq40 => 40
  | .ldq41 => 41
  | .ldq42 => 42
  | .ldq43 => 43
  | .ldq44 => 44
  | .ldq45 => 45
  | .ldq46 => 46
  | .ldq47 => 47
  | .ldq48 => 48
  | .ldq49 => 49
  | .ldq50 => 50
  | .ldq51 => 51
  | .ldq52 => 52
  | .ldq53 => 53
  | .ldq54 => 54
  | .ldq55 => 55
  | .ldq56 => 56
  | .ldq57 => 57
  | .ldq58 => 58
  | .ldq59 => 59
  | .ldq60 => 60
  | .ldq61 => 61
  | .ldq62 => 62
  | .ldq63 => 63
  | .stq0_0
    | .stq0_1
    | .stq0_2
    | .stq0_3
    | .stq1_0
    | .stq1_1
    | .stq1_2
    | .stq1_3
    | .stq2_0
    | .stq2_1
    | .stq2_2
    | .stq2_3
    | .stq3_0
    | .stq3_1
    | .stq3_2
    | .stq3_3
    | .stq4_0
    | .stq4_1
    | .stq4_2
    | .stq4_3
    | .stq5_0
    | .stq5_1
    | .stq5_2
    | .stq5_3
    | .stq6_0
    | .stq6_1
    | .stq6_2
    | .stq6_3
    | .stq7_0
    | .stq7_1
    | .stq7_2
    | .stq7_3
    | .fnc1
    | .st8
    | .st9_0
    | .st9_1
    | .bar18 => 64
  | _ => 0

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
