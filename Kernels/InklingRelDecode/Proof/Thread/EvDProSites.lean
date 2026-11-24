-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvDProBase

@[expose] public section

/-!
# The prologue's sites, indexed by function

`ProA.Site` has one constructor per event instruction. The shape theorems are uniform over a family
of sites that play the same role, so this file indexes the families:

* `elSite i` (`i < 24`): the elections, `el 0 … 11` before the mbarrier initializations, then
  the twelve elections of the K/V copies (`pel b c`, block `b`, copy `c`: `i = 12 + 4 b + c`);
* `inSite i` (`i < 12`): the mbarrier initializations, in the order of `EvD.initBar`;
* `arrSite j` (`j < 3`): the `expect_tx` arrivals of block `j`;
* `lbSite i` (`i < 6`): the block-table loads, block `i / 2`, slab `i % 2`;
* `ptcSite i` (`i < 12`): the copies, block `i / 4`; per block K slab 0, V slab 0, K slab 1,
  V slab 1 (`i % 4`);
* `ldqSite k` (`k < 64`): the query loads, in program order;
* `stqSite i` (`i < 32`): element `i % 4` of the `i / 4`-th `st.shared.v4.b32` of the packed Q.

All are plain lists of constructors; `evPc` of a site is its pc, and the prologue's role table and
`(num_pre, num_iters)` write are the sites `st8`, `st9_0`, `st9_1`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The elections: before the initializations, then before each K/V copy. -/
def elSites : List Site :=
  [.el0, .el1, .el2, .el3, .el4, .el5,
    .el6, .el7, .el8, .el9, .el10, .el11,
    .pel0_0, .pel0_1, .pel0_2, .pel0_3, .pel1_0, .pel1_1,
    .pel1_2, .pel1_3, .pel2_0, .pel2_1, .pel2_2, .pel2_3]

def elSite (i : Nat) : Site := elSites.getD i .el0

/-- The mbarrier initializations. -/
def inSites : List Site :=
  [.in0, .in1, .in2, .in3, .in4, .in5,
    .in6, .in7, .in8, .in9, .in10, .in11]

def inSite (i : Nat) : Site := inSites.getD i .in0

/-- The `expect_tx` arrivals. -/
def arrSites : List Site :=
  [.arr0, .arr1, .arr2]

def arrSite (i : Nat) : Site := arrSites.getD i .arr0

/-- The block-table loads: block `i / 2`, slab `i % 2`. -/
def lbSites : List Site :=
  [.lbA0, .lbB0, .lbA1, .lbB1, .lbA2, .lbB2]

def lbSite (i : Nat) : Site := lbSites.getD i .lbA0

/-- The K/V copies: block `i / 4`, copy `i % 4`. -/
def ptcSites : List Site :=
  [.ptc0_0, .ptc0_1, .ptc0_2, .ptc0_3, .ptc1_0, .ptc1_1,
    .ptc1_2, .ptc1_3, .ptc2_0, .ptc2_1, .ptc2_2, .ptc2_3]

def ptcSite (i : Nat) : Site := ptcSites.getD i .ptc0_0

/-- The query loads in program order. -/
def ldqSites : List Site :=
  [.ldq0, .ldq1, .ldq2, .ldq3, .ldq4, .ldq5,
    .ldq6, .ldq7, .ldq8, .ldq9, .ldq10, .ldq11,
    .ldq12, .ldq13, .ldq14, .ldq15, .ldq16, .ldq17,
    .ldq18, .ldq19, .ldq20, .ldq21, .ldq22, .ldq23,
    .ldq24, .ldq25, .ldq26, .ldq27, .ldq28, .ldq29,
    .ldq30, .ldq31, .ldq32, .ldq33, .ldq34, .ldq35,
    .ldq36, .ldq37, .ldq38, .ldq39, .ldq40, .ldq41,
    .ldq42, .ldq43, .ldq44, .ldq45, .ldq46, .ldq47,
    .ldq48, .ldq49, .ldq50, .ldq51, .ldq52, .ldq53,
    .ldq54, .ldq55, .ldq56, .ldq57, .ldq58, .ldq59,
    .ldq60, .ldq61, .ldq62, .ldq63]

def ldqSite (i : Nat) : Site := ldqSites.getD i .ldq0

theorem ldqSites_length : ldqSites.length = 64 := by decide

/-- The elements of the packed Q stores (index `4 m + w`). -/
def stqSites : List Site :=
  [.stq0_0, .stq0_1, .stq0_2, .stq0_3, .stq1_0, .stq1_1,
    .stq1_2, .stq1_3, .stq2_0, .stq2_1, .stq2_2, .stq2_3,
    .stq3_0, .stq3_1, .stq3_2, .stq3_3, .stq4_0, .stq4_1,
    .stq4_2, .stq4_3, .stq5_0, .stq5_1, .stq5_2, .stq5_3,
    .stq6_0, .stq6_1, .stq6_2, .stq6_3, .stq7_0, .stq7_1,
    .stq7_2, .stq7_3]

def stqSite (i : Nat) : Site := stqSites.getD i .stq0_0

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
