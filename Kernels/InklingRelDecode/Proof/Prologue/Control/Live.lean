-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Flow.Sites

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control

def copyReg (r : Nat) : Bool :=
  682≤r && r≤740 && r ∈ [682,685,688,690,693,695,696,702,705,708,710,714,716,717,718,
    724,727,730,732,736,738,739,740]

/-- Keep request addresses and words, the guards, mbarrier operands, tensor map and
the live scalars handed to Softmax. Query payloads and their packed store operands
have no effect on the control path or on an mbarrier use. -/
def ctl (r : Nat) : Bool :=
  copyReg r || r ∈ [3,177,199,490,491,492,493,526,527,528,532,533,666,
    746,751,756,761,766,771,776,781,791,792,1912,1949,2018,2019,2020,2021,2022,2023,2024] ||
  [(26,84),(182,197),(462,464),(478,489),(649,664),(1951,1954),(610,639),(641,648),(678,680),
    (2055,2058),(2059,2070),(691,692),(711,713),(733,735),(1955,1955),(2071,2076),
    (2077,2140),(2205,2205)].any fun (lo,hi) => lo ≤ r && r ≤ hi

noncomputable def ctlLive (pc : Nat) : List Nat := (Flow.live pc).filter ctl

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
