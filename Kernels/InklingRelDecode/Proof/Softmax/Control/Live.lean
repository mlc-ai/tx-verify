-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Flow.Sites

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control

/-- The guards of observable instructions, the block/slot counters and the addresses
of the bias loads, TMEM operations, scratch word and barriers. The final poll also
carries the integer address inputs of the epilogue. Registers 1542 to 1544 carry the
scratch word read at pc 2252, the word its xor-2 neighbour sent and their minimum, the
sent word of shuffle 2255. The other float minima and the 64 score words require no
site facts. -/
def ctl (r : Nat) : Bool :=
  r ∈ [3,169,175,177,478,481,483,527,610,666,1532,1533,1534,1536,1538,1540,1542,1543,1544,1611,
    1676,1709,1760,
    1993,2019,2446,2511,2608] ||
  [(85,95),(171,173),(327,331),(462,464),(485,487),(490,491),(496,497),(500,506),
   (532,533),(623,624),(792,798),(801,803),(806,809),(874,875),(940,945),(1912,1913),
   (1956,1959),(2023,2024),(2141,2204),(2206,2274)].any fun (lo,hi) => lo ≤ r && r ≤ hi

noncomputable def ctlLive (pc : Nat) : List Nat := (Flow.live pc).filter ctl

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
