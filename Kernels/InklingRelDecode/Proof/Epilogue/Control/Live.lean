-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Flow.Sites

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control

/-- The float payloads affect neither the store guards nor the mbarrier row. The O load
address, allocation word and final barrier remain live, and so do the registers the store
addresses are computed from and the addresses themselves. -/
def ctl (r : Nat) : Bool :=
  r ∈ [3,173,174,175,176,462,463,464,478,491,496,497,533,610,624,1760,1827,1828,1829,1830,
    1896,1897,1898,1899,1900,1956,2023,2024,2379,2444,2445] || (2380 ≤ r && r ≤ 2443)

noncomputable def ctlLive (pc : Nat) := (Flow.live pc).filter ctl

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
