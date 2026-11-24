-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvWComp
public import Kernels.InklingRelDecode.Proof.Thread.EvWLoaderSpec

/-! # The event shapes of the Inkling loader and MMA warps: umbrella

`EvWBar` (the twelve mbarriers as shared locations), `EvWBase` (what the event of a poll, an
arrival, a tensor load, a shared or global load, a barrier or an election is, from the registers
its instruction reads), `EvWTc` (commits, MMAs and the warp-index broadcast), `EvWLoader`
(`LdShape` and `ld_shape`: the event of each loader state), `EvWMma` (`MmShape` and `mm_shape`:
the event of each MMA state) and `EvWComp` (the same on the states of `WComp.code`:
`loader_shape`, `mma_shape`, and the invariant `ProMeans` of the reachable states) and
`EvWLoaderSpec` (the origin of a copy and the address of a block-table load in `Spec`'s
quantities). -/
