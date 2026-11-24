-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.BarAll
public import Kernels.InklingRelDecode.Proof.Protocol.MbarAll
public import Kernels.InklingRelDecode.Proof.Protocol.KvAll
public import Kernels.InklingRelDecode.Proof.Protocol.TmemAll
public import Kernels.InklingRelDecode.Proof.Protocol.SrAll
public import Kernels.InklingRelDecode.Proof.Protocol.BarLaneAll
public import Kernels.InklingRelDecode.Proof.Protocol.Ring
public import Kernels.InklingRelDecode.Proof.Protocol.RingCommit
public import Kernels.InklingRelDecode.Proof.Protocol.RingCount
public import Kernels.InklingRelDecode.Proof.Protocol.RingExec
public import Kernels.InklingRelDecode.Proof.Protocol.RingKvFoot
public import Kernels.InklingRelDecode.Proof.Protocol.RingKvMma
public import Kernels.InklingRelDecode.Proof.Protocol.RingKvPreload
public import Kernels.InklingRelDecode.Proof.Protocol.RingKvSlot
public import Kernels.InklingRelDecode.Proof.Protocol.RingLoader
public import Kernels.InklingRelDecode.Proof.Protocol.RingLoaderCount
public import Kernels.InklingRelDecode.Proof.Protocol.RingLoaderExec
public import Kernels.InklingRelDecode.Proof.Protocol.RingMma
public import Kernels.InklingRelDecode.Proof.Protocol.RingSched
public import Kernels.InklingRelDecode.Proof.Protocol.SO
public import Kernels.InklingRelDecode.Proof.Protocol.SOEpi
public import Kernels.InklingRelDecode.Proof.Protocol.SOHandoff
public import Kernels.InklingRelDecode.Proof.Protocol.SOHyp
public import Kernels.InklingRelDecode.Proof.Protocol.SOMmaCount
public import Kernels.InklingRelDecode.Proof.Protocol.SOMmaEvents
public import Kernels.InklingRelDecode.Proof.Protocol.SOMmaExec
public import Kernels.InklingRelDecode.Proof.Protocol.SOMmaRun
public import Kernels.InklingRelDecode.Proof.Protocol.SOOdone
public import Kernels.InklingRelDecode.Proof.Protocol.SOParity
public import Kernels.InklingRelDecode.Proof.Protocol.SOSched
public import Kernels.InklingRelDecode.Proof.Protocol.SOSites
public import Kernels.InklingRelDecode.Proof.Protocol.SOSmCount
public import Kernels.InklingRelDecode.Proof.Protocol.SOSmEvents
public import Kernels.InklingRelDecode.Proof.Protocol.SOSmExec
public import Kernels.InklingRelDecode.Proof.Protocol.SOSmOdone
public import Kernels.InklingRelDecode.Proof.Protocol.SOSmRun
public import Kernels.InklingRelDecode.Proof.Protocol.SOTmemCols
public import Kernels.InklingRelDecode.Proof.Protocol.SOTmemLife
public import Kernels.InklingRelDecode.Proof.Protocol.SOTmemOrder

/-! # The Inkling protocol layer: umbrella

`Ring` (the design note of the KV ring protocol and the phase statements of the polls),
`RingSched` (the ring's schedule and parity arithmetic), `RingCount` (counting events along a
machine run), `RingLoader` and `RingMma` (the loader's `kv_empty` polls and the MMA warp's
`kv_ready` polls along their runs), `RingExec` (the same on an execution through the worker
thread frame), `RingCommit` (the MMA warp's PV commits to `kv_empty`), `RingLoaderCount` and
`RingLoaderExec` (the loader's arrivals and copies on `kv_ready`, along a run and on an
execution).

The one-CTA TMA ring slot: `RingKvSlot` (the hypothesis structure `Kv.Hyp`), `Lib.KvSingle` (the
conversion to the library's single-CTA ring, and its results at the KV slot: the items and the
exact phases of the designated pollers through `MbarRing.Items.Ring`, the phase every poll
finds, RAW and WAR between the slot's copies and the MMA lane's reads, fault freedom),
`RingKvFoot` (the bytes of the copies and of the MMA operands), `RingKvMma` (the MMA lane's reads
of block `i` and its commit gate, on an execution), `RingKvPreload` (what the default partition
has to supply).

The S/P/O handshake and the Tensor Memory lifetime (design note in `SO`): `SOSched` (double-buffer
arithmetic), `SOSites` (the program's polls, arrivals and commits by site), the MMA warp's counts
(`SOMmaCount`, `SOMmaEvents`, `SOMmaRun`, `SOMmaExec`), the default partition's
(`SOSmCount`, `SOSmEvents`, `SOSmRun`, `SOSmExec`, `SOSmOdone`, `SOEpi`), the `o_done` phase
(`SOOdone`), the objects and handoffs (`SOHyp`,
`SOHandoff`), and Tensor Memory (`SOTmemCols`, `SOTmemOrder`, `SOTmemLife`). -/
