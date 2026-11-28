-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Next
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.LagTma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Lag
public import Lemmas.Kernel.Progress.Blocked
public import Lemmas.Step.StoreDone
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Bar9

@[expose] public section

/-! # The progress classes

An open obligation of a maximal, followed execution of a safe launch (`Descent.Obl`) is of one
class, by the next event of a lane (never by its state):

* a pending released lane that steps or whose next event is a failed poll (`next_cls`, from the
  roles' rows `NextRow.Next`, proved: `Prog.nextRow`);
* a failed poll at one of the sixteen `mbarrier` waits (`poll_pcs`), grouped by channel:
  `qTma` (1931, proved: `Prog/QTmaPoll.lean`), the MMA lane's `qUtccp` (1983, proved:
  `Prog/QUtccpPoll.lean`), `dequantReady` (2012, proved: `Prog/DequantReadyPoll.lean`),
  `close` (2209, proved: `Prog/ClosePoll.lean`), the other `qUtccp` waiters (2205, 2644),
  `coord` (ready waits 264, 2234, proved: `Prog/CoordReadyPoll.lean`; free waits 2446, 2534),
  `qkDone` (272, proved: `Prog/QkDonePoll.lean`), `svDone` (1184, 2684, proved:
  `Prog/SvDonePoll.lean`), `soReady` (2107, proved: `Prog/SoReadyPoll.lean`), the raw ring's
  free wait (2245, proved: `Prog/RawFreePoll.lean`) and ready wait (2677, proved:
  `Prog/RawReadyPoll.lean`) (`Prog.PollSteps`);
* a pending lane that is not released: it is blocked by its last event (`Prog.BlockedSteps`;
  proved: `Prog/Blocked.lean`);
* the asynchronous items: the tensor loads (`tensor`), the `tcgen05.mma`/`cp` completions and
  their commits (`tc`, proved: `Prog/Tc.lean`), the tensor stores' drain (`store`, proved from
  the stores' publication
  `Prog.StorePub`, from warpgroup 0's output facts `Prog.outRows`: `Prog/Store.lean`), the
  tensor memory's release (`tmem`, proved: `Prog/Tmem.lean`),
  and the bulk copies, asynchronous arrivals and cluster launch control (`other`, proved:
  `Prog/Other.lean`) (`Prog.AsyncSteps`).

Every class is proved; the inputs of the classes are the premise `Top.Inputs`
(`Top/Inputs.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

/-- The `qTma` wait. -/
def Prog.qTmaSites : List Nat := [1931]
/-- The MMA lane's `qUtccp` wait. -/
def Prog.qUtccpMmaSites : List Nat := [1983]

/-- The other `qUtccp` waits: the TMA lane's and the dequant lanes'. -/
def Prog.qUtccpSites : List Nat := [2205, 2644]
/-- The coordination ring's waits. -/
def Prog.coordSites : List Nat := [264, 2234, 2446, 2534]
/-- The coordination ring's ready waits (warpgroup 0's and the TMA lane's). -/
def Prog.coordReadySites : List Nat := [264, 2234]
/-- The coordination ring's free waits (the index lanes'). -/
def Prog.coordFreeSites : List Nat := [2446, 2534]
/-- The `S = QK` completion wait. -/
def Prog.qkDoneSites : List Nat := [272]
/-- The `O += SV` completion waits. -/
def Prog.svDoneSites : List Nat := [1184, 2684]
/-- The dequantized tile's wait. -/
def Prog.dequantReadySites : List Nat := [2012]
/-- The softmax output's wait. -/
def Prog.soReadySites : List Nat := [2107]
/-- The closing wait of the TMA lane. -/
def Prog.closeSites : List Nat := [2209]
/-- The raw tile ring's free wait (the TMA lane's). -/
def Prog.rawFreeSites : List Nat := [2245]
/-- The raw tile ring's ready wait (the dequant lanes'). -/
def Prog.rawReadySites : List Nat := [2677]

/-- **A failed poll at a pc of `pcs` steps.** -/
def Prog.PollSteps (P : Params) (L : Launch) (m : Mem0) (pcs : List Nat) : Prop :=
  SafeGoal kernel Assumptions.all L m → ∀ X, Maximal L kernel Assumptions.all m X →
    Follow P L X → ∀ {g pc : Nat}, pc ∈ pcs → Frame.Pending L X g → Step.Released L X g →
    FailsAt L m X g pc → Sched.Steps (timed P L) m X (.thread g)

/-- **A pending lane that is not released steps.** -/
def Prog.BlockedSteps (P : Params) (L : Launch) (m : Mem0) : Prop :=
  SafeGoal kernel Assumptions.all L m → ∀ X, Maximal L kernel Assumptions.all m X →
    Follow P L X → ∀ {g : Nat}, Frame.Pending L X g → ¬ Step.Released L X g →
    Sched.Steps (timed P L) m X (.thread g)

/-- **An open asynchronous obligation of `os` steps.** -/
def Prog.AsyncSteps (P : Params) (L : Launch) (m : Mem0) (os : List Descent.Obligation) : Prop :=
  SafeGoal kernel Assumptions.all L m → ∀ X, Maximal L kernel Assumptions.all m X →
    Follow P L X → ∀ o ∈ os, Descent.Obl L X o → Sched.Steps (timed P L) m X o

/-- **The output stores' publication** (the open part of the store class, `split_of`
`prog.store`): in a consistent followed execution, each source byte of an output tensor store
(warpgroup 0's elected lanes, pcs 1358, 1516, 1673, 1831) has a covering write ordered before the
store's read of it (`Step.StoreDone.VisibleReadSources`, its first half). The writes are warpgroup
0's staging stores (`MemRow.Wg0Stage`, inside the store's box `wg0Stage_box`): each lane stores its
row of the chunk, makes a proxy fence and passes barrier 9 (128 threads) before the elected lane
issues the store. -/
def Prog.StorePub (P : Params) (L : Launch) (m : Mem0) : Prop :=
  ∀ X, Consistent L kernel Assumptions.all m X → Follow P L X → ¬ HasUb X →
    ∀ i a s, X.TensorStoreIssue i a s → ∀ slot loc, TensorStore.destination s slot = some loc →
      ∃ w b bs, X.MemWrites w b bs ∧ b.Covers (s.sharedLoc slot) ∧
        ByteCausality L X (s.sharedLoc slot) w (storeSlotReadRef i slot)

/-- The coordination ring's waits are its ready and its free waits. -/
theorem Prog.coord_split {pc : Nat} (h : pc ∈ Prog.coordSites) :
    pc ∈ Prog.coordReadySites ∨ pc ∈ Prog.coordFreeSites := by
  simp only [Prog.coordSites, Prog.coordReadySites, Prog.coordFreeSites, List.mem_cons,
    List.not_mem_nil, or_false] at h ⊢
  omega

/-- **The sixteen waits by class.** -/
theorem Prog.sites_cls {pc : Nat}
    (h : pc ∈ [264, 272, 1184, 1931, 1983, 2012, 2107, 2205, 2209, 2234, 2245, 2446, 2534,
      2644, 2677, 2684]) :
    pc ∈ Prog.qTmaSites ∨ pc ∈ Prog.qUtccpMmaSites ∨ pc ∈ Prog.qUtccpSites ∨
      pc ∈ Prog.coordSites ∨ pc ∈ Prog.qkDoneSites ∨ pc ∈ Prog.svDoneSites ∨
      pc ∈ Prog.dequantReadySites ∨ pc ∈ Prog.soReadySites ∨ pc ∈ Prog.closeSites ∨
      pc ∈ Prog.rawFreeSites ∨ pc ∈ Prog.rawReadySites := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [Prog.qTmaSites, Prog.qUtccpMmaSites, Prog.qUtccpSites, Prog.coordSites,
    Prog.qkDoneSites, Prog.svDoneSites, Prog.dequantReadySites, Prog.soReadySites,
    Prog.closeSites, Prog.rawFreeSites, Prog.rawReadySites, List.mem_cons, List.not_mem_nil,
    or_false]
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
