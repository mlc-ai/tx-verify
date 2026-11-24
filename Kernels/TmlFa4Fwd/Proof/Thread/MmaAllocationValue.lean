-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.AllocationPublication
public import Lemmas.Flow.Regs
import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsAllocationExclusion
import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsStoreGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingSetup
import Kernels.TmlFa4Fwd.Proof.Thread.TerminalStatisticsWrites
import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputBank
import Kernels.TmlFa4Fwd.Proof.MmaResources
import Lemmas.Tmem.TmemPairOrder
import Lemmas.Tmem.TmemPairRecord

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof Prologue Mma

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The single allocator warp is the actual MMA warp of each CTA. -/
theorem allocatorWarp {cta : Nat} {r : Tmem.Pair.Requests} (hr : r ∈ X.tmemHistory cta) :
    r.own.warp = 12 := by
  have hValid := (hX.tmemPair.1 cta).1 r hr
  have hGet := hValid.2.2.2.2.1 0
  have hSites := (actualResourceRequest hX hGet).2
  have hLow : 173 < r.own.pc := by
    rcases hSites with ⟨hPc, _⟩ | ⟨hPc, _⟩ | ⟨hPc, _⟩ <;> omega
  have hHi : r.own.pc < 2768 := by
    rcases hSites with ⟨hPc, _⟩ | ⟨hPc, _⟩ | ⟨hPc, _⟩ <;> omega
  have hHint : r.own.pc ∉ registerHintSites := by
    rcases hSites with ⟨hPc, _⟩ | ⟨hPc, _⟩ | ⟨hPc, _⟩ <;> rw [hPc] <;> decide
  have hBody := roleBodyPcOfEvent hp hX hGet hLow hHint
  have hRoom : (r.own.warp + 1) * 32 ≤ l.block := hValid.2.2.2.1
  have hWarp : warpIndex l (r.own.event l 0).1 = r.own.warp := by
    unfold warpIndex Tmem.Pair.WarpRequest.event
    rw [hp.block] at hRoom ⊢
    change (r.own.cta * 512 + r.own.warp * 32 + 0) % 512 / 32 = r.own.warp
    omega
  change roleBodyPc (warpIndex l (r.own.event l 0).1) r.own.pc at hBody
  rw [hWarp] at hBody
  unfold roleBodyPc at hBody
  rcases hBody with h | h
  · omega
  · split_ifs at h <;> omega

private theorem firstAllocRecord {cta g inst : Nat} {r : Tmem.Pair.Requests}
    (hr : r ∈ X.tmemHistory cta) (hLane : r.own.event l 0 = (g, 6))
    (hHint : X.get (g, 5) = some ⟨1907, .setMaxReg false 80 inst⟩) :
    (X.tmemHistory cta)[0]? = some r := by
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hr
  by_cases hN : n = 0
  · exact hN ▸ hn
  have hLen := (List.getElem?_eq_some_iff.mp hn).1
  let first := (X.tmemHistory cta)[0]'(by omega)
  have hFirst : (X.tmemHistory cta)[0]? = some first :=
    List.getElem?_eq_getElem (by omega)
  have hMember := List.mem_of_getElem? hFirst
  have hValid := (hX.tmemPair.1 cta).1 first hMember
  have hCta := (hX.tmemPair.1 cta).2.1 first hMember
  have hCta' := (hX.tmemPair.1 cta).2.1 r hr
  have hWarp := (allocatorWarp hp hX hMember).trans (allocatorWarp hp hX hr).symm
  have hEarlier := hX.object.warp_ordered hFirst hn (Nat.pos_of_ne_zero hN)
    hValid.2.2 (hCta.trans hCta'.symm) hWarp
  have hSame : (first.own.event l 0).1 = g := by
    have hG := congrArg Prod.fst hLane
    simpa only [Tmem.Pair.WarpRequest.event, hWarp, hCta.trans hCta'.symm] using hG
  have hIndex : first.own.indices 0 < 6 := by
    have hOrder := hEarlier.2.2 0
    have hEq := congrArg Prod.snd hLane
    change r.own.indices 0 = 6 at hEq
    omega
  have hGet := hValid.2.2.2.2.1 0
  change X.get ((first.own.event l 0).1, first.own.indices 0) = _ at hGet
  rw [hSame] at hGet
  have hSites := (actualResourceRequest hX hGet).2
  have hLow : 173 < first.own.pc := by
    rcases hSites with ⟨hPc, _⟩ | ⟨hPc, _⟩ | ⟨hPc, _⟩ <;> omega
  have hG := event_thread_lt hX hGet
  have hWarpPos : 0 < warpIndex l g := by
    have hG' := congrArg Prod.fst hLane
    change r.own.cta * l.block + r.own.warp * 32 + 0 = g at hG'
    rw [← hG', allocatorWarp hp hX hr, hp.block]
    unfold warpIndex
    rw [hp.block]
    omega
  obtain ⟨_, _, hPrefix, _, _⟩ := nonzeroCommonPrefixOfLateEvent hp hX hG hWarpPos hGet hLow
  rw [show first.own.indices 0 = 5 by omega, hHint] at hGet
  exact Kind.noConfusion (congrArg Event.kind (Option.some.inj hGet))

omit hp hX in
/-- The first allocator record starts with empty Tensor Memory, so a 512-column
allocation takes column zero. Later records need not have been executed. -/
theorem allocatorInitialBase {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {cta base : Nat} {r : Tmem.Pair.Requests} (hFirst : (X.tmemHistory cta)[0]? = some r)
    (hAction : r.action = .alloc 512 base) : base = 0 := by
  have hFit : Tmem.available {} base 512 = true := by
    by_contra! hNot
    have hBlocked : Tmem.perform {} (.alloc 512 base) = .blocked := by
      simp [Tmem.perform, hNot, show Tmem.validColumns 512 = true from rfl]
    apply (hX.tmemPair.1 cta).2.2
    cases hHist : X.tmemHistory cta with
    | nil => simp [hHist] at hFirst
    | cons first tail =>
      have hEq : first = r := Option.some.inj (by simpa [hHist] using hFirst)
      subst first
      rw [Tmem.Pair.runRequests, hAction, hBlocked]
  have hBound := (Bool.and_eq_true_iff.mp hFit).1
  exact Nat.eq_zero_of_le_zero (Nat.le_of_add_le_add_right (of_decide_eq_true hBound))


/-- The allocation result in shared memory comes from the CTA's actual, completed
512-column allocation. -/
theorem allocationStoreRecord {g j : Nat} {a : Acc} {bytes : List Byte}
    (he : X.get (g, j) = some ⟨1909, .wr a bytes⟩) :
    ∃ r ∈ X.tmemHistory (g / l.block), r.action = .alloc 512 0 ∧
      r.own.event l 0 = (g, j - 1) ∧
      a = {loc := allocationSlot l g, size := 4} ∧ bytes = (b32 0).toBytes := by
  obtain ⟨hFootprint, hZero, rfl, inst, hHint, hAlloc⟩ := allocatorStoreOrigin hp hX he
  have hContinued : 6 + 1 < (X.tr g).length := PTX.len_of_get he
  obtain ⟨cta, r, hr, lane, hLane⟩ := hX.tmemPairBlocking.performed hAlloc hContinued
  have hValid := (hX.tmemPair.1 cta).1 r hr
  have hLaneEq := congrArg Prod.fst hLane
  change r.own.cta * l.block + r.own.warp * 32 + lane.val = g at hLaneEq
  have hLaneZero : lane = 0 := Fin.ext (by
    change lane.val = 0
    have hLaneRange := lane.isLt
    rw [hp.block] at hLaneEq
    change g % l.block % 32 = 0 at hZero
    rw [hp.block] at hZero
    omega)
  subst lane
  have hEvent := hValid.2.2.2.2.1 0
  rw [hLane, hAlloc] at hEvent
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hEvent
  obtain ⟨base, hAction⟩ := Tmem.Action.request_eq_alloc (hValid.2.1.trans hEvent.2.2.2.symm)
  have hFirst := firstAllocRecord hp hX hr hLane hHint
  have hBase := allocatorInitialBase hX hFirst hAction
  subst base
  have hCta : cta = g / l.block := by
    have hOwn := (hX.tmemPair.1 cta).2.1 r hr
    have hRoom := hValid.2.2.2.1
    change r.own.cta * l.block + r.own.warp * 32 + 0 = g at hLaneEq
    rw [hOwn, hp.block] at hLaneEq
    rw [hp.block] at hRoom ⊢
    omega
  exact ⟨r, hCta ▸ hr, hAction, hLane, hFootprint,
    hX.tmemPairResult _ _ _ _ _ hAlloc cta r 0 hr hLane hAction _ _ _ he⟩

private theorem sourceCoveringAllocation {g k : Nat} (hk : k < 4) {source : AsyncCopy.Ref} {a : Acc}
    {bytes : List Byte} (hWrite : X.MemWrites source a bytes)
    (hCover : a.Covers ((allocationSlot l g).at k)) :
    ∃ owner, source = .thread (owner, 7) ∧ owner / l.block = g / l.block ∧
      warpIndex l owner = 12 ∧ laneOf l owner = 0 ∧
      a = {loc := allocationSlot l g, size := 4} ∧ bytes = (b32 0).toBytes := by
  let loc := (allocationSlot l g).at k
  have hAddress : loc.addr = l.sharedBase + 312 + k := rfl
  have hBelow : loc.addr < l.sharedBase + 68608 := by omega
  rcases sharedWriteBeforeCache hp hX hWrite hCover rfl hBelow with
    ⟨i, rfl, hOrdinary⟩ | ⟨input, x, y, b, rfl⟩
  · rcases sharedWriteSite hX hOrdinary hCover.1.symm with
      hAlloc | ⟨site, hStats⟩ | ⟨stage, box, chunk, hStage⟩
    · obtain ⟨rec, hr, _, hSource, hi, hZero⟩ := allocationStoreRecord hp hX hAlloc
      have hCta := hCover.2.1
      rw [hi] at hCta
      change g / l.block = i.1 / l.block at hCta
      obtain ⟨_, hLane, hIdx, _⟩ := allocatorStoreOrigin hp hX hAlloc
      have hOwner := (hX.tmemPair.1 _).2.1 rec hr
      have hWarp := allocatorWarp hp hX hr
      have hTid := congrArg Prod.fst hSource
      change rec.own.cta * l.block + rec.own.warp * 32 + 0 = i.1 at hTid
      have hAtWarp : warpIndex l i.1 = 12 := by
        unfold warpIndex
        rw [← hTid, hOwner, hWarp, hp.block]
        omega
      have hID : i = (i.1, 7) := Prod.ext rfl hIdx
      exact ⟨i.1, congrArg AsyncCopy.Ref.thread hID, hCta.symm, hAtWarp,
        hLane, by rw [hi]; simp [allocationSlot, hCta], hZero⟩
    · obtain ⟨warp, _, hStatsFoot⟩ := Scores.statisticsStoreFootprint hp hX site hStats
      have hLow := hCover.2.2.1
      rw [hStatsFoot] at hLow
      change l.sharedBase + 4 * (32 * warp.val + laneOf l i.1) +
        (Softmax.statsStore site).offset ≤ loc.addr at hLow
      have hMin := (by decide : ∀ j : Fin 4, 368 ≤ (Softmax.statsStore j).offset) site
      omega
    · obtain ⟨elem, hFootprint⟩ := Correction.stagingWriteElement hp hX stage box chunk hStage
      have hLow := hCover.2.2.1
      rw [hFootprint] at hLow
      simp only [TmlFa4Fwd.Correction.outputElementAccess,
        TmlFa4Fwd.Correction.outputChunkLoc, Epilogue.sharedSlot, Loc.at] at hLow
      change _ ≤ loc.addr at hLow
      omega
  · have hPrior := (tensorInputWriteAboveScratch hp hX hWrite.intent hCover).2
    change l.sharedBase + 3072 ≤ loc.addr at hPrior
    omega

private theorem writeCoveringAllocation {g k : Nat} (hk : k < 4) {source : AsyncCopy.Ref} {a : Acc}
    {bytes : List Byte} (hWrite : X.MemWrites source a bytes)
    (hCover : a.Covers ((allocationSlot l g).at k)) :
    a = {loc := allocationSlot l g, size := 4} ∧ bytes = (b32 0).toBytes := by
  obtain ⟨_, _, _, _, _, hA, hBytes⟩ := sourceCoveringAllocation hp hX hk hWrite hCover
  exact ⟨hA, hBytes⟩

/-- Each allocation result byte has exactly one possible writer in its CTA. -/
theorem allocationResultWriter {g k : Nat} (hk : k < 4) {source : AsyncCopy.Ref} {a : Acc}
    {bytes : List Byte} (hWrite : X.MemWrites source a bytes)
    (hCover : a.Covers ((allocationSlot l g).at k)) :
    source = .thread (g / l.block * l.block + 384, 7) := by
  obtain ⟨owner, hSource, hCta, hWarp, hLane, _, _⟩ :=
    sourceCoveringAllocation hp hX hk hWrite hCover
  have hOwner : owner = g / l.block * l.block + 384 := by
    have hDecompose := Nat.div_add_mod owner l.block
    have hWarp' : owner % l.block / 32 = 12 := hWarp
    have hLane' : owner % l.block % 32 = 0 := hLane
    rw [hCta, Nat.mul_comm] at hDecompose
    omega
  rw [hSource, hOwner]

/-- The warp-12 startup reads its completed 512-column allocation through the CTA
rendezvous. Every possible source of its four bytes carries column zero. -/
theorem mmaAllocationReadZero {g j : Nat} {bytes : List (Option Byte)}
    (he : X.get (g, j) = some ⟨1911, .rd {loc := allocationSlot l g, size := 4} bytes⟩) :
    bytes = (b32 0).toBytes.map some := by
  let a : Acc := {loc := allocationSlot l g, size := 4}
  have hRead : X.MemReads (.thread (g, j)) a bytes := .inl ⟨_, he⟩
  obtain ⟨owner, pos, col, _, _, _, hStore, hSync⟩ := allocationStorePublished hp hX he
  have hWrite : X.MemWrites (.thread (owner, pos)) a (b32 col).toBytes := .inl ⟨_, hStore⟩
  have hVisible (loc : Loc) :
      ByteCausality l X loc (.thread (owner, pos)) (.thread (g, j)) :=
    .direct (.inl (.single (.inr (.inl hSync))))
  obtain ⟨hLen, hRf⟩ := hX.rf _ _ _ hRead
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 4
  · have hCovers : a.Covers (a.loc.at k) := Acc.covers_at hk
    have hHidden := hX.hidden _ _ _ k _ _ _ hRead hk hWrite hCovers (hVisible _)
    have hSelected := hRf k hk
    cases hSrc : X.rf (.thread (g, j)) k with
    | none => simp [hSrc] at hHidden
    | some src =>
      rw [hSrc] at hSelected
      obtain ⟨dst, stored, hWritten, hDst, hValue⟩ := hSelected
      obtain ⟨rfl, rfl⟩ := writeCoveringAllocation hp hX hk hWritten hDst
      rw [hValue]
      simp only [wbyte, a, Loc.at, Nat.add_sub_cancel_left, List.getElem?_map,
        List.getElem?_eq_getElem (show k < (b32 0).toBytes.length from hk), Option.map_some]
  · rw [List.getElem?_eq_none (by change bytes.length = 4 at hLen; omega),
      List.getElem?_eq_none (by
        rw [List.length_map]
        change 4 ≤ k
        exact Nat.le_of_not_gt hk)]

end PTX.Kernels.TmlFa4Fwd.Thread
