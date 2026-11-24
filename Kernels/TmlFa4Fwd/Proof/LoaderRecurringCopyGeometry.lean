-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderCopyGeometry
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringDestinations
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringSwizzle
public import Kernels.TmlFa4Fwd.Proof.LoaderReadyBarriers
public import Kernels.TmlFa4Fwd.Proof.LoaderWalkCheckpoint
import Kernels.TmlFa4Fwd.Flow.Code.Part015
import Kernels.TmlFa4Fwd.Flow.Code.Part019
import Kernels.TmlFa4Fwd.Flow.Code.Part022
import Kernels.TmlFa4Fwd.Flow.Code.Part023
import Kernels.TmlFa4Fwd.Flow.Code.Part025

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- Stage and swizzled stage-zero bases before the recurring packet computes its vectors. -/
def recurringAddressInputs (l : Launch) (site : Fin 4) (stage tid : Nat) : List (Nat × Value) :=
  [((recurringStageInputs site).1, b32 stage),
   ((recurringDstBases site).1, b32 (kvCopyAddress l.sharedBase 0 tid 0 false)),
   ((recurringDstBases site).2, b32 (kvCopyAddress l.sharedBase 0 tid 1 false))]

/-- Barrier-preparation entrance of a recurring copy packet. -/
def recurringGeometryEntry (site : Fin 4) : Nat := (recurringEmptyWait site).pc - 3

private theorem oddSeedCode (site : Fin 4) :
    ∃ ins, kernel.code[recurringOddSeed site]? = some ins ∧ ins.op.isLocal = true := by
  fin_cases site
  · exact ⟨_, Flow.code_1019, rfl⟩
  · exact ⟨_, Flow.code_1253, rfl⟩
  · exact ⟨_, Flow.code_1484, rfl⟩
  · exact ⟨_, Flow.code_1646, rfl⟩

private theorem localPairFrame (site : Fin 4) :
    ((kernel.code.drop (recurringEvenSeed site)).take
      (recurringEvenSeed site + 2 - recurringEvenSeed site)).all
        (fun ins => Epilogue.schedulerFallsThrough ins.op &&
          [(recurringDstBases site).2].all fun r => !(loaderRingWrites ins.op).contains r) =
      true := by
  fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)

private theorem beforeOddSeed (site : Fin 4) :
    ((kernel.code.drop (recurringEvenSeed site + 2)).take
      (recurringOddSeed site - (recurringEvenSeed site + 2))).all
      (fun ins => loaderPipelineCutOp (recurringEvenSeed site + 2) (recurringOddSeed site)
        (copyCommitPc (recurringPacketSite site) - 1)
        [(recurringDstBases site).2, (recurringStageInputs site).2] ins.op) = true := by
  fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)

private theorem recurringBody (site : Fin 4) (isOdd : Bool) :
    let start := if isOdd then recurringOddSeed site + 1 else recurringEvenSeed site + 2
    let stop := copyCommitPc (recurringPacketSite site)
    ((kernel.code.drop start).take (stop - start)).all
      (fun ins => loaderPipelineCutOp start stop (stop - 1)
        [packetDstReg (recurringPacketSite site) (if isOdd then 1 else 0)] ins.op) = true := by
  fin_cases site <;> cases isOdd <;> (set_option maxRecDepth 100000 in kernel_rfl)

private theorem planeAfterEven (site : Fin 4) (group : Fin 16) (upper : Bool) :
    recurringEvenSeed site + 2 ≤ packetPlanePc (recurringPacketSite site) group upper := by
  fin_cases site <;> fin_cases group <;> cases upper <;> decide

private theorem planeAfterOdd (site : Fin 4) (group : Fin 16) (upper : Bool)
    (hOdd : group.val % 2 = 1) :
    recurringOddSeed site + 1 ≤ packetPlanePc (recurringPacketSite site) group upper := by
  fin_cases site <;> fin_cases group <;> cases upper <;> first | contradiction | decide

/-- A recurring packet's actual copy names the exact vector identified by the decoded
pair and plane, provided its stage and two stage-zero bases are established at the seed. -/
theorem recurringCopyDestinationFromSeeds {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g stage scopeLower : Nat} (hStage : stage < 3) (site : Fin 4)
    (hScope : scopeLower ≤ recurringEvenSeed site)
    {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s (recurringEvenSeed site) (recurringAddressInputs l site stage (g % l.block)))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (group : Fin 16) (upper : Bool) {sp : AsyncCopy.Spec}
    (hSeen : ⟨packetPlanePc (recurringPacketSite site) group upper, .copy sp⟩ ∈
      loaderSliceEvents scopeLower (copyCommitPc (recurringPacketSite site)) vs) :
    sp.dst = {loc := ⟨.shared, g / l.block,
      kvCopyAddress l.sharedBase stage (g % l.block) group upper⟩, size := 16} := by
  let tid := g % l.block
  let packet := recurringPacketSite site
  let stop := copyCommitPc packet
  let e : Event := ⟨packetPlanePc packet group upper, .copy sp⟩
  have hLo : 174 ≤ recurringEvenSeed site := by fin_cases site <;> decide
  have hOddLo : 174 ≤ recurringOddSeed site := by fin_cases site <;> decide
  have hEnd : stop ≤ 1901 := by fin_cases site <;> decide
  have hOrd : recurringEvenSeed site + 2 ≤ recurringOddSeed site := by fin_cases site <;> decide
  have hBefore : recurringOddSeed site + 1 < stop := by fin_cases site <;> decide
  have hOddHi : recurringOddSeed site ≤ 1901 := by omega
  have hCut : recurringOddSeed site < copyCommitPc (recurringPacketSite site) := by
    change recurringOddSeed site < stop
    omega
  have hShift : stage + packetStageShift packet < 3 := by
    have hZero : packetStageShift packet = 0 := by fin_cases site <;> rfl
    simpa [hZero] using hStage
  obtain ⟨u, hr, hu⟩ := recurringEvenSeedRun hp (g := g) site hStage s
    (hs.mono ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1, trivial⟩)
  obtain ⟨uv, hWalk, _, hSaw⟩ := loaderEventAfterLocal hr hw hSeen
  have hNext : ∃ t v, t.pc = e.pc ∧ t.regs (packetDstReg packet group) =
      some (b32 (kvCopyAddress l.sharedBase stage tid (group.val % 2) false)) ∧
      EStep kernel Assumptions.all l g t e (some v) := by
    by_cases hEven : group.val % 2 = 0
    · let F := [(packetDstReg packet 0, b32 (kvCopyAddress l.sharedBase stage tid 0 false))]
      have hF : Holds u.regs F := ⟨hu.2.2.2.2.1, trivial⟩
      obtain ⟨t, v, ht, hRegs, hStep⟩ := loaderCopyWithRegisters
        (F := F) (lower := recurringEvenSeed site + 2) (by omega) (by omega) hEnd
        (recurringBody site false) hWalk hu.1.ge (ringShapeOfAt hu) hF hSaw rfl
      have hReg : packetDstReg packet group = packetDstReg packet 0 := by
        simp [packetDstReg, hEven]
      exact ⟨t, v, ht, by simpa only [hReg, hEven] using hRegs.1, hStep⟩
    have hOdd : group.val % 2 = 1 := by omega
    obtain ⟨_, hf⟩ := loaderSegmentFrame (regs := [(recurringDstBases site).2])
      hLo (by omega : recurringEvenSeed site + 2 ≤ 1901) (localPairFrame site) hr
      hs.1.ge (by rw [hs.1])
    let F := [((recurringDstBases site).2, b32 (kvCopyAddress l.sharedBase 0 tid 1 false)),
      ((recurringStageInputs site).2, b32 (32768 * stage))]
    have hF : Holds u.regs F :=
      ⟨(hf _ (by simp)).trans hs.2.2.2.2.2.2.1, hu.2.2.2.2.2.1, trivial⟩
    obtain ⟨t, _, tv, ht, hW, _, hT⟩ := loaderCopyThroughCheckpoint
      (cut := recurringOddSeed site) (lower := recurringEvenSeed site + 2)
      (F := F) (by omega) (by omega) hOddHi hCut
      (oddSeedCode site) (beforeOddSeed site) hWalk ⟨hu.1.ge, hu.1.le.trans hOrd⟩
      (ringShapeOfAt hu) hF hSaw (by
        change recurringOddSeed site ≤ packetPlanePc packet group upper
        exact (Nat.le_succ _).trans (planeAfterOdd site group upper hOdd)) rfl
    obtain ⟨o, ho, hO⟩ := recurringOddSeedRun hp site hStage t ht
    obtain ⟨ov, hWalk', _, hSaw'⟩ := loaderEventAfterLocal ho hW hT
    let G := [(packetDstReg packet 1, b32 (kvCopyAddress l.sharedBase stage tid 1 false))]
    obtain ⟨a, v, ha, hRegs, hStep⟩ := loaderCopyWithRegisters
      (F := G) (lower := recurringOddSeed site + 1) (by omega) (by omega) hEnd
      (recurringBody site true) hWalk' hO.1.ge (ringShapeOfAt hO) hO.2.2.2.2 hSaw' rfl
    have hReg : packetDstReg packet group = packetDstReg packet 1 := by simp [packetDstReg, hOdd]
    exact ⟨a, v, ha, by simpa only [hReg, hOdd] using hRegs.1, hStep⟩
  obtain ⟨t, u, hPc, hDst, hStep⟩ := hNext
  have hE : e = ⟨t.pc, .copy sp⟩ := by rw [hPc]
  rw [hE] at hStep
  have hZero : packetStageShift packet = 0 := by fin_cases site <;> rfl
  simpa only [hZero, Nat.add_zero] using packetCopyDestination hp packet group upper
    hShift hPc hDst hStep

/-- The recurring sites with their own swizzle calculation. -/
def recurringSwizzlePacket (site : Fin 3) : Fin 4 := ⟨site, by have := site.isLt; omega⟩

/-- Input registers at the empty-barrier entry of a packet which computes its own swizzle. -/
def recurringSwizzleEntryFacts (l : Launch) (site : Fin 3) (tid stage : Nat) :
    List (Nat × Value) :=
  recurringSwizzleInputs l tid site ++
    [((recurringStageInputs (recurringSwizzlePacket site)).1, b32 stage)]

/-- Barrier operand preparation before a packet-specific swizzle. -/
def recurringSwizzleEntry (site : Fin 3) : Nat :=
  recurringGeometryEntry (recurringSwizzlePacket site)

private theorem recurringSwizzleCode (site : Fin 3) :
    ∃ ins, kernel.code[recurringSwizzleStart site]? = some ins ∧ ins.op.isLocal = true := by
  fin_cases site
  · exact ⟨_, Flow.code_983, rfl⟩
  · exact ⟨_, Flow.code_1227, rfl⟩
  · exact ⟨_, Flow.code_1451, rfl⟩

private theorem evenSeedCode (site : Fin 3) :
    ∃ ins, kernel.code[recurringEvenSeed (recurringSwizzlePacket site)]? = some ins ∧
      ins.op.isLocal = true := by
  fin_cases site
  · exact ⟨_, Flow.code_1009, rfl⟩
  · exact ⟨_, Flow.code_1245, rfl⟩
  · exact ⟨_, Flow.code_1474, rfl⟩

private theorem reachesSwizzle (l : Launch) (site : Fin 3) (tid stage : Nat) :
    let stop := copyCommitPc (recurringPacketSite (recurringSwizzlePacket site))
    let cut := recurringSwizzleStart site
    ((kernel.code.drop (recurringSwizzleEntry site)).take (cut - recurringSwizzleEntry site)).all
      (fun ins => loaderPipelineCutOp (recurringSwizzleEntry site) cut (stop - 1)
        ((recurringSwizzleEntryFacts l site tid stage).map Prod.fst) ins.op) = true := by
  fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)

private theorem swizzleKeepsStage (site : Fin 3) :
    ((kernel.code.drop (recurringSwizzleStart site)).take
      (recurringSwizzleFinish site - recurringSwizzleStart site)).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op &&
        [(recurringStageInputs (recurringSwizzlePacket site)).1].all
          fun r => !(loaderRingWrites ins.op).contains r) = true := by
  fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)

private theorem reachesEvenSeed (l : Launch) (site : Fin 3) (tid stage : Nat) :
    let stop := copyCommitPc (recurringPacketSite (recurringSwizzlePacket site))
    let cut := recurringEvenSeed (recurringSwizzlePacket site)
    let lower := recurringSwizzleFinish site
    ((kernel.code.drop lower).take (cut - lower)).all
      (fun ins => loaderPipelineCutOp lower cut (stop - 1)
        ((recurringAddressInputs l (recurringSwizzlePacket site) stage tid).map Prod.fst)
        ins.op) = true := by
  fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)

private theorem recurringSwizzleBaseRegs (site : Fin 3) :
    recurringSwizzleRegs site = recurringDstBases (recurringSwizzlePacket site) := by
  fin_cases site <;> rfl

/-- Warm K, warm V, and steady K use the same two vector seeds after their own swizzle.
The target event is retained through the actual barrier and local address calculations. -/
theorem recurringCopyDestinationFromEntry {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g stage : Nat} (hStage : stage < 3) (site : Fin 3)
    {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s (recurringSwizzleEntry site) (recurringSwizzleEntryFacts l site (g % l.block) stage))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (group : Fin 16) (upper : Bool) {sp : AsyncCopy.Spec}
    (hSeen : let packet := recurringPacketSite (recurringSwizzlePacket site)
      ⟨packetPlanePc packet group upper, .copy sp⟩ ∈
        loaderSliceEvents (recurringSwizzleEntry site) (copyCommitPc packet) vs) :
    sp.dst = {loc := ⟨.shared, g / l.block,
      kvCopyAddress l.sharedBase stage (g % l.block) group upper⟩, size := 16} := by
  let tid := g % l.block
  let packet := recurringPacketSite (recurringSwizzlePacket site)
  let stop := copyCommitPc packet
  let e : Event := ⟨packetPlanePc packet group upper, .copy sp⟩
  let start := recurringSwizzleStart site
  let finish := recurringSwizzleFinish site
  let even := recurringEvenSeed (recurringSwizzlePacket site)
  have hTid : tid < 512 := by
    dsimp only [tid]
    rw [hp.block]
    exact Nat.mod_lt _ (by decide)
  have hL : 174 ≤ recurringSwizzleEntry site ∧ recurringSwizzleEntry site ≤ start ∧ start ≤ finish ∧
      finish ≤ even ∧ even < stop ∧ stop ≤ 1901 := by fin_cases site <;> decide
  have hBefore : start ≤ e.pc := by
    change start ≤ packetPlanePc packet group upper
    have hPlane := planeAfterEven (recurringSwizzlePacket site) group upper
    change even + 2 ≤ packetPlanePc packet group upper at hPlane
    omega
  obtain ⟨t, _, tv, ht, hW, _, hSaw⟩ := loaderCopyThroughCheckpoint
    (F := recurringSwizzleEntryFacts l site tid stage)
    (cut := start) (lower := recurringSwizzleEntry site) (stop := stop)
    le_rfl hL.1 (by omega) (by omega)
    (recurringSwizzleCode site) (reachesSwizzle l site tid stage) hw
    ⟨hs.1.ge, hs.1.le.trans hL.2.1⟩ (ringShapeOfAt hs) hs.2.2.2.2 hSeen hBefore rfl
  obtain ⟨u, hr, hu⟩ := recurringSwizzleRun hp hTid site t
    (ht.mono ((holds_append ..).mp ht.2.2.2.2).1)
  have hStart : start ≤ t.pc := ht.1.ge
  have hStop : t.pc + (finish - start) ≤ finish := by
    have := ht.1
    omega
  obtain ⟨_, hStageKeep⟩ := loaderSegmentFrame
    (regs := [(recurringStageInputs (recurringSwizzlePacket site)).1])
    (by omega : 174 ≤ start) (by omega : finish ≤ 1901)
    (swizzleKeepsStage site) hr hStart hStop
  obtain ⟨uv, hWu, _, hU⟩ := loaderEventAfterLocal hr hW hSaw
  let F := recurringAddressInputs l (recurringSwizzlePacket site) stage tid
  have hFrame : Holds u.regs F := by
    have h := hu.2.2.2.2
    rw [recurringSwizzleFacts, recurringSwizzleBaseRegs] at h
    exact ⟨(hStageKeep _ (by simp)).trans ((holds_append ..).mp ht.2.2.2.2).2.1,
      h.1, h.2.1, trivial⟩
  have hEven : even ≤ e.pc := by
    change even ≤ packetPlanePc packet group upper
    exact (Nat.le_add_right even 2).trans (planeAfterEven (recurringSwizzlePacket site) group upper)
  obtain ⟨v, _, vv, hv, hWv, _, hV⟩ := loaderCopyThroughCheckpoint
    (F := F) (cut := even) (lower := finish) (stop := stop)
    (by omega) (by omega) (by omega) (by omega)
    (evenSeedCode site) (reachesEvenSeed l site tid stage) hWu
    ⟨hu.1.ge, hu.1.le.trans hL.2.2.2.1⟩ (ringShapeOfAt hu) hFrame hU hEven rfl
  exact recurringCopyDestinationFromSeeds hp hStage (recurringSwizzlePacket site) (by omega)
    hv hWv group upper hV

/-- The recurring V path can reuse the swizzled bases of its paired steady K packet.
Once its actual entry has those bases, all its vectors follow the same copy rule. -/
theorem steadyVCopyDestinationFromEntry {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g stage scopeLower : Nat} (hStage : stage < 3)
    (hScope : scopeLower ≤ 1608) {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s 1608 (recurringAddressInputs l 3 stage (g % l.block)))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (group : Fin 16) (upper : Bool) {sp : AsyncCopy.Spec}
    (hSeen : ⟨packetPlanePc 5 group upper, .copy sp⟩ ∈ loaderSliceEvents scopeLower 1734 vs) :
    sp.dst = {loc := ⟨.shared, g / l.block,
      kvCopyAddress l.sharedBase stage (g % l.block) group upper⟩, size := 16} := by
  let F := recurringAddressInputs l 3 stage (g % l.block)
  have hCode : ((kernel.code.drop 1608).take (1638 - 1608)).all
      (fun ins => loaderPipelineCutOp 1608 1638 1733 [1170, 1153, 1152] ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hSource : 1638 ≤ packetPlanePc 5 group upper := by
    exact (show 1638 ≤ recurringEvenSeed 3 + 2 by decide).trans (planeAfterEven 3 group upper)
  obtain ⟨t, _, tail, ht, hWalk, _, hNext⟩ := loaderCopyThroughCheckpoint
    (scopeLower := scopeLower) (lower := 1608) (cut := 1638) (stop := 1734) (F := F)
    hScope (by decide) (by decide) (by decide) ⟨_, Flow.code_1638, rfl⟩ hCode
    hw ⟨hs.1.ge, hs.1.le.trans (by decide)⟩ (ringShapeOfAt hs) hs.2.2.2.2 hSeen hSource rfl
  exact recurringCopyDestinationFromSeeds hp hStage 3 (hScope.trans (by decide)) ht hWalk
    group upper hNext

/-- The steady K to V transition advances the stage before its parity update. -/
theorem steadyVStageRun {l : Launch} {g : Nat} (k : Fin 3) :
    Seg kernel Assumptions.all l g 3 1603 [(7179, b32 k)] 1606
      [(1170, b32 ((k.val + 1) % 3))] := by
  have hCore : Seg kernel [] l g 3 1603 [(7179, b32 k)] 1606
      [(1170, b32 ((k.val + 1) % 3))] := by
    fin_cases k <;> intro t ht <;> seg_fp ht using decide
  intro t ht
  obtain ⟨u, hr, hu⟩ := hCore t ht
  have hSeq : ((kernel.code.drop 1603).take 2).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hLo : 174 ≤ 1603 := by decide
  have hHi : 1603 + 3 ≤ 1906 := by decide
  exact ⟨u, (loaderLinear (regs := []) hLo hHi ht.1
    (by simp) hSeq hr).1, hu⟩

/-- A steady V copy uses the stage following steady K and the same CTA-lane swizzle.
The actual slice starts at the immediately paired K packet's swizzle. -/
theorem steadyVCopyDestinationFromSwizzle {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} (k : Fin 3) {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s 1451 (recurringSwizzleInputs l (g % l.block) 2 ++ [(7179, b32 k)]))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (group : Fin 16) (upper : Bool) {sp : AsyncCopy.Spec}
    (hSeen : ⟨packetPlanePc 5 group upper, .copy sp⟩ ∈ loaderSliceEvents 1451 1734 vs) :
    sp.dst = {loc := ⟨.shared, g / l.block,
      kvCopyAddress l.sharedBase ((k.val + 1) % 3) (g % l.block) group upper⟩, size := 16} := by
  let tid := g % l.block
  let stage := (k.val + 1) % 3
  let sw := recurringSwizzleFacts l tid 2
  let F := (7179, b32 k) :: sw
  let G := recurringAddressInputs l 3 stage tid
  let e : Event := ⟨packetPlanePc 5 group upper, .copy sp⟩
  have hTid : tid < 512 := by dsimp only [tid]; rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hPc : 1608 ≤ e.pc :=
    (show 1608 ≤ recurringEvenSeed 3 + 2 by decide).trans (planeAfterEven 3 group upper)
  obtain ⟨u, hr, hu⟩ := recurringSwizzleRun hp (g := g) hTid 2 s
    (hs.mono ((holds_append ..).mp hs.2.2.2.2).1)
  have hKeep : ((kernel.code.drop 1451).take (1464 - 1451)).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op &&
        [7179].all fun r => !(loaderRingWrites ins.op).contains r) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨_, hf⟩ := loaderSegmentFrame (regs := [7179])
    (by decide) (by decide) hKeep hr hs.1.ge (by rw [hs.1]; decide)
  obtain ⟨uVisits, hU, _, hCopy⟩ := loaderEventAfterLocal hr hw hSeen
  have hUF : Holds u.regs F :=
    ⟨(hf 7179 (by simp)).trans ((holds_append ..).mp hs.2.2.2.2).2.1, hu.2.2.2.2⟩
  have hCutCode : ((kernel.code.drop 1464).take (1603 - 1464)).all
      (fun ins => loaderPipelineCutOp 1464 1603 1733 [7179, 1153, 1152] ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  change 1608 ≤ packetPlanePc 5 group upper at hPc
  have hBefore : 1603 ≤ packetPlanePc 5 group upper := by omega
  obtain ⟨t, _, tv, ht, hW, _, hT⟩ := loaderCopyThroughCheckpoint
    (scopeLower := 1451) (lower := 1464) (cut := 1603) (stop := 1734) (F := F)
    (by decide) (by decide) (by decide) (by decide) ⟨_, Flow.code_1603, rfl⟩ hCutCode
    hU ⟨hu.1.ge, hu.1.le.trans (by decide)⟩ (ringShapeOfAt hu) hUF hCopy hBefore rfl
  obtain ⟨v, hR, hv⟩ := steadyVStageRun (g := g) k t (ht.mono ⟨ht.2.2.2.2.1, trivial⟩)
  have hSeedFrame : ((kernel.code.drop 1603).take (1606 - 1603)).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op &&
        [1153, 1152].all fun r => !(loaderRingWrites ins.op).contains r) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨_, hKeepSeed⟩ := loaderSegmentFrame (regs := [1153, 1152]) (by decide) (by decide)
    hSeedFrame hR ht.1.ge (by rw [ht.1])
  have hVG : Holds v.regs G :=
    ⟨hv.2.2.2.2.1, (hKeepSeed 1153 (by simp)).trans ht.2.2.2.2.2.1,
      (hKeepSeed 1152 (by simp)).trans ht.2.2.2.2.2.2.1, trivial⟩
  obtain ⟨vv, hWV, _, hV⟩ := loaderEventAfterLocal hR hW hT
  have hEntryCode : ((kernel.code.drop 1606).take (1608 - 1606)).all
      (fun ins => loaderPipelineCutOp 1606 1608 1733 [1170, 1153, 1152] ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨a, _, av, ha, hA, _, hLast⟩ := loaderCopyThroughCheckpoint
    (scopeLower := 1451) (lower := 1606) (cut := 1608) (stop := 1734) (F := G)
    (by decide) (by decide) (by decide) (by decide) ⟨_, Flow.code_1608, rfl⟩ hEntryCode
    hWV ⟨hv.1.ge, hv.1.le.trans (by decide)⟩ (ringShapeOfAt hv) hVG hV hPc rfl
  exact steadyVCopyDestinationFromEntry hp (Nat.mod_lt _ (by decide)) (by decide)
    ha hA group upper hLast

end
end PTX.Kernels.TmlFa4Fwd.Loader
