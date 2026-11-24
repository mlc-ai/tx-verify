-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingVectors
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingAcquire
import Kernels.TmlFa4Fwd.Proof.CorrectionMbarAddress
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Flow.Code.Part143
import Kernels.TmlFa4Fwd.Proof.CorrectionPrefixAccumulator
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Kernels.TmlFa4Fwd.Flow.Code.Part121
import Kernels.TmlFa4Fwd.Flow.Code.Part123
import Kernels.TmlFa4Fwd.Flow.Code.Part124

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Epilogue Softmax Prologue
open PTX.Kernels.TmlFa4Fwd.Correction

noncomputable section

private def rowInputs (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(1612, b32 (g % l.block)), (1613, b32 (rowOf l g)), (2535, b32 l.sharedBase)]

private def rowAddresses (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(1630, b32 (l.sharedBase + 128 * rowOf l g)),
    (1631, b32 (l.sharedBase + 3072 + 128 * rowOf l g)), (1632, b32 (rowOf l g % 2))]

private theorem rowBaseBits (tid : Nat) :
    (tid * 128) &&& 3968 = (tid % 32) * 128 := by
  have h (n : Nat) : n <<< 7 = n * 128 := by rw [Nat.shiftLeft_eq]
  rw [← h tid, ← h (tid % 32), show (3968 : Nat) = (2 ^ 5 - 1) <<< 7 by decide,
    ← Nat.shiftLeft_and_distrib, Nat.and_two_pow_sub_one_eq_mod]

private theorem rowSetupCore {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) :
    Seg kernel [] l g 10 7938 (rowInputs l g) 7948 (rowAddresses l g) := by
  let tid := g % l.block
  let row := rowOf l g
  have hTid : tid < 512 := by rw [← hp.block]; exact Nat.mod_lt _ (by rw [hp.block]; decide)
  have hRow : row < 128 := Nat.mod_lt _ (by decide)
  have hParity : tid % 2 = row % 2 := by change tid % 2 = (tid % 128) % 2; omega
  have hOr : ((row / 32) * 4096) ||| ((tid % 32) * 128) = row * 128 := by
    rw [lor_4096 (by omega) (by omega)]
    change (g % l.block % 128 / 32) * 4096 + g % l.block % 32 * 128 =
      (g % l.block % 128) * 128
    omega
  have hTidAnd : tid &&& 1 = row % 2 :=
    (Nat.and_two_pow_sub_one_eq_mod tid 1).trans hParity
  have hShared := hp.shared.2.1
  have hTid32 : tid % 4294967296 = tid := Nat.mod_eq_of_lt (by omega)
  have hTid64 : tid % 18446744073709551616 = tid := Nat.mod_eq_of_lt (by omega)
  have hRow32 : row % 4294967296 = row := Nat.mod_eq_of_lt (by omega)
  have hRow64 : row % 18446744073709551616 = row := Nat.mod_eq_of_lt (by omega)
  have hGroup32 : (row / 32) % 4294967296 = row / 32 := Nat.mod_eq_of_lt (by omega)
  have hGroup64 : (row / 32) % 18446744073709551616 = row / 32 := Nat.mod_eq_of_lt (by omega)
  have hEnc32 : ((row / 32) * 2097152) % 4294967296 = (row / 32) * 2097152 :=
    Nat.mod_eq_of_lt (by omega)
  have hEnc64 : ((row / 32) * 2097152) % 18446744073709551616 = (row / 32) * 2097152 :=
    Nat.mod_eq_of_lt (by omega)
  have hStridedTid : (tid * 128) % 4294967296 = tid * 128 :=
    Nat.mod_eq_of_lt (by omega)
  have hStridedTid64 : (tid * 128) % 18446744073709551616 = tid * 128 :=
    Nat.mod_eq_of_lt (by omega)
  have hBox32 : ((row / 32) * 4096) % 4294967296 = (row / 32) * 4096 :=
    Nat.mod_eq_of_lt (by omega)
  have hBox64 : ((row / 32) * 4096) % 18446744073709551616 = (row / 32) * 4096 :=
    Nat.mod_eq_of_lt (by omega)
  have hLane32 : ((tid % 32) * 128) % 4294967296 = tid % 32 * 128 :=
    Nat.mod_eq_of_lt (by omega)
  have hLane64 : ((tid % 32) * 128) % 18446744073709551616 = tid % 32 * 128 :=
    Nat.mod_eq_of_lt (by omega)
  intro t ht
  change At t 7938 [(1612, b32 tid), (1613, b32 row), (2535, b32 l.sharedBase)] at ht
  unfold rowAddresses
  seg_fp ht using
    norm_bits [hTidAnd, rowBaseBits, hOr, hRow32, hRow64, hTid32, hTid64,
      hGroup32, hGroup64, hEnc32, hEnc64, hStridedTid, hStridedTid64,
      hBox32, hBox64, hLane32, hLane64]

private def paused (s : TState) (op : Op) : Prop :=
  match op with
  | .mem a => a.kind = .load ∨ scoreStoreOp a = true
  | .tcLd .. => Assumptions.all.any (·.tcLdWait s.pc) = true
  | .tcSt .. => Assumptions.all.any (·.tcStWaitLd s.pc) = true
  | _ => False

/-- Outside a paused split instruction, a correction cursor has clear sub-step state. -/
@[no_expose] def SetupScratch (s : TState) : Prop :=
  s.acc = [] ∧ (s.sub = 0 ∨ ∃ i, kernel.code[s.pc]? = some i ∧
    i.op.isLocal = false ∧ paused s i.op)

/-- Clear sub-step state qualifies at any correction instruction. -/
theorem SetupScratch.clear {s : TState} (hSub : s.sub = 0) (hAcc : s.acc = []) :
    SetupScratch s := ⟨hAcc, .inl hSub⟩

theorem SetupScratch.clearAccumulator {s : TState} (h : SetupScratch s) :
    s.acc = [] := h.1

/-- A local correction instruction begins with no pending access element. -/
theorem scratchLocal {s : TState} {i : Instr} (h : SetupScratch s)
    (hc : kernel.code[s.pc]? = some i) (hl : i.op.isLocal = true) :
    s.sub = 0 ∧ s.acc = [] := by
  refine ⟨?_, h.1⟩
  rcases h.2 with hSub | ⟨j, hj, hNonlocal, _⟩
  · exact hSub
  · obtain rfl := Option.some.inj (hc.symm.trans hj)
    rw [hl] at hNonlocal
    cases hNonlocal

/-- A named statistics wait is never a paused split access. -/
theorem SetupScratch.namedWaitSubZero {s : TState} {reg count : Opnd}
    (h : SetupScratch s) (hc : kernel.code[s.pc]? =
      some ⟨none,.barSyncN reg count true⟩) :
    s.sub = 0 := by
  rcases h.2 with hSub | ⟨i,hi,_,hPause⟩
  · exact hSub
  · have hEq := Option.some.inj (hi.symm.trans hc)
    subst i
    exact (show False from hPause).elim

/-- A returning correction event clears its scratch data when it changes instruction. -/
theorem scratchReturningAndClears {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {i : Instr} (h : SetupScratch s) (hSub : s.sub ≤ 3)
    (hc : kernel.code[s.pc]? = some i) (hNonlocal : i.op.isLocal = false)
    (hOp : correctionReturningOp i.op = true) {r : Nat} (hKeep : r ∉ scoreEventWrites i.op)
    (hScalar : match i.op with | .mem a => a.kind = .load → a.regs.length ≤ 1 | _ => True)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    SetupScratch u ∧ (u.pc ≠ s.pc → u.sub = 0) := by
  have hAcc := correctionEventAccumulator hc hOp hScalar h.1 he
  have hPause : s.sub = 0 ∨ paused s i.op := by
    rcases h.2 with hs | ⟨j, hj, _, hP⟩
    · exact .inl hs
    · exact .inr (Option.some.inj (hj.symm.trans hc) ▸ hP)
  simp only [correctionReturningOp, Bool.or_eq_true] at hOp
  rcases hOp with hScore | hWait
  · have hsReady : ScoreScratchReady i.op s := by
      rcases hPause with hs | hPause
      · cases hi : i.op <;> simp [ScoreScratchReady, ScoreScratchClear, hs, h.1]
      · have ha := h.1
        cases hi : i.op <;> simp_all [paused, ScoreScratchReady]
    have hAfter := scoreEventScratch hc hScore hSub hKeep he hsReady
    by_cases hp : u.pc = s.pc
    · refine ⟨⟨hAcc,?_⟩, fun h => (h hp).elim⟩
      rw [ite_eq_left hp] at hAfter
      have hc' : kernel.code[u.pc]? = some i := hp ▸ hc
      have hMk (hp : paused u i.op) : u.sub = 0 ∨
          ∃ i, kernel.code[u.pc]? = some i ∧ i.op.isLocal = false ∧ paused u i.op :=
        .inr ⟨i, hc', hNonlocal, hp⟩
      cases hi : i.op <;> simp only [hi, ScoreScratchReady, ScoreScratchClear] at hAfter
      case mem a =>
        have hMem : a.kind = .load ∨ scoreStoreOp a = true := by
          simp only [hi, scoreEventOp, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hScore
          exact hScore.elim (fun h => .inl h.1.1.1) .inr
        exact hMk (hi ▸ hMem)
      case tcLd ds ta sh red =>
        exact hAfter.1.elim (fun hh => hMk (hi ▸ hh)) .inl
      case tcSt ta rs sh =>
        exact hAfter.1.elim (fun hh => hMk (hi ▸ hh)) .inl
      all_goals exact .inl hAfter.1
    · rw [ite_eq_right hp] at hAfter
      exact ⟨SetupScratch.clear hAfter.1 hAfter.2, fun _ => hAfter.1⟩
  · have hWaitOp : i.op = .tcWaitLd := by
      cases hi : i.op <;> simp_all
    have hSource : s.sub = 0 := hPause.resolve_right (by simp [hWaitOp, paused])
    obtain ⟨j, hj, _, hf⟩ := estep_event_source he
    obtain rfl := Option.some.inj (hc.symm.trans hj)
    rw [hWaitOp, eventTmpl, tcTmpl] at hf
    split at hf
    · obtain rfl := Option.some.inj hf.2
      exact ⟨⟨hAcc,.inl hSource⟩, fun _ => hSource⟩
    · cases hf.2

/-- A correction callback preserves the scratch shape when ordinary loads are scalar. -/
theorem scratchReturning {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {i : Instr} (h : SetupScratch s) (hSub : s.sub ≤ 3)
    (hc : kernel.code[s.pc]? = some i) (hNonlocal : i.op.isLocal = false)
    (hOp : correctionReturningOp i.op = true) {r : Nat} (hKeep : r ∉ scoreEventWrites i.op)
    (hScalar : match i.op with | .mem a => a.kind = .load → a.regs.length ≤ 1 | _ => True)
    (he : EStep kernel Assumptions.all l g s e (some u)) : SetupScratch u :=
  (scratchReturningAndClears h hSub hc hNonlocal hOp hKeep hScalar he).1

private def setupWrites (op : Op) : List Nat := writesRegs op ++ scoreEventWrites op

private def setupCode (pc : Nat) (i : Instr) : Bool :=
  (i.op.isLocal || correctionReturningOp i.op) &&
  (match i.op with | .mem a => a.kind != .load || a.regs.length ≤ 1 | _ => true) &&
  [2535, 1612, 1613, 1630, 1631, 1632].all (fun r =>
    (r == 1612 && pc == 7748) || (r == 1613 && pc == 7749) ||
      (r == 1630 && pc == 7945) || (r == 1631 && pc == 7946) ||
      (r == 1632 && pc == 7947) || !(setupWrites i.op).contains r) &&
  (if (7938 ≤ pc && pc < 7948) || (8448 ≤ pc && pc < 8464) then
    i.op.isLocal && i.guard.isNone && schedulerFallsThrough i.op else true) &&
  match i.op with
  | .bra target _ => 7745 ≤ target && (target < 8464 || target == 9201) &&
      ((target ≤ 7748) || 7749 ≤ pc) && ((target ≤ 7749) || 7750 ≤ pc) &&
      ((target ≤ 7938) || (7948 < target && 7948 ≤ pc)) &&
      (target ≤ 8448 || target == 9201)
  | .brx .. => false
  | _ => true

private theorem setupCodeAt {pc : Nat} {i : Instr} (hLo : 7745 ≤ pc) (hHi : pc < 8464)
    (hc : kernel.code[pc]? = some i) : setupCode pc i = true := by
  let region := ((kernel.code.drop 7745).take (8464 - 7745)).zipIdx 7745
  have hRegion : region.all (fun (ins, site) => setupCode site ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hRegion (i, pc)
  apply List.mem_of_getElem? (i := pc - 7745)
  dsimp only [region]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private def localRemainder (l : Launch) (g stop : Nat) (s : TState)
    (F : List (Nat × Value)) : Prop :=
  ∃ t, run kernel Assumptions.all l g (stop - s.pc) s = some t ∧ At t stop F

private theorem localRemainderStep {l : Launch} {g stop : Nat} {s u : TState}
    {F : List (Nat × Value)} (h : localRemainder l g stop s F) (hLt : s.pc < stop)
    (hNext : u.pc = s.pc + 1) (ht : Tau kernel Assumptions.all l g s u) :
    localRemainder l g stop u F := by
  obtain ⟨v, hv, hAt⟩ := h
  refine ⟨v, ?_, hAt⟩
  rwa [show stop - s.pc = (stop - u.pc) + 1 by omega, run, tauStep_iff.mpr ht,
    Option.bind_some] at hv

private theorem rowSetup {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} (h : At s 7938 (rowInputs l g)) :
    localRemainder l g 7948 s (rowAddresses l g) := by
  obtain ⟨t, ht, hAt⟩ := rowSetupCore hp g s h
  refine ⟨t, ?_, hAt⟩
  rw [h.1]
  change run kernel Assumptions.all l g 10 s = some t
  apply schedulerLocalTransport (lo := 7938) (len := 10)
    (by set_option maxRecDepth 100000 in kernel_rfl) _ ht h.1.ge (by rw [h.1])
  intro u hLo hHi
  cases hc : kernel.code[u.pc]? with
  | none => cases hf : u.fault <;> simp only [out, hc, hf]
  | some i =>
    have hTable : ((kernel.code.drop 7938).take 10).all
        (fun i => Assumptions.coreOp i.op) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    have hi : i ∈ (kernel.code.drop 7938).take 10 := by
      apply List.mem_of_getElem? (i := u.pc - 7938)
      have hRange : u.pc - 7938 < 10 := by omega
      rw [List.getElem?_take_of_lt hRange, List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hc
    apply Assumptions.out_all_eq_nil _ _ _ hc (List.all_eq_true.mp hTable _ hi)
    all_goals
      simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
        Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega

private def layoutInputs (l : Launch) (g : Nat) : List (Nat × Value) :=
  (1612, b32 (g % l.block)) :: rowAddresses l g

private theorem layoutSetup {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} (h : At s 8448 (layoutInputs l g)) :
    localRemainder l g 8464 s (finalizeLayoutFacts l g) := by
  obtain ⟨u, hu, hAt⟩ := finalizeLayoutRun (g := g) hp h
    (by simp [layoutInputs, rowAddresses]) (by simp [layoutInputs])
    (by simp [layoutInputs, rowAddresses]) (by simp [layoutInputs, rowAddresses])
    (by set_option maxRecDepth 100000 in kernel_rfl)
  exact ⟨u, by simpa only [h.1] using hu, hAt.mono ((holds_append _ _ _).1 hAt.2.2.2.2).1⟩

/-- The actual correction lane ID instruction defines the CTA-local lane. -/
theorem tidDefinition {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s u : TState} (hPc : s.pc = 7748) (hClean : s.fault = none)
    (h : Tau kernel Assumptions.all l g s u) : u.regs 1612 = some (b32 (g % l.block)) := by
  let tid := g % l.block
  let op : Op := .move ⟨.scalar, .int .u 32, [some 1612],
    [.sreg ⟨.tid, some .x⟩]⟩
  have hBound : tid < 2 ^ 32 := by
    have h := Nat.mod_lt g (by rw [hp.block]; decide : 0 < l.block)
    dsimp only [tid]
    rw [hp.block] at h ⊢
    omega
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hPc]; decide
  have hExec : execLocalA Assumptions.all l g s op =
      .ok (next (setReg s 1612 (b32 tid))) := by
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl]
    rw [execLocalA_nil, show op = .move _ from rfl, execLocal_move rfl]
    have hs := (sregValue_oneDim hp.cluster.2.2 g).1
    simp [execMove, readValue, readBits, SReg.width, hs, DType.width, Value.bytes, b32, tid,
      bind, Except.bind, pure, Except.pure, truncBits_ofNat hBound (by decide)]
  have hStep : Tau kernel Assumptions.all l g s (next (setReg s 1612 (b32 tid))) :=
    out_tau hClean (hPc.symm ▸ Flow.code_7748) rfl rfl hExec
  obtain rfl := tau_det h hStep
  simp only [next, setReg, Function.update_self, tid]

/-- The correction row is the CTA-local lane modulo the row-group size. -/
theorem rowDefinition {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s u : TState} (hPc : s.pc = 7749) (hClean : s.fault = none)
    (hTid : s.regs 1612 = some (b32 (g % l.block)))
    (h : Tau kernel Assumptions.all l g s u) : u.regs 1613 = some (b32 (rowOf l g)) := by
  let tid := g % l.block
  let op : Op := .int ⟨.and, .int .b 32, false, [some 1613], [.reg 1612, .imm 127]⟩
  have hBound : tid < 2 ^ 32 := by
    have h := Nat.mod_lt g (by rw [hp.block]; decide : 0 < l.block)
    dsimp only [tid]
    rw [hp.block] at h ⊢
    omega
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hPc]; decide
  have hAnd : BitVec.ofNat 64 tid &&& 127 = BitVec.ofNat 64 (rowOf l g) := by
    apply BitVec.eq_of_toNat_eq
    have hTid64 : tid < 2 ^ 64 := by omega
    have hRow := Nat.mod_lt tid (by decide : 0 < 128)
    rw [BitVec.toNat_and, toNat_ofNat_lt hTid64, show (127 : BitVec 64).toNat = 127 by rfl,
      toNat_ofNat_lt (by unfold rowOf; change tid % 128 < 2 ^ 64; omega)]
    exact Nat.and_two_pow_sub_one_eq_mod tid 7
  have hExec : execLocalA Assumptions.all l g s op =
      .ok (next (setReg s 1613 (b32 (rowOf l g)))) := by
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl]
    rw [execLocalA_nil, show op = .int _ from rfl, execLocal_int rfl]
    change s.regs 1612 = some (b32 tid) at hTid
    simp only [execInt, DType.width, readBits, readReg, hTid, b32, bind, Except.bind,
      pure, Except.pure, truncBits_ofNat hBound (by decide)]
    change Except.ok (next (setReg s 1613 (.bits 32 (BitVec.ofNat 64 tid &&& 127)))) = _
    rw [hAnd]
  have hStep : Tau kernel Assumptions.all l g s (next (setReg s 1613 (b32 (rowOf l g)))) :=
    out_tau hClean (hPc.symm ▸ Flow.code_7749) rfl rfl hExec
  obtain rfl := tau_det h hStep
  simp only [next, setReg, Function.update_self]

private theorem endRemainder {l : Launch} {g n : Nat} {u : TState} {F : List (Nat × Value)}
    (h : localRemainder l g n u F) (hPc : u.pc = n) : At u n F := by
  obtain ⟨v, hv, hV⟩ := h
  rw [hPc, Nat.sub_self] at hv
  exact Option.some.inj hv ▸ hV

private structure SeedFrame (l : Launch) (g : Nat) (s : TState) : Prop where
  early : s.pc < 8464
  scratch : SetupScratch s
  base : s.regs 2535 = some (b32 l.sharedBase)
  tid : 7748 < s.pc → s.regs 1612 = some (b32 (g % l.block))
  row : 7749 < s.pc → s.regs 1613 = some (b32 (rowOf l g))
  rowRun : 7938 < s.pc → s.pc < 7948 → localRemainder l g 7948 s (rowAddresses l g)
  rowWords : 7948 ≤ s.pc → Holds s.regs (rowAddresses l g)
  layoutRun : 8448 < s.pc → localRemainder l g 8464 s (finalizeLayoutFacts l g)

private def StagingSetupFrame (l : Launch) (g : Nat) (s : TState) : Prop :=
  SeedFrame l g s ∨ StagingVectorState l g s ∨ 9201 ≤ s.pc

private structure SetupRoute (s u : TState) : Prop where
  bound : u.pc ≤ 8464 ∨ 9201 ≤ u.pc
  tid : 7748 < u.pc → s.pc = 7748 ∨ 7748 < s.pc
  row : 7749 < u.pc → s.pc = 7749 ∨ 7749 < s.pc
  rowWords : 7948 < u.pc → 7948 ≤ s.pc

private theorem setupForward {s u : TState} (hs : s.pc < 8464)
    (h : u.pc = s.pc + 1 ∨ u.pc = s.pc) : SetupRoute s u := by
  rcases h with h | h <;> exact ⟨by omega, by omega, by omega, by omega⟩

private theorem seedFrameStep {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} {s u : TState} {event : Option Event}
    (hLo : 7745 ≤ s.pc) (hSub : s.sub ≤ 3) (h : SeedFrame l g s)
    (hStep : WStep kernel Assumptions.all l g s event u) : StagingSetupFrame l g u := by
  have table {i : Instr} (hc : kernel.code[s.pc]? = some i) := setupCodeAt hLo h.early hc
  have keepAt {i : Instr} (hc : kernel.code[s.pc]? = some i) {r : Nat}
      (hr : r ∈ [2535, 1612, 1613, 1630, 1631, 1632]) :
      ((r == 1612 && s.pc == 7748) || (r == 1613 && s.pc == 7749) ||
        (r == 1630 && s.pc == 7945) || (r == 1631 && s.pc == 7946) ||
        (r == 1632 && s.pc == 7947) || !(setupWrites i.op).contains r) = true := by
    have hl := table hc
    simp only [setupCode, Bool.and_eq_true] at hl
    exact List.all_eq_true.mp hl.1.1.2 r hr
  have keepBase {i : Instr} (hc : kernel.code[s.pc]? = some i) :
      2535 ∉ setupWrites i.op := by simpa using keepAt hc (r := 2535) (by simp)
  have localInBlock {i : Instr} (hc : kernel.code[s.pc]? = some i)
      (hm : 7938 ≤ s.pc ∧ s.pc < 7948 ∨ 8448 ≤ s.pc ∧ s.pc < 8464) :
      i.op.isLocal = true ∧ i.guard.isNone = true ∧ schedulerFallsThrough i.op = true := by
    have hl := table hc
    simp only [setupCode, Bool.and_eq_true] at hl
    have hh : (decide (7938 ≤ s.pc) && decide (s.pc < 7948) ||
        decide (8448 ≤ s.pc) && decide (s.pc < 8464)) = true := by simpa using hm
    simpa only [hh, ↓reduceIte, Bool.and_eq_true, and_assoc] using hl.1.2
  have replay {i : Instr} {lo hi : Nat} {F G : List (Nat × Value)}
      (hc : kernel.code[s.pc]? = some i)
      (start : At s lo F → localRemainder l g hi s G)
      (hs : s.pc = lo → Holds s.regs F)
      (prior : lo < s.pc → s.pc < hi → localRemainder l g hi s G)
      (hB : 7938 ≤ s.pc ∧ s.pc < 7948 ∨ 8448 ≤ s.pc ∧ s.pc < 8464)
      (hTau : Tau kernel Assumptions.all l g s u) (hClean : s.fault = none)
      (hFrom : lo ≤ s.pc) (hTo : s.pc < hi) (hNext : u.pc = s.pc + 1) :
      localRemainder l g hi u G := by
    have hScratch := scratchLocal h.scratch hc (localInBlock hc hB).1
    apply localRemainderStep _ hTo hNext hTau
    by_cases hEq : s.pc = lo
    · exact start ⟨hEq, hScratch.1, hScratch.2, hClean, hs hEq⟩
    · exact prior (by omega) hTo
  have done {i : Instr} (hc : kernel.code[s.pc]? = some i) (route : SetupRoute s u)
      (scratch : SetupScratch u) (keep : ∀ r, r ∉ setupWrites i.op → u.regs r = s.regs r)
      (newTid : s.pc = 7748 → u.regs 1612 = some (b32 (g % l.block)))
      (newRow : s.pc = 7749 → u.regs 1613 = some (b32 (rowOf l g)))
      (rows : 7938 < u.pc → u.pc ≤ 7948 → localRemainder l g 7948 u (rowAddresses l g))
      (layout : 8448 < u.pc → u.pc ≤ 8464 →
        localRemainder l g 8464 u (finalizeLayoutFacts l g)) :
      StagingSetupFrame l g u := by
    rcases route.bound with hBound | hExit
    · by_cases hEq : u.pc = 8464
      · exact .inr (.inl (StagingVectorState.ofLayout
          (endRemainder (layout (by omega) hBound) hEq)))
      · refine .inl ⟨by omega, scratch, (keep _ (keepBase hc)).trans h.base, ?_, ?_,
          fun ha hb => rows ha (by omega), ?_, fun ha => layout ha hBound⟩
        · intro hu
          rcases route.tid hu with he | he
          · exact newTid he
          · have hNe : s.pc ≠ 7748 := by omega
            exact (keep _ (by simpa [hNe] using keepAt hc (r := 1612) (by simp))).trans (h.tid he)
        · intro hu
          rcases route.row hu with he | he
          · exact newRow he
          · have hNe : s.pc ≠ 7749 := by omega
            exact (keep _ (by simpa [hNe] using keepAt hc (r := 1613) (by simp))).trans (h.row he)
        · intro hu
          by_cases he : u.pc = 7948
          · exact (endRemainder (rows (by omega) (by omega)) he).2.2.2.2
          · have hPrior := route.rowWords (by omega)
            have h45 : s.pc ≠ 7945 := by omega
            have h46 : s.pc ≠ 7946 := by omega
            have h47 : s.pc ≠ 7947 := by omega
            have hW := h.rowWords hPrior
            exact ⟨(keep _ (by simpa [h45] using keepAt hc (r := 1630) (by simp))).trans hW.1,
              (keep _ (by simpa [h46] using keepAt hc (r := 1631) (by simp))).trans hW.2.1,
              (keep _ (by simpa [h47] using keepAt hc (r := 1632) (by simp))).trans hW.2.2.1,
              trivial⟩
    · exact .inr (.inr hExit)
  rcases hStep with ⟨_, ht⟩ | ⟨_, _, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, hClean, hTau⟩ := correctionTauFrame hOff ht
    have fallthrough (hn : u.pc = s.pc + 1) (hScratch : SetupScratch u)
        (hKeep : ∀ r, r ∉ setupWrites i.op → u.regs r = s.regs r) :
        StagingSetupFrame l g u := by
      refine done hc (setupForward h.early (.inl hn)) hScratch hKeep
        (fun hs => tidDefinition hp hs hClean ht)
        (fun hs => rowDefinition hp hs hClean (h.tid (by omega)) ht) ?_ ?_
      · intro hL hU
        exact replay (lo := 7938) (hi := 7948) (F := rowInputs l g) hc (rowSetup hp)
          (fun hs => ⟨h.tid (by omega), h.row (by omega), h.base, trivial⟩)
          h.rowRun (.inl ⟨by omega, by omega⟩) ht hClean
          (by omega) (by omega) hn
      · intro hL hU
        exact replay (lo := 8448) (hi := 8464) (F := layoutInputs l g) hc (layoutSetup hp)
          (fun hs => ⟨h.tid (by omega), h.rowWords (by omega)⟩)
          (fun hs _ => h.layoutRun hs)
          (.inr ⟨by omega, by omega⟩) ht hClean (by omega) (by omega) hn
    rcases hTau with ⟨rfl, _⟩ | ⟨_, hLocal, hFrame⟩
    · exact fallthrough rfl ⟨rfl, .inl rfl⟩ (fun _ _ => rfl)
    have hScratch := scratchLocal h.scratch hc hLocal
    have nextScratch : SetupScratch u :=
      ⟨hFrame.acc.trans hScratch.2, .inl (hFrame.sub.trans hScratch.1)⟩
    have hKeep : ∀ r, r ∉ setupWrites i.op → u.regs r = s.regs r :=
      fun r hr => hFrame.regs r (fun hm => hr (List.mem_append_left _ hm))
    have hPc := hFrame.pc
    cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
    case bra dest uni =>
      have hCheck := table hc
      simp only [setupCode, Bool.and_eq_true, ho] at hCheck
      have hJump := hCheck.2
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hJump
      have hNever (n : Nat) (hEq : s.pc = n) (hCode : (kernel.code[n]?).map
          (fun x => x.op) ≠ some (.bra dest uni)) : False := by
        apply hCode
        rw [← hEq, hc]
        simp [ho]
      apply done hc (⟨by omega, by omega, by omega, by omega⟩ : SetupRoute s u)
        nextScratch hKeep
      · exact fun hEq => (hNever 7748 hEq (by rw [Flow.code_7748]; simp)).elim
      · exact fun hEq => (hNever 7749 hEq (by rw [Flow.code_7749]; simp)).elim
      · omega
      · omega
    case brx =>
      have hCheck := table hc
      simp [setupCode, ho] at hCheck
    all_goals exact fallthrough hPc nextScratch hKeep
  · obtain ⟨i, hc, hLocal, _⟩ := estep_event_source he
    have hCheck := table hc
    simp only [setupCode, Bool.and_eq_true, hLocal, Bool.false_or] at hCheck
    have hEvent := hCheck.1.1.1.1
    obtain ⟨hProg, _⟩ := correctionEventProgress (r := 2535) hc hEvent hSub
      (fun he => keepBase hc (List.mem_append_right _ he)) he
    have hPc : u.pc = s.pc + 1 ∨ u.pc = s.pc :=
      hProg.pc.elim (fun he => .inl he.1) (fun he => .inr he.1)
    have hNoLocal (hm : 7938 ≤ s.pc ∧ s.pc < 7948 ∨ 8448 ≤ s.pc ∧ s.pc < 8464) :
        False := by rw [(localInBlock hc hm).1] at hLocal; cases hLocal
    have hEarly := h.early
    have hScalar : match i.op with | .mem a => a.kind = .load → a.regs.length ≤ 1 | _ => True := by
      have hOK := hCheck.1.1.1.2
      cases hi : i.op <;> try trivial
      case mem a =>
        intro hLoad
        simpa only [hi, hLoad, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] using hOK
    refine done hc (setupForward h.early hPc)
      (scratchReturning h.scratch hSub hc hLocal hEvent
        (fun he => keepBase hc (List.mem_append_right _ he)) hScalar he)
      (fun r hr => (correctionEventProgress hc hEvent hSub
        (fun hm => hr (List.mem_append_right _ hm)) he).2) ?_ ?_ ?_ ?_
    · intro hEq
      rw [hEq, Flow.code_7748] at hc
      obtain rfl := Option.some.inj hc.symm
      cases hLocal
    · intro hEq
      rw [hEq, Flow.code_7749] at hc
      obtain rfl := Option.some.inj hc.symm
      cases hLocal
    · intro hL hU
      have hAbsent : u.pc = s.pc → s.pc = 7948 := by
        intro he
        by_contra hn
        exact hNoLocal (.inl ⟨by omega, by omega⟩)
      rcases hPc with hPc | hPc
      · exact (hNoLocal (.inl ⟨by omega, by omega⟩)).elim
      · have hs : s.pc = 7948 := hAbsent hPc
        rw [hs, Flow.code_7948] at hc
        obtain rfl := Option.some.inj hc.symm
        cases hLocal
    · intro hL hU
      exact (hNoLocal (.inr ⟨by omega, by omega⟩)).elim

private theorem terminalRegionStep {l : Launch} {g : Nat} {s u : TState}
    {event : Option Event} (hLo : 9201 ≤ s.pc) (hHi : s.pc < 9205) (hSub : s.sub ≤ 3)
    (h : WStep kernel Assumptions.all l g s event u) : 9201 ≤ u.pc := by
  have hCheck {i : Instr} (hc : kernel.code[s.pc]? = some i) :
      ((i.op.isLocal || correctionReturningOp i.op) && !(scoreEventWrites i.op).contains 0 &&
        match i.op with
        | .bra dest _ => 9201 ≤ dest
        | .brx .. => false
        | _ => true) = true := by
    interval_cases hs : s.pc
    · rw [Flow.code_9201] at hc; obtain rfl := Option.some.inj hc.symm; decide
    · rw [Flow.code_9202] at hc; obtain rfl := Option.some.inj hc.symm; decide
    · rw [Flow.code_9203] at hc; obtain rfl := Option.some.inj hc.symm; decide
    · rw [Flow.code_9204] at hc; obtain rfl := Option.some.inj hc.symm; decide
  rcases h with ⟨_, ht⟩ | ⟨_, _, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, _, hTau⟩ := correctionTauFrame hOff ht
    rcases hTau with ⟨rfl, _⟩ | ⟨_, _, hFrame⟩
    · change 9201 ≤ s.pc + 1
      omega
    have hn := hFrame.pc
    have hCode := (Bool.and_eq_true_iff.mp (hCheck hc)).2
    cases hi : i.op <;> simp only [hi, nextPc, BrxTarget, or_false] at hn
    case bra dest uni => rw [hn]; simpa only [hi, decide_eq_true_eq] using hCode
    case brx => simp [hi] at hCode
    all_goals omega
  · obtain ⟨i, hc, hLocal, _⟩ := estep_event_source he
    have hCode := (Bool.and_eq_true_iff.mp (hCheck hc)).1
    simp only [Bool.and_eq_true, hLocal, Bool.false_or, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not] at hCode
    have hn := (correctionEventProgress hc hCode.1 hSub hCode.2 he).1.pc
    rcases hn with hn | hn <;> omega

/-- The staging store belongs to a correction warp. -/
theorem stagingWriteWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {writer : EvId} {a : Acc} {bytes : List Byte} (stage : Fin 2) (subbox : Fin 4)
    (chunk : Fin 8) (he : X.get writer = some ⟨outputStorePc stage subbox chunk, .wr a bytes⟩) :
    8 ≤ warpIndex l writer.1 ∧ warpIndex l writer.1 < 12 ∧
      8492 ≤ outputStorePc stage subbox chunk ∧ outputStorePc stage subbox chunk < 9201 := by
  have hBounds : 8492 ≤ outputStorePc stage subbox chunk ∧
      outputStorePc stage subbox chunk < 9201 := by
    fin_cases stage <;> fin_cases subbox <;> fin_cases chunk <;> decide
  have hHint : outputStorePc stage subbox chunk ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  let target : Event := ⟨outputStorePc stage subbox chunk, .wr a bytes⟩
  have hLo : 173 < target.pc := by
    change 173 < outputStorePc stage subbox chunk
    omega
  have hRole := roleBodyPcOfEvent hp hX (e := target) he hLo hHint
  have hw : 8 ≤ warpIndex l writer.1 ∧ warpIndex l writer.1 < 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · dsimp only [target] at h
      omega
    · dsimp only [target] at h
      split_ifs at h <;> omega
  exact ⟨hw.1, hw.2, hBounds⟩

/-- The actual vector write from any correction lane in an execution prefix uses its
decoded stage, subbox, swizzled column, and lane row. -/
theorem stagingWriteElement {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {writer : EvId} {a : Acc} {bytes : List Byte} (stage : Fin 2) (subbox : Fin 4)
    (chunk : Fin 8) (he : X.get writer = some ⟨outputStorePc stage subbox chunk, .wr a bytes⟩) :
    ∃ elem : Fin 4, a = outputElementAccess l writer.1 stage subbox
      (4 * chunk.val + elem.val) (rowOf l writer.1) := by
  obtain ⟨g, index⟩ := writer
  let target : Event := ⟨outputStorePc stage subbox chunk, .wr a bytes⟩
  obtain ⟨hWarpLo, hWarpHi, hMin, hMax⟩ := stagingWriteWarp hp hX stage subbox chunk he
  have hLo : 173 < target.pc := by change 173 < outputStorePc stage subbox chunk; omega
  have hHi : target.pc < 9205 := by change outputStorePc stage subbox chunk < 9205; omega
  obtain ⟨t, o, ht, _, hFrame, hEvent⟩ := correctionRoleEventWith hp hX hWarpLo hWarpHi
    (e := target) he hLo hHi (Q := StagingSetupFrame l g)
    (by
      intro s hs
      refine .inl ⟨by rw [hs.1]; decide, ⟨hs.2.2.1, .inl hs.2.1⟩,
        holds_mem hs.2.2.2.2 (by simp [nonzeroBarrierFacts]), ?_, ?_, ?_, ?_, ?_⟩
      all_goals intro hn; rw [hs.1] at hn; omega)
    (by
      intro s u event hl hh hSub hStep hMove
      rcases hStep with h | h | h
      · exact seedFrameStep hp hl hSub h hMove
      · exact .inr (.inl (StagingVectorState.step hp h hh hMove))
      · exact .inr (.inr (terminalRegionStep h hh hSub hMove)))
  change t.pc = outputStorePc stage subbox chunk at ht
  rcases hFrame with hSeed | hStaging | hExit
  · exact (by have := hSeed.early; omega : False).elim
  · exact hStaging.element hp stage subbox chunk hEvent
  · exact (by omega : False).elim

/-- An actual staging write has its stage and subbox, physical footprint, and the stage-zero
observation consumed by the input reuse protocol. -/
theorem StagingWrite.element {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {writer : EvId} {a : Acc} {bytes : List Byte} (h : StagingWrite X (.thread writer) a bytes) :
    ∃ (stage : Fin 2) (subbox : Fin 4) (x row : Nat), x < 32 ∧ row < 128 ∧
      a = outputElementAccess l writer.1 stage subbox x row ∧
      (stage = 0 → StageZeroStagingWrites X writer a bytes) := by
  obtain ⟨stage, subbox, chunk, he⟩ := h.decoded
  obtain ⟨elem, ha⟩ := stagingWriteElement hp hX stage subbox chunk he
  refine ⟨stage, subbox, 4 * chunk.val + elem.val, rowOf l writer.1, ?_,
    Nat.mod_lt _ (by decide), ha, ?_⟩
  · have := chunk.isLt
    have := elem.isLt
    omega
  · intro hs
    subst stage
    exact StageZeroStagingWrites.of_event subbox chunk he

end
end PTX.Kernels.TmlFa4Fwd.Thread.Correction
