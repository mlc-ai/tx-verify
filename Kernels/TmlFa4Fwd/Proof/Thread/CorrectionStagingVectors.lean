-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingGeometry
public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalLayout
public import Lemmas.Flow.WarpUniform
import Lemmas.Flow.MemTmpl
import Kernels.TmlFa4Fwd.Proof.CorrectionMbarAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Epilogue Softmax
open PTX.Kernels.TmlFa4Fwd.Correction

noncomputable section

private def stageVectorDefinition (stage : Fin 2) (chunk : Fin 8) : Nat :=
  if chunk.val = 0 then if stage.val = 0 then 8462 else 8459
  else 8493 + 296 * stage.val + 19 * (chunk.val / 2) - (if chunk.val % 2 = 0 then 14 else 0)

private def stageVectorParent (chunk : Fin 8) : Fin 8 :=
  ⟨if chunk.val % 2 = 1 then chunk.val - 1
    else if chunk.val = 6 then 4 else 0, by
    have := chunk.isLt
    split <;> (first | omega | split <;> decide)⟩

private def stageVectorStride (chunk : Fin 8) : Nat :=
  if chunk.val % 2 = 1 then 6500 else if chunk.val = 4 then 6504 else 6502

private def stageVectorStrideValue (l : Launch) (g : Nat) (chunk : Fin 8) : Nat :=
  if chunk.val % 2 = 1 then finalizeVectorDelta l g
  else if chunk.val = 4 then finalizeEvenDelta l g 2 else finalizeEvenDelta l g 1

private def stageVectorAddress (l : Launch) (g : Nat) (stage : Fin 2) (chunk : Fin 8) : Nat :=
  (outputChunkLoc l g stage 0 (rowOf l g) chunk.val).addr

private def stageVectorAdd (stage : Fin 2) (chunk : Fin 8) : IntInstr :=
  ⟨.add, .int .s 32, false, [some (outputStoreAddrReg stage chunk)],
    [.reg (outputStoreAddrReg stage (stageVectorParent chunk)), .reg (stageVectorStride chunk)]⟩

private def integerForm : Option Instr → Option (Option (Nat × Bool) × IntInstr)
  | some ⟨guard, .int instruction⟩ => some (guard, instruction)
  | _ => none

private theorem stageVectorDefinitionCode (stage : Fin 2) (chunk : Fin 8)
    (hNz : chunk.val ≠ 0) :
    kernel.code[stageVectorDefinition stage chunk]? =
      some ⟨none, .int (stageVectorAdd stage chunk)⟩ := by
  have hCheck : ∀ (s : Fin 2) (c : Fin 8), c.val ≠ 0 →
      integerForm (kernel.code[stageVectorDefinition s c]?) = some (none, stageVectorAdd s c) := by
    decide +kernel
  have h := hCheck stage chunk hNz
  cases hCode : kernel.code[stageVectorDefinition stage chunk]? with
  | none => cases (hCode ▸ h)
  | some ins =>
    obtain ⟨guard, op⟩ := ins
    rw [hCode] at h
    cases op <;> cases h
    rfl

variable {p : Params} {l : Launch} {m : Mem0}

private theorem stageVectorAddressBound (hp : Pre p l m) (g : Nat) (stage : Fin 2) (chunk : Fin 8) :
    stageVectorAddress l g stage chunk < 2 ^ 32 := by
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  have hXor : chunk.val ^^^ (rowOf l g) % 8 < 8 :=
    Nat.xor_lt_two_pow (n := 3) chunk.isLt (Nat.mod_lt _ (by decide))
  have hStage := stage.isLt
  have hLimit := hp.shared.2.1
  simp only [stageVectorAddress, outputChunkLoc, sharedSlot, Loc.at]
  omega

private theorem vectorStrideArithmetic (hp : Pre p l m) (g : Nat) (stage : Fin 2) (chunk : Fin 8)
    (hNz : chunk.val ≠ 0) :
    (stageVectorAddress l g stage (stageVectorParent chunk) +
      stageVectorStrideValue l g chunk) % 2 ^ 32 = stageVectorAddress l g stage chunk := by
  let phase := rowOf l g % 8
  let offset (c : Fin 8) := 16 * (c.val ^^^ phase)
  let base := l.sharedBase + (3072 + 65536 * stage.val) + 128 * rowOf l g
  have hA (c : Fin 8) : stageVectorAddress l g stage c = base + offset c := by
    simp only [stageVectorAddress, outputChunkLoc, sharedSlot, Loc.at, base, offset, phase]
    omega
  have hParity : rowOf l g % 2 = phase % 2 := by dsimp only [phase]; omega
  have hStride : (offset (stageVectorParent chunk) + stageVectorStrideValue l g chunk) %
      2 ^ 32 = offset chunk := by
    dsimp only [offset, stageVectorStrideValue, finalizeVectorDelta, finalizeEvenDelta]
    change (16 * ((stageVectorParent chunk).val ^^^ phase) +
      (if chunk.val % 2 = 1 then if rowOf l g % 2 = 0 then 16 else 2 ^ 32 - 16
        else if chunk.val = 4 then if phase &&& 4 = 0 then 64 else 2 ^ 32 - 64
        else if phase &&& 2 = 0 then 32 else 2 ^ 32 - 32)) % 2 ^ 32 =
        16 * (chunk.val ^^^ phase)
    rw [hParity]
    have hPhase : phase < 8 := Nat.mod_lt _ (by decide)
    generalize phase = x at hPhase ⊢
    fin_cases chunk <;> try (cases hNz rfl)
    all_goals interval_cases x <;> decide
  have hBound := stageVectorAddressBound hp g stage chunk
  rw [hA] at hBound
  rw [hA, hA, Nat.add_assoc, Nat.add_mod base, hStride,
    Nat.mod_eq_of_lt (a := base) (by omega), Nat.mod_eq_of_lt hBound]

private theorem vectorDefinitionStep (hp : Pre p l m) {g : Nat} {s u : TState} (stage : Fin 2)
    (chunk : Fin 8) (hPc : s.pc = stageVectorDefinition stage chunk) (hNz : chunk.val ≠ 0)
    (hClean : s.fault = none)
    (hParent : s.regs (outputStoreAddrReg stage (stageVectorParent chunk)) =
      some (b32 (stageVectorAddress l g stage (stageVectorParent chunk))))
    (hStride : s.regs (stageVectorStride chunk) = some (b32 (stageVectorStrideValue l g chunk)))
    (hTau : Tau kernel Assumptions.all l g s u) :
    u.regs (outputStoreAddrReg stage chunk) = some (b32 (stageVectorAddress l g stage chunk)) := by
  let d := outputStoreAddrReg stage chunk
  let a := stageVectorAddress l g stage (stageVectorParent chunk)
  let b := stageVectorStrideValue l g chunk
  let c := stageVectorAddress l g stage chunk
  let i : IntInstr := ⟨.add, .int .s 32, false, [some d],
    [.reg (outputStoreAddrReg stage (stageVectorParent chunk)), .reg (stageVectorStride chunk)]⟩
  have hLo : 8480 ≤ s.pc := by
    rw [hPc]
    fin_cases stage <;> fin_cases chunk <;> first | decide | cases hNz rfl
  have hCode : kernel.code[s.pc]? = some ⟨none, .int i⟩ := by
    rw [hPc]
    exact stageVectorDefinitionCode stage chunk hNz
  have ha : a < 2 ^ 32 := stageVectorAddressBound hp g stage _
  have hb : b < 2 ^ 32 := by
    simp only [b, stageVectorStrideValue]
    split
    · unfold finalizeVectorDelta; split <;> decide
    · split
      · change (if rowOf l g % 8 &&& 4 = 0 then 64 else 2 ^ 32 - 64) < 2 ^ 32
        split <;> decide
      · change (if rowOf l g % 8 &&& 2 = 0 then 32 else 2 ^ 32 - 32) < 2 ^ 32
        split <;> decide
  have hSum : truncBits 32 (BitVec.ofNat 64 a + BitVec.ofNat 64 b) = BitVec.ofNat 64 c := by
    rw [← BitVec.ofNat_add, truncBits, toNat_ofNat_lt (by omega), vectorStrideArithmetic hp]
    exact hNz
  have hExec : execLocalA Assumptions.all l g s (.int i) = .ok (next (setReg s d (b32 c))) := by
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil _ rfl]
    · change execInt l g s i = _
      change s.regs (outputStoreAddrReg stage (stageVectorParent chunk)) = some (b32 a)
        at hParent
      change s.regs (stageVectorStride chunk) = some (b32 b) at hStride
      simp only [i, execInt, DType.width, readValue, readReg, hParent, hStride, b32,
        readBits, pure, Except.pure, bind, Except.bind,
        truncBits_ofNat ha (by decide), truncBits_ofNat hb (by decide), hSum]
    · simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
  have hStep : tauStep kernel Assumptions.all l g s = some (next (setReg s d (b32 c))) :=
    tauStep_iff.mpr (out_tau hClean hCode rfl rfl hExec)
  obtain rfl := Option.some.inj ((tauStep_iff.mpr hTau).symm.trans hStep)
  exact Function.update_self ..

private def vectorRegisters : List (Fin 2 × Fin 8) :=
  (List.finRange 2).flatMap (fun stage => (List.finRange 8).map (fun chunk => (stage, chunk)))

private theorem vectorRegisterMem (stage : Fin 2) (chunk : Fin 8) :
    (stage, chunk) ∈ vectorRegisters := by
  simp only [vectorRegisters, List.mem_flatMap, List.mem_map]
  exact ⟨stage, List.mem_finRange _, chunk, List.mem_finRange _, rfl⟩

private def vectorWrites (op : Op) : List Nat := writesRegs op ++ scoreEventWrites op

private def vectorRegionCode (pc : Nat) (i : Instr) : Bool :=
  (i.op.isLocal || correctionReturningOp i.op) &&
  [6500, 6502, 6504].all (fun r => !(vectorWrites i.op).contains r) &&
  vectorRegisters.all (fun (stage, chunk) =>
    pc == stageVectorDefinition stage chunk || !(vectorWrites i.op).contains
      (outputStoreAddrReg stage chunk)) &&
  match i.op with
  | .bra dest _ => 8464 ≤ dest && dest ≤ 9205 &&
      vectorRegisters.all (fun (stage, chunk) =>
        decide (stageVectorDefinition stage chunk < dest →
          stageVectorDefinition stage chunk < pc))
  | .brx .. => false
  | _ => true

private theorem vectorRegionCodeAt {pc : Nat} {i : Instr} (hLo : 8464 ≤ pc) (hHi : pc < 9205)
    (hc : kernel.code[pc]? = some i) : vectorRegionCode pc i = true := by
  let region := ((kernel.code.drop 8464).take (9205 - 8464)).zipIdx 8464
  have hRegion : region.all (fun (ins, site) => vectorRegionCode site ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hRegion (i, pc)
  apply List.mem_of_getElem? (i := pc - 8464)
  dsimp only [region]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

/-- The lane has computed all earlier swizzled vector bases and is in the staging suffix. -/
@[no_expose] def StagingVectorState (l : Launch) (g : Nat) (s : TState) : Prop :=
  8464 ≤ s.pc ∧ s.pc ≤ 9205 ∧ s.sub ≤ 3 ∧ Holds s.regs (finalizeDeltas l g) ∧
  ∀ stage chunk, stageVectorDefinition stage chunk < s.pc →
    s.regs (outputStoreAddrReg stage chunk) = some (b32 (stageVectorAddress l g stage chunk))

private theorem vectorFrameStep (hp : Pre p l m) {g : Nat} {s u : TState} {e : Option Event}
    (hFrame : StagingVectorState l g s) (hEnd : s.pc < 9205)
    (hStep : WStep kernel Assumptions.all l g s e u) : StagingVectorState l g u := by
  rcases hFrame with ⟨hLo, hHi, hSub, hDeltas, hAddresses⟩
  have hTable {i : Instr} (hc : kernel.code[s.pc]? = some i) :=
    vectorRegionCodeAt hLo hEnd hc
  have hDelta {i : Instr} (hc : kernel.code[s.pc]? = some i) {r : Nat}
      (hr : r ∈ [6500, 6502, 6504]) : r ∉ vectorWrites i.op := by
    have h := hTable hc
    simp only [vectorRegionCode, Bool.and_eq_true] at h
    simpa using List.all_eq_true.mp h.1.1.2 r hr
  have finish {i : Instr} (hc : kernel.code[s.pc]? = some i)
      (hPc : 8464 ≤ u.pc ∧ u.pc ≤ 9205) (huSub : u.sub ≤ 3)
      (hReg : ∀ r, r ∉ vectorWrites i.op → u.regs r = s.regs r)
      (hScope : ∀ stage chunk, stageVectorDefinition stage chunk < u.pc →
        s.pc = stageVectorDefinition stage chunk ∨ stageVectorDefinition stage chunk < s.pc)
      (hNew : ∀ stage chunk, s.pc = stageVectorDefinition stage chunk →
        u.regs (outputStoreAddrReg stage chunk) =
          some (b32 (stageVectorAddress l g stage chunk))) : StagingVectorState l g u := by
    refine ⟨hPc.1, hPc.2, huSub, ?_, ?_⟩
    · exact ⟨(hReg _ (hDelta hc (by simp))).trans hDeltas.1,
        (hReg _ (hDelta hc (by simp))).trans hDeltas.2.1,
        (hReg _ (hDelta hc (by simp))).trans hDeltas.2.2.1, trivial⟩
    · intro stage chunk hTarget
      rcases hScope stage chunk hTarget with he | he
      · exact hNew stage chunk he
      · have h := hTable hc
        simp only [vectorRegionCode, Bool.and_eq_true] at h
        have hKeep := List.all_eq_true.mp h.1.2 (stage, chunk) (vectorRegisterMem stage chunk)
        dsimp only at hKeep
        have hNe : s.pc ≠ stageVectorDefinition stage chunk := by omega
        exact (hReg _ (by simpa [hNe] using hKeep)).trans (hAddresses stage chunk he)
  have hNonzero (stage : Fin 2) (chunk : Fin 8) (he : s.pc = stageVectorDefinition stage chunk) :
      chunk.val ≠ 0 := by
    intro hz
    unfold stageVectorDefinition at he
    rw [ite_eq_left hz] at he
    split at he <;> omega
  rcases hStep with ⟨_, ht⟩ | ⟨_, _, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, hClean, hTau⟩ := correctionTauFrame hOff ht
    have hNew (stage : Fin 2) (chunk : Fin 8)
        (he : s.pc = stageVectorDefinition stage chunk) :
        u.regs (outputStoreAddrReg stage chunk) =
          some (b32 (stageVectorAddress l g stage chunk)) := by
      have hn := hNonzero stage chunk he
      have hPrior : stageVectorDefinition stage (stageVectorParent chunk) < s.pc := by
        rw [he]
        fin_cases stage <;> fin_cases chunk <;> first | decide | exact (hn rfl).elim
      have hStride : s.regs (stageVectorStride chunk) =
          some (b32 (stageVectorStrideValue l g chunk)) := by
        simp only [stageVectorStride, stageVectorStrideValue]
        split
        · exact hDeltas.1
        · split
          · exact hDeltas.2.2.1
          · exact hDeltas.2.1
      exact vectorDefinitionStep hp stage chunk he hn hClean
        (hAddresses stage _ hPrior) hStride ht
    rcases hTau with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
    · refine finish hc (by change 8464 ≤ s.pc + 1 ∧ s.pc + 1 ≤ 9205; omega)
        (by simp [skip]) (fun _ _ => rfl) ?_ hNew
      intro stage chunk
      change stageVectorDefinition stage chunk < s.pc + 1 → _
      omega
    have hPc := hLocal.pc
    have hCheck := hTable hc
    simp only [vectorRegionCode, Bool.and_eq_true] at hCheck
    refine finish hc ?_ (hLocal.sub.symm ▸ hSub)
      (fun r hr => hLocal.regs r (fun hm => hr (List.mem_append_left _ hm))) ?_ hNew
    · cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
      case bra dest uni =>
        simp only [ho, Bool.and_eq_true, decide_eq_true_eq] at hCheck
        omega
      case brx => simp [ho] at hCheck
      all_goals omega
    · intro stage chunk hTarget
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
      case bra dest uni =>
        have hBranch := hCheck.2
        simp only [ho, Bool.and_eq_true, decide_eq_true_eq] at hBranch
        have h := List.all_eq_true.mp hBranch.2 (stage, chunk) (vectorRegisterMem stage chunk)
        exact .inr (of_decide_eq_true h (hPc ▸ hTarget))
      case brx => simp [ho] at hCheck
      all_goals omega
  · obtain ⟨i, hc, hLocal, _⟩ := estep_event_source he
    have hCheck := hTable hc
    simp only [vectorRegionCode, Bool.and_eq_true, hLocal, Bool.false_or] at hCheck
    obtain ⟨hProg, _⟩ := correctionEventProgress (r := 6500) hc hCheck.1.1.1 hSub
      (fun h => hDelta hc (by simp) (List.mem_append_right _ h)) he
    have hPc : u.pc = s.pc ∨ u.pc = s.pc + 1 :=
      hProg.pc.elim (fun h => .inr h.1) (fun h => .inl h.1)
    refine finish hc (by omega) hProg.sub (fun r hr =>
      (correctionEventProgress hc hCheck.1.1.1 hSub
        (fun h => hr (List.mem_append_right _ h)) he).2) ?_ ?_
    · intro stage chunk hTarget
      omega
    · intro stage chunk hPc
      rw [hPc, stageVectorDefinitionCode stage chunk (hNonzero stage chunk hPc)] at hc
      obtain rfl := Option.some.inj hc.symm
      cases hLocal

/-- The staging register invariant starts at the decoded final-layout exit. -/
theorem StagingVectorState.ofLayout {l : Launch} {g : Nat} {t : TState}
    (h : At t 8464 (finalizeLayoutFacts l g)) : StagingVectorState l g t := by
  refine ⟨h.1.ge, by rw [h.1]; decide, by rw [h.2.1]; decide, ?_, ?_⟩
  · exact h.2.2.2.2.2.2.2
  · intro stage chunk hSource
    rw [h.1] at hSource
    have hZero : chunk.val = 0 := by
      fin_cases stage <;> fin_cases chunk <;>
        first | rfl | exact ((by decide : ¬ _ < 8464) hSource).elim
    have hc : chunk = 0 := Fin.ext hZero
    subst chunk
    fin_cases stage
    · exact h.2.2.2.2.2.2.1
    · exact h.2.2.2.2.2.1

/-- Each actual continuation preserves the geometry of the computed staging vectors. -/
theorem StagingVectorState.step {g : Nat} {s u : TState} {e : Option Event} (hp : Pre p l m)
    (h : StagingVectorState l g s) (hEnd : s.pc < 9205)
    (he : WStep kernel Assumptions.all l g s e u) :
    StagingVectorState l g u :=
  vectorFrameStep hp h hEnd he

/-- A write fired by a thread in the staging suffix has its exact swizzled element footprint. -/
theorem StagingVectorState.element {g : Nat} {s : TState} {o : Option TState} {a : Acc}
    {bytes : List Byte} (hp : Pre p l m) (h : StagingVectorState l g s) (stage : Fin 2)
    (subbox : Fin 4) (chunk : Fin 8)
    (he : EStep kernel Assumptions.all l g s ⟨outputStorePc stage subbox chunk, .wr a bytes⟩ o) :
    ∃ elem : Fin 4, a = outputElementAccess l g stage subbox
      (4 * chunk.val + elem.val) (rowOf l g) := by
  apply stagingWriteElementOfAddress hp stage subbox chunk he
  have hPrior : stageVectorDefinition stage chunk < outputStorePc stage subbox chunk := by
    fin_cases stage <;> fin_cases subbox <;> fin_cases chunk <;> decide
  exact h.2.2.2.2 stage chunk ((estep_source_pc he) ▸ hPrior)

end
end PTX.Kernels.TmlFa4Fwd.Thread.Correction
