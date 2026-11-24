-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaGeometry
public import Kernels.TmlFa4Fwd.Proof.MmaModel
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
public import Lemmas.Flow.TcTmpl
public import Kernels.TmlFa4Fwd.Flow.Code.Part034
public import Kernels.TmlFa4Fwd.Flow.Code.Part035
public import Kernels.TmlFa4Fwd.Flow.Code.Part037
public import Kernels.TmlFa4Fwd.Flow.Code.Part039

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

/-- The two prologue and two loop copies of the QK assembly. -/
def qkPc : Fin 4 → Nat
  | 0 => 2197
  | 1 => 2259
  | 2 => 2407
  | 3 => 2508

def qkGuard : Fin 4 → Nat
  | 0 => 9636
  | 1 => 9653
  | 2 => 9682
  | 3 => 9709

def qkDestination : Fin 4 → Nat
  | 0 => 9638
  | 1 => 9655
  | 2 => 9684
  | 3 => 9711

def qkBReg : Fin 4 → Nat
  | 0 => 9644
  | 1 => 9661
  | 2 => 9690
  | 3 => 9717

def qkStage (block : Fin 4) : Fin 2 := ⟨block.val % 2, Nat.mod_lt _ (by decide)⟩

/-- Project the fields of an MMA instruction, whose syntax has decidable equality. -/
def mmaFields : Instr → Option (Option (Nat × Bool) × TcMmaInstr)
  | ⟨guard, .tcMma mma⟩ => some (guard,mma)
  | _ => none

/-- Equality of the decoded MMA fields determines the complete instruction. -/
theorem codeOfMmaFields {pos : Nat} {guard : Option (Nat × Bool)} {mma : TcMmaInstr}
    (h : (kernel.code[pos]?).bind mmaFields = some (guard,mma)) :
    kernel.code[pos]? = some ⟨guard, .tcMma mma⟩ := by
  obtain ⟨⟨g,op⟩,hCode,hMma⟩ := Option.bind_eq_some_iff.mp h
  cases op <;> simp only [mmaFields, reduceCtorEq] at hMma
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hMma)
  exact hCode

private def qkMma (block : Fin 4) (step : Fin 8) : TcMmaInstr :=
  .dense .one false .f16 (qkDestination block) (.smem (.reg (9624 + step.val)))
    (.reg (qkBReg block + step.val)) (.reg 9632) (List.replicate 4 (.imm 0))
    (.imm (if step.val = 0 then 0 else 1))

private theorem qkCodeAudit : ∀ (block : Fin 4) (step : Fin 8),
    (kernel.code[qkPc block + step.val]?).bind mmaFields =
      some (some (qkGuard block, false), qkMma block step) := by
  decide +kernel

/-- All 32 QK instructions use the same shape and the stage's first instruction clears D. -/
theorem qkCode (block : Fin 4) (step : Fin 8) :
    kernel.code[qkPc block + step.val]? = some ⟨some (qkGuard block, false),
      .tcMma (.dense .one false .f16 (qkDestination block) (.smem (.reg (9624 + step.val)))
        (.reg (qkBReg block + step.val)) (.reg 9632) (List.replicate 4 (.imm 0))
        (.imm (if step.val = 0 then 0 else 1)))⟩ :=
  codeOfMmaFields (qkCodeAudit block step)

/-- The producer and consumer use the physical fragment layouts of the selected Q stage and K
ring slot. This descriptor records only addresses, independently of the values read later. -/
def qkOperands (l : Launch) (g : Nat) (block : Fin 4) (step : Fin 8) (kvUse : Nat) :
    TcMma.OperandSpec :=
  ⟨qkDescriptor, sharedDescriptor (qStart l (qkStage block) + qkFragment step) 16,
    sharedDescriptor (kvStart l kvUse + qkFragment step) 16, g / l.block, g / l.block, none, {}⟩

/-- Facts for the instruction issued by the elected lane, shared by all four QK blocks. -/
def qkIssueFacts (l : Launch) (block : Fin 4) (step : Fin 8) (kvUse : Nat) :
    List (Nat × Value) :=
  [(qkGuard block, .pred true), (qkDestination block, b32 (scoreColumn (qkStage block))),
    (9624 + step.val, b64 (sharedDescriptorWord (qStart l (qkStage block) + qkFragment step) 16)),
    (qkBReg block + step.val, b64 (sharedDescriptorWord (kvStart l kvUse + qkFragment step) 16)),
    (9632, b32 0x8200490)]

theorem singleCtaGroup {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) : l.ctaGroup (g / l.block) .one = some [g / l.block] := by
  have hBlock : 0 < l.block := by rw [hp.block]; decide
  have hCta := (Nat.div_lt_iff_lt_mul hBlock).2 (show g < l.grid * l.block from hg)
  have hOne := hp.cluster.2.2
  have hSize := hp.cluster.1
  rw [Launch.ctaGroup_one]
  simp [Launch.peerCta, Launch.oneDim_rankOfCta hOne, Launch.oneDim_clusterOfCta hOne,
    Launch.oneDim_clusterSizeOf hOne, Launch.oneDim_clusterStart hOne, hSize, Nat.mod_one, hCta]

private theorem qkMmaTemplate {l : Launch} {g d a b id : Nat} {t : TState}
    {qword kword : BitVec 64} {qd kd : TcShared.Descriptor} {dst : Nat} {en : Opnd} {acc : Bool}
    {spec : TcMma.OperandSpec} (hg : g < l.threads)
    (hD : readBits l g t 32 (.reg d) = .ok (BitVec.ofNat 64 dst)) (hDst : dst < 2 ^ 64)
    (hQ : readBits l g t 64 (.reg a) = .ok qword)
    (hK : readBits l g t 64 (.reg b) = .ok kword)
    (hId : readBits l g t 32 (.reg id) = .ok (BitVec.ofNat 64 0x8200490))
    (hEnable : mmaEnable t en = .ok acc) (hQD : TcShared.decode qword.toNat = some qd)
    (hKD : TcShared.decode kword.toNat = some kd)
    (hSpec : TcMma.makeOperands l (g / l.block) qkDescriptor qd kd = some spec)
    (hCollector : spec.collector = {}) :
    mmaSmemTmpl l g t .one false .f16 d (.reg a) (.reg b) (.reg id)
      (List.replicate 4 (.imm 0)) en none {} =
        .tc (.mma dst spec acc (List.replicate 4 0)) (next t) := by
  have hMask : (List.replicate 4 (.imm 0)).mapM (readBits l g t 32) = .ok (List.replicate 4 0) :=
    rfl
  have hIdBits : (BitVec.ofNat 64 0x8200490).toNat = 0x8200490 := rfl
  have hUpdate : { spec with collector := {} } = spec := by
    cases spec
    simp_all
  simp only [mmaSmemTmpl, hg, hD, hQ, hK, hId, hMask, hEnable, zeroColumnMaskOk,
    List.length_replicate, CtaGroup.size, Nat.reduceMul, ↓reduceIte, bind, Except.bind, pure,
    Except.pure, ofExec, toNat_ofNat_lt hDst, hIdBits, hQD, hKD, qkDescriptor_decode, hSpec,
    hUpdate]
  rfl

private theorem qkAddressBounds {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (stage : Fin 2) (step : Fin 8) (use : Nat) :
    let q := qStart l stage + qkFragment step
    let k := kvStart l use + qkFragment step
    q < 2 ^ 18 ∧ k < 2 ^ 18 ∧ q % 16 = 0 ∧ k % 16 = 0 := by
  have hShared := hp.shared.2.1
  have hAlign := hp.shared.1
  have hStage := stage.isLt
  have hSlot : kvSlot use < 3 := Nat.mod_lt _ (by decide)
  have hFrag : qkFragment step ≤ 16480 := by fin_cases step <;> decide
  have hFrag16 : qkFragment step % 16 = 0 := by fin_cases step <;> decide
  dsimp only [qStart, kvStart]
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- One decoded QK instruction issues the verified same-CTA operands and score columns. -/
theorem qkIssueOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) (block : Fin 4) (step : Fin 8) (kvUse : Nat)
    {t : TState} (ht : At t (qkPc block + step.val) (qkIssueFacts l block step kvUse)) :
    out kernel Assumptions.all l g t =
      .ev (.tc (.mma (scoreColumn (qkStage block)) (qkOperands l g block step kvUse)
        (decide (step.val ≠ 0)) (List.replicate 4 0)) (next t)) := by
  let q := qStart l (qkStage block) + qkFragment step
  let k := kvStart l kvUse + qkFragment step
  have hCode := qkCode block step
  rw [← ht.1] at hCode
  have hLo : 2197 ≤ t.pc := by
    rw [ht.1]
    fin_cases block <;> simp [qkPc] <;> omega
  have hHi : t.pc < 2516 := by
    rw [ht.1]
    have hs := step.isLt
    fin_cases block <;> simp [qkPc] <;> omega
  have hGuard : guardHolds t (some (qkGuard block, false)) = .ok true := by
    simp [guardHolds, readReg, ht.2.2.2.2.1, bind, Except.bind, pure, Except.pure]
  rw [out_eq_core (by omega) (by omega), out_event ht.2.2.2.1 hCode hGuard rfl]
  change Out.ev (mmaSmemTmpl l g t .one false .f16 (qkDestination block)
    (.reg (9624 + step.val)) (.reg (qkBReg block + step.val)) (.reg 9632)
    (List.replicate 4 (.imm 0)) (.imm (if step.val = 0 then 0 else 1)) none {}) = _
  have ⟨hQ, hK, hQ16, hK16⟩ := qkAddressBounds hp (qkStage block) step kvUse
  have hQ64 := sharedDescriptorWord_lt hQ hQ16 (Or.inl rfl)
  have hK64 := sharedDescriptorWord_lt hK hK16 (Or.inl rfl)
  have hD32 : scoreColumn (qkStage block) < 2 ^ 32 := by unfold scoreColumn; omega
  have hD64 : scoreColumn (qkStage block) < 2 ^ 64 := by omega
  have hs := ht.2.2.2.2
  have hD : readBits l g t 32 (.reg (qkDestination block)) =
      .ok (BitVec.ofNat 64 (scoreColumn (qkStage block))) := readBits_b32 hs.2.1 hD32
  have ha : readBits l g t 64 (.reg (9624 + step.val)) =
      .ok (BitVec.ofNat 64 (sharedDescriptorWord q 16)) := readBits_b64 hs.2.2.1 hQ64
  have hb : readBits l g t 64 (.reg (qkBReg block + step.val)) =
      .ok (BitVec.ofNat 64 (sharedDescriptorWord k 16)) := readBits_b64 hs.2.2.2.1 hK64
  have hi : readBits l g t 32 (.reg 9632) = .ok (BitVec.ofNat 64 0x8200490) :=
    readBits_b32 hs.2.2.2.2.1 (by decide)
  have hEnable : mmaEnable t (.imm (if step.val = 0 then 0 else 1)) =
      .ok (decide (step.val ≠ 0)) := by
    by_cases h : step.val = 0 <;> simp [mmaEnable, h, pure, Except.pure]
  have hCta : TcMma.makeOperands l (g / l.block) qkDescriptor (sharedDescriptor q 16)
      (sharedDescriptor k 16) = some (qkOperands l g block step kvUse) := by
    simp [TcMma.makeOperands, qkDescriptor, qkOperands, q, k, singleCtaGroup hp hg]
  have hQD : TcShared.decode (BitVec.ofNat 64 (sharedDescriptorWord q 16)).toNat =
      some (sharedDescriptor q 16) := by
    rw [toNat_ofNat_lt hQ64]
    exact sharedDescriptor_decode hQ hQ16 (Or.inl rfl)
  have hKD : TcShared.decode (BitVec.ofNat 64 (sharedDescriptorWord k 16)).toNat =
      some (sharedDescriptor k 16) := by
    rw [toNat_ofNat_lt hK64]
    exact sharedDescriptor_decode hK hK16 (Or.inl rfl)
  exact congrArg Out.ev (qkMmaTemplate hg hD hD64 ha hb hi hEnable hQD hKD hCta rfl)

/-- The normalized event specified by the decoded QK operands. -/
def qkIssueEvent (l : Launch) (g : Nat) (block : Fin 4) (step : Fin 8) (kvUse : Nat) : Event :=
  ⟨qkPc block + step.val, .tc (.mma (scoreColumn (qkStage block))
    (qkOperands l g block step kvUse) (decide (step.val ≠ 0)) (List.replicate 4 0))⟩

end PTX.Kernels.TmlFa4Fwd.Mma
