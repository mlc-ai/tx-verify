-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalizePrefix
public import Kernels.TmlFa4Fwd.Proof.MmaRoleSetup
public import Kernels.TmlFa4Fwd.Proof.MmaScanPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Mma Softmax

noncomputable section

def correctionSearch (drain : Bool) : GroupScan :=
  if drain then .correctionDrain else .correctionSelect

def searchLo (drain : Bool) : Nat := (scanSite (correctionSearch drain)).head
def searchHi (drain : Bool) : Nat := (scanSite (correctionSearch drain)).compare + 3

private def correctionSearchCode (drain : Bool) (pair : Instr × Nat) : Bool :=
  let ins := pair.1
  (ins.op.isLocal || correctionReturningOp ins.op) &&
    !(Assumptions.swExp2Sites.contains pair.2) &&
    !(scoreEventWrites ins.op).contains 1618 && !(writesRegs ins.op).contains 1618 &&
    (match ins.op with
      | .bra dst _ => searchLo drain ≤ dst && dst ≤ searchHi drain
      | .brx .. => false
      | _ => true)

private theorem searchCodeAt (drain : Bool) {pc : Nat} {ins : Instr}
    (hLo : searchLo drain ≤ pc) (hHi : pc < searchHi drain)
    (hc : kernel.code[pc]? = some ins) : correctionSearchCode drain (ins, pc) = true := by
  let code := ((kernel.code.drop (searchLo drain)).take
    (searchHi drain - searchLo drain)).zipIdx (searchLo drain)
  have hAll : code.all (correctionSearchCode drain) = true := by
    cases drain <;> set_option maxRecDepth 100000 in kernel_rfl
  have hm : (ins, pc) ∈ code := by
    apply List.mem_of_getElem? (i := pc - searchLo drain)
    dsimp only [code]
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hLo, hc]
    rfl
  exact List.all_eq_true.mp hAll _ hm

private theorem healthyReturningEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (he : EStep kernel Assumptions.all l g s e (some u)) : s.fault = none := by
  cases h : s.fault
  · rfl
  · obtain ⟨m, hm, hf⟩ := he
    simp only [out, h, Out.ev.injEq] at hm
    subst m
    cases hf.2

private theorem searchStep (drain : Bool) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hLo : searchLo drain ≤ s.pc) (hHi : s.pc < searchHi drain)
    (hSub : s.sub ≤ 3) (he : WStep kernel Assumptions.all l g s e u) :
    (searchLo drain ≤ u.pc ∧ u.pc < searchHi drain ∨
      u.pc ∈ [searchHi drain] ∧ u.fault = none) ∧
      u.sub ≤ 3 ∧ u.regs 1618 = s.regs 1618 := by
  have destination (hl : searchLo drain ≤ u.pc) (hh : u.pc ≤ searchHi drain)
      (hf : u.fault = none) :
      searchLo drain ≤ u.pc ∧ u.pc < searchHi drain ∨
        u.pc ∈ [searchHi drain] ∧ u.fault = none := by
    by_cases h : u.pc < searchHi drain
    · exact .inl ⟨hl, h⟩
    · exact .inr ⟨List.mem_singleton.mpr (by omega), hf⟩
  rcases he with ⟨_, ht⟩ | ⟨e, _, he⟩
  · have hExp : s.pc ∉ Assumptions.swExp2Sites := by
      obtain ⟨ins, hc⟩ : ∃ ins, kernel.code[s.pc]? = some ins := by
        unfold Tau out at ht
        cases hf : s.fault <;> cases hc : kernel.code[s.pc]? <;> simp_all
      have hCode := searchCodeAt drain hLo hHi hc
      simp only [correctionSearchCode, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not] at hCode
      exact hCode.1.1.1.2
    obtain ⟨ins, hc, hF, hLocal⟩ := correctionTauFrame hExp ht
    have hCode := searchCodeAt drain hLo hHi hc
    simp only [correctionSearchCode, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hCode
    rcases hLocal with ⟨rfl, _⟩ | ⟨_, _, hFrame⟩
    · have hp : (skip s).pc = s.pc + 1 := rfl
      exact ⟨destination (by omega) (by omega) hF, Nat.zero_le _, rfl⟩
    · have hPC := hFrame.pc
      have hDst : searchLo drain ≤ u.pc ∧ u.pc ≤ searchHi drain := by
        cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hPC
        case bra dst aligned =>
          rw [hPC]
          simpa [hop] using hCode.2
        case brx => simp [hop] at hCode
        all_goals omega
      exact ⟨destination hDst.1 hDst.2 (hFrame.fault.trans hF), hFrame.sub ▸ hSub,
        hFrame.regs _ hCode.1.2⟩
  · obtain ⟨ins, hc, hLocal, _⟩ := estep_event_source he
    have hCode := searchCodeAt drain hLo hHi hc
    simp only [correctionSearchCode, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not, hLocal, Bool.false_or] at hCode
    obtain ⟨hP, hKeep⟩ := correctionEventProgress hc hCode.1.1.1.1 hSub hCode.1.1.2 he
    rcases hP.pc with ⟨hp, hf⟩ | ⟨hp, _⟩
    · exact ⟨destination (by omega) (by omega) (hf.trans (healthyReturningEvent he)),
        hP.sub, hKeep⟩
    · exact ⟨.inl ⟨hp ▸ hLo, hp ▸ hHi⟩, hP.sub, hKeep⟩

/-- Both request scans retain their decoded CTA and count at most one batch-size budget
before entering the following linear region. -/
theorem cutCorrectionSearch (drain : Bool) {l : Launch} {g batch cta : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (hBatch : batch + 31 < 2 ^ 31) (hCta : cta + 1 < 2 ^ 31)
    (hs : At s (searchLo drain) (groupScanFacts (correctionSearch drain) 0 batch cta))
    (hw : Walk kernel Assumptions.all l g s events visits) :
    countedUntil 9206 visits ≤ 64 * (batch + 1) ∨
    ∃ u rest tail, u.pc = searchHi drain ∧ u.sub ≤ 3 ∧ u.fault = none ∧
      u.regs 1618 = some (b32 cta) ∧ Walk kernel Assumptions.all l g u rest tail ∧
      countedUntil 9206 visits ≤ 64 * (batch + 1) + countedUntil 9206 tail := by
  have hB : countedUntil (searchHi drain) visits ≤ 64 * (batch + 1) := by
    simpa only [searchHi, Nat.sub_zero] using
      groupScanPrefixBound (correctionSearch drain) hBatch hCta (Nat.zero_le _) hs hw
  have hReg : s.regs 1618 = some (b32 cta) := by
    cases drain <;> exact hs.2.2.2.2.2.2.2.1
  have hSub : s.sub ≤ 3 := by rw [hs.2.1]; decide
  have hLt : s.pc < searchHi drain := by rw [hs.1]; cases drain <;> decide
  have hCut : searchHi drain ≤ 9206 := by cases drain <;> decide
  rcases cutWalkInterval (P := fun u => u.sub ≤ 3 ∧ u.regs 1618 = some (b32 cta))
      hw hs.1.ge hLt ⟨hSub, hReg⟩ hCut (fun hl hh he hu => by
        obtain ⟨h, hS, hR⟩ := searchStep drain hl hh hu.1 he
        exact ⟨h, hS, hR.trans hu.2⟩) with h | ⟨u, rest, tail, hp, hf, hu, hw, hb⟩
  · exact .inl (h.trans hB)
  · exact .inr ⟨u, rest, tail, List.mem_singleton.mp hp, hu.1, hf, hu.2, hw,
      hb.trans (Nat.add_le_add_right hB _)⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
