-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionSearchSetupPrefix
public import Kernels.TmlFa4Fwd.Proof.CorrectionPostSearchPrefix
public import Kernels.TmlFa4Fwd.Proof.CountedVisits
public import Kernels.TmlFa4Fwd.Proof.NonzeroTraceBound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Mma Softmax

noncomputable section

private def tileFrameCode (i : Instr) : Bool :=
  (i.op.isLocal || correctionReturningOp i.op) &&
    !(writesRegs i.op).contains 1618 && !(scoreEventWrites i.op).contains 1618 &&
    (match i.op with
      | .bra dst _ => 7864 ≤ dst && (dst ≤ 9083 || dst == 9201)
      | .brx .. => false
      | _ => true)

private theorem tileFrameAt {pc : Nat} {i : Instr}
    (hLo : 7864 ≤ pc) (hHi : pc < 9083) (hc : kernel.code[pc]? = some i) :
    tileFrameCode i = true := by
  have hall : ((kernel.code.drop 7864).take (9083 - 7864)).all tileFrameCode = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hall i
  apply List.mem_of_getElem? (i := pc - 7864)
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo, hc]

private theorem tileFrameStep {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 7864 ≤ s.pc) (hHi : s.pc < 9083) (he : WStep kernel Assumptions.all l g s e u)
    (hSub : s.sub ≤ 3) :
    (7864 ≤ u.pc ∧ u.pc < 9083 ∨ u.pc ∈ [9083, 9201] ∧ u.fault = none) ∧
      u.sub ≤ 3 ∧ u.regs 1618 = s.regs 1618 := by
  have hNext (hPc : u.pc = s.pc + 1) (hf : u.fault = none) :
      7864 ≤ u.pc ∧ u.pc < 9083 ∨ u.pc ∈ [9083, 9201] ∧ u.fault = none := by
    by_cases h : u.pc < 9083
    · exact .inl ⟨by omega, h⟩
    · exact .inr ⟨by simp; omega, hf⟩
  rcases he with ⟨_, ht⟩ | ⟨e, _, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, hf, hTau⟩ := correctionTauFrame hOff ht
    have hCode := tileFrameAt hLo hHi hc
    simp only [tileFrameCode, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hCode
    rcases hTau with ⟨rfl, _⟩ | ⟨_, _, hFrame⟩
    · exact ⟨hNext rfl hf, Nat.zero_le _, rfl⟩
    have hPc := hFrame.pc
    have hFault := hFrame.fault.trans hf
    refine ⟨?_, hFrame.sub ▸ hSub, hFrame.regs _ hCode.1.1.2⟩
    cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
    case bra dst aligned =>
      have hDst : 7864 ≤ dst ∧ (dst ≤ 9083 ∨ dst = 9201) := by simpa [ho] using hCode.2
      rw [hPc]
      by_cases h : dst < 9083
      · exact .inl ⟨hDst.1, h⟩
      · exact .inr ⟨by simp; omega, hFault⟩
    case brx => simp [ho] at hCode
    all_goals exact hNext hPc hFault
  · obtain ⟨i, hc, hl, _⟩ := estep_event_source he
    have hCode := tileFrameAt hLo hHi hc
    simp only [tileFrameCode, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not, hl, Bool.false_or] at hCode
    obtain ⟨hP, hReg⟩ := correctionEventProgress hc hCode.1.1.1 hSub hCode.1.2 he
    refine ⟨?_, hP.sub, hReg⟩
    rcases hP.pc with ⟨hPc, hf⟩ | ⟨hPc, _⟩
    · have hS : s.fault = none := by
        cases h : s.fault
        · rfl
        · obtain ⟨m, hm, hFire⟩ := he
          simp only [out, h, Out.ev.injEq] at hm
          subst m
          cases hFire.2
      exact hNext hPc (hf.trans hS)
    · exact .inl ⟨by omega, by omega⟩

private theorem correctionTileCount {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hp : s.pc = 7864) (hs : s.sub ≤ 3) : countedUntil 9083 vs ≤ correctionTileBudget := by
  rcases cutCorrectionTilePrefix hp hs (.inl rfl) hw with h | ⟨u, es, vs', hu, _, _, hW, hB⟩
  · exact h
  · have hZ := countedPastCut (by omega : ¬ u.pc < 9083) hW
    omega

variable {p : Params} {l : Launch} {m : Mem0}

private theorem correctionDrainCount (hp : Pre p l m) {g : Nat} (hCta : g / l.block + 1 < 2 ^ 31)
    {s : TState} {es : List Event} {vs : List Visit} (hPc : s.pc = 9083) (hSub : s.sub ≤ 3)
    (hF : s.fault = none) (hR : s.regs 1618 = some (b32 (g / l.block)))
    (hw : Walk kernel Assumptions.all l g s es vs) :
    countedUntil 9206 vs ≤ 64 * (p.batch + 1) + 399 := by
  rcases cutCorrectionSearchFromParam hp true hCta hPc hF hSub (fun _ => hR) hw with
    h | ⟨u, es, vs', hu, huS, _, _, hW, hB⟩
  · exact h.trans (by omega)
  · have h := correctionPostDrainPrefix hu huS hW
    omega

private theorem correctionSelectedCount (hp : Pre p l m) {g : Nat} (hCta : g / l.block + 1 < 2 ^ 31)
    {s : TState} {es : List Event} {vs : List Visit} (hPc : s.pc = 7864) (hSub : s.sub ≤ 3)
    (hR : s.regs 1618 = some (b32 (g / l.block))) (hw : Walk kernel Assumptions.all l g s es vs) :
    countedUntil 9206 vs ≤ correctionTileBudget + 64 * (p.batch + 1) + 399 := by
  have hN := correctionTileCount hw hPc hSub
  rcases cutWalkInterval (P := fun u => u.sub ≤ 3 ∧ u.regs 1618 = some (b32 (g / l.block)))
      (cutoff := 9206) hw hPc.ge (by omega : s.pc < 9083)
      ⟨hSub, hR⟩ (by decide) (by
        intro t u e hl hh he h
        obtain ⟨hD, hS, hC⟩ := tileFrameStep hl hh he h.1
        exact ⟨hD, hS, hC.trans h.2⟩) with h | ⟨u, es, vs', hu, hf, hs, hW, hB⟩
  · omega
  · have hExitPc : u.pc = 9083 ∨ u.pc = 9201 := by simpa using hu
    rcases hExitPc with h | h
    · have hDrain := correctionDrainCount hp hCta h hs.1 hf hs.2 hW
      omega
    · have hExit := correctionExitPrefix h hs.1 hW
      omega

/-- The correction role's entire finite instruction walk from its actual ABI entry is bounded.
The bound accounts for both request lookups, rescale, finalize, and the exit path. -/
theorem correctionRolePrefixBound (hp : Pre p l m) {g : Nat} (hCta : g / l.block + 1 < 2 ^ 31)
    {s : TState} {es : List Event} {vs : List Visit} (hPc : s.pc = 7745) (hSub : s.sub ≤ 3)
    (hF : s.fault = none) (hw : Walk kernel Assumptions.all l g s es vs) :
    countedUntil 9206 vs ≤ correctionTileBudget + 128 * (p.batch + 1) + 709 := by
  rcases cutCorrectionSearchFromParam hp false hCta hPc hF hSub (by intro h; cases h) hw with
    h | ⟨u, es, vs', hu, huS, _, huR, hW, hB⟩
  · omega
  · have hTile := correctionSelectedCount hp hCta hu huS huR hW
    omega

/-- The correction warp's count bound starts at the actual common-barrier continuation. -/
theorem correctionRolePrefixFromDispatch (hp : Pre p l m) {g : Nat} (hg : g < l.threads)
    (warp : Fin 16) (hLo : 8 ≤ warp.val) (hHi : warp.val < 12) {s : TState} {es : List Event}
    {vs : List Visit} (hs : At s 174 [(1062, b32 warp.val), (2535, b32 l.sharedBase)])
    (hw : Walk kernel Assumptions.all l g s es vs) :
    es.countP Event.counts ≤ correctionTileBudget + 128 * (p.batch + 1) + 710 := by
  obtain ⟨u, hu, huAt⟩ := Prologue.dispatchRunFromCommon hp warp hg hs
  have hGrid : g / l.block < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hCta : g / l.block + 1 < 2 ^ 31 := (Nat.succ_le_of_lt hGrid).trans_lt hp.grid.2.2
  have hPc : u.pc = 7745 := by
    have h := huAt.1
    change u.pc = (if 14 ≤ warp.val then 178 else if warp.val = 13 then 2768
      else if warp.val = 12 then 1906 else if warp.val < 8 then 3101 else 7745) at h
    have h14 : ¬ 14 ≤ warp.val := by omega
    have h13 : warp.val ≠ 13 := by omega
    have h12 : warp.val ≠ 12 := by omega
    have h8 : ¬ warp.val < 8 := by omega
    simpa only [h14, h13, h12, h8, ↓reduceIte] using h
  rcases advanceWalkLocals hu hw with h | ⟨post, _, hCount, hW⟩
  · subst es
    simp
  · have hBound := correctionRolePrefixBound hp hCta hPc (by rw [huAt.2.1]; decide)
        huAt.2.2.2.1 hW
    have hTotal := countedThroughCode hw
    rw [Decoded.code_length] at hTotal
    have hCount' := hCount 9206
    omega


/-- A consistent lane trace in a correction warp is bounded even when the CTA is unfinished. -/
theorem correctionLaneTraceBound {X : Execution} {g : Nat} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hg : g < l.threads)
    (hLo : 8 ≤ Prologue.warpIndex l g) (hHi : Prologue.warpIndex l g < 12) :
    (X.tr g).countP Event.counts ≤ correctionTileBudget + 128 * (p.batch + 1) + 715 := by
  let warp : Fin 16 := ⟨Prologue.warpIndex l g, by omega⟩
  apply nonzeroTraceBound hp hX hg (by omega)
  intro s es vs hs _ hw
  exact correctionRolePrefixFromDispatch hp hg warp hLo hHi
    (hs.mono ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1, trivial⟩) hw

end
end PTX.Kernels.TmlFa4Fwd.Correction
