-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionSearchPrefix
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Flow.Code.Part121
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Kernels.TmlFa4Fwd.Flow.Code.Part142
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Mma Softmax

noncomputable section

def correctionSearchParamPc (drain : Bool) : Nat := if drain then 9083 else 7745

private theorem correctionLocalRun {l : Launch} {g : Nat} {s u : TState} {i : Instr}
    (hF : s.fault = none) (hc : kernel.code[s.pc]? = some i)
    (hl : i.op.isLocal = true) (hG : guardHolds s i.guard = .ok true)
    (hOff : s.pc ∉ Assumptions.swExp2Sites) (hCore : Assumptions.coreOp i.op = true)
    (hExec : execLocal l g s i.op = .ok u) :
    run kernel Assumptions.all l g 1 s = some u := by
  have hA : execLocalA Assumptions.all l g s i.op = .ok u := by
    rwa [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff hCore,
      execLocalA_nil]
  simp only [run, tauStep, out_tau hF hc hG hl hA]
  rfl

/-- The two request lookups read the batch count from the same ABI slot. -/
theorem searchBatchRun {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {g : Nat}
    (drain : Bool) {s : TState} (hs : s.pc = correctionSearchParamPc drain) (hf : s.fault = none) :
    run kernel Assumptions.all l g 1 s = some
      (next (setReg s (scanSite (correctionSearch drain)).batch (b32 p.batch))) := by
  obtain ⟨hBound, hParam⟩ := hp.values (19, p.batch) (by simp [Params.scalarWords])
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at hParam
  rw [param19_name] at hParam
  cases drain
  · have hPc : s.pc = 7745 := hs
    refine correctionLocalRun hf (hPc.symm ▸ Flow.code_7745) rfl rfl (by rw [hPc]; decide) rfl ?_
    rw [execLocal_mem rfl]
    simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq, hParam,
      DType.width, MemExt.extendBits_same, pure, Except.pure, truncBits_ofNat hBound (by decide)]
    rfl
  · have hPc : s.pc = 9083 := hs
    refine correctionLocalRun hf (hPc.symm ▸ Flow.code_9083) rfl rfl (by rw [hPc]; decide) rfl ?_
    rw [execLocal_mem rfl]
    simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq, hParam,
      DType.width, MemExt.extendBits_same, pure, Except.pure, truncBits_ofNat hBound (by decide)]
    rfl

private def searchPreludeLo (drain : Bool) : Nat := if drain then 9084 else 7746
private def searchPreludeHi (drain : Bool) : Nat := searchLo drain - 4
private def searchPreludeBatch (drain : Bool) : Nat := (scanSite (correctionSearch drain)).batch

private def searchPreludeCode (drain : Bool) (pair : Instr × Nat) : Bool :=
  let ins := pair.1
  let pc := pair.2
  (ins.op.isLocal || correctionReturningOp ins.op) &&
    !(writesRegs ins.op).contains (searchPreludeBatch drain) &&
    !(scoreEventWrites ins.op).contains (searchPreludeBatch drain) &&
    (pc == 7803 ||
      (!(writesRegs ins.op).contains 1618 && !(scoreEventWrites ins.op).contains 1618)) &&
    (match ins.op with
      | .bra d _ => pc < d && d ≤ searchPreludeHi drain
      | .brx .. => false
      | _ => true)

private theorem searchPreludeAudited (drain : Bool) :
    (((kernel.code.drop (searchPreludeLo drain)).take
      (searchPreludeHi drain - searchPreludeLo drain)).zipIdx (searchPreludeLo drain)).all
        (searchPreludeCode drain) = true := by
  cases drain <;> set_option maxRecDepth 100000 in kernel_rfl


private theorem searchPreludeMember (drain : Bool) {pc : Nat} {ins : Instr}
    (hLo : searchPreludeLo drain ≤ pc) (hHi : pc < searchPreludeHi drain)
    (hc : kernel.code[pc]? = some ins) : searchPreludeCode drain (ins, pc) = true := by
  apply List.all_eq_true.mp (searchPreludeAudited drain) _
  apply List.mem_of_getElem? (i := pc - searchPreludeLo drain)
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem noCtaWriteInPrelude (drain : Bool) {pc : Nat} {ins : Instr}
    (hLo : searchPreludeLo drain ≤ pc) (hHi : pc < searchPreludeHi drain)
    (hc : kernel.code[pc]? = some ins) (hPc : pc ≠ 7803) :
    1618 ∉ writesRegs ins.op ∧ 1618 ∉ scoreEventWrites ins.op := by
  have h := searchPreludeMember drain hLo hHi hc
  simp only [searchPreludeCode, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, hPc, false_or] at h
  exact h.1.2

private theorem earlyCtaWriter {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s u : TState} (hG : g / l.block < 2 ^ 31)
    (hPc : s.pc = 7803) (ht : Tau kernel Assumptions.all l g s u) :
    u.pc = 7804 ∧ u.regs 1618 = some (b32 (g / l.block)) := by
  have hf : s.fault = none := by
    cases h : s.fault
    · rfl
    · simp [Tau, out, h] at ht
  let t := next (setReg s 1618 (b32 (g / l.block)))
  have hCta := (sregValue_oneDim hp.cluster.2.2 g).2.2.1
  have hn : g / l.block < 2 ^ 32 := by omega
  have hRun : run kernel Assumptions.all l g 1 s = some t := by
    refine correctionLocalRun hf (hPc.symm ▸ Flow.code_7803) rfl rfl (by rw [hPc]; decide) rfl ?_
    rw [execLocal_move rfl]
    simp only [execMove, DType.width, readValue, SReg.width, readBits,
      hCta, bind, Except.bind, pure, Except.pure, truncBits_ofNat hn (by decide)]
    rfl
  have ht' := tauStep_iff.mpr ht
  simp only [run, ht', Option.bind_some] at hRun
  obtain rfl := Option.some.inj hRun.symm
  exact ⟨by simp [t, next, setReg, hPc], by simp [t, next, setReg]⟩

private def SearchPreludeFacts (drain : Bool) (p : Params) (l : Launch) (g : Nat)
    (s : TState) : Prop :=
  s.sub ≤ 3 ∧ s.regs (searchPreludeBatch drain) = some (b32 p.batch) ∧
    (7804 ≤ s.pc → s.regs 1618 = some (b32 (g / l.block)))

private theorem searchPreludeStep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (drain : Bool) {g : Nat} (hG : g / l.block < 2 ^ 31) {s u : TState} {e : Option Event}
    (hLo : searchPreludeLo drain ≤ s.pc) (hHi : s.pc < searchPreludeHi drain)
    (he : WStep kernel Assumptions.all l g s e u) (hs : SearchPreludeFacts drain p l g s) :
    (searchPreludeLo drain ≤ u.pc ∧ u.pc < searchPreludeHi drain ∨
      u.pc ∈ [searchPreludeHi drain] ∧ u.fault = none) ∧
      SearchPreludeFacts drain p l g u := by
  have stepTo (hPc : u.pc = s.pc + 1) (hf : u.fault = none) :
      searchPreludeLo drain ≤ u.pc ∧ u.pc < searchPreludeHi drain ∨
        u.pc ∈ [searchPreludeHi drain] ∧ u.fault = none := by
    by_cases hLt : u.pc < searchPreludeHi drain
    · exact .inl ⟨by omega, hLt⟩
    · exact .inr ⟨by simp; omega, hf⟩
  have hLow : 7746 ≤ s.pc := by
    cases drain <;> simp [searchPreludeLo] at hLo <;> omega
  by_cases hr : s.pc = 7803
  · rcases he with ⟨_, ht⟩ | ⟨e, _, he⟩
    · obtain ⟨hu, hC⟩ := earlyCtaWriter hp hG hr ht
      have hc := hr.symm ▸ Flow.code_7803
      obtain ⟨ins, hc', hf, hStep⟩ := correctionTauFrame
        (by rw [hr]; decide) ht
      rw [hc] at hc'
      obtain rfl := Option.some.inj hc'
      rcases hStep with ⟨_, hNever⟩ | ⟨_, _, hFrame⟩
      · cases hNever
      · refine ⟨stepTo (by omega) (hFrame.fault.trans hf), hFrame.sub ▸ hs.1,
          ?_, fun _ => hC⟩
        exact (hFrame.regs _ (by cases drain <;> decide)).trans hs.2.1
    · obtain ⟨ins, hc, hLoc, _⟩ := estep_event_source he
      rw [hr, Flow.code_7803] at hc
      obtain rfl := Option.some.inj hc
      cases hLoc
  have keepCta (hAdvance : u.pc ≤ s.pc + 1) (hReg : u.regs 1618 = s.regs 1618)
      (hCta : 7804 ≤ u.pc) : u.regs 1618 = some (b32 (g / l.block)) := by
    exact hReg.trans (hs.2.2 (by omega))
  rcases he with ⟨_, ht⟩ | ⟨e, _, he⟩
  · have hExp : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨ins, hc, hf, hT⟩ := correctionTauFrame hExp ht
    have hCode := searchPreludeMember drain hLo hHi hc
    simp only [searchPreludeCode, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hCode
    rcases hT with ⟨rfl, _⟩ | ⟨_, _, hF⟩
    · exact ⟨stepTo rfl hf, Nat.zero_le _, hs.2.1, keepCta (by simp [skip]) rfl⟩
    have hBatch := (hF.regs _ hCode.1.1.1.2).trans hs.2.1
    have hCta := hF.regs _ (noCtaWriteInPrelude drain hLo hHi hc hr).1
    have hPC := hF.pc
    refine ⟨?_, hF.sub ▸ hs.1, hBatch, ?_⟩
    · cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hPC
      case bra dst aligned =>
        have hBranch : s.pc < dst ∧ dst ≤ searchPreludeHi drain := by
          simpa [hop] using hCode.2
        rw [hPC]
        by_cases h : dst < searchPreludeHi drain
        · exact .inl ⟨by omega, h⟩
        · have hEq : dst = searchPreludeHi drain := by omega
          exact .inr ⟨List.mem_singleton.mpr hEq, hF.fault.trans hf⟩
      case brx => simp [hop] at hCode
      all_goals exact stepTo hPC (hF.fault.trans hf)
    · intro hDestination
      cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hPC
      case bra dst aligned =>
        have hNoJump : s.pc ≥ 7804 := by
          by_contra hBefore
          have hCheck : (((kernel.code.drop 7746).take (7803 - 7746)).all fun i =>
              match i.op with
              | .bra pc _ => decide (pc < 7804)
              | .brx .. => false
              | _ => true) = true := by set_option maxRecDepth 100000 in kernel_rfl
          have hElem : ((kernel.code.drop 7746).take (7803 - 7746))[s.pc - 7746]? = some ins := by
            rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
              Nat.add_sub_of_le hLow, hc]
          have hd := List.all_eq_true.mp hCheck ins (List.mem_of_getElem? hElem)
          simp only [hop, decide_eq_true_eq] at hd
          omega
        exact hCta.trans (hs.2.2 hNoJump)
      case brx => simp [hop] at hCode
      all_goals exact keepCta hPC.le hCta hDestination
  · obtain ⟨ins, hc, hLocal, _⟩ := estep_event_source he
    have hCode := searchPreludeMember drain hLo hHi hc
    simp only [searchPreludeCode, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not, hLocal, Bool.false_or] at hCode
    have hOp := hCode.1.1.1.1
    obtain ⟨hP, hb⟩ := correctionEventProgress hc hOp hs.1 hCode.1.1.2 he
    obtain ⟨_, hC⟩ := correctionEventProgress hc hOp hs.1
      (noCtaWriteInPrelude drain hLo hHi hc hr).2 he
    refine ⟨?_, hP.sub, hb.trans hs.2.1, ?_⟩
    · rcases hP.pc with ⟨hNext, hF⟩ | ⟨hSame, _⟩
      · have hf : s.fault = none := by
          cases h : s.fault
          · rfl
          · obtain ⟨tmp, ht, hf⟩ := he
            simp only [out, h, Out.ev.injEq] at ht
            subst tmp
            cases hf.2
        exact stepTo hNext (hF.trans hf)
      · exact .inl ⟨hSame ▸ hLo, hSame ▸ hHi⟩
    · apply keepCta _ hC
      exact hP.pc.elim (fun h => h.1.le) (fun h => Nat.le_trans h.1.le (Nat.le_succ _))


private theorem cutSearchGate {l : Launch} {g dst pred : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hc : kernel.code[s.pc]? = some ⟨some (pred, false), .bra dst false⟩)
    (hOff : s.pc ∉ Assumptions.swExp2Sites) (hCut : s.pc < 9206) :
    countedUntil 9206 vs ≤ 1 ∨
      ∃ u rest tail, (u.pc = dst ∨ u.pc = s.pc + 1 ∧ u.sub = 0 ∧ u.acc = []) ∧
        u.sub ≤ s.sub ∧ u.fault = none ∧ u.regs = s.regs ∧
        Walk kernel Assumptions.all l g u rest tail ∧
        countedUntil 9206 vs ≤ countedUntil 9206 tail := by
  cases hw with
  | stop => exact .inl (by simp [countedUntil])
  | ev he _ =>
    obtain ⟨i, hi, hl, _⟩ := estep_event_source he
    rw [hc] at hi
    obtain rfl := Option.some.inj hi
    cases hl
  | @last s e he =>
    left
    rw [countedCorrectionCons hCut (some e)]
    simp only [countedUntil, List.takeWhile_nil, List.filterMap_nil, List.countP_nil, Nat.zero_add]
    split <;> decide
  | @tau s u es vs ht hw =>
    obtain ⟨i, hi, hf, hx⟩ := correctionTauFrame hOff ht
    rw [hc] at hi
    obtain rfl := Option.some.inj hi
    rw [countedCorrectionCons hCut none]
    simp only [Option.map_none, Option.getD_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    rcases hx with ⟨rfl, _⟩ | ⟨_, _, hF⟩
    · exact .inr ⟨skip s, es, vs, .inr ⟨rfl, rfl, rfl⟩, Nat.zero_le _, hf, rfl, hw, le_rfl⟩
    · exact .inr ⟨u, es, vs, .inl (hF.pc.resolve_right id), hF.sub.le,
        hF.fault.trans hf, funext fun r => hF.regs r (by simp [writesRegs]), hw, le_rfl⟩

private theorem setupStep (drain : Bool) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hl : searchLo drain - 3 ≤ s.pc) (hh : s.pc < searchLo drain)
    (he : WStep kernel Assumptions.all l g s e u) :
    e = none ∧ Tau kernel Assumptions.all l g s u ∧ u.pc = s.pc + 1 := by
  have hc : ∃ ins, kernel.code[s.pc]? = some ins ∧ ins.op.isLocal = true ∧
      nextPc ins.op s.pc = s.pc + 1 ∧ ¬ BrxTarget ins.op u.pc := by
    cases drain
    · have hp : s.pc = 7807 ∨ s.pc = 7808 ∨ s.pc = 7809 := by
        change 7807 ≤ s.pc at hl
        change s.pc < 7810 at hh
        omega
      rcases hp with h | h | h
      · exact ⟨_, h.symm ▸ Flow.code_7807, rfl, rfl, id⟩
      · exact ⟨_, h.symm ▸ Flow.code_7808, rfl, rfl, id⟩
      · exact ⟨_, h.symm ▸ Flow.code_7809, rfl, rfl, id⟩
    · have hp : s.pc = 9130 ∨ s.pc = 9131 ∨ s.pc = 9132 := by
        change 9130 ≤ s.pc at hl
        change s.pc < 9133 at hh
        omega
      rcases hp with h | h | h
      · exact ⟨_, h.symm ▸ Flow.code_9130, rfl, rfl, id⟩
      · exact ⟨_, h.symm ▸ Flow.code_9131, rfl, rfl, id⟩
      · exact ⟨_, h.symm ▸ Flow.code_9132, rfl, rfl, id⟩
  obtain ⟨i, hc, hL, hNext, hBrx⟩ := hc
  rcases he with ⟨rfl, ht⟩ | ⟨ev, rfl, he⟩
  · have hf : s.pc ∉ Assumptions.swExp2Sites := by
      have hRange : 7807 ≤ s.pc := by
        cases drain <;> simp [searchLo, correctionSearch, scanSite] at hl <;> omega
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨j, hj, _, hx⟩ := correctionTauFrame hf ht
    rw [hc] at hj
    obtain rfl := Option.some.inj hj
    rcases hx with ⟨rfl, _⟩ | ⟨_, _, hF⟩
    · exact ⟨rfl, ht, rfl⟩
    · exact ⟨rfl, ht, (hF.pc.resolve_right hBrx).trans hNext⟩
  · obtain ⟨j, hj, hNode, _⟩ := estep_event_source he
    rw [hc] at hj
    obtain rfl := Option.some.inj hj
    rw [hL] at hNode
    cases hNode

private theorem cutSetupSearch (drain : Bool) {l : Launch} {g batch cta : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hCta : cta + 1 < 2 ^ 31)
    (hs : At s (searchLo drain - 3)
      [((scanSite (correctionSearch drain)).cta, b32 cta),
        ((scanSite (correctionSearch drain)).batch, b32 batch)]) :
    countedUntil 9206 vs ≤ 1 ∨
      ∃ u tail, At u (searchLo drain) (groupScanFacts (correctionSearch drain) 0 batch cta) ∧
        Walk kernel Assumptions.all l g u es tail ∧
        countedUntil 9206 vs ≤ countedUntil 9206 tail := by
  rcases Epilogue.cutWalkFallthrough (cutoff := 9206) hw hs.1.ge
      (by rw [hs.1]; omega) (setupStep drain) with h | ⟨u, tail, hR, _, hw, hb⟩
  · exact .inl h
  · have hRun : run kernel Assumptions.all l g 3 s = some u := by
      rw [hs.1] at hR
      cases drain <;> exact hR
    exact .inr ⟨u, tail, groupInitFromRun (correctionSearch drain) hCta hs hRun, hw, hb⟩

private theorem countMonotone {a b : Nat} (h : a ≤ b) (visits : List Visit) :
    countedUntil a visits ≤ countedUntil b visits := by
  induction visits with
  | nil => exact le_rfl
  | cons v vs ih =>
    by_cases ha : v.pc < a
    · have hb : v.pc < b := by omega
      cases he : v.ev with
      | none => simpa [countedUntil, ha, hb, List.filterMap_cons, he] using ih
      | some e =>
        simpa [countedUntil, ha, hb, List.filterMap_cons, he, List.countP_cons] using
          Nat.add_le_add_right ih (if e.counts then 1 else 0)
    · simp [countedUntil, ha]

/-- Follow the actual correction request setup, including the decoded fast-path branch.
If the branch skips the scan, it advances to the same continuation as the scan. -/
theorem cutCorrectionSearchFromParam {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (drain : Bool) {g : Nat} (hCta : g / l.block + 1 < 2 ^ 31) {s : TState}
    {events : List Event} {visits : List Visit} (hs : s.pc = correctionSearchParamPc drain)
    (hF : s.fault = none) (hSub : s.sub ≤ 3)
    (hReg : drain = true → s.regs 1618 = some (b32 (g / l.block)))
    (hw : Walk kernel Assumptions.all l g s events visits) :
    countedUntil 9206 visits ≤ 64 * (p.batch + 1) + 310 ∨
    ∃ u rest tail, u.pc = searchHi drain ∧ u.sub ≤ 3 ∧ u.fault = none ∧
      u.regs 1618 = some (b32 (g / l.block)) ∧ Walk kernel Assumptions.all l g u rest tail ∧
      countedUntil 9206 visits ≤ 64 * (p.batch + 1) + 310 + countedUntil 9206 tail := by
  let t := next (setReg s (scanSite (correctionSearch drain)).batch (b32 p.batch))
  have hInit : t.pc = searchPreludeLo drain := by
    change s.pc + 1 = _
    rw [hs]
    cases drain <;> rfl
  have hCT : SearchPreludeFacts drain p l g t := by
    refine ⟨hSub, by simp [t, next, setReg, searchPreludeBatch], ?_⟩
    intro hAt
    cases drain
    · rw [hInit] at hAt
      contradiction
    · have hReg' := hReg rfl
      change Function.update s.regs 7153 (some (b32 p.batch)) 1618 = _
      rw [Function.update_of_ne (by decide : 1618 ≠ 7153)]
      exact hReg'
  rcases advanceWalkLocals (searchBatchRun hp drain hs hF) hw with h | ⟨post, _, hLater, hW⟩
  · subst events
    exact .inl (by simp [zeroCountNoEvents hw])
  have hLater' := hLater 9206
  have hPre : countedUntil (searchPreludeHi drain) post ≤ 309 := by
    cases drain
    · have hU := correctionLinearBound 0 hW hInit.ge (by rw [hInit]; decide) hSub
      rw [hInit] at hU
      exact (countMonotone (by decide : searchPreludeHi false ≤ 7807) _).trans hU
    · have hGe : (correctionLinearRegion 7).lo ≤ t.pc := by rw [hInit]; decide
      have hU := correctionLinearBound 7 hW hGe (by rw [hInit]; decide) hSub
      rw [hInit] at hU
      exact (countMonotone (by decide : searchPreludeHi true ≤ 9130) _).trans
        (hU.trans (by decide))
  have hHi : t.pc < searchPreludeHi drain := by rw [hInit]; cases drain <;> decide
  have hCut : searchPreludeHi drain ≤ 9206 := by cases drain <;> decide
  rcases cutWalkInterval (cutoff := 9206) hW hInit.ge hHi hCT hCut
      (searchPreludeStep hp drain (by omega)) with
    h | ⟨v, ves, vvs, hv, hvF, hvFacts, hvW, hvB⟩
  · exact .inl (by omega)
  have hv' := List.mem_singleton.mp hv
  have hC : v.regs 1618 = some (b32 (g / l.block)) :=
    hvFacts.2.2 (by rw [hv']; cases drain <;> decide)
  have hB := hvFacts.2.1
  obtain ⟨pred, hCode⟩ : ∃ pred, kernel.code[v.pc]? = some
      ⟨some (pred, false), .bra (searchHi drain) false⟩ := by
    cases drain
    · have hPc : v.pc = 7806 := hv'
      exact ⟨694, hPc.symm ▸ Flow.code_7806⟩
    · have hPc : v.pc = 9129 := hv'
      exact ⟨753, hPc.symm ▸ Flow.code_9129⟩
  rcases cutSearchGate hvW hCode (by rw [hv']; cases drain <;> decide)
      (by rw [hv']; cases drain <;> decide) with
    h | ⟨u, ues, uvs, hu, huSub, huF, huR, huW, huB⟩
  · exact .inl (by omega)
  have huCT := huSub.trans hvFacts.1
  have hUC : u.regs 1618 = some (b32 (g / l.block)) := by rw [huR]; exact hC
  rcases hu with hu | ⟨hu, hS, hA⟩
  · exact .inr ⟨u, ues, uvs, hu, huCT, huF, hUC, huW, by omega⟩
  have hPc : u.pc = searchLo drain - 3 := by
    rw [hu, hv']
    cases drain <;> rfl
  have hAt : At u (searchLo drain - 3)
      [((scanSite (correctionSearch drain)).cta, b32 (g / l.block)),
        ((scanSite (correctionSearch drain)).batch, b32 p.batch)] := by
    refine ⟨hPc, hS, hA, huF, ?_⟩
    rw [huR]
    cases drain <;> exact ⟨hC, hB, trivial⟩
  rcases cutSetupSearch drain huW hCta hAt with h | ⟨w, wvs, hwAt, hwW, hwB⟩
  · exact .inl (by omega)
  have hBatch : p.batch + 31 < 2 ^ 31 := by have := hp.shape.2.2.2.2.2; omega
  rcases cutCorrectionSearch drain hBatch hCta hwAt hwW with h |
      ⟨z, zes, zvs, hz, hzS, hzF, hzC, hzW, hzB⟩
  · exact .inl (by omega)
  · exact .inr ⟨z, zes, zvs, hz, hzS, hzF, hzC, hzW, by omega⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
