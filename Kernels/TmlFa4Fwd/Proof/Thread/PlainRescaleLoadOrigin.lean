-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescalePlainScoreInputs
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Kernels.TmlFa4Fwd.Flow.Code.Part108
import Kernels.TmlFa4Fwd.Flow.Code.Part109
import Kernels.TmlFa4Fwd.Flow.Code.Part111
import Kernels.TmlFa4Fwd.Flow.Code.Part116
import Lemmas.Flow.Hooks

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

private def plainLoads : List Nat := [6679,6696,6713,6730]

private def plainRank (pc sub : Nat) : Nat :=
  2*plainLoads.countP (fun q => decide (q < pc)) +
    if pc ∈ plainLoads ∧ sub ≠ 0 then 1 else 0

private def plainWindow (pc : Nat) : Prop := 6679 ≤ pc ∧ pc ≤ 6890

private instance (pc : Nat) : Decidable (plainWindow pc) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def trackedPlainLoad (s : TState) : Prop :=
  plainWindow s.pc ∧ (6679 < s.pc ∨ s.sub ≠ 0)

private def plainOriginAudit (pc : Nat) (ins : Instr) : Bool :=
  (ins.op.isLocal || scoreEventOp ins.op) &&
  !(scoreEventWrites ins.op).contains 0 &&
  (if plainWindow pc then
    if pc ∈ plainLoads then
      ins.guard.isNone && (match ins.op with | .tcLd _ _ .s32x32b none => true | _ => false)
    else if pc = 6890 then true
    else ins.op.isLocal && decide (plainRank (pc+1) 0 = plainRank pc 0)
    else true) &&
  (match ins.op with
    | .bra dst _ => decide (¬ (6679 < dst ∧ plainWindow dst))
    | .brx .. => false
    | _ => true) &&
  (if pc = 6678 then ins.op.isLocal else true)

private theorem plainAuditAt {pc : Nat} {ins : Instr} (hLo : 3103 ≤ pc)
    (hHi : pc < 7742) (hc : kernel.code[pc]? = some ins) :
    plainOriginAudit pc ins = true := by
  let code := ((kernel.code.drop 3103).take (7742-3103)).zipIdx 3103
  have hAudit : code.all (fun (ins,i) => plainOriginAudit i ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAudit (ins,pc)
  apply List.mem_of_getElem? (i := pc-3103)
  dsimp only [code]
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),
    List.getElem?_drop,Nat.add_sub_of_le hLo,hc]
  rfl

private theorem plainSegmentNoIngress {site : Nat} {seg : SegMatch CuteSlot}
    (hs : site ∈ Assumptions.swExp2Sites) (hm : cuteExp2.matchAt kernel site = some seg) :
    ¬ plainWindow seg.stop := by
  have hAudit : Assumptions.swExp2Sites.all (fun s => (cuteExp2.matchAt kernel s).any
      (fun seg => !decide (plainWindow seg.stop))) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAudit site hs
  simpa only [hm,Option.any_some,Bool.not_eq_true',decide_eq_false_iff_not] using h

private theorem plainRankAtLoad {pc : Nat} (h : pc ∈ plainLoads) :
    plainRank pc 1 = plainRank pc 0+1 ∧
      plainRank (pc+1) 0 = plainRank pc 1+1 ∧
      Assumptions.all.any (·.tcLdWait pc) = true := by
  simp only [plainLoads,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide +kernel

private theorem plainLoadFires {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {ds : List Nat} {ta : Nat} (hs : s.sub = 0)
    (hHook : Assumptions.all.any (·.tcLdWait s.pc) = true)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.tcLd ds ta .s32x32b none)) e (some u)) :
    ∃ address vals, e = ⟨s.pc,.tc (.ld address vals .s32x32b)⟩ ∧
      u = {setRegs (next s) ds vals with pc := s.pc, sub := 1} := by
  have hShape : ∀ shape, TcShape.s32x32b ≠ .packed16 shape := by
    intro shape h
    cases h
  simp only [eventTmpl,tcLdTmpl,hHook,hs,ite_true,tcTmpl_tcLd_none hShape] at hf
  cases hv : readBits l g s 32 (.reg ta) with
  | error f =>
    simp only [hv,bind,Except.bind,ofExec,Tmpl.thenWaitLd] at hf
    split_ifs at hf <;> cases hf.2
  | ok v =>
    simp only [hv,bind,Except.bind,pure,Except.pure,ofExec,Tmpl.thenWaitLd] at hf
    split_ifs at hf
    all_goals first
      | (solve | cases hf.2)
      | (obtain ⟨words,_,he,hState⟩ := hf; exact ⟨_,words,he,Option.some.inj hState⟩)

private def HasPlainOrigin (X : Execution) (g pos : Nat) (s : TState) : Prop :=
  trackedPlainLoad s →
    ∃ start address vals, start+plainRank s.pc s.sub = pos ∧
      X.get (g,start) = some ⟨scorePc .unbiased 0,.tc (.ld address vals .s32x32b)⟩

private theorem plainLoadCode {pc : Nat} (h : pc ∈ plainLoads) :
    ∃ ds ta, kernel.code[pc]? = some ⟨none,.tcLd ds ta .s32x32b none⟩ := by
  simp only [plainLoads,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨_,_,Flow.code_6679⟩
  · exact ⟨_,_,Flow.code_6696⟩
  · exact ⟨_,_,Flow.code_6713⟩
  · exact ⟨_,_,Flow.code_6730⟩

private theorem plainStoreAdvances {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hs : s.pc = 6890) (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.pc = s.pc+1 := by
  obtain ⟨ins,hCode,_,hf⟩ := estep_event_source he
  rw [hs,Flow.code_6890] at hCode
  obtain rfl := Option.some.inj hCode
  change Fires s.pc (storeTmpl l g s .shared 32 5518 368 [.reg 1492]) e (some u) at hf
  unfold storeTmpl at hf
  split at hf
  · cases hf.2
  · cases hSub : s.sub with
    | succ n =>
      simp only [hSub,List.getElem?_cons_succ,List.getElem?_nil] at hf
      cases hf.2
    | zero =>
      simp only [hSub,List.getElem?_cons_zero] at hf
      split at hf
      · cases hf.2
      · obtain rfl := Option.some.inj hf.2
        simp [afterStore,hSub]

private theorem plainOriginStep {l : Launch} {X : Execution} {g pos : Nat}
    {s u : TState} {ev : Option Event}
    (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742) (hSub : s.sub ≤ 3)
    (hScratch : ScoreScratchState s) (hPrev : HasPlainOrigin X g pos s)
    (hStep : WStep kernel Assumptions.all l g s ev u)
    (hGet : ∀ e, ev = some e → X.get (g,pos) = some e) :
    HasPlainOrigin X g (pos+ev.toList.length) u := by
  intro hNow
  have hWin := hNow.1
  have hsBound : 6679 ≤ u.pc ∧ u.pc ≤ 6890 := hWin
  have localAdvance {ins : Instr} (hc : kernel.code[s.pc]? = some ins)
      (hNoLoad : s.pc ∉ plainLoads) (hPc : u.pc = s.pc+1) (hU : u.sub = 0) :
      HasPlainOrigin X g pos u := by
    intro hu
    have hFrom : plainWindow s.pc := by
      rcases hu.2 with hPast | hBad
      · exact ⟨by omega,by omega⟩
      · exact (hBad hU).elim
    have hBefore : s.pc < 6890 := by omega
    have hCode := plainAuditAt hLo hHi hc
    simp only [plainOriginAudit,Bool.and_eq_true,ite_eq_left hFrom,ite_eq_right hNoLoad,
      ite_eq_right (Nat.ne_of_lt hBefore),decide_eq_true_eq] at hCode
    have hRank : plainRank u.pc u.sub = plainRank s.pc s.sub := by
      rw [hPc,hU,hCode.1.1.2.2]
      simp [plainRank,hNoLoad]
    have hS : trackedPlainLoad s := by
      refine ⟨hFrom,.inl ?_⟩
      by_contra! h
      exact hNoLoad (by
        have hEq : s.pc = 6679 := le_antisymm h hFrom.1
        rw [hEq,plainLoads]
        simp)
    obtain ⟨j,a,vals,hRank',he⟩ := hPrev hS
    exact ⟨j,a,vals,hRank ▸ hRank',he⟩
  rcases hStep with ⟨rfl,hTau⟩ | ⟨e,rfl,hEvent⟩
  · obtain ⟨ins,hc,_,hExec⟩ := tauScoreSource hTau
    rcases hExec with ⟨rfl,hGuard⟩ | ⟨_,hLocal,hExec⟩
    · have hNoLoad : s.pc ∉ plainLoads := by
        intro h
        obtain ⟨ds,ta,hInstr⟩ := plainLoadCode h
        obtain rfl := Option.some.inj (hc.symm.trans hInstr)
        cases hGuard
      exact localAdvance hc hNoLoad rfl rfl hNow
    · rcases scoreExecLocal hExec with hFrame | ⟨seg,hSite,hMatch,hSeg⟩
      · have hNoLoad : s.pc ∉ plainLoads := by
          intro h
          obtain ⟨ds,ta,hInstr⟩ := plainLoadCode h
          obtain rfl := Option.some.inj (hc.symm.trans hInstr)
          cases hLocal
        have hU := hFrame.sub.trans (scratchClearOfLocal hc hLocal hScratch).1
        have hPc := hFrame.pc
        have hAudit := plainAuditAt hLo hHi hc
        cases hop : ins.op <;> simp only [hop,nextPc,BrxTarget,or_false] at hPc
        case bra target uni =>
          simp only [plainOriginAudit,Bool.and_eq_true,hop,decide_eq_true_eq] at hAudit
          rcases hNow.2 with hInside | hBad
          · exact (hAudit.1.2 ⟨hPc ▸ hInside,hPc ▸ hNow.1⟩).elim
          · exact (hBad hU).elim
        case brx => simp [plainOriginAudit,hop] at hAudit
        all_goals exact localAdvance hc hNoLoad hPc hU hNow
      · exact (plainSegmentNoIngress hSite hMatch ((scoreSegmentFrame hSeg).1 ▸ hWin)).elim
  · obtain ⟨ins,hc,hLoc,hFire⟩ := estep_event_source hEvent
    have hAudit := plainAuditAt hLo hHi hc
    simp only [plainOriginAudit,Bool.and_eq_true,hLoc,Bool.false_or,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at hAudit
    have hp := (scoreEventStep hc hAudit.1.1.1.1 hSub hAudit.1.1.1.2 hEvent).1.pc
    have hFrom : plainWindow s.pc := by
      rcases hp with ⟨hPc,_⟩ | ⟨hPc,_⟩
      · rcases Nat.eq_or_lt_of_le hsBound.1 with hEdge | hPast
        · have hStart : s.pc = 6678 := by omega
          have hBad := hAudit.2
          rw [ite_eq_left hStart] at hBad
          cases hBad
        · exact ⟨by omega,by omega⟩
      · exact hPc ▸ hWin
    have hTail : s.pc ≠ 6890 := by
      intro he
      have hPc := plainStoreAdvances he hEvent
      omega
    have hLoad : s.pc ∈ plainLoads := by
      by_contra hOther
      have h := hAudit.1.1.2
      rw [ite_eq_left hFrom,ite_eq_right hOther,ite_eq_right hTail] at h
      cases h
    have hShape := plainRankAtLoad hLoad
    obtain ⟨ds,addr,hLoadCode⟩ := plainLoadCode hLoad
    obtain rfl := Option.some.inj (hc.symm.trans hLoadCode)
    have retain (hTracked : trackedPlainLoad s)
        (hRank : plainRank u.pc u.sub = plainRank s.pc s.sub+1) :
        ∃ start address vals, start+plainRank u.pc u.sub = pos+1 ∧
          X.get (g,start) = some ⟨scorePc .unbiased 0,.tc (.ld address vals .s32x32b)⟩ := by
      obtain ⟨j,a,vals,hIdx,he⟩ := hPrev hTracked
      exact ⟨j,a,vals,by rw [hRank,← Nat.add_assoc,hIdx],he⟩
    by_cases hSub0 : s.sub = 0
    · obtain ⟨a,vals,he,rfl⟩ := plainLoadFires hSub0 hShape.2.2 hFire
      by_cases hFirst : s.pc = 6679
      · refine ⟨pos,a,vals,?_,?_⟩
        · change pos+plainRank s.pc 1 = pos+1
          rw [hFirst]
          rfl
        · change X.get (g,pos) = some ⟨6679,.tc (.ld a vals .s32x32b)⟩
          simpa only [he,hFirst] using hGet e rfl
      · refine retain ⟨hFrom,.inl (lt_of_le_of_ne hFrom.1 (Ne.symm hFirst))⟩ ?_
        simpa only [hSub0] using hShape.1
    · obtain ⟨_,rfl⟩ := fires_tcLd_wait hShape.2.2 hSub0 hFire
      refine retain ⟨hFrom,.inr hSub0⟩ ?_
      have hEq : plainRank s.pc s.sub = plainRank s.pc 1 := by
        simp [plainRank,hLoad,hSub0]
      rw [hEq]
      exact hShape.2.1

/-- A recorded plain rescale word immediately follows the four actual score
loads and their four implicit load waits on the same lane. -/
theorem plainRescaleScoreOrigin {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos : Nat} {a : Acc} {data : List Byte}
    (he : StatisticsStore X (g,pos) (rescaleStore false) a data) :
    ∃ start address vals, start+8 = pos ∧
      X.get (g,start) = some ⟨scorePc .unbiased 0,.tc (.ld address vals .s32x32b)⟩ := by
  obtain ⟨s,u,hFrame,hEvent⟩ := softmaxRoleReplayAt hp hX he
    (by decide : 3420 ≤ 6890) (by decide : 6890 < 7742)
    (fun j s => ScoreScratchState s ∧ HasPlainOrigin X g j s)
    (fun _ _ _ hs => ⟨scratchStateOfClear ⟨hs.2.1,hs.2.2.1⟩,fun h =>
      ((by decide : ¬ plainWindow 3103) (hs.1 ▸ h.1)).elim⟩)
    (fun hLo hHi hSub hPrev hs hGet =>
      ⟨softmaxScratchStep hLo hHi hSub hPrev.1 hs,
        plainOriginStep hLo hHi hSub hPrev.1 hPrev.2 hs hGet⟩)
  have hPc : s.pc = 6890 := (estep_source_pc hEvent).symm
  obtain ⟨j,address,words,hIdx,hGet⟩ := hFrame.2
    ⟨hPc.symm ▸ (by decide : plainWindow 6890), .inl (by omega)⟩
  have hRank : plainRank s.pc s.sub = 8 := by simp [hPc,plainRank,plainLoads]
  exact ⟨j,address,words,hRank ▸ hIdx,hGet⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
