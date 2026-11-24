-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleArithmeticCursor
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Flow.Code.Part079
import Kernels.TmlFa4Fwd.Flow.Code.Part080
import Kernels.TmlFa4Fwd.Flow.Code.Part081

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.EventFrame PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

private def inBiasedRescaleWindow (pc : Nat) : Prop := 5112 < pc ∧ pc ≤ 5682

private instance (pc : Nat) : Decidable (inBiasedRescaleWindow pc) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def biasedLoads : List Nat := [5112,5129,5146,5163]

private def biasedRank (pc : Nat) : Nat := biasedLoads.countP (fun q => decide (q < pc))

private theorem biasedRankAdvance {pc : Nat} (hNo : pc ∉ biasedLoads) :
    biasedRank (pc+1) = biasedRank pc := by
  simp only [biasedLoads,List.mem_cons,List.not_mem_nil,or_false,not_or] at hNo
  have h0 : 5112 < pc+1 ↔ 5112 < pc := by omega
  have h1 : 5129 < pc+1 ↔ 5129 < pc := by omega
  have h2 : 5146 < pc+1 ↔ 5146 < pc := by omega
  have h3 : 5163 < pc+1 ↔ 5163 < pc := by omega
  simp only [biasedRank,biasedLoads,List.countP_cons,List.countP_nil,h0,h1,h2,h3]

private theorem biasedRankGrowth (pc : Nat) : biasedRank (pc+1) ≤ biasedRank pc+1 := by
  by_cases h : pc ∈ biasedLoads
  · simp only [biasedLoads,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> decide
  · rw [biasedRankAdvance h]
    omega

private theorem biasedLoadCode {pc : Nat} (h : pc ∈ biasedLoads) :
    ∃ ds ta, kernel.code[pc]? = some ⟨none,.tcLd ds ta .s32x32b none⟩ := by
  simp only [biasedLoads,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨_,_,Flow.code_5112⟩
  · exact ⟨_,_,Flow.code_5129⟩
  · exact ⟨_,_,Flow.code_5146⟩
  · exact ⟨_,_,Flow.code_5163⟩

private def branchKeepsBiasedOrigin (pc : Nat) (ins : Instr) : Bool :=
  match ins.op with
  | .bra dst _ => decide (inBiasedRescaleWindow dst →
      inBiasedRescaleWindow pc ∧ biasedRank dst ≤ biasedRank pc)
  | .brx .. => false
  | _ => true

private theorem biasedOriginAudit {pc : Nat} {ins : Instr} (hl : 3103 ≤ pc)
    (hh : pc < 7742) (hc : kernel.code[pc]? = some ins) :
    branchKeepsBiasedOrigin pc ins = true := by
  let code := ((kernel.code.drop 3103).take (7742-3103)).zipIdx 3103
  have hAudit : code.all (fun (ins,i) => branchKeepsBiasedOrigin i ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAudit (ins,pc)
  apply List.mem_of_getElem? (i := pc-3103)
  dsimp only [code]
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),
    List.getElem?_drop,Nat.add_sub_of_le hl,hc]
  rfl

private theorem noBiasedSegmentIngress {site : Nat} {seg : SegMatch CuteSlot}
    (hs : site ∈ Assumptions.swExp2Sites) (hm : cuteExp2.matchAt kernel site = some seg) :
    ¬ inBiasedRescaleWindow seg.stop := by
  have hAudit : Assumptions.swExp2Sites.all (fun s => (cuteExp2.matchAt kernel s).any
      (fun seg => !decide (inBiasedRescaleWindow seg.stop))) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAudit site hs
  simpa only [hm,Option.any_some,Bool.not_eq_true',decide_eq_false_iff_not] using h

private theorem biasedOriginLoad {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hs : s.pc = 5112) (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ address vals, e = ⟨scorePc .biased 0,.tc (.ld address vals .s32x32b)⟩ := by
  obtain ⟨ins,hCode,_,hf⟩ := estep_event_source he
  obtain ⟨ds,_,hScore⟩ := scoreCode .biased 0
  change kernel.code[5112]? = _ at hScore
  rw [hs,hScore] at hCode
  obtain rfl := Option.some.inj hCode
  have hHook : Assumptions.all.any (·.tcLdWait s.pc) = false := by
    rw [hs]
    decide +kernel
  have hShape : ∀ shape, TcShape.s32x32b ≠ .packed16 shape := by
    intro shape h
    cases h
  rw [eventTmpl_tcLd_noWait hHook,tcTmpl_tcLd_none hShape] at hf
  cases hv : readBits l g s 32 (.reg (scoreReg .biased 0)) with
  | error f =>
    simp only [hv,bind,Except.bind,ofExec] at hf
    split_ifs at hf <;> cases hf.2
  | ok v =>
    simp only [hv,bind,Except.bind,pure,Except.pure,ofExec] at hf
    split_ifs at hf
    all_goals first
      | (solve | cases hf.2)
      | (obtain ⟨vals,_,hEvent,_⟩ := hf; exact ⟨_,vals,hs ▸ hEvent⟩)

private def BiasedScoreOrigin (X : Execution) (g pos : Nat) (s : TState) : Prop :=
  inBiasedRescaleWindow s.pc →
    ∃ start address vals, start+biasedRank s.pc ≤ pos ∧
      X.get (g,start) = some ⟨scorePc .biased 0,.tc (.ld address vals .s32x32b)⟩ ∧
      ∀ k, start ≤ k → k < pos → ∀ e, X.get (g,k) = some e → e.pc ≠ 5682

private theorem biasedScoreOriginStep {l : Launch} {X : Execution} {g pos : Nat}
    {s u : TState} {ev : Option Event} (hl : 3103 ≤ s.pc) (hh : s.pc < 7742) (hSub : s.sub ≤ 3)
    (hPrev : BiasedScoreOrigin X g pos s) (hStep : WStep kernel Assumptions.all l g s ev u)
    (hGet : ∀ e, ev = some e → X.get (g,pos) = some e) :
    BiasedScoreOrigin X g (pos+ev.toList.length) u := by
  intro hNow
  have hBound : 5112 < u.pc ∧ u.pc ≤ 5682 := hNow
  have prevLocal (hNo : s.pc ∉ biasedLoads) (hp : u.pc = s.pc+1) :
      BiasedScoreOrigin X g pos u := by
    intro hWin
    have hBad : s.pc ≠ 5112 := fun h => hNo (h.symm ▸ (by decide : 5112 ∈ biasedLoads))
    obtain ⟨j,a,words,hIdx,he,hNoStore⟩ := hPrev ⟨by omega,by omega⟩
    exact ⟨j,a,words,by rwa [hp,biasedRankAdvance hNo],he,hNoStore⟩
  rcases hStep with ⟨rfl,hTau⟩ | ⟨e,rfl,hEvent⟩
  · obtain ⟨ins,hCode,_,hExec⟩ := tauScoreSource hTau
    rcases hExec with ⟨rfl,hGuard⟩ | ⟨_,hLocal,hExec⟩
    · have hBad : s.pc ∉ biasedLoads := by
        intro h
        obtain ⟨ds,addr,hc⟩ := biasedLoadCode h
        obtain rfl := Option.some.inj (hCode.symm.trans hc)
        cases hGuard
      exact prevLocal hBad rfl hNow
    · rcases scoreExecLocal hExec with hF | ⟨seg,hSite,hMatch,hSeg⟩
      · have hBad : s.pc ∉ biasedLoads := by
          intro h
          obtain ⟨ds,addr,hc⟩ := biasedLoadCode h
          obtain rfl := Option.some.inj (hCode.symm.trans hc)
          cases hLocal
        have hPc := hF.pc
        have hAudit := biasedOriginAudit hl hh hCode
        cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
        case bra dst uni =>
          simp only [branchKeepsBiasedOrigin,hOp,decide_eq_true_eq] at hAudit
          obtain ⟨hFrom,hRank⟩ := hAudit (hPc ▸ hNow)
          obtain ⟨j,a,words,hIdx,he,hNoStore⟩ := hPrev hFrom
          exact ⟨j,a,words,by rw [hPc]; omega,he,hNoStore⟩
        case brx => simp [branchKeepsBiasedOrigin,hOp] at hAudit
        all_goals exact prevLocal hBad hPc hNow
      · exact (noBiasedSegmentIngress hSite hMatch ((scoreSegmentFrame hSeg).1 ▸ hNow)).elim
  · have hp := softmaxReturningPc hl hh hSub hEvent
    by_cases hStart : s.pc = 5112
    · obtain ⟨a,words,rfl⟩ := biasedOriginLoad hStart hEvent
      have hPc : u.pc = 5113 := by omega
      refine ⟨pos,a,words,by simp [hPc,biasedRank,biasedLoads],hGet _ rfl,?_⟩
      intro k hLo hHi v hEvent hStore
      have hK : k = pos := by simp at hHi; omega
      subst k
      have hEq := congrArg Event.pc (Option.some.inj (hEvent.symm.trans (hGet _ rfl)))
      change v.pc = scorePc .biased 0 at hEq
      rw [hStore] at hEq
      cases hEq
    · have hFrom : inBiasedRescaleWindow s.pc := by
        rcases hp with hPc | hPc
        · exact ⟨by omega,by omega⟩
        · exact hPc ▸ hNow
      obtain ⟨j,a,words,hIdx,he,hNoStore⟩ := hPrev hFrom
      have hRank : biasedRank u.pc ≤ biasedRank s.pc+1 := by
        rcases hp with hPc | hPc
        · exact hPc.symm ▸ biasedRankGrowth s.pc
        · rw [hPc]
          omega
      have hBound : j+biasedRank u.pc ≤ pos+1 := by omega
      refine ⟨j,a,words,hBound,he,?_⟩
      intro k hK hEnd v hv hStore
      by_cases hBefore : k < pos
      · exact hNoStore k hK hBefore v hv hStore
      have hEq : k = pos := by simp at hEnd; omega
      subst k
      have hPc := (congrArg Event.pc (Option.some.inj (hv.symm.trans (hGet e rfl)))).symm
      have hSource : s.pc = 5682 := (estep_source_pc hEvent).symm.trans (hPc.trans hStore)
      have hOut := rescaleStoreAdvances true hSource hEvent
      omega

/-- The biased rescale store has a preceding first QK read in the same numerical window. -/
theorem biasedRescaleScoreOrigin {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos : Nat} {a : Acc} {data : List Byte}
    (he : StatisticsStore X (g,pos) (rescaleStore true) a data) :
    ∃ start address vals, start+4 ≤ pos ∧
      X.get (g,start) = some ⟨scorePc .biased 0,.tc (.ld address vals .s32x32b)⟩ ∧
      ∀ k, start ≤ k → k < pos → ∀ e, X.get (g,k) = some e → e.pc ≠ 5682 := by
  obtain ⟨s,u,hFrame,hEvent⟩ := softmaxRoleReplayAt hp hX he
    (by decide : 3420 ≤ 5682) (by decide : 5682 < 7742)
    (BiasedScoreOrigin X g)
    (fun _ _ _ hs h =>
      ((by decide : ¬ inBiasedRescaleWindow 3103) (hs.1 ▸ h)).elim)
    (fun hLo hHi hSub hPrev hStep hGet => biasedScoreOriginStep hLo hHi hSub hPrev hStep hGet)
  have hPc : s.pc = 5682 := (estep_source_pc hEvent).symm
  obtain ⟨start,address,vals,hIdx,hGet,hNoStore⟩ :=
    hFrame (hPc.symm ▸ (by decide : inBiasedRescaleWindow 5682))
  have hRank : biasedRank s.pc = 4 := by rw [hPc]; decide
  exact ⟨start,address,vals,hRank ▸ hIdx,hGet,hNoStore⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
