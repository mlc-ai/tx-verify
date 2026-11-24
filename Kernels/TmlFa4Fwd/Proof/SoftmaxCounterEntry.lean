-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstCounterTrace
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstLoopEntry
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Flow.Code.Part078

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Epilogue

noncomputable section

private def counterPrepLo (biased : Bool) : Nat := if biased then 5026 else 5009
private def counterPrepHi (biased : Bool) : Nat := if biased then 5032 else 5020

private def counterPrepRegs (biased : Bool) : List Nat :=
  if biased then [7248,1229,1359] else [1226,1229,1359]

private def counterPrepOk (biased : Bool) (ins : Instr) : Bool :=
  ins.op.isLocal && schedulerFallsThrough ins.op &&
    (counterPrepRegs biased).all (fun r => !(writesRegs ins.op).contains r)

private theorem counterPrepCode (biased : Bool) {pc : Nat} {ins : Instr}
    (hLo : counterPrepLo biased ≤ pc) (hHi : pc < counterPrepHi biased)
    (hc : kernel.code[pc]? = some ins) :
    counterPrepOk biased ins = true := by
  let lo := counterPrepLo biased
  let hi := counterPrepHi biased
  have hCode : ((kernel.code.drop lo).take (hi-lo)).all (counterPrepOk biased) = true := by
    cases biased <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hCode ins
  apply List.mem_of_getElem? (i := pc-lo)
  exact (show ((kernel.code.drop lo).take (hi-lo))[pc-lo]? = some ins by
    rw [List.getElem?_take_of_lt (by dsimp [lo,hi]; omega), List.getElem?_drop,
      Nat.add_sub_of_le hLo, hc])

private theorem counterPrepStep (biased : Bool) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hLo : counterPrepLo biased ≤ s.pc) (hHi : s.pc < counterPrepHi biased)
    (hs : ScoreScratchClear s) (hf : s.fault = none)
    (he : WStep kernel Assumptions.all l g s e u) :
    e = none ∧ u.pc = s.pc+1 ∧ ScoreScratchClear u ∧ u.fault = none ∧
      ∀ r ∈ counterPrepRegs biased, u.regs r = s.regs r := by
  rcases he with ⟨rfl,hT⟩ | ⟨_,rfl,hE⟩
  · obtain ⟨ins,hc,_,hStep⟩ := tauScoreSource hT
    rcases hStep with ⟨rfl,_⟩ | ⟨_,_,hExec⟩
    · exact ⟨rfl,rfl,⟨rfl,rfl⟩,hf,fun _ _ => rfl⟩
    have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      cases biased <;> simp only [counterPrepLo, counterPrepHi, Bool.false_eq_true,
        ite_false, ite_true] at hLo hHi <;>
        simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] <;> omega
    have hF := (scoreExecLocal hExec).resolve_right (fun ⟨_,hSite,_⟩ => hOff hSite)
    have hCode := counterPrepCode biased hLo hHi hc
    simp only [counterPrepOk, Bool.and_eq_true] at hCode
    have hPc : u.pc = s.pc+1 := by
      have hp := hF.pc
      cases hop : ins.op <;> simp_all [schedulerFallsThrough, nextPc, BrxTarget]
    exact ⟨rfl,hPc,⟨hF.sub.trans hs.1,hF.acc.trans hs.2⟩,hF.fault.trans hf,
      fun r hr => hF.regs r (by simpa using List.all_eq_true.mp hCode.2 r hr)⟩
  · obtain ⟨ins,hc,hLocal,_⟩ := estep_event_source hE
    have hCode := counterPrepCode biased hLo hHi hc
    simp only [counterPrepOk, Bool.and_eq_true] at hCode
    rw [hCode.1.1] at hLocal
    cases hLocal

private def counterPrepRegion (biased : Bool) (origin s : TState) : Prop :=
  counterPrepLo biased ≤ s.pc ∧ s.pc ≤ counterPrepHi biased ∧
  ScoreScratchClear s ∧ s.fault = none ∧
  ∀ r ∈ counterPrepRegs biased, s.regs r = origin.regs r

private theorem counterPrepWalk (biased : Bool) {l : Launch} {g : Nat} {s : TState}
    {F : List (Nat × Value)} {es : List Event} {vs : List Visit} {target : Event}
    (hF : ∀ x ∈ F, x.1 ∈ counterPrepRegs biased) (hs : At s (counterPrepLo biased) F)
    (hw : Walk kernel Assumptions.all l g s es vs) (he : target ∈ es)
    (hLate : 7605 ≤ target.pc) :
    ∃ u tail, At u (counterPrepHi biased) F ∧ Walk kernel Assumptions.all l g u es tail := by
  have hInit : counterPrepRegion biased s s := ⟨hs.1.ge,
    hs.1.le.trans (by cases biased <;> decide),⟨hs.2.1,hs.2.2.1⟩,hs.2.2.2.1,fun _ _ => rfl⟩
  obtain ⟨u,pre,rest,tail,hEs,_,hU,hCut,hPre,hWalk⟩ :=
    hw.cut_marked (P := counterPrepRegion biased s)
      (cut := fun t => t.pc = counterPrepHi biased)
      (fun _ => 0) (fun _ => true) (by intros; rfl)
      (fun {t v e} hT hNe hStep => by
        obtain ⟨hl,hh,hClear,hf,hRegs⟩ := hT
        have hlt : t.pc < counterPrepHi biased := by omega
        obtain ⟨rfl,hPC,hClear',hf',hKeep⟩ :=
          counterPrepStep biased hl hlt hClear hf hStep
        exact ⟨⟨by omega,by omega,hClear',hf',fun r hr => (hKeep r hr).trans (hRegs r hr)⟩,rfl⟩)
      hInit he (fun t ht _ hg => by
        change t.pc = target.pc at hg
        have hHi := ht.2.1
        cases biased <;> simp [counterPrepHi] at hHi <;> omega)
  have hNil : pre = [] := by simpa using hPre
  rw [hNil,List.nil_append] at hEs
  exact ⟨u,tail,⟨hCut,hU.2.2.1.1,hU.2.2.1.2,hU.2.2.2.1,
    holdsSchedulerFrame hs.2.2.2.2 hU.2.2.2.2 hF⟩,hEs.symm ▸ hWalk⟩

private theorem pastCounterRun {l : Launch} {g n : Nat} {s u : TState} {es : List Event}
    {vs : List Visit} {target : Event} (hr : run kernel Assumptions.all l g n s = some u)
    (hw : Walk kernel Assumptions.all l g s es vs) (he : target ∈ es) :
    ∃ tail, Walk kernel Assumptions.all l g u es tail := by
  rcases Mma.advanceWalkLocals hr hw with rfl | ⟨_,_,_,hTail⟩
  · cases he
  · exact ⟨_,hTail⟩

/-- Repeated passes read the last-block and ordinary-loop split words unchanged. -/
def repeatCountLimits (blocks split : Nat) : List (Nat × Value) :=
  [(1229,b32 (blocks-1)), (1359,b32 split)]

private theorem biasedSeed (l : Launch) (g blocks split : Nat)
    (hb : blocks < 2^31) (hSplit : split < blocks) :
    Seg kernel Assumptions.all l g 1 5025
      ((1226,b32 blocks) :: repeatCountLimits blocks split)
      5026 ((7248,b32 (2^32 - (blocks-split))) :: repeatCountLimits blocks split) := by
  intro t ht
  simp only [repeatCountLimits] at ht ⊢
  seg_fp ht using norm_bits

variable {l : Launch} {g blocks cap past : Nat} {s : TState} {es : List Event} {vs : List Visit}

/-- The actual repeated-round continuation depends only on the integer loop geometry.
The decoded FP32 operations need no mathematical values for this control proof. -/
theorem firstCountEntryWalkOfLateEvent {target : Event} (hBlocks : 0 < blocks) (hb : blocks < 2^31)
    (hCap : 0 < cap) (hc : cap < 2^31) (hs : At s 5006 (firstLoopGeometry blocks cap past))
    (hw : Walk kernel Assumptions.all l g s es vs) (he : target ∈ es) (hLate : 7605 ≤ target.pc) :
    let split := firstPlainSplit blocks cap
    ∃ u tail, (if firstBiasedRepeats blocks cap = 0 then At u 6654 (repeatCountLimits blocks split)
      else At u 5032 ((7248,b32 (2^32 - (blocks-split))) :: repeatCountLimits blocks split)) ∧
      Walk kernel Assumptions.all l g u es tail := by
  dsimp only
  let split := firstPlainSplit blocks cap
  have hSplit : split < blocks := by unfold split firstPlainSplit; omega
  obtain ⟨t,ht,hT⟩ := (firstLoopSplitCounts l g blocks cap hb hc).apply
    (hs.mono ⟨hs.2.2.2.2.2.2.1,hs.2.2.2.2.2.1,trivial⟩)
  have hStable := firstLoopSplitFrame hs.1 ht
  have hCount : At t 5009 ((1226,b32 blocks) :: repeatCountLimits blocks split) :=
    hT.mono ⟨(hStable _ (by decide)).trans hs.2.2.2.2.2.1,
      (hStable _ (by decide)).trans hs.2.2.2.2.2.2.2.1,hT.2.2.2.2.1,trivial⟩
  obtain ⟨_,hWT⟩ := pastCounterRun ht hw he
  obtain ⟨u,_,hU,hWU⟩ := counterPrepWalk false (by
    intro x h
    simpa [repeatCountLimits,counterPrepRegs] using List.mem_map_of_mem (f := Prod.fst) h)
    hCount hWT he hLate
  obtain ⟨v,hv,hV⟩ := (firstLoopCountDecision l g blocks split hBlocks hb hSplit).apply hU
  obtain ⟨_,hWV⟩ := pastCounterRun hv hWU he
  let reps := firstBiasedRepeats blocks cap
  let F := (630,.pred (decide (reps = 0))) :: (1226,b32 blocks) :: repeatCountLimits blocks split
  have hV' : At v 5024 F := hV
  have hCode : kernel.code[5024]? = some ⟨some (630,false), .bra 6654 false⟩ := Flow.code_5024
  obtain ⟨w,hw,hW⟩ := (Seg.bra (A := Assumptions.all) (L := l) (g := g)
    (pick := decide (reps = 0)) hCode (by simp [F]) (fun _ _ a ha => by
      simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (maxSeg (by decide))).apply hV'
  obtain ⟨_,hWW⟩ := pastCounterRun hw hWV he
  by_cases hPlain : reps = 0
  · have hAt : At w 6654 (repeatCountLimits blocks split) := by
      simpa only [hPlain, decide_true, ite_true] using hW.mono hW.2.2.2.2.2.2
    exact ⟨w,_,by simpa only [show firstBiasedRepeats blocks cap = 0 from hPlain, ite_true]
      using hAt,hWW⟩
  · have hAt : At w 5025 ((1226,b32 blocks) :: repeatCountLimits blocks split) := by
      simpa only [decide_eq_false hPlain, Bool.false_eq_true, ite_false] using
        hW.mono hW.2.2.2.2.2
    obtain ⟨q,hq,hQ⟩ := (biasedSeed l g blocks split hb hSplit).apply hAt
    obtain ⟨_,hWQ⟩ := pastCounterRun hq hWW he
    obtain ⟨r,_,hR,hWR⟩ := counterPrepWalk true (by
      intro x hx
      simpa [repeatCountLimits,counterPrepRegs] using List.mem_map_of_mem (f := Prod.fst) hx)
      hQ hWQ he hLate
    change At r 5032 ((7248,b32 (2^32 - (blocks-split))) :: repeatCountLimits blocks split) at hR
    exact ⟨r,_,by simpa only [show firstBiasedRepeats blocks cap ≠ 0 from hPlain, ite_false]
      using hR,hWR⟩

/-- An exiting walk reaches the repeated-round entry for its computed loop geometry. -/
theorem firstCountEntryWalk (hBlocks : 0 < blocks) (hb : blocks < 2^31) (hCap : 0 < cap)
    (hc : cap < 2^31) (hs : At s 5006 (firstLoopGeometry blocks cap past))
    (hw : Walk kernel Assumptions.all l g s es vs) (he : (⟨9205,.exit⟩ : Event) ∈ es) :
    let split := firstPlainSplit blocks cap
    ∃ u tail, (if firstBiasedRepeats blocks cap = 0 then At u 6654 (repeatCountLimits blocks split)
      else At u 5032 ((7248,b32 (2^32 - (blocks-split))) :: repeatCountLimits blocks split)) ∧
      Walk kernel Assumptions.all l g u es tail :=
  firstCountEntryWalkOfLateEvent hBlocks hb hCap hc hs hw he (by decide)

end
end PTX.Kernels.TmlFa4Fwd.Softmax
