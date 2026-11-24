-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreProgress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedBiasAddresses
import all Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedBiasAddresses
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedAddress
import Kernels.TmlFa4Fwd.Flow.Code.Part079

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction

/-- The bias-address setup and score poll preparation write these registers. -/
def biasedScoreSetupWrites (lo length : Nat) : List Nat :=
  ((kernel.code.drop lo).take length).flatMap (writesRegs ∘ Instr.op)

private def setupOp (pc : Nat) (i : Instr) : Bool :=
  !(Assumptions.swExp2Sites.contains pc) && Assumptions.coreOp i.op &&
    Epilogue.schedulerFallsThrough i.op

private theorem setupAudit {pc : Nat} {i : Instr} (hLo : 5032 ≤ pc) (hHi : pc < 5109)
    (hc : kernel.code[pc]? = some i) : setupOp pc i = true := by
  have hTable : ((((kernel.code.drop 5032).take 77).zipIdx 5032).all
      (fun (i,pc) => setupOp pc i)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hTable (i,pc)
  apply List.mem_of_getElem? (i := pc-5032)
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hc]
  rfl

private theorem setupFrame {l : Launch} {g lo n : Nat} {s u : TState}
    (hLo : 5032 ≤ lo) (hHi : lo+n ≤ 5109) (hs : s.pc = lo)
    (hr : run kernel Assumptions.all l g n s = some u) :
    ∀ r ∉ biasedScoreSetupWrites lo n, u.regs r = s.regs r := by
  apply fixedFrame (first := lo) (stop := lo+n) (kept := fun r =>
    r ∉ biasedScoreSetupWrites lo n) _ _ hs.ge (by omega) hr
  · intro pc hlo hhi
    have hLen : pc < kernel.code.length := by
      have : 5109 ≤ kernel.code.length := by decide +kernel
      omega
    let i := kernel.code[pc]'hLen
    have hc : kernel.code[pc]? = some i := List.getElem?_eq_getElem hLen
    have ha := setupAudit (by omega) (by omega) hc
    simp only [setupOp,Bool.and_eq_true] at ha
    refine ⟨i,hc,ha.1.2,?_,?_,?_⟩
    · cases ho : i.op <;> simp [ho,nextPc,Epilogue.schedulerFallsThrough] at ha ⊢
    · intro target
      cases ho : i.op <;> simp [ho,BrxTarget,Epilogue.schedulerFallsThrough] at ha ⊢
    · intro r hn hw
      apply hn
      apply List.mem_flatMap.mpr
      refine ⟨i,?_,hw⟩
      apply List.mem_of_getElem? (i := pc-lo)
      rwa [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hlo]
  · intro pc hlo hhi hm
    have hLen : pc < kernel.code.length := by
      have : 5109 ≤ kernel.code.length := by decide +kernel
      omega
    let i := kernel.code[pc]'hLen
    have hc : kernel.code[pc]? = some i := List.getElem?_eq_getElem hLen
    have ha := setupAudit (by omega) (by omega) hc
    simp [setupOp,hm] at ha

private def biasRowInput (l : Launch) (g : Nat) (w : Fin 8) : List (Nat × Value) :=
  [(3978,b32 (repeatedBiasRowBase l g+repeatedBiasStageOffset w))]

private theorem biasVectorSetups {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (w : Fin 8) (n : Nat) (hn : n ≤ 14) :
    Seg kernel Assumptions.all l g (4*n) 5046 (biasRowInput l g w)
      (5046+4*n) (biasRowInput l g w) := by
  induction n with
  | zero =>
    intro s hs
    exact ⟨s,rfl,hs⟩
  | succ n ih =>
    have hi := ih (by omega)
    let i : Fin 14 := ⟨n,by omega⟩
    have hNext : Seg kernel Assumptions.all l g 4 (5046+4*n) (biasRowInput l g w)
        (5046+4*(n+1)) (biasRowInput l g w) := by
      intro t ht
      obtain ⟨u,hr,hu⟩ := (repeatedBiasOtherVectorSetup hp g w i).apply ht
      have hPc : 5050+4*i.val = 5046+4*(n+1) := by dsimp [i]; omega
      exact ⟨u,hr,(hPc ▸ hu).mono hu.2.2.2.2.2⟩
    simpa only [Nat.mul_succ] using hi.comp hNext

private theorem biasPollSetup {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) (tid block : Nat) :
    Seg kernel Assumptions.all l g 7 5102
      [(3967,b32 tid),(7249,b32 block),(631,.pred (stage.val = 1)),(2535,b32 l.sharedBase)]
      5109 [((waitSite (qkWaitSite .biased)).base,
        b32 (waitLoc l g stage (qkWaitSite .biased)).addr),
        (4037,b32 (l.sharedBase+8*stage.val)),(7249,b32 ((block+(2^32-1))%2^32))] := by
  have hBase := hp.shared.2.1
  have hBounds : l.sharedBase+88 < 2^32 := by omega
  fin_cases stage <;> intro t ht <;> seg_fp ht using
    (nf_simp [waitLoc,waitSite,qkWaitSite]
     all_goals omega)

/-- The live frame at a biased score wait, including the decoded TMEM addresses. -/
def biasedScoreReadyFacts (l : Launch) (g : Nat) (stage : Fin 2) (phase block : Nat)
    (facts : List (Nat × Value)) : List (Nat × Value) :=
  [(3964,b32 (waitLoc l g stage (qkWaitSite .biased)).addr),(7253,b32 phase),
    (4037,b32 (l.sharedBase+8*stage.val)),(7249,b32 ((block+(2^32-1))%2^32))] ++
    roundScoreFacts l g stage .biased ++ facts

/-- The biased loop computes the stage and row addresses before its score-ready wait. -/
theorem biasedScoreReadyLocal {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g phase block : Nat} (warp : Fin 8) (facts : List (Nat × Value))
    (hStable : ∀ x ∈ facts, x.1 ∉ biasedScoreSetupWrites 5032 77) {s : TState}
    (hs : At s 5032
      ((1062,b32 warp.val)::(2535,b32 l.sharedBase)::(7253,b32 phase)::(7249,b32 block)::facts)) :
    ∃ u, At u 5109 (biasedScoreReadyFacts l g (stageOf warp) phase block facts) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u := by
  let stage := stageOf warp
  let top := decide (stage.val = 1)
  have hTop : decide (3 < warp.val) = top := by fin_cases warp <;> rfl
  have hSize : (if top then 32768 else 0) = repeatedBiasStageOffset warp := by
    fin_cases warp <;> rfl
  have hInput : At s 5032 [(1062,b32 warp.val),(2535,b32 l.sharedBase)] :=
    hs.mono ⟨hs.2.2.2.2.1,hs.2.2.2.2.2.1,trivial⟩
  obtain ⟨a,hFirst,ha⟩ := (repeatedStage l g warp).apply hInput
  rw [hTop] at ha
  obtain ⟨b,hTid,hb⟩ := (repeatedTid hp g top).apply ha
  obtain ⟨v,hRow,hv⟩ := (repeatedRow hp g top).apply hb
  rw [hSize] at hv
  obtain ⟨w,hVectors,hw⟩ := (biasVectorSetups hp g warp 14 (by decide)).apply
    (hv.mono ⟨hv.2.2.2.2.2.2.1,trivial⟩)
  have hRun : run kernel Assumptions.all l g 70 s = some w :=
    run_comp (run_comp (run_comp hFirst hTid) hRow) hVectors
  have hAfterTid : run kernel Assumptions.all l g 61 b = some w := run_comp hRow hVectors
  have hI := setupFrame (lo := 5032) (n := 70) (by decide) (by decide) hs.1 hRun
  have hAfter := setupFrame (lo := 5041) (n := 61) (by decide) (by decide) hb.1 hAfterTid
  have hw' : At w 5102
      [(3967,b32 (g%l.block)),(7249,b32 block),(631,.pred (stage.val = 1)),
        (2535,b32 l.sharedBase)] := hw.mono
    ⟨(hAfter 3967 (by decide +kernel)).trans hb.2.2.2.2.2.2.1,
      (hI 7249 (by decide +kernel)).trans hs.2.2.2.2.2.2.2.1,
      (hAfter 631 (by decide +kernel)).trans hb.2.2.2.2.1,
      (hI 2535 (by decide +kernel)).trans hs.2.2.2.2.2.1,trivial⟩
  obtain ⟨u,hPoll,hu⟩ := (biasPollSetup hp g stage (g%l.block) block).apply hw'
  have hFinal := run_comp hRun hPoll
  have hRegs := setupFrame (lo := 5032) (n := 77) (by decide) (by decide) hs.1 hFinal
  obtain ⟨b',hB',hb'⟩ := (biasedScoreAddressSegment hp g warp).apply hInput
  have hShare : b' = b := Option.some.inj (hB'.symm.trans (run_comp hFirst hTid))
  subst b'
  have hScoreReg := setupFrame (lo := 5041) (n := 68) (by decide) (by decide) hb.1
    (run_comp hAfterTid hPoll)
  have hScores : Holds u.regs (roundScoreFacts l g stage .biased) := by
    apply Epilogue.holdsSchedulerFrame (regs := (roundScoreFacts l g stage .biased).map Prod.fst)
      hb'.2.2.2.2
    · intro r hr
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
      obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hx
      apply hScoreReg
      change scoreReg .biased q ∉ biasedScoreSetupWrites 5041 68
      fin_cases q <;> decide +kernel
    · exact fun _ hx => List.mem_map_of_mem hx
  have hFacts : Holds u.regs facts := by
    apply Epilogue.holdsSchedulerFrame (regs := facts.map Prod.fst)
      hs.2.2.2.2.2.2.2.2
    · intro r hr
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
      exact hRegs _ (hStable x hx)
    · exact fun _ hx => List.mem_map_of_mem hx
  exact ⟨u,hu.mono ⟨hu.2.2.2.2.1,(hRegs 7253 (by decide +kernel)).trans hs.2.2.2.2.2.2.1,
    hu.2.2.2.2.2.1,hu.2.2.2.2.2.2.1,(holds_append ..).mpr ⟨hScores,hFacts⟩⟩,run_rtg hFinal⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads) (warp : Fin 8)
    (phase block : Nat) (hPhase : phase < 2) (facts : List (Nat × Value))
    (hStable : ∀ x ∈ facts, x.1 ∉ biasedScoreSetupWrites 5032 77) (hFresh : ∀ x ∈ facts, x.1 ≠ 9754)
    (c : OpeningTripCursor l X g 5032
      ((1062,b32 warp.val)::(2535,b32 l.sharedBase)::(7253,b32 phase)::(7249,b32 block)::facts))
include hp hMax hg warp phase block hPhase facts hStable hFresh c

/-- The actual biased-loop head completes its score acquire once the producer
has advanced the stage's score-ready object. -/
theorem biasedScoreReturnOfPending
    (hReady : let loc := Thread.Scores.scoreReadyObject l (g/l.block) (stageOf warp)
      okPolls loc (X.tr g) = okPolls loc ((X.tr g).take c.pos) →
      OpeningPollReady X
      (Thread.Scores.scoreReadyObject l (g/l.block) (stageOf warp)) phase) :
    ∃ u : RepeatedScoreCursor l X g .biased (stageOf warp) phase
        (biasedScoreReadyFacts l g (stageOf warp) phase block facts),
      c.pos ≤ u.index ∧ u.cursor.ending = c.ending ∧
      (X.tr g).drop c.pos = List.replicate (u.index-c.pos)
        ⟨(waitSite (qkWaitSite .biased)).pc,
          .wait (Thread.Scores.scoreReadyObject l (g/l.block) (stageOf warp))
            phase false true .cta⟩ ++
        ⟨(waitSite (qkWaitSite .biased)).pc,
          .wait (Thread.Scores.scoreReadyObject l (g/l.block) (stageOf warp))
            phase true true .cta⟩ :: (X.tr g).drop u.cursor.pos := by
  obtain ⟨s,hs,hLocal⟩ := biasedScoreReadyLocal hp warp facts hStable c.checkpoint
  have hNone : ∀ x ∈ biasedScoreReadyFacts l g (stageOf warp) phase block facts,
      x.1 ≠ (waitSite (qkWaitSite .biased)).result := by
    intro x hx
    simp only [biasedScoreReadyFacts,List.cons_append,List.nil_append,List.mem_cons,
      List.mem_append] at hx
    rcases hx with rfl | rfl | rfl | rfl | hx | hx
    · dsimp only
      decide
    · dsimp only
      decide
    · dsimp only
      decide
    · dsimp only
      decide
    · obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hx
      fin_cases q <;> dsimp only <;> decide
    · exact hFresh x hx
  exact scoreReturnAtWaitOfPending hp hMax hg .biased (stageOf warp) phase hPhase
    (.head _) (.tail _ (.head _)) hNone
    ⟨c.pos,c.before,s,c.ending,c.positive,c.bounded,c.released,hs,c.recorded,c.remaining,
      c.localSteps.trans hLocal⟩ hReady

end PTX.Kernels.TmlFa4Fwd.Softmax
