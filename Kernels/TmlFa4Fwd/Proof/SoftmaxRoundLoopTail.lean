-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopOrdinal
public import Kernels.TmlFa4Fwd.Proof.SoftmaxScoreNumeric
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedAddress
import Kernels.TmlFa4Fwd.Proof.SoftmaxMax
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Lemmas.Flow.FloatOutcome

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption

def roundPriorMaxReg : ScoreLoop → Nat
  | .biased => 7251
  | .plain => 7255

def tailPhaseWords (x y : Bool) : ScoreLoop → List (Nat × Value)
  | .biased => [(7250,b32 x.toNat),(7253,b32 y.toNat)]
  | .plain => [(7253,b32 y.toNat)]

def tailCreditScorePhase (loop : ScoreLoop) (phase : Bool) : Bool :=
  match loop with
  | .biased => !phase
  | .plain => phase

private theorem tailExtraPhases {l : Launch} {g : Nat} (loop : ScoreLoop) (x y : Bool)
    (frame : List (Nat × Value)) (hFrame : ∀ r ∈ frame, r.1 ≠ 7250 ∧ r.1 ≠ 7253) :
    Seg kernel Assumptions.all l g ((scoreLoopSite loop).increment-(loopCreditTogglePc loop+1))
      (loopCreditTogglePc loop+1) (tailPhaseWords x y loop ++ frame)
      (scoreLoopSite loop).increment
      (tailPhaseWords (!x) (tailCreditScorePhase loop y) loop ++ frame) := by
  cases loop
  · have hFlip : Seg kernel Assumptions.all l g 2 6648
        (tailPhaseWords x y .biased) 6650 (tailPhaseWords (!x) (!y) .biased) := by
      cases x <;> cases y <;> intro t ht <;>
        simp only [tailPhaseWords] at ht ⊢ <;> seg_fp ht using rfl
    intro t ht
    obtain ⟨u,hr,hu⟩ := hFlip.apply (ht.mono ((holds_append ..).mp ht.2.2.2.2).1)
    have hKeep : ∀ r, (r ≠ 7250 ∧ r ≠ 7253) → u.regs r = t.regs r := by
      refine fixedFrame (first := 6648) (stop := 6650) ?_ ?_ (by rw [ht.1]; decide)
        (by rw [ht.1]; decide) hr
      · intro pc hlo hhi
        interval_cases pc
        · exact ⟨_,Flow.code_6648,rfl,rfl,fun _ => nofun,fun r h => by simpa [writesRegs] using h.1⟩
        · exact ⟨_,Flow.code_6649,rfl,rfl,fun _ => nofun,fun r h => by simpa [writesRegs] using h.2⟩
      · intro pc hlo hhi hm
        simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false] at hm
        omega
    have hOld := ((holds_append ..).mp ht.2.2.2.2).2
    have hFacts := Epilogue.holdsSchedulerFrame (regs := frame.map Prod.fst) hOld
      (fun r hr => by
        obtain ⟨fact,hFact,rfl⟩ := List.mem_map.mp hr
        exact hKeep fact.1 (hFrame fact hFact))
      (fun _ hr => List.mem_map_of_mem hr)
    exact ⟨u,hr,hu.mono ((holds_append ..).mpr ⟨hu.2.2.2.2,hFacts⟩)⟩
  · intro t ht
    exact ⟨t,rfl,ht⟩

private theorem tailCopyReference {l : Launch} {g : Nat} {t : TState} (loop : ScoreLoop)
    (mx : Option ℝ) (ht : At t ((scoreLoopSite loop).increment+2) [])
    (hMax : t.regs 7256 = some (scoreValue mx)) :
    run kernel Assumptions.all l g 1 t =
      some (next (setReg t (roundPriorMaxReg loop) (scoreValue mx))) := by
  have hCode : kernel.code[(scoreLoopSite loop).increment+2]? = some ⟨none,
      .move ⟨.scalar,.int .b 32,[some (roundPriorMaxReg loop)],[.reg 7256]⟩⟩ := by
    cases loop
    · exact Flow.code_6652
    · exact Flow.code_7603
  apply run_local hCode rfl ht
  rw [Assumptions.execLocalA_all_eq_numeric,
    Assumptions.execLocalA_eq_nil (by rw [ht.1]; cases loop <;> decide) rfl]
  have h := exec_movE (A := []) (L := l) (g := g) (d := roundPriorMaxReg loop)
    (by simp [CoreMoves]) (by simp [NoSegments]) hMax
  simpa only [movE,scoreValue_bytes,ite_true,Except.map] using h

private theorem advanceTailBranchLocal {l : Launch} {g : Nat} {t : TState}
    (loop : ScoreLoop) (take : Bool) (frame : List (Nat × Value))
    (ht : At t ((scoreLoopSite loop).increment+3) (((scoreLoopSite loop).pred,.pred take)::frame)) :
    ∃ u, At u (if take then (scoreLoopSite loop).head else (scoreLoopSite loop).increment+4)
      frame ∧ Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧ u.regs = t.regs := by
  have hCode : kernel.code[(scoreLoopSite loop).increment+3]? =
      some ⟨some ((scoreLoopSite loop).pred,false),.bra (scoreLoopSite loop).head false⟩ := by
    cases loop
    · exact Flow.code_6653
    · exact Flow.code_7604
  obtain ⟨u,hr,hu⟩ := run_bra (K := kernel) (A := Assumptions.all) (L := l) (g := g)
    hCode take (ht.mono ht.2.2.2.2.2) ht.2.2.2.2.1
    (fun a ha => by
      simp [Assumptions.all,Assumptions.numeric,Assumptions.synchronization] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (maxSeg (by cases loop <;> decide))
  have hStep : Tau kernel Assumptions.all l g t u := by
    apply tauStep_iff.mp
    simpa [run] using hr
  have hRegs := (tailBranchFrame loop ht.1 ht.2.2.2.2.1 hStep).2.2
  exact ⟨u,by simpa only [Nat.add_assoc] using hu,run_rtg hr,hRegs⟩

private theorem counterTestKeepsAccumulation {l : Launch} {g : Nat} {t u : TState}
    (loop : ScoreLoop) (ht : t.pc = (scoreLoopSite loop).increment)
    (htAcc : t.acc = []) (hr : run kernel Assumptions.all l g 2 t = some u) : u.acc = [] := by
  have hCode (n : Fin 2) : ∃ i,
      kernel.code[(scoreLoopSite loop).increment+n.val]? = some i ∧
      Assumptions.coreOp i.op = true ∧
      nextPc i.op ((scoreLoopSite loop).increment+n.val) =
        (scoreLoopSite loop).increment+n.val+1 ∧
      (∀ pc, ¬BrxTarget i.op pc) := by
    cases loop <;> fin_cases n
    · exact ⟨_,Flow.code_6650,rfl,rfl,fun _ => nofun⟩
    · exact ⟨_,Flow.code_6651,rfl,rfl,fun _ => nofun⟩
    · exact ⟨_,Flow.code_7601,rfl,rfl,fun _ => nofun⟩
    · exact ⟨_,Flow.code_7602,rfl,rfl,fun _ => nofun⟩
  have hLocal {a b : TState} (n : Fin 2) (hAt : a.pc = (scoreLoopSite loop).increment+n.val)
      (hStep : tauStep kernel Assumptions.all l g a = some b) (hAcc : a.acc = []) :
      b.pc = a.pc+1 ∧ b.acc = [] := by
    obtain ⟨i,hLookup,hCore,hPc,hNo⟩ := hCode n
    have hOff : a.pc ∉ Assumptions.swExp2Sites := by
      rw [hAt]
      cases loop <;> fin_cases n <;> decide
    rw [Assumptions.tauStep_all_eq_nil hOff (hAt.symm ▸ hLookup) hCore] at hStep
    rcases tau_core_frame (hAt.symm ▸ hLookup) (tauStep_iff.mp hStep) with rfl | hFrame
    · exact ⟨rfl,rfl⟩
    · exact ⟨hFrame.pc.elim (·.trans (hAt.symm ▸ hPc)) (fun bad => (hNo _ bad).elim),
        hFrame.acc.trans hAcc⟩
  cases hv : tauStep kernel Assumptions.all l g t with
  | none => simp [run,hv] at hr
  | some v =>
    have hu : tauStep kernel Assumptions.all l g v = some u := by
      cases hh : tauStep kernel Assumptions.all l g v <;> simp_all only
        [run,Option.bind_some,Option.bind_none]
    have hFirst := hLocal 0 (by simpa only [Fin.val_zero,Nat.add_zero] using ht) hv htAcc
    exact (hLocal 1 (by simpa only [ht,Fin.val_one] using hFirst.1) hu hFirst.2).2

/-- After a repeated denominator update, the real tail moves the chosen maximum to
the next reference register, flips the reusable phase and retains the new sum. -/
theorem repeatedLoopTailCarriesStateLocal {l : Launch} {g : Nat} {t : TState}
    (loop : ScoreLoop) (phase biasPhase scorePhase : Bool) (word : Nat) (hw : word < 2^32)
    (mx : Option ℝ) (mass : ℝ)
    (ht : At t (loopCreditTogglePc loop)
      (tailPhaseWords biasPhase scorePhase loop ++
        [((scoreLoopSite loop).word,b32 word),(7256,scoreValue mx),(7257,fl mass),
          (7258,b32 phase.toNat)])) :
    let site := scoreLoopSite loop
    let nextWord := (word+1)%2^32
    ∃ u, At u (if nextWord ≠ site.sentinel then site.head else site.increment+4)
      ([(site.word,b32 nextWord),(roundPriorMaxReg loop,scoreValue mx),(7256,scoreValue mx),
        (7257,fl mass),(7258,b32 (!phase).toNat)] ++
        tailPhaseWords (!biasPhase) (tailCreditScorePhase loop scorePhase) loop) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      u.regs 7249 = t.regs 7249 := by
  dsimp only
  let site := scoreLoopSite loop
  let nextWord := (word+1)%2^32
  let F := [(site.word,b32 word),(7256,scoreValue mx),(7257,fl mass),(7258,b32 (!phase).toNat)]
  have hFrames := (holds_append ..).mp ht.2.2.2.2
  obtain ⟨hWord,hMax,hMass,hPhase,_⟩ := hFrames.2
  obtain ⟨hFlip,hPc,hCredit⟩ := loopCreditToggle (l := l) (g := g) loop phase ht.1 ht.2.2.2.1 hPhase
  let v := next (setReg t 7258 (b32 (!phase).toNat))
  have hOther : Holds v.regs (tailPhaseWords biasPhase scorePhase loop) := by
    cases loop
    · exact ⟨by simpa only [v,next,setReg,Function.update_of_ne (by decide : 7250 ≠ 7258)]
          using hFrames.1.1,
        by simpa only [v,next,setReg,Function.update_of_ne (by decide : 7253 ≠ 7258)]
          using hFrames.1.2.1,
        trivial⟩
    · exact ⟨by simpa only [v,next,setReg,Function.update_of_ne (by decide : 7253 ≠ 7258)]
          using hFrames.1.1,
        trivial⟩
  have hUnchanged (r : Nat) (hr : r ≠ 7258) : v.regs r = t.regs r := by
    simp only [v,next,setReg,Function.update_of_ne hr]
  have hNe : site.word ≠ 7258 := by cases loop <;> decide
  have hAt : At v (loopCreditTogglePc loop+1) (tailPhaseWords biasPhase scorePhase loop ++ F) := by
    exact ⟨hPc,ht.2.1,ht.2.2.1,ht.2.2.2.1,(holds_append ..).mpr ⟨hOther,
      (hUnchanged _ hNe).trans hWord,
      (hUnchanged _ (by decide)).trans hMax,
      (hUnchanged _ (by decide)).trans hMass,hCredit,trivial⟩⟩
  obtain ⟨s,hPrelude,hs⟩ := (tailExtraPhases (l := l) (g := g) loop biasPhase scorePhase F (by
    intro r hr
    cases loop <;>
      simp only [F,site,scoreLoopSite,List.mem_cons,List.not_mem_nil,or_false] at hr <;>
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> decide)).apply hAt
  have hEarlier : s.regs 7249 = v.regs 7249 := by
    cases loop
    · refine fixedFrame (first := 6648) (stop := 6650) (kept := fun r => r = 7249)
        ?_ ?_ (by rw [hAt.1]; decide) (by rw [hAt.1]; decide) hPrelude _ rfl
      · intro pc hlo hhi
        interval_cases pc
        · exact ⟨_,Flow.code_6648,rfl,rfl,fun _ => nofun,by rintro _ rfl; decide⟩
        · exact ⟨_,Flow.code_6649,rfl,rfl,fun _ => nofun,by rintro _ rfl; decide⟩
      · intro pc hlo hhi hm
        simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false] at hm
        omega
    · have hSame : some v = some s := hPrelude
      rw [← Option.some.inj hSame]
  have hState := ((holds_append ..).mp hs.2.2.2.2).2
  obtain ⟨w,hTest,hWP,hSub,hFault,hWord',hPred,hKeep⟩ :=
    scoreLoopTestActualFrame (l := l) (g := g) loop hw hs.2.2.2.1 hs.1 hState.1
  let b := decide (nextWord ≠ site.sentinel)
  let copy := next (setReg w (roundPriorMaxReg loop) (scoreValue mx))
  have hStable (n : Nat) (hn : n ∈ [7256,7257,7258,7250,7253]) : w.regs n = s.regs n := by
    apply hKeep <;> (
      cases loop <;> simp_all [site,scoreLoopSite] <;> omega)
  have hMx : w.regs 7256 = some (scoreValue mx) :=
    (hStable _ (by decide)).trans hState.2.1
  have hAtW : At w (site.increment+2) [] :=
    ⟨hWP,hSub.trans hs.2.1,counterTestKeepsAccumulation loop hs.1 hs.2.2.1 hTest,
      hFault,trivial⟩
  have hCopy := tailCopyReference (l := l) (g := g) loop mx hAtW hMx
  have hFact (n : Nat) (hn : n ∈ [7256,7257,7258,7250,7253]) : copy.regs n = s.regs n := by
    have hNe : n ≠ roundPriorMaxReg loop := by
      cases loop <;> simp_all [roundPriorMaxReg] <;> omega
    exact (Function.update_of_ne hNe _ _).trans (hStable n hn)
  have hCounter : copy.regs site.word = some (b32 nextWord) :=
    (Function.update_of_ne (by cases loop <;> decide) _ _).trans hWord'
  have hPredicate : copy.regs site.pred = some (.pred b) :=
    (Function.update_of_ne (by cases loop <;> decide) _ _).trans hPred
  let G := [(site.word,b32 nextWord),(roundPriorMaxReg loop,scoreValue mx),(7256,scoreValue mx),
    (7257,fl mass),(7258,b32 (!phase).toNat)]
  let phases := tailPhaseWords (!biasPhase) (tailCreditScorePhase loop scorePhase) loop
  have hPhasesOld : Holds s.regs phases := ((holds_append ..).mp hs.2.2.2.2).1
  have hPhases : Holds copy.regs phases := by
    cases loop
    · exact ⟨(hFact _ (by decide)).trans hPhasesOld.1,
        (hFact _ (by decide)).trans hPhasesOld.2.1,trivial⟩
    · exact ⟨(hFact _ (by decide)).trans hPhasesOld.1,trivial⟩
  have hNumeric : Holds copy.regs G :=
    ⟨hCounter,Function.update_self ..,
      (hFact _ (by decide)).trans hState.2.1,(hFact _ (by decide)).trans hState.2.2.1,
      (hFact _ (by decide)).trans hState.2.2.2.1,trivial⟩
  have hReady : At copy (site.increment+3) ((site.pred,.pred b)::(G++phases)) := by
    exact ⟨by simpa only [copy,next,setReg,Nat.add_assoc] using congrArg (·+1) hWP,
      hAtW.2.1,hAtW.2.2.1,hAtW.2.2.2.1,hPredicate,
      (holds_append ..).mpr ⟨hNumeric,hPhases⟩⟩
  have hResume := run_rtg (run_comp (run_comp (run_comp hFlip hPrelude) hTest) hCopy)
  obtain ⟨u,hu,hBranch,hExtra⟩ := advanceTailBranchLocal (l := l) (g := g) loop b (G++phases) hReady
  have hWordStable : w.regs 7249 = s.regs 7249 :=
    hKeep _ (by cases loop <;> decide) (by cases loop <;> decide)
  have hCopyStable : copy.regs 7249 = w.regs 7249 :=
    Function.update_of_ne (by cases loop <;> decide) _ _
  have hStable := (congrFun hExtra 7249).trans
    (hCopyStable.trans (hWordStable.trans (hEarlier.trans (hUnchanged _ (by decide)))))
  exact ⟨u,by simpa only [b,decide_eq_true_eq] using hu,hResume.trans hBranch,hStable⟩

/-- The plain loop toggles the score-ready phase before its correction phase
and next-reference update. The denominator and other tail inputs survive. -/
theorem plainSumTailToCreditToggle {l : Launch} {g : Nat} (bit : Bool)
    (frame : List (Nat × Value)) (hFrame : ∀ r ∈ frame, r.1 ≠ 7253) :
    Seg kernel Assumptions.all l g 1 7599 ((7253,b32 bit.toNat)::frame)
      7600 ((7253,b32 (!bit).toNat)::frame) := by
  have hFlip : Seg kernel Assumptions.all l g 1 7599 [(7253,b32 bit.toNat)]
      7600 [(7253,b32 (!bit).toNat)] := by
    cases bit <;> intro t ht <;> seg_fp ht using rfl
  intro t ht
  obtain ⟨u,hr,hu⟩ := hFlip.apply (ht.mono ⟨ht.2.2.2.2.1,trivial⟩)
  have hKeep : ∀ r, r ≠ 7253 → u.regs r = t.regs r := by
    refine fixedFrame (first := 7599) (stop := 7600) ?_ ?_ (by simp only [ht.1,Nat.le_refl])
      (by simp only [ht.1,Nat.reduceAdd,Nat.le_refl]) hr
    · intro pc hLo hHi
      interval_cases pc
      exact ⟨_,Flow.code_7599,rfl,rfl,fun _ => nofun,fun r h => by simpa [writesRegs] using h⟩
    · intro pc hLo hHi
      interval_cases pc
      decide
  have hFacts := Epilogue.holdsSchedulerFrame (regs := frame.map Prod.fst)
    ht.2.2.2.2.2 (fun r hr => by
      obtain ⟨f,h,rfl⟩ := List.mem_map.mp hr
      exact hKeep f.1 (hFrame f h)) (fun _ hr => List.mem_map_of_mem hr)
  exact ⟨u,hr,hu.mono ⟨hu.2.2.2.2.1,hFacts⟩⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
