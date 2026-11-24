-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedScoreTrace
public import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyPhase
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Kernels.TmlFa4Fwd.Flow.Code.Part080

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Thread.Scores

noncomputable section

/-- At an event boundary the same entry state and consumed trace determine the
unique source state, including its packed score registers. -/
theorem reachedEventSourceUnique {l : Launch} {g : Nat} {s t u : TState} {es : List Event}
    (ht : TraceReach kernel Assumptions.all l g s es t)
    (hu : TraceReach kernel Assumptions.all l g s es u)
    (hT : Stops kernel Assumptions.all l g t) (hU : Stops kernel Assumptions.all l g u) :
    t = u := by
  induction ht generalizing u with
  | refl =>
    cases hu with
    | refl => rfl
    | tau hs _ => exact (not_tau_of_stops hT hs).elim
  | tau hs ht ih =>
    cases hu with
    | refl => exact (not_tau_of_stops hU hs).elim
    | tau hu hn => exact ih (tau_det hs hu ▸ hn) hT hU
    | event he _ => exact (not_tau_of_stops (stops_of_estep he) hs).elim
  | event he ht ih =>
    cases hu with
    | tau hLocal _ => exact (not_tau_of_stops (stops_of_estep he) hLocal).elim
    | event hu hn => exact ih (Option.some.inj (estep_det he hu) ▸ hn) hT hU

private theorem frameOfFacts {regs : Nat → Option Value} {facts : List (Nat × Value)}
    (h : ∀ q ∈ facts, regs q.1 = some q.2) : Holds regs facts := by
  induction facts with
  | nil => exact trivial
  | cons a rest ih =>
    exact ⟨h a (by simp),ih (fun q hq => h q (List.mem_cons_of_mem _ hq))⟩

private theorem biasedWaitAddressCore {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (stage : Fin 2) (g : Nat) :
    Seg kernel [] l g 1 5180 [(4037,b32 (l.sharedBase+8*stage.val))]
      5181 [(3965,b32 (waitLoc l g stage 5).addr)] := by
  let base := l.sharedBase+8*stage.val
  have hStage := stage.isLt
  have hShared := hp.shared.2.1
  have h32 : base < 4294967296 := by omega
  have h64 : base < 18446744073709551616 := by omega
  have hAdd32 : base+320 < 4294967296 := by omega
  have hAdd64 : base+320 < 18446744073709551616 := by omega
  have hLoc : (waitLoc l g stage 5).addr = base+320 := by
    change l.sharedBase+(320+8*stage.val) = l.sharedBase+8*stage.val+320
    omega
  rw [hLoc]
  intro s hs
  seg_fp hs using norm_bits [Nat.mod_eq_of_lt h32,Nat.mod_eq_of_lt h64,
    Nat.mod_eq_of_lt hAdd32,Nat.mod_eq_of_lt hAdd64]

set_option maxRecDepth 100000 in
private theorem biasedWaitAddress {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (stage : Fin 2) (g : Nat) {t : TState} {F : List (Nat × Value)}
    (ht : At t 5180 F) (hBase : t.regs 4037 = some (b32 (l.sharedBase+8*stage.val)))
    (hFresh : ∀ x ∈ F, x.1 ≠ 3965) :
    ∃ u, TraceReach kernel Assumptions.all l g t [] u ∧
      At u 5181 ((3965,b32 (waitLoc l g stage 5).addr)::F) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  obtain ⟨u,hStep,hU⟩ := biasedWaitAddressCore hp stage g t (ht.mono ⟨hBase,trivial⟩)
  have hEq := Assumptions.tauStep_all_eq_nil (L := l) (g := g) (by rw [ht.1]; decide)
    (by rw [ht.1]; exact Flow.code_5180) rfl
  have hRun : run kernel Assumptions.all l g 1 t = some u := by
    simpa only [run,hEq] using hStep
  have hAudit : ((kernel.code.drop 5180).take 1).all
      (fun ins => (F.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) = true := by
    rw [List.take_one,List.head?_drop,Flow.code_5180]
    simp only [Option.toList_some,List.all_cons,List.all_nil,Bool.and_true,List.all_eq_true]
    intro r hR
    obtain ⟨f,hF,rfl⟩ := List.mem_map.mp hR
    have hn := hFresh f hF
    change (!([3965] : List Nat).contains f.1) = true
    simp [hn]
  have hKeep := Epilogue.holdsSchedulerFrame ht.2.2.2.2
    (fun r hR => Epilogue.schedulerLocalFrame (len := 1) hAudit (by simp) hStep
      ht.1.ge (by rw [ht.1]) hR)
    (fun _ h => List.mem_map_of_mem h)
  exact ⟨u,TraceReach.of_local (run_rtg hRun),hU.mono ⟨hU.2.2.2.2.1,hKeep⟩,run_rtg hRun⟩

/-- The four biased score loads feed the first successful Bias poll on the
same actual role trace, preserving every packed score through the retries. -/
theorem biasedScoreWaitPackedInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (w : Fin 8) {g entry start : Nat} {s : TState} {ending : Option TState}
    (hs : At s 3103 [(1062,b32 w.val),(2535,b32 l.sharedBase)])
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop entry) ending)
    {address : Nat} {words : List Value} {shape : TcShape}
    (he : X.get (g,start) = some ⟨scorePc .biased 0,.tc (.ld address words shape)⟩)
    (hStart : entry ≤ start)
    (hBytes : ∀ (q : Fin 4) (xs : List Value),
      X.get (g,start+q.val) =
        some ⟨scorePc .biased q,.tc (.ld (scoreAddress l g (stageOf w) q) xs .s32x32b)⟩ →
      ∀ k < 32, (xs.getD k (b32 0)).bytes = 4)
    (hPresent : ending = none ∨ ∃ target ∈ (X.tr g).drop (start+4), target.pc ≠ 5181) :
    ∃ wait phase pre, ∃ values : Fin 4 → List Value, start+4 ≤ wait ∧
      X.get (g,wait) = some ⟨5181,.wait (waitLoc l g (stageOf w) 5) phase true true .cta⟩ ∧
      (∀ q : Fin 4, (values q).length = 32 ∧
        X.get (g,start+q.val) =
          some ⟨scorePc .biased q,.tc (.ld (scoreAddress l g (stageOf w) q) (values q) .s32x32b)⟩) ∧
      (∀ (q : Fin 4) (k : Fin 16), pre.regs (repeatedScorePairReg .biased q k.val) =
        some (joinValue ((values q).getD (2*k.val) (b32 0))
          ((values q).getD (2*k.val+1) (b32 0)))) ∧
      TraceReach kernel Assumptions.all l g s (((X.tr g).drop entry).take (wait-entry)) pre ∧
      Stops kernel Assumptions.all l g pre ∧
      (∀ q : Fin 4, ((X.tr g).take wait).countP earlyProbabilityMark =
        ((X.tr g).take (start+q.val)).countP earlyProbabilityMark) ∧
      ∀ j target, start+4 ≤ j → X.get (g,j) = some target → target.pc ≠ 5181 → wait < j := by
  obtain ⟨t,out,ht,hRegs,hStep,hRun,hPrefix⟩ := biasedScoreStartFromEntry hp w hs hr he hStart
  obtain ⟨v,out',hBaseReach,hBaseStep,hBase⟩ := repeatedBiasBaseOfScoreStart hp w hs hr he hStart
  have hSame := reachedEventSourceUnique hPrefix hBaseReach
    (stops_of_estep hStep) (stops_of_estep hBaseStep)
  subst v
  have hRun' : Run kernel Assumptions.all l g t
      ((X.tr g).drop (start+repeatedScoreStride .biased*(0 : Fin 4).val)) ending := by
    simpa only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] using hRun
  have hLength : ending = none ∨ start+4 < (X.tr g).length := by
    refine hPresent.imp_right ?_
    rintro ⟨target,hMem,_⟩
    by_contra! hShort
    rw [List.drop_eq_nil_iff.mpr hShort] at hMem
    cases hMem
  obtain ⟨u,hu,hPacked,_,hKeep,hTail,hReach⟩ :=
    repeatedScoreTraceFromInPrefix hp .biased (stageOf w) 0 ht
      (fun q _ => hRegs q)
      (fun q xs _ h => hBytes q xs (by simpa only [Repeated.round,repeatedScoreStride,ite_false,
        show Repeated.biased ≠ .unbiased by decide,Nat.one_mul] using h)) hRun' hLength
  change At u 5180 [] at hu
  change Run kernel Assumptions.all l g u ((X.tr g).drop (start+4)) ending at hTail
  have huReach : TraceReach kernel Assumptions.all l g s
      (((X.tr g).drop entry).take (start+4-entry)) u := by
    rw [show start+4-entry = (start-entry)+4 by omega,List.take_add,List.drop_drop,
      Nat.add_sub_of_le hStart]
    exact hPrefix.append hReach
  obtain ⟨phase,hPhase,hParity⟩ := repeatedBiasPhaseWordOfScoreTail (hs.mono trivial) hu.1 huReach
  let values := fun q => Classical.choose (hPacked q (Fin.zero_le q))
  have hValues (q : Fin 4) := Classical.choose_spec (hPacked q (Fin.zero_le q))
  let packed := (List.finRange 4).flatMap fun q => (List.finRange 16).map fun k =>
    (repeatedScorePairReg .biased q k.val,
      joinValue ((values q).getD (2*k.val) (b32 0))
        ((values q).getD (2*k.val+1) (b32 0)))
  let F := (7250,b32 phase)::packed
  have hPack : Holds u.regs packed := by
    apply frameOfFacts
    intro q hQ
    obtain ⟨p,_,hp⟩ := List.mem_flatMap.mp hQ
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hp
    exact (hValues p).2.2 k.val k.isLt
  have huFrame : At u 5180 F := hu.mono ⟨hParity,hPack⟩
  have hFresh (r : Nat) (hR : r = 3965 ∨ r = 9755) : ∀ x ∈ F, x.1 ≠ r := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · change 7250 ≠ r
      rcases hR with rfl | rfl <;> decide
    obtain ⟨q,_,hq⟩ := List.mem_flatMap.mp hx
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hq
    have hq := q.isLt
    have hk := k.isLt
    change 7367+16*q.val+k.val ≠ r
    omega
  have huBase : u.regs 4037 = some (b32 (l.sharedBase+8*(stageOf w).val)) := by
    rw [hKeep 4037 (by intro q _; fin_cases q <;> decide)]
    exact hBase
  obtain ⟨v,hLocal,hV,hPath⟩ := biasedWaitAddress hp (stageOf w) g huFrame huBase
    (hFresh 3965 (.inl rfl))
  have hMore : (X.tr g).drop (start+4) ≠ [] := by
    intro hEmpty
    rw [hEmpty] at hTail
    cases hTail
    exact hLength.elim (by simp) (fun h => (Nat.not_lt_of_ge (List.drop_eq_nil_iff.mp hEmpty)) h)
  have hPoll := hTail.after_local_nonempty hPath hMore
  let failure := Event.mk 5181 (.wait (waitLoc l g (stageOf w) 5) phase false true .cta)
  let success := Event.mk 5181 (.wait (waitLoc l g (stageOf w) 5) phase true true .cta)
  obtain ⟨failed,_,suffix,hEvents,_,_,pre,hPre,hRetries,hStop⟩ :=
    waitTraceWithSourceInPrefix hp (stageOf w) 5 g phase hPhase
      (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · change 3965 ≠ 9755
          decide
        · exact hFresh 9755 (.inr rfl) x hx) hV hPoll hPresent
  let wait := start+4+failed
  have hw : X.get (g,wait) = some success := by
    change (X.tr g)[start+4+failed]? = some success
    rw [← List.getElem?_drop,hEvents,List.getElem?_append_right (by simp),
      List.length_replicate,Nat.sub_self]
    rfl
  have hInitial : TraceReach kernel Assumptions.all l g s
      (((X.tr g).drop entry).take (start+4-entry)) v := by
    simpa only [List.append_nil] using huReach.append hLocal
  have hFails : ((X.tr g).drop (start+4)).take failed = List.replicate failed failure := by
    rw [hEvents]
    change (List.replicate failed failure ++ success::suffix).take failed = _
    simpa only [List.length_replicate] using
      (List.take_append_length (l₁ := List.replicate failed failure) (l₂ := success::suffix))
  refine ⟨wait,phase,pre,values,by omega,hw,?_,?_,?_,hStop,?_,?_⟩
  · intro q
    have h := hValues q
    exact ⟨h.1,by simpa only [values,Repeated.round,repeatedScoreStride,ite_false,
      show Repeated.biased ≠ .unbiased by decide,Nat.one_mul] using h.2.1⟩
  · intro q k
    apply holds_mem hPre.2.2.2.2
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    exact ⟨q,List.mem_finRange _,List.mem_map.mpr ⟨k,List.mem_finRange _,rfl⟩⟩
  · rw [show wait-entry = (start+4-entry)+failed by unfold wait; omega,
      List.take_add,List.drop_drop,Nat.add_sub_of_le (show entry ≤ start+4 by omega),hFails]
    exact hInitial.append hRetries
  · have hReadCount (q : Fin 4) :
        ((X.tr g).take (start+q.val+1)).countP earlyProbabilityMark =
          ((X.tr g).take (start+q.val)).countP earlyProbabilityMark := by
      have hGet : X.get (g,start+q.val) = some
          ⟨scorePc .biased q,.tc (.ld (scoreAddress l g (stageOf w) q) (values q) .s32x32b)⟩ :=
        by simpa only [values,Repeated.round,repeatedScoreStride,ite_false,
          show Repeated.biased ≠ .unbiased by decide,Nat.one_mul] using (hValues q).2.1
      exact countP_take_succ_false (p := earlyProbabilityMark) hGet (by fin_cases q <;> rfl)
    have h0 := hReadCount 0
    have h1 := hReadCount 1
    have h2 := hReadCount 2
    have h3 := hReadCount 3
    change ((X.tr g).take (start+1)).countP earlyProbabilityMark =
      ((X.tr g).take start).countP earlyProbabilityMark at h0
    change ((X.tr g).take (start+2)).countP earlyProbabilityMark =
      ((X.tr g).take (start+1)).countP earlyProbabilityMark at h1
    change ((X.tr g).take (start+3)).countP earlyProbabilityMark =
      ((X.tr g).take (start+2)).countP earlyProbabilityMark at h2
    change ((X.tr g).take (start+4)).countP earlyProbabilityMark =
      ((X.tr g).take (start+3)).countP earlyProbabilityMark at h3
    have hNo : (List.replicate failed failure).countP earlyProbabilityMark = 0 := by
      simp [show earlyProbabilityMark failure = false from rfl]
    have hQuiet : ((X.tr g).take wait).countP earlyProbabilityMark =
        ((X.tr g).take (start+4)).countP earlyProbabilityMark := by
      unfold wait
      rw [List.take_add,List.countP_append,hFails,hNo,Nat.add_zero]
    intro q
    rw [hQuiet]
    fin_cases q <;> first
      | exact h3.trans (h2.trans (h1.trans h0))
      | exact h3.trans (h2.trans h1)
      | exact h3.trans h2
      | exact h3

  · intro j target hBefore hTarget hDifferent
    by_contra! hAfter
    have hEntry : ((X.tr g).drop (start+4))[j-(start+4)]? = some target := by
      rw [List.getElem?_drop,Nat.add_sub_of_le hBefore]
      exact hTarget
    rcases Nat.eq_or_lt_of_le hAfter with rfl | hLt
    · exact hDifferent (congrArg Event.pc (Option.some.inj (hTarget.symm.trans hw)))
    · have hRank : j-(start+4) < failed := by dsimp [wait] at hLt; omega
      rw [hEvents,List.getElem?_append_left (by rw [List.length_replicate]; exact hRank),
        List.getElem?_replicate,ite_eq_left hRank] at hEntry
      exact hDifferent (congrArg Event.pc (Option.some.inj hEntry.symm))

end
end PTX.Kernels.TmlFa4Fwd.Softmax
