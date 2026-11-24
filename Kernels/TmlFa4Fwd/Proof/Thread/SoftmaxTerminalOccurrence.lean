-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxStatistics
import Kernels.TmlFa4Fwd.Proof.MarkedBarrierCut
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Lemmas.Flow.NthEv
import Kernels.TmlFa4Fwd.Flow.Code.Part068
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Kernels.TmlFa4Fwd.Flow.Code.Part119

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Softmax

private def publicationSite : Round → Nat
  | .first => 4397
  | .biased => 5683
  | .plain => 6891
  | .final => 7616

private theorem publicationSiteOfNotice {e : Event} {round : Round}
    (h : notice e = some round) : e.pc = publicationSite round := by
  unfold notice at h
  split at h <;> try contradiction
  unfold noticeRound at h
  split at h <;> cases round <;> simp_all [publicationSite]

private theorem publicationCode (round : Round) :
    kernel.code[publicationSite round]? = some ⟨none, .barArrive (.reg 5127) (.imm 64) true⟩ := by
  cases round
  · exact Flow.code_4397
  · exact Flow.code_5683
  · exact Flow.code_6891
  · exact Flow.code_7616

private def afterFirstCode (pc : Nat) (i : Instr) : Bool :=
  (i.op.isLocal || Epilogue.ordinaryEvent i.op) &&
  match i.op with
  | .bra dst _ => 4398 ≤ dst && decide (pc ≤ 7616 ↔ dst ≤ 7616)
  | .brx .. => false
  | _ => true

private theorem afterFirstAtCode {pc : Nat} {i : Instr} (hLow : 4398 ≤ pc)
    (hc : kernel.code[pc]? = some i) : afterFirstCode pc i = true := by
  let slice := (kernel.code.drop 4398).zipIdx 4398
  have hAll : slice.all (fun (ins, src) => afterFirstCode src ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hAt : slice[pc - 4398]? = some (i, pc) := by
    dsimp only [slice]
    rw [List.getElem?_zipIdx, List.getElem?_drop, Nat.add_sub_of_le hLow, hc]
    rfl
  exact List.all_eq_true.mp hAll _ (List.mem_of_getElem? hAt)

private theorem afterFirstSegment {s : TState} {m : SegMatch CuteSlot}
    (hLow : 4398 ≤ s.pc) (hs : s.pc ∈ Assumptions.swExp2Sites)
    (hm : cuteExp2.matchAt kernel s.pc = some m) :
    4398 ≤ m.stop ∧ (s.pc ≤ 7616 ↔ m.stop ≤ 7616) := by
  have hAll : Assumptions.swExp2Sites.all (fun pc =>
      if 4398 ≤ pc then
        match cuteExp2.matchAt kernel pc with
        | none => false
        | some m => 4398 ≤ m.stop && decide (pc ≤ 7616 ↔ m.stop ≤ 7616)
      else true) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAll s.pc hs
  rw [ite_eq_left hLow, hm] at h
  exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h).1,
    of_decide_eq_true (Bool.and_eq_true_iff.mp h).2⟩

private theorem afterFirstStep {l : Launch} {g : Nat} {s u : TState}
    {event : Option Event} (hLow : 4398 ≤ s.pc)
    (hStep : WStep kernel Assumptions.all l g s event u) :
    4398 ≤ u.pc ∧ barrierRemaining 7616 s =
      event.toList.countP (barrierMark 7616) + barrierRemaining 7616 u := by
  refine ⟨?_, markedBarrierTransition
    ⟨_, publicationCode .final, rfl, rfl⟩ ?_ ?_
    (fun m hs hm => (afterFirstSegment hLow hs hm).2) hStep⟩
  · rcases hStep with ⟨_, ht⟩ | ⟨_, _, he⟩
    · obtain ⟨i, hc, _, hSource⟩ := tauScoreSource ht
      rcases hSource with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
      · change 4398 ≤ s.pc + 1
        omega
      rcases scoreExecLocal hLocal with hFrame | ⟨m, hs, hm, hRun⟩
      · have hCode := (Bool.and_eq_true_iff.mp (afterFirstAtCode hLow hc)).2
        have hPc := hFrame.pc
        cases hop : i.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hPc
        case bra dst uni =>
          have h : 4398 ≤ dst := by
            simp only [hop, Bool.and_eq_true, decide_eq_true_eq]
              at hCode
            exact hCode.1
          exact hPc.symm ▸ h
        case brx => simp [hop] at hCode
        all_goals omega
      · exact (scoreSegmentFrame hRun).1.symm ▸ (afterFirstSegment hLow hs hm).1
    · obtain ⟨i, hc, hLocal, hf⟩ := estep_event_source he
      have hOp := (Bool.and_eq_true_iff.mp (afterFirstAtCode hLow hc)).1
      simp only [hLocal, Bool.false_or] at hOp
      rcases callbackFrame_fires (Epilogue.ordinaryEventFrame hOp) hf with h | h <;> omega
  · intro ins dest uni hc ho
    have h := (Bool.and_eq_true_iff.mp (afterFirstAtCode hLow hc)).2
    simp only [ho, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2
  · intro ins index ds uni hc ho
    have h := (Bool.and_eq_true_iff.mp (afterFirstAtCode hLow hc)).2
    simp [ho] at h

private theorem countFinalInReach {l : Launch} {g : Nat} {s u : TState} {es : List Event}
    (hr : TraceReach kernel Assumptions.all l g s es u) (hLow : 4398 ≤ s.pc) :
    4398 ≤ u.pc ∧
      barrierRemaining 7616 s = es.countP (barrierMark 7616) + barrierRemaining 7616 u := by
  induction hr with
  | refl => exact ⟨hLow, by simp⟩
  | tau ht _ ih =>
    obtain ⟨hv, h⟩ := afterFirstStep hLow (.inl ⟨rfl, ht⟩)
    obtain ⟨hu, hn⟩ := ih hv
    simp only [Option.toList_none, List.countP_nil, Nat.zero_add] at h
    exact ⟨hu, h.trans hn⟩
  | event he _ ih =>
    obtain ⟨hv, h⟩ := afterFirstStep hLow (.inr ⟨_, rfl, he⟩)
    obtain ⟨hu, hn⟩ := ih hv
    refine ⟨hu, ?_⟩
    rw [hn] at h
    simpa only [Option.toList_some, List.countP_cons, List.countP_nil, Nat.zero_add, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using h

private theorem finalObservedAtSite {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i : Nat} {e : Event} (he : X.get (g,i) = some e) (hSite : e.pc = 7616)
    (hMore : i + 1 < (X.tr g).length) : Publishes X (g,i) .final := by
  obtain ⟨_, hr⟩ := hX.thr _ (event_thread_lt hX he)
  obtain ⟨s, u, hStep, _⟩ := hr.after_event he hMore
  have hPc := (estep_source_pc hStep).symm.trans hSite
  obtain ⟨_, id, count, mode, hk⟩ :=
    markedBarrierContinues hPc (publicationCode .final) rfl hStep
  obtain ⟨rfl⟩ : e = ⟨7616, .bar id count mode⟩ := by cases e; simp_all
  have hNamed := actualNamedBarrier hp hX he
  have hMode : mode = .arrive := hNamed.2.2.1
  subst mode
  exact ⟨_, he, rfl⟩

/-- A producer that has published and then exited necessarily issued its final publication. -/
theorem finalPublicationOfExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i : Nat} {round : Round} (hPub : Publishes X (g,i) round) (hExit : Exited X g) :
    ∃ j, i ≤ j ∧ Publishes X (g,j) .final := by
  by_cases hFinal : round = .final
  · exact ⟨i, le_rfl, hFinal ▸ hPub⟩
  obtain ⟨j, ⟨pc, kind⟩, hGet, hKind⟩ := hExit
  change kind = .exit at hKind
  subst kind
  have hj := Execution.exit_last hX (event_thread_lt hX hGet) hGet
  change j + 1 = (X.tr g).length at hj
  have hExitSite := actualExitPc hX hGet
  subst pc
  obtain ⟨e, he, hn⟩ := hPub
  have hSite := publicationSiteOfNotice hn
  have hi : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hNe : i ≠ j := by
    intro h
    subst j
    rw [he] at hGet
    obtain rfl := Option.some.inj hGet
    cases round <;> simp [publicationSite] at hSite
  have hBefore : i < j := by omega
  obtain ⟨_, hr⟩ := hX.thr _ (event_thread_lt hX he)
  have hiPast : i + 1 < (X.tr g).length := by omega
  obtain ⟨s, u, hStep, hTail⟩ := hr.after_event he hiPast
  have hs := (estep_source_pc hStep).symm.trans hSite
  have hu := followsMarkedBarrier hs (publicationCode round) rfl hStep
  have hlo : 4398 ≤ u.pc := by rw [hu, hs]; cases round <;> decide
  have hhi : u.pc ≤ 7616 := by
    rw [hu, hs]
    cases round <;> first | decide | exact (hFinal rfl).elim
  let idx := j - (i + 1)
  have hEnd : ((X.tr g).drop (i + 1))[idx]? = some ⟨9205, .exit⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le (by omega : i + 1 ≤ j)]
    exact hGet
  obtain ⟨v, _, hReach, hFinalStep⟩ := hTail.before_event hEnd
  have hv := (estep_source_pc hFinalStep).symm
  change v.pc = 9205 at hv
  have hCount := (countFinalInReach hReach hlo).2
  simp only [barrierRemaining, ite_eq_left hhi, hv, Nat.reduceLeDiff, ↓reduceIte,
    Nat.add_zero] at hCount
  have hExists := (List.countP_pos_iff.mp (Nat.pos_of_ne_zero (by omega :
    ((((X.tr g).drop (i + 1)).take idx).countP (barrierMark 7616)) ≠ 0)))
  obtain ⟨f, hMem, hf⟩ := hExists
  obtain ⟨pos, hp'⟩ := List.mem_iff_getElem?.mp hMem
  have hLen := (List.getElem?_eq_some_iff.mp hp').1
  simp only [List.length_take] at hLen
  have hPos : pos < idx := by omega
  rw [List.getElem?_take_of_lt hPos, List.getElem?_drop] at hp'
  exact ⟨i + 1 + pos, by omega, finalObservedAtSite hp hX hp'
    (by simpa [barrierMark] using hf) (by dsimp [idx] at hPos; omega)⟩

/-- A role event following the final publication is already past all statistics writes. -/
theorem afterFinalPublicationPc {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i j : Nat} {f : Event}
    (hFinal : Publishes X (g,i) .final) (hAfter : i < j)
    (hf : X.get (g,j) = some f) : 7616 < f.pc := by
  obtain ⟨e, he, hNotice⟩ := hFinal
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hf).1
  obtain ⟨_, hr⟩ := hX.thr _ (event_thread_lt hX he)
  have hLater : i + 1 < (X.tr g).length := by omega
  obtain ⟨s, u, hStep, hTail⟩ := hr.after_event he hLater
  have hPc := (estep_source_pc hStep).symm.trans (publicationSiteOfNotice hNotice)
  have hu : u.pc = 7617 := by
    rw [followsMarkedBarrier hPc (publicationCode .final) rfl hStep, hPc]
    rfl
  have hLater : ((X.tr g).drop (i + 1))[j - (i + 1)]? = some f := by
    rwa [List.getElem?_drop, Nat.add_sub_of_le (by omega : i + 1 ≤ j)]
  obtain ⟨v, _, hReach, hv⟩ := hTail.before_event hLater
  have hCount := (countFinalInReach hReach (by omega)).2
  by_contra! h
  have hLe := (estep_source_pc hv) ▸ h
  simp [barrierRemaining, hu, hLe] at hCount

/-- No statistics publication follows the lane's actual final publication. -/
theorem noPublicationAfterFinal {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i j : Nat} {round : Round}
    (hFinal : Publishes X (g,i) .final) (hAfter : i < j) :
    ¬ Publishes X (g,j) round := by
  intro hPub
  obtain ⟨f, hf, hn⟩ := hPub
  have hPast := afterFinalPublicationPc hX hFinal hAfter hf
  rw [publicationSiteOfNotice hn] at hPast
  cases round <;> contradiction


/-- The total publication count is one more than the actual final publication's ordinal. -/
theorem noticesThroughFinal {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i : Nat}
    (hFinal : Publishes X (g,i) .final) :
    (before X (g,(X.tr g).length)).notices = (before X (g,i)).notices + 1 := by
  have hNo : ((X.tr g).drop (i+1)).countP publishesStats = 0 := by
    apply List.countP_eq_zero.mpr
    intro e hm hMark
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
    rw [List.getElem?_drop] at hk
    obtain ⟨round, hn⟩ := Option.isSome_iff_exists.mp hMark
    exact noPublicationAfterFinal hX hFinal (by omega : i < i+1+k) ⟨e,hk,hn⟩
  obtain ⟨e, he, hn⟩ := hFinal
  have hMarked : publishesStats e = true := by simp [publishesStats, hn]
  have hPrefix := countP_take_succ he hMarked
  rw [beforeNotices, beforeNotices]
  change ((X.tr g).take (X.tr g).length).countP publishesStats =
    ((X.tr g).take i).countP publishesStats + 1
  calc
    _ = ((X.tr g).take (i+1)).countP publishesStats +
          ((X.tr g).drop (i+1)).countP publishesStats := by
      rw [List.take_length, ← List.countP_append, List.take_append_drop]
    _ = _ := by rw [hPrefix, hNo, Nat.add_zero]

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
