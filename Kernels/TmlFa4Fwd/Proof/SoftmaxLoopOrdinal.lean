-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.MarkedBarrierCut
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part103
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Kernels.TmlFa4Fwd.Flow.Code.Part118
import Lemmas.Flow.TcTmpl
import Lemmas.Flow.MarkedCut
import Lemmas.Flow.EventCont
import Kernels.TmlFa4Fwd.Flow.Code.Part102
import Kernels.TmlFa4Fwd.Flow.Code.Part116

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Mma

private def publishPc : ScoreLoop → Nat
  | .biased => 5683
  | .plain => 6891

/-- The unique statistics publication in a pass through this decoded score loop. -/
@[no_expose] def loopPublication (loop : ScoreLoop) : Event → Bool := barrierMark (publishPc loop)

private def markerPc (loop : ScoreLoop) (probability : Bool) : Nat :=
  if probability then (if loop = .biased then 6532 else 7437) else publishPc loop

private def remaining (loop : ScoreLoop) (probability : Bool) : TState → Nat :=
  barrierRemaining (markerPc loop probability)

private def marker (loop : ScoreLoop) (probability : Bool) : Event → Bool :=
  barrierMark (markerPc loop probability)

private theorem markerCode (loop : ScoreLoop) :
    kernel.code[publishPc loop]? = some ⟨none, .barArrive (.reg 5127) (.imm 64) true⟩ := by
  cases loop
  · exact Flow.code_5683
  · exact Flow.code_6891

/-- The marker names this decoded statistics publication. -/
theorem loopPublicationPc (loop : ScoreLoop) {e : Event}
    (hm : loopPublication loop e = true) : e.pc = (if loop = .biased then 5683 else 6891) := by
  have h : e.pc = publishPc loop := beq_iff_eq.mp hm
  cases loop <;> exact h

theorem loopPublicationOfPc (loop : ScoreLoop) {e : Event}
    (h : e.pc = (if loop = .biased then 5683 else 6891)) : loopPublication loop e = true := by
  cases loop <;> exact beq_iff_eq.mpr h

private theorem markerOperation (loop : ScoreLoop) (probability : Bool) :
    ∃ ins, kernel.code[markerPc loop probability]? = some ins ∧ ins.guard = none ∧
      ins.op.isLocal = false := by
  cases probability
  · cases loop
    · exact ⟨_, Flow.code_5683, rfl, rfl⟩
    · exact ⟨_, Flow.code_6891, rfl, rfl⟩
  · cases loop
    · exact ⟨_, Flow.code_6532, rfl, rfl⟩
    · exact ⟨_, Flow.code_7437, rfl, rfl⟩

private theorem markerReturns (loop : ScoreLoop) (probability : Bool)
    {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hs : s.pc = markerPc loop probability) (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.pc = s.pc+1 := by
  cases probability
  · exact followsMarkedBarrier hs (markerCode loop) rfl he
  · obtain ⟨ins, hc, _, hf⟩ := estep_event_source he
    rw [hs] at hc
    cases loop
    · change kernel.code[6532]? = some ins at hc
      rw [Flow.code_6532] at hc
      obtain rfl := Option.some.inj hc.symm
      exact congrArg TState.pc (fires_arrive_state hf).1
    · change kernel.code[7437]? = some ins at hc
      rw [Flow.code_7437] at hc
      obtain rfl := Option.some.inj hc.symm
      exact congrArg TState.pc (fires_arrive_state hf).1

private def keepsMarker (loop : ScoreLoop) (probability : Bool) (pc : Nat) (op : Op) : Bool :=
  match op with
  | .bra dst _ => decide (pc ≤ markerPc loop probability ↔ dst ≤ markerPc loop probability)
  | .brx .. => false
  | _ => true

private theorem markerAudit (loop : ScoreLoop) (probability : Bool) {pc : Nat} {i : Instr}
    (hLo : windowHead loop ≤ pc) (hHi : pc < windowEnd loop)
    (hc : kernel.code[pc]? = some i) : keepsMarker loop probability pc i.op = true := by
  let lo := windowHead loop
  let len := windowEnd loop - lo
  let code := ((kernel.code.drop lo).take len).zipIdx lo
  have hAll : code.all (fun (i, pc) => keepsMarker loop probability pc i.op) = true := by
    cases loop <;> cases probability <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (i,pc)
  apply List.mem_of_getElem? (i := pc-lo)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by dsimp [lo, len]; omega),
    List.getElem?_drop, Nat.add_sub_of_le hLo, hc]
  rfl

private theorem segmentsKeepMarker (loop : ScoreLoop) (probability : Bool)
    {pc : Nat} {m : SegMatch CuteSlot}
    (hs : pc ∈ Assumptions.swExp2Sites) (hm : cuteExp2.matchAt kernel pc = some m) :
    pc ≤ markerPc loop probability ↔ m.stop ≤ markerPc loop probability := by
  have hAll : Assumptions.swExp2Sites.all (fun pc =>
      match cuteExp2.matchAt kernel pc with
      | some m => decide (pc ≤ markerPc loop probability ↔ m.stop ≤ markerPc loop probability)
      | none => false) = true := by
    cases loop <;> cases probability <;> set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAll pc hs
  rw [hm] at h
  exact of_decide_eq_true h

private def scoreLoopRegion (loop : ScoreLoop) (w : Nat) (origin s : TState) : Prop :=
  windowHead loop ≤ s.pc ∧ s.pc ≤ windowEnd loop ∧ s.sub ≤ 3 ∧
    s.regs (scoreLoopSite loop).word = some (b32 w) ∧
    (s.pc = windowEnd loop → s.fault = none) ∧
    ∀ r ∈ [1229, 1359], s.regs r = origin.regs r

private theorem regionStep (loop : ScoreLoop) (probability : Bool)
    {l : Launch} {g w : Nat} {origin s u : TState} {ev : Option Event}
    (hs : scoreLoopRegion loop w origin s) (hCut : s.pc ≠ windowEnd loop)
    (he : WStep kernel Assumptions.all l g s ev u) :
    scoreLoopRegion loop w origin u ∧ remaining loop probability s =
      ev.toList.countP (marker loop probability) + remaining loop probability u := by
  obtain ⟨hLo,hHi,hSub,hWord,_,hGeometry⟩ := hs
  have hLt : s.pc < windowEnd loop := by omega
  obtain ⟨hl, hh, hs, hf, hReg⟩ := windowStepFrame (loopWindow loop) hLo hLt hSub he
  have hEmpty : (windowSite (loopWindow loop)).exits = [] := by cases loop <;> rfl
  simp only [hEmpty, List.not_mem_nil, or_false] at hh
  have hWordKeep : (scoreLoopSite loop).word ∈ (windowSite (loopWindow loop)).keeps := by
    cases loop <;> decide
  refine ⟨⟨hl, hh, hs, (hReg _ hWordKeep).trans hWord, ?_, ?_⟩, ?_⟩
  · intro hPc
    exact hf.resolve_right (fun h => hCut (h.symm.trans hPc))
  · intro r hR
    have hKeep : r ∈ (windowSite (loopWindow loop)).keeps := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl <;> cases loop <;> decide
    exact (hReg _ hKeep).trans (hGeometry _ hR)
  · refine markedEventTransition (markerOperation loop probability)
      (fun h {_} hm => markerReturns loop probability h hm) ?_ ?_
      (fun m hm => segmentsKeepMarker loop probability hm) he
    · intro ins dst uni hc hop
      simpa only [keepsMarker, hop, decide_eq_true_eq] using markerAudit loop probability hLo hLt hc
    · intro ins index targets uni hc hop
      simpa [keepsMarker, hop] using markerAudit loop probability hLo hLt hc

private theorem tailMoveKeepsGeometry {l : Launch} {g : Nat} (loop : ScoreLoop)
    {s t : TState} (hPc : s.pc = (scoreLoopSite loop).increment + 2)
    (ht : Tau kernel Assumptions.all l g s t) {r : Nat} (hr : r ∈ [1229, 1359]) :
    t.regs r = s.regs r := by
  obtain ⟨i, hc, _, hExec⟩ := tauScoreSource ht
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hPc]; cases loop <;> decide
  rcases hExec with ⟨rfl, _⟩ | ⟨_, _, he⟩
  · rfl
  · have hFrame := (scoreExecLocal he).resolve_right (fun ⟨_, hm, _, _⟩ => hOff hm)
    have hKeep : r ∉ writesRegs i.op := by
      rw [hPc] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      cases loop
      · rw [show (scoreLoopSite .biased).increment + 2 = 6652 by decide, Flow.code_6652] at hc
        obtain rfl := Option.some.inj hc
        rcases hr with rfl | rfl <;> decide
      · rw [show (scoreLoopSite .plain).increment + 2 = 7603 by decide, Flow.code_7603] at hc
        obtain rfl := Option.some.inj hc
        rcases hr with rfl | rfl <;> decide
    exact hFrame.regs _ hKeep

private theorem tailFallthroughClean {l : Launch} {g : Nat} (loop : ScoreLoop)
    {s t : TState} (hPc : s.pc = (scoreLoopSite loop).increment + 3)
    (hPredicate : s.regs (scoreLoopSite loop).pred = some (.pred false))
    (hHealthy : s.fault = none) (ht : Tau kernel Assumptions.all l g s t) :
    t.sub = 0 ∧ t.acc = [] ∧ t.fault = none := by
  have hc : kernel.code[s.pc]? =
      some ⟨some ((scoreLoopSite loop).pred, false), .bra (scoreLoopSite loop).head false⟩ :=
    hPc.symm ▸ tailBranchCode loop
  have hSkip : Tau kernel Assumptions.all l g s (skip s) := by
    simp [Tau, out, hHealthy, hc, guardHolds, readReg, hPredicate, bind, Except.bind,
      pure, Except.pure]
  obtain rfl := tau_det ht hSkip
  exact ⟨rfl, rfl, hHealthy⟩

theorem scoreTailForLaterEvent {l : Launch} {g : Nat} (loop : ScoreLoop)
    {s : TState} {b : Bool} {es : List Event} {vs : List Visit} {target : Event}
    (hp : s.pc = (scoreLoopSite loop).increment + 2)
    (hR : s.regs (scoreLoopSite loop).pred = some (.pred b))
    (hw : Walk kernel Assumptions.all l g s es vs) (hm : target ∈ es)
    (hLate : (scoreLoopSite loop).increment + 4 ≤ target.pc) :
    ∃ u tail, u.pc = (if b then (scoreLoopSite loop).head else
      (scoreLoopSite loop).increment + 4) ∧
      u.sub ≤ s.sub ∧ u.regs (scoreLoopSite loop).word = s.regs (scoreLoopSite loop).word ∧
      (∀ r ∈ [1229, 1359], u.regs r = s.regs r) ∧
      (b = false → u.sub = 0 ∧ u.acc = [] ∧ u.fault = none) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      Walk kernel Assumptions.all l g u es tail := by
  cases hw with
  | stop => cases hm
  | ev h _ =>
    obtain ⟨m, hc, hl, _, _⟩ := tailMoveCode loop
    exact (noLocalEvent (hp.symm ▸ hc) hl h).elim
  | last h =>
    obtain rfl := List.mem_singleton.mp hm
    have hPc := estep_source_pc h
    omega
  | @tau s t es vs ht hw =>
    obtain ⟨hPc, hSub, hFault, hWord, hPred⟩ := tailMoveFrame loop hp ht
    have hR' := hPred.trans hR
    cases hw with
    | stop => cases hm
    | ev h _ =>
      have hc := tailBranchCode loop
      dsimp only at hc
      exact (noLocalEvent (hPc.symm ▸ hc) rfl h).elim
    | last h =>
      obtain rfl := List.mem_singleton.mp hm
      have hPc' := estep_source_pc h
      omega
    | tau hu hW =>
      obtain ⟨hEnd, hS, hU⟩ := tailBranchFrame loop hPc hR' hu
      refine ⟨_, _, hEnd, hS.trans hSub.le, (congrFun hU _).trans hWord,
        fun r hr => (congrFun hU _).trans (tailMoveKeepsGeometry loop hp ht hr),
        ?_, .tail (.single ht) hu, hW⟩
      rintro rfl
      exact tailFallthroughClean loop hPc hR' hFault hu

theorem distanceOnExit (loop : ScoreLoop) {w : Nat} (hw : w < 2^32)
    (he : (w+1) % 2^32 = (scoreLoopSite loop).sentinel) :
    scoreLoopDistance loop w = 1 := by
  by_cases hWrap : w+1 = 2^32
  · rw [hWrap, Nat.mod_self] at he
    cases loop
    · change 0 = 4294967295 at he
      cases he
    · simp [scoreLoopDistance, scoreLoopSite]
      omega
  · have hLt : w+1 < 2^32 := by omega
    rw [Nat.mod_eq_of_lt hLt] at he
    cases loop
    · change w+1 = 4294967295 at he
      change (if w < 4294967295 then 4294967295-w else 4294967296-w+4294967295) = 1
      rw [ite_eq_left (by omega)]
      omega
    · change w+1 = 0 at he
      omega

private theorem loopMarkerCountBounds {l : Launch} {g w : Nat} {s : TState}
    (loop : ScoreLoop) (probability : Bool) {es : List Event} {vs : List Visit} {target : Event}
    (hr : Walk kernel Assumptions.all l g s es vs)
    (hPc : s.pc = (scoreLoopSite loop).head) (hSub : s.sub ≤ 3)
    (hWord : s.regs (scoreLoopSite loop).word = some (b32 w)) (hw : w < 2^32)
    (hTarget : target ∈ es) (hLate : (scoreLoopSite loop).increment + 4 ≤ target.pc) :
    ∃ u before rest tail, es = before ++ rest ∧ target ∈ rest ∧
      u.pc = (scoreLoopSite loop).increment + 4 ∧
      before.countP (marker loop probability) = scoreLoopDistance loop w ∧
      (∀ r ∈ [1229, 1359], u.regs r = s.regs r) ∧
      u.sub = 0 ∧ u.acc = [] ∧ u.fault = none ∧
      Walk kernel Assumptions.all l g u rest tail ∧
      ∀ e ∈ before, windowHead loop ≤ e.pc ∧ e.pc < windowEnd loop := by
  generalize hd : scoreLoopDistance loop w = n
  induction n using Nat.strong_induction_on generalizing s es vs w with
  | h n ih =>
    have hHead : s.pc = windowHead loop := by cases loop <;> exact hPc
    have hSpan : windowHead loop < windowEnd loop := by cases loop <;> decide
    have hEndAfter : windowEnd loop < (scoreLoopSite loop).increment + 4 := by
      cases loop <;> decide
    have hRegion : scoreLoopRegion loop w s s :=
      ⟨hHead.ge, by omega, hSub, hWord, fun h => (by omega : False).elim, fun _ _ => rfl⟩
    have hCount : remaining loop probability s = 1 := by
      unfold remaining barrierRemaining
      rw [hHead]
      cases loop <;> cases probability <;> decide
    obtain ⟨v, pre, rest, tail, hEs, hIn, hV, hCut, hPre, hBounds, hv⟩ :=
      hr.cut_marked_where (P := scoreLoopRegion loop w s) (cut := fun t => t.pc = windowEnd loop)
        (good := fun e => windowHead loop ≤ e.pc ∧ e.pc < windowEnd loop)
        (remaining loop probability) (marker loop probability)
        (fun t _ h => by
          unfold remaining barrierRemaining
          rw [show t.pc = windowEnd loop from h]
          cases loop <;> cases probability <;> decide)
        (regionStep loop probability) (fun ht hn he => by
          rw [estep_source_pc he]
          exact ⟨ht.1,lt_of_le_of_ne ht.2.1 hn⟩)
        hRegion hTarget (fun t ht _ => by
          have h := ht.2.1
          omega)
    have hDone : v.pc = windowEnd loop := hCut
    have hInc : v.pc = (scoreLoopSite loop).increment := by cases loop <;> exact hDone
    obtain ⟨q, hRun, hQ, hQSub, _, hQWord, hPred, hKeep⟩ :=
      scoreLoopTestActualFrame loop hw (hV.2.2.2.2.1 hDone) hInc hV.2.2.2.1
    rcases advanceWalkLocals hRun hv with rfl | ⟨t, _, _, ht⟩
    · cases hIn
    obtain ⟨u, uTail, hu, huSub, huWord, huKeep, huClean, _, huWalk⟩ :=
      scoreTailForLaterEvent loop hQ hPred ht hIn hLate
    have hGeometry (r : Nat) (hR : r ∈ [1229, 1359]) : u.regs r = s.regs r := by
      have hStep : q.regs r = v.regs r := by
        apply hKeep <;> (
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
          rcases hR with rfl | rfl <;> cases loop <;> decide)
      exact (huKeep r hR).trans (hStep.trans (hV.2.2.2.2.2 r hR))
    let w' := (w+1) % 2^32
    change u.pc = (if decide (w' ≠ (scoreLoopSite loop).sentinel) then
      (scoreLoopSite loop).head else (scoreLoopSite loop).increment + 4) at hu
    by_cases hMore : w' ≠ (scoreLoopSite loop).sentinel
    · have hDist : scoreLoopDistance loop w' + 1 = n :=
        (scoreLoopDistance_step loop hw hMore).trans hd
      have hBack : u.pc = (scoreLoopSite loop).head := by
        rw [decide_eq_true hMore] at hu
        exact hu
      obtain ⟨out,mid,after,walk,hSplit,hAfter,hOut,hMid,hRegs,hS,hA,hF,hWalk,hMidBounds⟩ :=
        ih (scoreLoopDistance loop w') (by omega) huWalk hBack
          (huSub.trans (hQSub.symm ▸ hV.2.2.1)) (huWord.trans hQWord)
          (Nat.mod_lt _ (by decide)) hIn rfl
      refine ⟨out, pre ++ mid, after, walk, by rw [hEs, hSplit, List.append_assoc],
        hAfter, hOut, ?_, fun r hr => (hRegs r hr).trans (hGeometry r hr), hS, hA, hF, hWalk, ?_⟩
      · rw [List.countP_append, hPre, hCount, hMid]
        omega
      · intro e he
        exact (List.mem_append.mp he).elim (hBounds e) (hMidBounds e)
    · have hOut : u.pc = (scoreLoopSite loop).increment + 4 := by
        rw [decide_eq_false hMore] at hu
        exact hu
      have hOne : scoreLoopDistance loop w = 1 := distanceOnExit loop hw (not_ne_iff.mp hMore)
      have hExact := hPre.trans (hCount.trans (hd.symm.trans hOne).symm)
      have ⟨hS, hA, hF⟩ := huClean (decide_eq_false hMore)
      exact ⟨u, pre, rest, uTail, hEs, hIn, hOut, hExact, hGeometry, hS, hA, hF, huWalk,hBounds⟩

section
variable {l : Launch} {g w : Nat} {s : TState} (loop : ScoreLoop) {es : List Event}
    {vs : List Visit} {target : Event} (hr : Walk kernel Assumptions.all l g s es vs)
    (hPc : s.pc = (scoreLoopSite loop).head) (hSub : s.sub ≤ 3)
    (hWord : s.regs (scoreLoopSite loop).word = some (b32 w)) (hw : w < 2^32)
    (hTarget : target ∈ es)
include loop hr hPc hSub hWord hw hTarget

/-- A finite execution prefix that reaches beyond the loop has issued one statistics notice
in each of exactly the seeded counter's remaining rounds. -/
theorem loopPublicationCountBounds (hLate : (scoreLoopSite loop).increment + 4 ≤ target.pc) :
    ∃ u before rest tail, es = before ++ rest ∧ target ∈ rest ∧
      u.pc = (scoreLoopSite loop).increment + 4 ∧
      before.countP (loopPublication loop) = scoreLoopDistance loop w ∧
      (∀ r ∈ [1229, 1359], u.regs r = s.regs r) ∧
      u.sub = 0 ∧ u.acc = [] ∧ u.fault = none ∧
      Walk kernel Assumptions.all l g u rest tail ∧
      ∀ e ∈ before, windowHead loop ≤ e.pc ∧ e.pc < windowEnd loop :=
  loopMarkerCountBounds loop false hr hPc hSub hWord hw hTarget hLate

/-- A finite execution prefix that reaches beyond the loop has issued one early probability credit
in each of exactly the seeded counter's remaining rounds. -/
theorem loopProbabilityCountBounds (hLate : (scoreLoopSite loop).increment + 4 ≤ target.pc) :
    ∃ u before rest tail, es = before ++ rest ∧ target ∈ rest ∧
      u.pc = (scoreLoopSite loop).increment + 4 ∧
      before.countP (barrierMark (if loop = .biased then 6532 else 7437)) =
        scoreLoopDistance loop w ∧
      (∀ r ∈ [1229, 1359], u.regs r = s.regs r) ∧
      u.sub = 0 ∧ u.acc = [] ∧ u.fault = none ∧
      Walk kernel Assumptions.all l g u rest tail ∧
      ∀ e ∈ before, windowHead loop ≤ e.pc ∧ e.pc < windowEnd loop :=
  loopMarkerCountBounds loop true hr hPc hSub hWord hw hTarget hLate

end

/-- Each repeated score loop toggles the phase used by the statistics credit poll. -/
def loopCreditTogglePc : ScoreLoop → Nat
  | .biased => 6647
  | .plain => 7600

/-- The decoded word update advances the reusable credit phase by one. -/
theorem loopCreditToggle {l : Launch} {g : Nat} {s : TState} (loop : ScoreLoop) (phase : Bool)
    (hPc : s.pc = loopCreditTogglePc loop) (hF : s.fault = none)
    (hWord : s.regs 7258 = some (b32 phase.toNat)) :
    let u := next (setReg s 7258 (b32 (!phase).toNat))
    run kernel Assumptions.all l g 1 s = some u ∧
      u.pc = loopCreditTogglePc loop + 1 ∧ u.regs 7258 = some (b32 (!phase).toNat) := by
  let op := Op.int ⟨.xor, .int .b 32, false, [some 7258], [.reg 7258, .imm 1]⟩
  have hc : kernel.code[s.pc]? = some ⟨none, op⟩ := by
    rw [hPc]
    cases loop
    · exact Flow.code_6647
    · exact Flow.code_7600
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hPc]; cases loop <;> decide
  have hExec : execLocalA [] l g s op =
      .ok (next (setReg s 7258 (b32 (!phase).toNat))) := by
    dsimp only [op]
    rw [execLocalA_nil, execLocal_int rfl]
    have hR := readBits_b32 (L := l) (g := g) hWord (by cases phase <;> decide)
    simp only [execInt, DType.width, hR, bind, Except.bind, pure, Except.pure]
    cases phase <;> rfl
  have hCore := Assumptions.tauStep_all_eq_nil (L := l) (g := g) hOff hc rfl
  refine ⟨?_, by simp [next, setReg, hPc], by simp [next, setReg]⟩
  simp only [run]
  rw [hCore]
  simp only [tauStep, out, hF, hc, guardHolds, pure, Except.pure,
    show op.isLocal = true from rfl, ↓reduceIte, hExec, Option.bind_some]

end PTX.Kernels.TmlFa4Fwd.Softmax
