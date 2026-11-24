-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxStatistics
import Kernels.TmlFa4Fwd.Proof.MarkedBarrierCut
import Kernels.TmlFa4Fwd.Flow.Code.Part118
import Kernels.TmlFa4Fwd.Flow.Code.Part119

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction

open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Prologue
open PTX.Kernels.TmlFa4Fwd.Correction

private def terminalInterior (pc : Nat) : Bool :=
  pc == 7615 || pc == 7616

private def avoidsTerminalEntry (i : Instr) : Bool :=
  match i.op with
  | .bra dst _ => !terminalInterior dst
  | .brx _ dsts _ => !(dsts.any terminalInterior)
  | _ => true

private theorem terminalEntryCode {pc : Nat} {i : Instr} (hc : kernel.code[pc]? = some i) :
    avoidsTerminalEntry i = true ∧ (i.op.isLocal || Epilogue.ordinaryEvent i.op) = true := by
  have h : kernel.code.all (fun ins =>
      avoidsTerminalEntry ins && (ins.op.isLocal || Epilogue.ordinaryEvent ins.op)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  exact Bool.and_eq_true_iff.mp (List.all_eq_true.mp h _ (List.mem_of_getElem? hc))

private theorem terminalEntrySegment {pc : Nat} {m : SegMatch CuteSlot}
    (hs : pc ∈ Assumptions.swExp2Sites) (hm : cuteExp2.matchAt kernel pc = some m) :
    terminalInterior m.stop = false := by
  have h : Assumptions.swExp2Sites.all (fun src =>
      match cuteExp2.matchAt kernel src with
      | none => false
      | some mat => !terminalInterior mat.stop) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hAll := List.all_eq_true.mp h pc hs
  rw [hm] at hAll
  simpa using hAll

private theorem noTerminalStoreTau {l : Launch} {g : Nat} {s u : TState}
    (hpc : s.pc = 7614 ∨ s.pc = 7615) (hStep : Tau kernel Assumptions.all l g s u) : False := by
  obtain ⟨i, hc, _, hSource⟩ := Softmax.tauScoreSource hStep
  rcases hpc with h | h
  · rw [h, Flow.code_7614] at hc
    obtain rfl := Option.some.inj hc
    rcases hSource with ⟨_, h⟩ | ⟨_, h, _⟩ <;> cases h
  · rw [h, Flow.code_7615] at hc
    obtain rfl := Option.some.inj hc
    rcases hSource with ⟨_, h⟩ | ⟨_, h, _⟩ <;> cases h

private theorem noTerminalInteriorTau {l : Launch} {g : Nat} {s u : TState}
    (hStep : Tau kernel Assumptions.all l g s u) : terminalInterior u.pc = false := by
  obtain ⟨i, hc, _, hSource⟩ := Softmax.tauScoreSource hStep
  have hSucc (hu : u.pc = s.pc + 1) : terminalInterior u.pc = false := by
    by_contra hBad
    have h : u.pc = 7615 ∨ u.pc = 7616 := by
      simpa only [terminalInterior, Bool.or_eq_true, beq_iff_eq] using Bool.eq_true_of_ne_false hBad
    exact noTerminalStoreTau (by omega) hStep
  rcases hSource with ⟨rfl, _⟩ | ⟨_, _, ht⟩
  · exact hSucc rfl
  rcases Softmax.scoreExecLocal ht with hFrame | ⟨m, hs, hm, hRun⟩
  · have hAllow := (terminalEntryCode hc).1
    rcases hFrame.pc with hpc | hpc
    · cases hop : i.op <;> simp only [hop, nextPc] at hpc
      case bra dst uni =>
        rw [hpc]
        simpa [avoidsTerminalEntry, hop] using hAllow
      all_goals exact hSucc hpc
    · cases hop : i.op <;> simp only [hop, BrxTarget] at hpc
      case brx index targets uni =>
        have hNo : targets.any terminalInterior = false := by
          simpa [avoidsTerminalEntry, hop] using hAllow
        rw [List.any_eq_false] at hNo
        exact Bool.eq_false_iff.mpr (hNo _ hpc)
  · exact (Softmax.scoreSegmentFrame hRun).1.symm ▸ terminalEntrySegment hs hm

private theorem scalarStoreContinues {l : Launch} {s u : TState} {g base src : Nat}
    {off : Int} {e : Event}
    (hf : Fires s.pc (storeTmpl l g s .shared 32 base off [.reg src]) e (some u)) :
    u.pc = s.pc + 1 ∧ ∃ a bs, e.kind = .wr a bs := by
  unfold storeTmpl at hf
  repeat' split at hf
  all_goals first
    | have hu := Option.some.inj hf.2
      exact ⟨by rw [hu]; simp [afterStore], _, _, congrArg Event.kind hf.1⟩
    | cases hf.2

private theorem terminalStoreAt {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hPc : s.pc = 7614 ∨ s.pc = 7615) (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.pc = s.pc + 1 ∧ ∃ a bs, e.kind = .wr a bs := by
  obtain ⟨i, hc, _, hf⟩ := estep_event_source he
  rcases hPc with h | h
  · rw [h, Flow.code_7614] at hc
    obtain rfl := Option.some.inj hc
    exact scalarStoreContinues (base := 5814) (off := 368) (src := 7257) hf
  · rw [h, Flow.code_7615] at hc
    obtain rfl := Option.some.inj hc
    exact scalarStoreContinues (base := 5814) (off := 1392) (src := 7256) hf

private theorem terminalInteriorEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (he : EStep kernel Assumptions.all l g s e (some u)) (hIn : terminalInterior u.pc = true) :
    u.pc = s.pc + 1 ∧ ∃ a bs, e = ⟨s.pc, .wr a bs⟩ := by
  have hPc : u.pc = 7615 ∨ u.pc = 7616 := by
    simpa only [terminalInterior, Bool.or_eq_true, beq_iff_eq] using hIn
  obtain ⟨i, hc, hLocal, hf⟩ := estep_event_source he
  have hOrd := (terminalEntryCode hc).2
  simp only [hLocal, Bool.false_or] at hOrd
  have hMove : u.pc = s.pc + 1 := by
    rcases callbackFrame_fires (Epilogue.ordinaryEventFrame hOrd) hf with h | h
    · have hs : s.pc = 7615 ∨ s.pc = 7616 := by omega
      rcases hs with hs | hs
      · have := (terminalStoreAt (.inr hs) he).1
        omega
      · have := followsMarkedBarrier hs Flow.code_7616 rfl he
        omega
    · exact h
  obtain ⟨a, bs, hk⟩ := (terminalStoreAt (by omega) he).2
  have hSource := estep_source_pc he
  exact ⟨hMove, a, bs, by cases e; congr⟩

private def ProducerTail (es : List Event) (state : TState) : Prop :=
  (state.pc = 7615 → ∃ pre a sum, es = pre ++ [⟨7614, .wr a sum⟩]) ∧
  (state.pc = 7616 → ∃ pre a b sum maximum,
    es = pre ++ [⟨7614, .wr a sum⟩, ⟨7615, .wr b maximum⟩])

private theorem terminalReach {l : Launch} {g : Nat} {s u : TState} {es : List Event}
    (hr : TraceReach kernel Assumptions.all l g s es u) (seen : List Event)
    (hTail : ProducerTail seen s) : ProducerTail (seen ++ es) u := by
  induction hr generalizing seen with
  | refl => simpa using hTail
  | tau ht _ ih =>
    apply ih seen
    have hNo := noTerminalInteriorTau ht
    constructor <;> intro h <;> simp [terminalInterior, h] at hNo
  | @event s v u es e he _ ih =>
    rw [show e :: es = [e] ++ es by rfl, ← List.append_assoc]
    apply ih (seen ++ [e])
    constructor
    · intro hv
      obtain ⟨hMove, a, bs, hE⟩ := terminalInteriorEvent he (by simp [terminalInterior, hv])
      have hs : s.pc = 7614 := by omega
      exact ⟨seen, a, bs, by rw [hE, hs]⟩
    · intro hv
      obtain ⟨hMove, b, max, hE⟩ := terminalInteriorEvent he (by simp [terminalInterior, hv])
      have hs : s.pc = 7615 := by omega
      obtain ⟨pre, a, sum, hS⟩ := hTail.1 hs
      exact ⟨pre, a, b, sum, max, by rw [hS, hE, hs, List.append_assoc]; rfl⟩

/-- The observed final publication follows the two actual stores in the producing lane. -/
theorem terminalStoresOfPublicationAtSites {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g publication : Nat}
    (hPub : Scores.Publishes X (g, publication) .final) :
    ∃ first, first + 2 = publication ∧ ∃ sumAcc maxAcc sum maximum,
      X.get (g, first) = some ⟨7614, .wr sumAcc sum⟩ ∧
      X.get (g, first + 1) = some ⟨7615, .wr maxAcc maximum⟩ := by
  obtain ⟨e, he, hNotice⟩ := hPub
  have hSite : e.pc = 7616 := by
    unfold Scores.notice at hNotice
    split at hNotice <;> try contradiction
    unfold Scores.noticeRound at hNotice
    split at hNotice <;> simp_all
  obtain ⟨_, hr⟩ := hX.thr _ (event_thread_lt hX he)
  obtain ⟨s, _, hReach, hStep⟩ := hr.before_event he
  have hs : s.pc = 7616 := (estep_source_pc hStep).symm.trans hSite
  obtain ⟨pre, a, b, sum, maximum, hList⟩ :=
    (terminalReach hReach [] (by simp [ProducerTail])).2 hs
  simp only [List.nil_append] at hList
  have hLen : publication < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hFirst := congrArg List.length hList
  simp only [List.length_take, List.length_append, List.length_cons, List.length_nil,
    Nat.min_eq_left (Nat.le_of_lt hLen)] at hFirst
  refine ⟨pre.length, by omega, a, b, sum, maximum, ?_, ?_⟩
  · change (X.tr g)[pre.length]? = _
    rw [← List.getElem?_take_of_lt (by omega : pre.length < publication), hList,
      List.getElem?_append_right (by rfl), Nat.sub_self]
    rfl
  · change (X.tr g)[pre.length + 1]? = _
    rw [← List.getElem?_take_of_lt (by omega : pre.length + 1 < publication), hList,
      List.getElem?_append_right (by omega),
      show pre.length + 1 - pre.length = 1 by omega]
    rfl

/-- The observed final publication follows the two actual stores in the producing lane. -/
theorem terminalStoresOfPublication {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g publication : Nat}
    (hPub : Scores.Publishes X (g, publication) .final) :
    ∃ first, first + 2 = publication ∧ ∃ sumAcc maxAcc sum maximum,
      X.Writes (g, first) sumAcc sum ∧ X.Writes (g, first + 1) maxAcc maximum := by
  obtain ⟨first, hFirst, a, b, sum, maximum, hS, hM⟩ := terminalStoresOfPublicationAtSites hX hPub
  exact ⟨first, hFirst, a, b, sum, maximum, ⟨_, hS⟩, ⟨_, hM⟩⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
