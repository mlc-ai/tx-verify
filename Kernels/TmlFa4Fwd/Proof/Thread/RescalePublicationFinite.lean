-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsStoreGeometry
public import Kernels.TmlFa4Fwd.Proof.SoftmaxAlpha
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Lemmas.Execution.EventFrameSource
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Lemmas.Flow.ContinuingEvent
import Lemmas.Flow.MemTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.EventFrame PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

private def rescaleStoreInst (biased : Bool) : Instr :=
  let site := statsStore (rescaleStore biased)
  ⟨none, .mem {
    kind := .store
    space := some (.shared .cta)
    sem := .weak
    elem := .int .b 32
    addr := ⟨.reg site.base 32, site.offset⟩
    srcs := [.reg site.word] }⟩

private theorem rescaleStoreCode (biased : Bool) :
    kernel.code[(statsStore (rescaleStore biased)).pc]? = some (rescaleStoreInst biased) := by
  cases biased
  · exact Flow.code_6890
  · exact Flow.code_5682

private def rescaleQuietReg (biased maximum : Bool) : Nat :=
  if maximum then 7256 else (alphaSite biased).alpha

private theorem rescaleQuietCode (biased maximum : Bool) {pc : Nat} {ins : Instr}
    (hLo : (alphaSite biased).pc+7 ≤ pc) (hHi : pc < (statsStore (rescaleStore biased)).pc)
    (hc : kernel.code[pc]? = some ins) :
    Epilogue.schedulerFallsThrough ins.op = true ∧
      rescaleQuietReg biased maximum ∉ writesRegs ins.op := by
  let lo := (alphaSite biased).pc+7
  let hi := (statsStore (rescaleStore biased)).pc
  have hAll : ((kernel.code.drop lo).take (hi-lo)).all (fun i =>
      Epilogue.schedulerFallsThrough i.op &&
        !(writesRegs i.op).contains (rescaleQuietReg biased maximum)) = true := by
    cases biased <;> cases maximum <;> decide +kernel
  have hMem : ins ∈ (kernel.code.drop lo).take (hi-lo) := by
    apply List.mem_of_getElem? (i := pc-lo)
    rw [List.getElem?_take_of_lt (Nat.sub_lt_sub_right hLo hHi),List.getElem?_drop,
      Nat.add_sub_of_le hLo,hc]
  simpa only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] using List.all_eq_true.mp hAll ins hMem

private theorem rescaleQuietStep (biased maximum : Bool) {l : Launch} {g : Nat} {s u : TState}
    (hLo : (alphaSite biased).pc+7 ≤ s.pc) (hHi : s.pc ≤ (statsStore (rescaleStore biased)).pc)
    (hStep : Tau kernel Assumptions.all l g s u) :
    u.pc = s.pc+1 ∧ u.pc ≤ (statsStore (rescaleStore biased)).pc ∧
      u.regs (rescaleQuietReg biased maximum) = s.regs (rescaleQuietReg biased maximum) := by
  obtain ⟨ins,hc,_,hLocal⟩ := tauScoreSource hStep
  have hLt : s.pc < (statsStore (rescaleStore biased)).pc := by
    refine lt_of_le_of_ne hHi ?_
    intro hEq
    rw [hEq,rescaleStoreCode biased] at hc
    obtain rfl := Option.some.inj hc
    rcases hLocal with ⟨_,hGuard⟩ | ⟨_,hIsLocal,_⟩
    · cases hGuard
    · cases biased <;> cases hIsLocal
  obtain ⟨hForward,hKeep⟩ := rescaleQuietCode biased maximum hLo hLt hc
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by
    cases biased
    · change 6886 ≤ s.pc at hLo
      change s.pc < 6890 at hLt
      simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false]
      omega
    · change 5675 ≤ s.pc at hLo
      change s.pc < 5682 at hLt
      simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false]
      omega
  rcases hLocal with ⟨rfl,_⟩ | ⟨_,_,hx⟩
  · exact ⟨rfl,by change s.pc+1 ≤ _; omega,rfl⟩
  have hF := (scoreExecLocal hx).resolve_right (fun ⟨_, hM, _, _⟩ => hOff hM)
  have hPc : u.pc = s.pc+1 := by
    have he := hF.pc
    cases hi : ins.op <;>
      simp [hi, Epilogue.schedulerFallsThrough, nextPc, BrxTarget] at hForward he
    all_goals exact he
  exact ⟨hPc,by omega,hF.regs _ hKeep⟩

private theorem rescaleQuietFrame (biased maximum : Bool) {l : Launch} {g : Nat} {s u : TState}
    {events : List Event} (h : TraceReach kernel Assumptions.all l g s events u)
    (hEmpty : events = [])
    (hLo : (alphaSite biased).pc+7 ≤ s.pc)
    (hHi : s.pc ≤ (statsStore (rescaleStore biased)).pc) :
    u.regs (rescaleQuietReg biased maximum) = s.regs (rescaleQuietReg biased maximum) := by
  induction h with
  | refl => rfl
  | tau ht _ ih =>
    obtain ⟨hPc,hUpper,hKeep⟩ := rescaleQuietStep biased maximum hLo hHi ht
    exact (ih hEmpty (by omega) hUpper).trans hKeep
  | event => cases hEmpty

/-- A returning event at the decoded rescale publication is its shared store. -/
theorem rescaleStoreEventKind (biased : Bool) {l : Launch} {g : Nat} {s u : TState}
    {e : Event} (hs : s.pc = (statsStore (rescaleStore biased)).pc)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ a bytes, e.kind = .wr a bytes := by
  obtain ⟨ins,hc,_,hf⟩ := estep_event_source he
  rw [hs,rescaleStoreCode biased] at hc
  obtain rfl := Option.some.inj hc
  let base := (statsStore (rescaleStore biased)).base
  have hf' : Fires s.pc (storeTmpl l g s .shared 32 base 368
      [.reg (alphaSite biased).alpha]) e (some u) := by
    cases biased <;> exact hf
  unfold storeTmpl at hf'
  cases hAddr : effAddr l g s .shared base 368 with
  | error f =>
    simp only [hAddr,bind,Except.bind] at hf'
    cases hf'.2
  | ok loc =>
    simp only [hAddr,bind,Except.bind,List.length_singleton] at hf'
    repeat' split at hf'
    all_goals solve
      | exact ⟨_,_,congrArg Event.kind hf'.1⟩
      | cases hf'.2

private theorem rescaleStoreData (biased : Bool) {l : Launch} {g : Nat} {s : TState}
    {a : Acc} {data : List Byte} {word : Value} {o : Option TState}
    (hs : s.pc = (statsStore (rescaleStore biased)).pc)
    (hw : s.regs (alphaSite biased).alpha = some word) (hWidth : word.bytes = 4)
    (he : EStep kernel Assumptions.all l g s ⟨s.pc, .wr a data⟩ o) :
    data = word.toBytes := by
  have hSome : ∃ u, o = some u := by
    cases o with
    | some u => exact ⟨u,rfl⟩
    | none =>
      obtain ⟨_,_,hf⟩ := he
      rcases fires_none_ends hf with ⟨_,h⟩ | h <;> exact Kind.noConfusion h
  obtain ⟨u,rfl⟩ := hSome
  obtain ⟨ins,hc,_,hf⟩ := estep_event_source he
  rw [hs,rescaleStoreCode biased] at hc
  obtain rfl := Option.some.inj hc
  let base := (statsStore (rescaleStore biased)).base
  have hf' : Fires s.pc (storeTmpl l g s .shared 32 base 368
      [.reg (alphaSite biased).alpha]) ⟨s.pc, .wr a data⟩ (some u) := by
    cases biased <;> exact hf
  unfold storeTmpl at hf'
  cases hAddr : effAddr l g s .shared base 368 with
  | error f =>
    simp only [hAddr, bind, Except.bind] at hf'
    cases hf'.2
  | ok loc =>
    simp only [hAddr, bind, Except.bind, List.length_singleton] at hf'
    split at hf'
    · cases hf'.2
    · cases hs : s.sub with
      | succ k =>
        simp only [hs, List.getElem?_cons_succ, List.getElem?_nil] at hf'
        cases hf'.2
      | zero =>
        simp only [hs, List.getElem?_cons_zero, readValue, readReg, hw,
          storeValue_of_bytes (w := 32) hWidth, pure, Except.pure] at hf'
        exact (Kind.wr.inj (congrArg Event.kind hf'.1)).2

/-- Canonical prior and candidate scores at the actual arithmetic entry suffice
to determine the rescale bytes, including when the lane is suspended at the store. -/
theorem rescaleSourceOfArithmeticEntry {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (biased : Bool) {g j : Nat}
    {t : TState} {ending : Option TState} {a : Acc} {data : List Byte}
    (old candidate : Option ℝ) {scaleWord : Value}
    (hScale : readEReal .f32 scaleWord = some (.ok (abiFloat p.scaleLog2Bits : EReal)))
    (ht : At t (alphaSite biased).pc [])
    (hRead : ∀ r ∈ (alphaSite biased).inputs,
      t.regs r = some ((alphaSite biased).valuesOfWord scaleWord old candidate r))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (he : StatisticsStore X (g,j) (rescaleStore biased) a data) :
    ∃ v o, TraceReach kernel Assumptions.all l g t [] v ∧
      EStep kernel Assumptions.all l g v ⟨(statsStore (rescaleStore biased)).pc,.wr a data⟩ o ∧
      v.regs 7256 = some (scoreValue (chosenReference (abiFloat p.scaleLog2Bits) old candidate)) ∧
      data = (alphaWord (abiFloat p.scaleLog2Bits) old candidate).toBytes := by
  obtain ⟨u,hLocal,hU,_⟩ :=
    alphaSegmentWithScaleWord biased (scalePositive hp).1 old candidate hScale ht hRead
  have hEvent : ((X.tr g).drop j)[0]? =
      some ⟨(statsStore (rescaleStore biased)).pc, .wr a data⟩ := by
    rw [List.getElem?_drop,Nat.add_zero]
    exact he
  have hRun := hr.after_local_nonempty (run_rtg hLocal) (by
    intro h
    simp [h] at hEvent)
  obtain ⟨v,o,hTrace,hStep⟩ := hRun.before_event hEvent
  have hPc : v.pc = (statsStore (rescaleStore biased)).pc := (estep_source_pc hStep).symm
  have hBound : (alphaSite biased).pc+7 ≤ (statsStore (rescaleStore biased)).pc := by
    cases biased <;> decide
  have hFrame := rescaleQuietFrame biased false hTrace (by simp) hU.1.ge (hU.1.symm ▸ hBound)
  have hMaximum := rescaleQuietFrame biased true hTrace (by simp) hU.1.ge (hU.1.symm ▸ hBound)
  have hAlpha := hFrame.trans hU.2.2.2.2.2.2.1
  have hMax := hMaximum.trans hU.2.2.2.2.1
  have hReach : TraceReach kernel Assumptions.all l g t [] v := by
    have h := (TraceReach.of_local (run_rtg hLocal)).append hTrace
    simpa only [List.take_zero,List.nil_append] using h
  have hWidth : (alphaWord (abiFloat p.scaleLog2Bits) old candidate).bytes = 4 := by
    unfold alphaWord
    split <;> rfl
  refine ⟨v,o,hReach,hStep,hMax,
    rescaleStoreData (l := l) (g := g) (a := a) (o := o) biased hPc hAlpha hWidth ?_⟩
  rwa [hPc]

/-- The actual event's arithmetic entry carries canonical scalar scores and the ABI scale. -/
def RescaleArithmeticEntry (p : Params) (l : Launch) (X : Execution) (i : EvId)
    (biased : Bool) : Prop :=
  ∃ t ending old candidate scaleWord,
    At t (alphaSite biased).pc [] ∧
    readEReal .f32 scaleWord = some (.ok (abiFloat p.scaleLog2Bits : EReal)) ∧
    (∀ r ∈ (alphaSite biased).inputs,
      t.regs r = some ((alphaSite biased).valuesOfWord scaleWord old candidate r)) ∧
    Run kernel Assumptions.all l i.1 t ((X.tr i.1).drop i.2) ending

/-- An arithmetic entry identifies the exact finite coefficient published by this
lane, whether or not its trace reaches the following notification. -/
theorem RescaleArithmeticEntry.data {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {i : EvId} {biased : Bool} {a : Acc} {bytes : List Byte}
    (hEntry : RescaleArithmeticEntry p l X i biased)
    (hStore : StatisticsStore X i (rescaleStore biased) a bytes) :
    ∃ old candidate, bytes = (alphaWord (abiFloat p.scaleLog2Bits) old candidate).toBytes := by
  obtain ⟨t,ending,old,candidate,word,hAt,hScale,hRead,hRun⟩ := hEntry
  obtain ⟨_,_,_,_,_,hData⟩ :=
    rescaleSourceOfArithmeticEntry hp biased old candidate hScale hAt hRead hRun hStore
  exact ⟨old,candidate,hData⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
