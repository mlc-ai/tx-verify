-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.BarrierOrdinals

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Flow PTX.EventFrame

variable {base : Nat → Nat → Nat} {L : Launch} {mem : Mem0} {X : Execution}

private theorem count_before (valid : Consistent L kernel (Prologue.assumptions base) mem X)
    (sites : StartupSites) {i : EvId} {e : Event} (seen : X.get i = some e) :
    ((X.tr i.1).take i.2).countP (atSync 379) = passedGate 379 e.pc := by
  obtain ⟨o,run⟩ := valid.thr i.1 (Step.CtaBar.thread_lt_of_get valid seen)
  obtain ⟨t,q,path,fire⟩ := run.before_event seen
  have h := barriers_passed (cut := 379) (by decide) (fun pc i p => (sites pc i p).1) path
  rw [estep_source_pc fire]
  simpa only [show passedGate 379 ({} : TState).pc = 0 by decide,Nat.add_zero] using h

private theorem before_late (valid : Consistent L kernel (Prologue.assumptions base) mem X)
    (sites : StartupSites) {i : EvId} {e : Event} (seen : X.get i = some e) (late : 379 < e.pc) :
    ∃ j < i.2, X.IsBarrier (i.1,j) 0 none 379 := by
  have h := count_before valid sites seen
  have pos : 0 < ((X.tr i.1).take i.2).countP (atSync 379) := by simp [h,passedGate,late]
  obtain ⟨ev,member,tag⟩ := List.countP_pos_iff.mp pos
  obtain ⟨j,low,eq⟩ := List.mem_take_iff_getElem.mp member
  refine ⟨j,by omega,?_⟩
  change (X.tr i.1)[j]? = _
  exact (List.getElem?_eq_getElem (by omega)).trans
    (congrArg some (eq.trans (atSync_iff.mp tag)))

private theorem read_before (valid : Consistent L kernel (Prologue.assumptions base) mem X)
    (sites : StartupSites) {g i j : Nat} {pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (read : X.get (g,i) = some ⟨pc,.rd a bs⟩) (early : pc < 379)
    (bar : X.IsBarrier (g,j) 0 none 379) : i < j := by
  have h := count_before valid sites read
  have zero : ((X.tr g).take i).countP (atSync 379) = 0 := by
    simpa [passedGate,show ¬379 < pc by omega] using h
  change (X.tr g)[j]? = some ⟨379,.bar 0 none .sync⟩ at bar
  obtain ⟨lt,ev⟩ := List.getElem?_eq_some_iff.mp bar
  rcases Nat.lt_trichotomy i j with h | rfl | h
  · exact h
  · change (X.tr g)[i]? = _ at read
    rw [read] at bar
    cases bar
  · exfalso
    have mem : (⟨379,.bar 0 none .sync⟩ : Event) ∈ (X.tr g).take i :=
      List.mem_take_iff_getElem.mpr ⟨j,by omega,ev⟩
    have pos := List.countP_pos_iff.mpr ⟨_,mem,atSync_iff.mpr rfl⟩
    omega

private theorem exit_late (valid : Consistent L kernel (Prologue.assumptions base) mem X)
    (sites : StartupSites) {i : EvId} {pc : Nat} (ex : X.get i = some ⟨pc,.exit⟩) :
    379 < pc := by
  rcases get_source valid ex with ⟨_,bad⟩ | ⟨t,ins,o,_,site,fire⟩
  · cases bad
  · have h := (sites _ _ site).1
    rcases fires_exit_op fire rfl with e | e <;> simpa [e,startupBranch] using h

private theorem ordinal_two (valid : Consistent L kernel (Prologue.assumptions base) mem X)
    (sites : StartupSites) {g j : Nat} (bar : X.IsBarrier (g,j) 0 none 379) :
    ((X.tr g).take j).countP (Execution.isBarId 0) = 2 := by
  have h := round_of_event valid sites bar
  change min 3 (((X.tr g).take j).countP (Execution.isBarId 0)) = 2 at h
  omega

theorem offset_before_write (valid : Consistent L kernel (Prologue.assumptions base) mem X)
    (done : Complete L X) (sites : StartupSites) (onlySync : kernel.NoBarArrive)
    (block : L.block = 192) (grid : L.grid = 1)
    {i : Nat} {pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (read : X.get (129,i) = some ⟨pc,.rd a bs⟩) (early : pc < 379)
    {e : EvId} {q : Nat} {dst : Acc} {data : List Byte} (w : X.get e = some ⟨q,.wr dst data⟩)
    (late : 379 < q) : baseCausality L X (129,i) e := by
  let : Fact kernel.NoBarArrive := ⟨onlySync⟩
  have reader := Step.CtaBar.thread_lt_of_get valid read
  have writer := Step.CtaBar.thread_lt_of_get valid w
  rcases done.1 129 reader with canceled | ⟨endPc,last⟩
  · change (X.tr 129)[i]? = some _ at read
    simp [canceled.1] at read
  · rw [List.getLast?_eq_getElem?] at last
    have ex : X.get (129,(X.tr 129).length-1) = some ⟨endPc,.exit⟩ := last
    obtain ⟨readerBar,_,rb⟩ := before_late valid sites ex (exit_late valid sites ex)
    obtain ⟨writerBar,prior,wb⟩ := before_late valid sites w late
    have readPrior := read_before valid sites read early rb
    have length := (List.getElem?_eq_some_iff.mp w).1
    have same : SameCta L 129 e.1 := by
      refine ⟨reader,writer,?_⟩
      simp only [Launch.threads,grid,block,Nat.one_mul] at writer
      simp [block,Nat.div_eq_of_lt writer]
    have right := ordinal_two valid sites wb
    exact NamedBar.early_same_ordinal_baseCausality valid (n := 6) (by decide)
      (by rw [block]; rfl) (Finset.card_range 6) (by rw [block]; simp) (by decide)
      (first_three_full valid sites block) same rb wb (by omega)
      ((ordinal_two valid sites rb).trans right.symm) (by omega) readPrior prior length

end FlashKda.Packed.ProducerControl
