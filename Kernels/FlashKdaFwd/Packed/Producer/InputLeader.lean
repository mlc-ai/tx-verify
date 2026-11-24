-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Prefix
import all Kernels.FlashKdaFwd.Packed.Producer.OffsetRegisters
import all Kernels.FlashKdaFwd.Packed.Producer
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Proof

structure LoaderState (t : TState) : Prop where
  thread : t.regs 307 = some (b32 129)
  offsets : t.regs 2247 = some (b64 65536)
  leader : t.regs 88 = some (.pred false)
  scalar : t.sub = 0
  fresh : t.acc = []
  clear : t.fault = none

private def header (t : TState) :=
  (t.pc,t.regs 331,t.regs 307,t.regs 2247,t.sub,t.acc,t.fault)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem before (base : Nat → Nat → Nat) (L : Launch) :
    (localWindow base (Producer.launch L) 13 19 19 (Prologue.ready 65536)).map header =
      some (32,some (b32 0xffffffff),some (b32 129),some (b64 65536),0,[],none) := by kernel_rfl

private def afterFields (t : TState) :=
  (t.pc,t.regs 88,t.regs 307,t.regs 2247,t.sub,t.acc,t.fault)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem afterChoice (base : Nat → Nat → Nat) (L : Launch) (t : TState) :
    (localWindow base L 33 9 9 (Producer.chosen {t with pc := 32,fault := none} 1)).map
      afterFields = some (48,some (.pred false),t.regs 307,t.regs 2247,t.sub,t.acc,none) := by
  kernel_rfl

theorem elected_input_state (base : Nat → Nat → Nat) (L : Launch) (block : L.block = 192)
    (threads : L.ntid = ⟨192,1,1⟩) (host : L.params (Prologue.param 15) = some 65536) :
    ∃ t u, Run kernel (Prologue.assumptions base) L 129 {}
      [⟨32,.elect 0xffffffff 0 1⟩] (some t) ∧
      run kernel (Prologue.assumptions base) L 129 9 t = some u ∧ u.pc = 48 ∧ LoaderState u := by
  have input := Entry.parameters base L 129 65536 host
  have h := before base L
  have shape : Producer.launch L = L := by unfold Producer.launch; rw [← threads,← block]
  rw [shape] at h
  obtain ⟨s,steps,fields⟩ := Option.map_eq_some_iff.mp h
  simp only [header,Prod.mk.injEq] at fields
  obtain ⟨pc,mask,idReg,offset,sub,acc,clear⟩ := fields
  have site : kernel.code[s.pc]? = some Election.elect := by
    rw [pc]; exact fetch (pc := 32) (i := 0) (by decide) (by decide) Election.sites.1
  have out' : out kernel (Prologue.assumptions base) L 129 s =
      .ev (.elect 0xffffffff fun n => next (setReg (setReg s 3415 (b32 n)) 3416
        (.pred (laneOf L 129 == n)))) := by
    rw [out_event clear site (by rfl) (by rfl)]
    exact congrArg Out.ev (Election.choose L 129 s mask)
  have lane : laneOf L 129 = 1 := by unfold laneOf; rw [block]
  have after := afterChoice base L s
  have same : {s with pc := 32,fault := none} = s := by rw [← pc,← clear]
  rw [same] at after
  obtain ⟨u,post,vals⟩ := Option.map_eq_some_iff.mp after
  simp only [afterFields,Prod.mk.injEq] at vals
  obtain ⟨finish,leader,tid,addr,scalar,fresh,good⟩ := vals
  refine ⟨Producer.chosen s 1,u,.step (run_rtg (run_comp input (localWindow_sound (by decide)
    steps))) ⟨_,out',0,1,by rw [pc],by simp [Producer.chosen,lane]⟩ (.nil _),
    localWindow_sound (by decide) post,finish,tid.trans idReg,addr.trans offset,leader,
      scalar.trans sub,fresh.trans acc,good⟩

end FlashKda.Packed.ProducerControl
