-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.LoopRoute
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Increment
import Kernels.InklingRelDecode.Flow.Code.Part015
import Lemmas.Flow.Step.Combinators
import Lemmas.Flow.SegPieces

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g i : Nat} {v : Carry}
local notation "tid" => g % L.block

private theorem next_round (s : Site) (lt : i < e.limit) (ok : e.Ok)
    (sub : ∀ r ∈ ctlLive 1046, r ∈ ctlLive s.pc) :
    let d := advance e tid ⟨s,i,v⟩
    SegU kernel Assumptions.all L g 1014 (facts e L g ⟨s,i,v⟩ s.pc) d.site.pc
      (facts e L g d d.site.pc) := by
  apply (before_increment sub).comp
  apply (increment (i := i) (z := loopSite e tid (i+1))).comp
  exact loop_route ok (by omega)

theorem step_arrive : (code e L g).StepAtU ⟨.arrive,i,v⟩ := by
  apply step_of_inv
  intro hi
  have lt : i < e.limit := hi.loop nofun nofun nofun (fun _ => nofun)
  have lead := hi.lead rfl
  have guard : Code.GuardTrue (facts e L g ⟨.arrive,i,v⟩ 1013) (some (177,false)) := by
    apply Code.guardTrue_factsFrom (by decide : 177 ∈ ctlLive 1013)
    change Value.pred (decide (tid % 128 = 0)) = .pred true
    simp [lead]
  refine ⟨fun _ => ⟨_,Flow.code_1013,rfl,guard⟩,?_⟩
  intro t ev u ins hat _ get hf
  obtain rfl := Option.some.inj (get.symm.trans Flow.code_1013)
  have hu : u = PTX.next t := Code.fires_arrive_next hf
  subst u
  let dn := advance e tid ⟨.arrive,i,v⟩
  have hInv : (code e L g).inv dn := loop_inv hi.entry hi.thread (by omega : i+1 ≤ e.limit)
  obtain ⟨u,hl,hu⟩ := Code.landsU (C := code e L g) (d := dn)
    (At.next (Code.at_of_atD (C := code e L g) hat rfl rfl))
    (next_round .arrive lt hi.entry (by decide +kernel)) hInv rfl rfl
  exact .inl (.inr ⟨dn,u,rfl,hl,hu⟩)

theorem step_bar21 : (code e L g).StepAtU ⟨.bar21,i,v⟩ := by
  apply step_of_inv
  intro hi
  have lt := hi.iter_lt (by decide : SiteBody .bar21)
  by_cases lead : tid % 128 = 0
  · have hInv : Inv e tid ⟨.arrive,i,v⟩ :=
      ⟨hi.entry,hi.thread,hi.bound,(by rintro (h|h) <;> cases h),
        fun _ => nofun,fun _ => nofun,fun _ => lead,fun _ _ _ _ => lt⟩
    apply Code.advanceU (C := code e L g) (d := ⟨.bar21,i,v⟩) (dn := ⟨.arrive,i,v⟩)
      Flow.code_1012 rfl fires_barSyncN_next (fun _ => by simp [next,lead])
      rfl rfl rfl rfl hInv
    exact project_seg (p := 1012) (q := 1013) (by decide +kernel)
  · let dn := advance e tid ⟨.bar21,i,v⟩
    have hInv : (code e L g).inv dn := loop_inv hi.entry hi.thread (by omega : i+1 ≤ e.limit)
    apply Code.advanceU (C := code e L g) (d := ⟨.bar21,i,v⟩) (dn := dn)
      Flow.code_1012 rfl fires_barSyncN_next
      (fun _ => by simp [next,lead,dn]) rfl rfl rfl rfl hInv
    have off : (177,Value.pred false) ∈ facts e L g ⟨.bar21,i,v⟩ 1012 := by
      apply mem_factsFrom_eq (by decide : 177 ∈ ctlLive 1012)
      change Value.pred (decide (tid % 128 = 0)) = .pred false
      simp [lead]
    exact (SegU.of_seg (Seg.guardSkip Flow.code_1013 off rfl)).comp
      (next_round .bar21 lt hi.entry (by decide +kernel))

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
