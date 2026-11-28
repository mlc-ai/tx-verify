-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.LaunchLane
public import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
public import Kernels.InklingRelDecode.Proof.Lib.ResPcs
public import Kernels.InklingRelDecode.Proof.Epilogue.Tmem
public import Kernels.InklingRelDecode.Proof.Startup.Tmem
import Kernels.InklingRelDecode.Flow.Code.Part044
import Lemmas.Flow.NotBulk

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame PTX.Tmem.Pair

theorem tmem_op_pc {L m X g k ev} (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ev) (res : isTmemOp ev=true) : ev.pc ∈ Lib.resPcs := by
  obtain ⟨_,grp,dst,act,rfl⟩ := tmemOp_resource res
  obtain ⟨_,bad⟩|⟨_,_,_,_,hc,fire⟩ := get_source hX he
  · cases bad
  · exact Lib.res_pc' hc fire rfl

private theorem worker_sites {Q L g w x} (s : (workerCode Q L g w x).D)
    (hi : (workerCode Q L g w x).inv s) (high : 128≤g%L.block) :
    (workerCode Q L g w x).pc s ∉ Lib.resPcs := by
  rcases s with ⟨s,r⟩|⟨i,s⟩
  · change s.pc ∉ Lib.resPcs
    cases s <;> try decide
    have low := hi.1 rfl
    omega
  · cases i
    all_goals change s.site.pc ∉ Lib.resPcs
    all_goals generalize s.site=site
    all_goals cases site <;> repeat' first | decide +kernel | (rename_i j; revert j)

theorem worker_no_resource {Q L m X g k w x s n ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (he : X.get (g,k)=some ev)
    (hu : ∀ f, ev.kind≠.ub f) (hs : stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dispatch w x),s⟩,n))) : isTmemOp ev=false := by
  cases h : isTmemOp ev with
  | false => rfl
  | true =>
    have pc := event_pcU (fun g hg => thread_sound hp hg) hX he hs hu
    have hi := (reached_table hf (lt_of_get hX he) (noUbBefore_of_get hX he) hs).1
    have high := (worker_warp hp hX (List.getElem?_eq_some_iff.mp he).1.le hs).1
    exact (worker_sites s hi high (pc ▸ tmem_op_pc hX he h)).elim

private theorem data_sites {Q L g w} (s : (dataCode Q L g w).D) :
    (dataCode Q L g w).pc s ∈ Lib.resPcs → (dataCode Q L g w).pc s=2851 := by
  rcases s with s|⟨_,s|⟨_,s⟩⟩
  · have h := s.site.pc_range
    change s.site.pc ∈ Lib.resPcs → s.site.pc=2851
    simp only [Lib.resPcs,List.mem_cons,List.not_mem_nil,or_false]; omega
  · rcases s.site.pc_range with h|h
    · change s.site.pc ∈ Lib.resPcs → s.site.pc=2851
      simp only [Lib.resPcs,List.mem_cons,List.not_mem_nil,or_false]; omega
    · change s.site.pc ∈ Lib.resPcs → s.site.pc=2851
      rw [h]; decide
  · change s.site.pc ∈ Lib.resPcs → s.site.pc=2851
    generalize s.site=site
    cases site <;> repeat' first | decide +kernel | (rename_i j; revert j)

theorem data_resource {Q L m X g k w s n ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ev)
    (hu : ∀ f, ev.kind≠.ub f) (hs : stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.prologue w),s⟩,n))) :
    isTmemOp ev = decide ((dataCode Q L g w).pc s=2851) := by
  have pc := event_pcU (fun g hg => thread_sound hp hg) hX he hs hu
  change ev.pc=(dataCode Q L g w).pc s at pc
  by_cases hd : (dataCode Q L g w).pc s=2851
  · rw [decide_eq_true hd]
    obtain ⟨t,ins,o,ht,_,hc,fire⟩ := fired_siteU (fun g hg => thread_sound hp hg) hX he hs hu
    change kernel.code[(dataCode Q L g w).pc s]?=_ at hc
    change Fires ((dataCode Q L g w).pc s) _ ev o at fire
    rw [hd] at hc fire
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2851)
    obtain ⟨_,eq⟩|⟨_,_,eq⟩ := fires_tmemTmpl tmemTmpl_dealloc fire
    · cases eq; exact (hu _ rfl).elim
    · cases ev; cases eq; rfl
  · rw [decide_eq_false hd]
    cases e : isTmemOp ev with
    | false => rfl
    | true => exact (hd (data_sites s (pc ▸ tmem_op_pc hX he e))).elim

end PTX.Kernels.InklingRelDecode.Proof
