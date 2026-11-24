-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Lemmas.Flow.ProjectU

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow
noncomputable section

variable {p : Params} {L : Launch} {g : Nat}

theorem facts_erase (a : Softmax.D) :
    (code p L g).facts (erase a) = (Softmax.code p L g).facts a := by
  obtain ⟨s,v,k,acc⟩ := a
  cases s <;> rfl

theorem good_erase {a : Softmax.D} {t : TState} (h : (Softmax.code p L g).Good (some a) t) :
    (code p L g).Good (some (erase a)) t := by
  obtain ⟨⟨hpc, hsub, hacc, hfault, hr⟩, hi⟩ := h
  refine ⟨⟨hpc,hsub,hacc,hfault,facts_erase a ▸ hr⟩, ?_⟩
  obtain ⟨s,v,k,acc⟩ := a
  cases s with
  | bld b c =>
    rcases hi with ⟨rfl,rfl,_⟩ | ⟨hlen,_⟩
    · rfl
    · exact hlen
  | _ => exact hi

def readsData : Site → Bool
  | .sld .. | .bld .. => true
  | _ => false

private theorem inv_of_control {d : D} (hs : readsData d.site = false) :
    Inv d → (Softmax.code p L g).inv d.scheduler := by
  obtain ⟨s,v,k,acc⟩ := d
  cases s <;> first | exact id | cases hs

private theorem next_of_control {d : D} (hs : readsData d.site = false) (e : Event) :
    succ p L g d e = (Softmax.succ p L g d.scheduler e).map (Option.map erase) := by
  obtain ⟨s,v,k,acc⟩ := d
  cases s <;> first | rfl | cases hs

theorem project {d : D} (hs : readsData d.site = false)
    (h : (Softmax.code p L g).StepAt d.scheduler) : (code p L g).StepAtU d :=
  h.projectU erase rfl rfl rfl rfl (inv_of_control hs) (next_of_control hs)
    (fun _ _ _ _ hg => good_erase hg)

theorem project_data {d : D} (hs : readsData d.site = false)
    (hF : (code p L g).facts d = (codeD p L g).facts d.scheduler)
    (h : (codeD p L g).StepAt d.scheduler) : (code p L g).StepAtU d := by
  refine h.projectU (C := code p L g) (q := d) erase rfl hF rfl rfl
    (inv_of_control (p := p) (L := L) (g := g) hs) (next_of_control hs) ?_
  intro e a t _ hg
  exact good_erase ⟨atD_mono hg.1, hg.2⟩

/-- The data machine has exactly the incoming control facts when all live registers
at the site are control registers. -/
theorem facts_eq_data {d : D}
    (hl : liveD (livePc d.scheduler) = ctlLive (livePc d.scheduler)) :
    (code p L g).facts d = (codeD p L g).facts d.scheduler := by
  change factsFrom _ _ = factsFrom _ _
  rw [hl]
  apply List.map_congr_left
  intro r hr
  rw [valueOfD_ctl _ (List.mem_filter.mp hr).2]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
