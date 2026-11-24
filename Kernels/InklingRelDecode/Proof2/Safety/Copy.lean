-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.Tmem
public import Kernels.InklingRelDecode.Proof2.Lib.PtcEvent
public import Lemmas.Flow.NotTensor

@[expose] public section

/-! # The tensor copies on the role table

`kvMapOnly`: every tensor copy of a consistent execution names the `kv_desc` map. The program's
tensor copies are the prologue's twelve and the loader's eight (`kernel_copy_pcs` of
`Ref/Fence.lean`, decided on the code); no other site of a machine is at one of them (`*_copy`).
A prologue copy's map operand is the inherited `%rd1`, which the prologue's reference fixes to
the pointer to the parameter `kv_desc` (`ProA.PRef.pro`, `Proof.ProA.ptc_event_map`); a loader
copy's is the tensor map register the worker's reference fixes (`EvW.LdShapeW`). This discharges
the first tree's `Safety.Protocol.kvMapOnly` (`KvMapOnly`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

local macro "site_none" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

theorem startup_copy : ∀ s : Startup.Site, s.pc ∈ copyPcs → False := by
  intro s h; revert h
  cases s with
  | enter r => cases r <;> decide
  | _ => decide

theorem proA_copy (s : ProA.Site) (h : s.pc ∈ copyPcs) : ∃ b j, s = .ptc b j := by
  cases s with
  | ptc b j => exact ⟨b, j, rfl⟩
  | ld k | el k | init k | arr k | psh k | ldq k | st9 k =>
    exfalso; revert h; revert k; decide
  | pb b j | lb b j | pel b j | stq b j =>
    exfalso; revert h; revert j; revert b; decide
  | _ => exfalso; revert h; decide

theorem sm_copy : ∀ s : Proof.Sm.Site, s.pc ∈ copyPcs → False := by site_none
theorem epi_copy : ∀ s : Proof.Epi.Site, s.pc ∈ copyPcs → False := by site_none
theorem worker_copy : ∀ s : Proof.Worker.Site, s.pc ∈ copyPcs → False := by site_none
theorem idle_copy : ∀ s : Proof.Worker.Idle.Site, s.pc ∈ copyPcs → False := by site_none
theorem mma_copy : ∀ s : Proof.Mma.Site, s.pc ∈ copyPcs → False := by site_none
theorem exitsite_copy : ∀ s : Proof.WComp.ExitSite, s.pc ∈ copyPcs → False := by site_none

/-- The prologue's copy site `(b, j)` is the flat machine's copy site `4 b + j`. -/
theorem ptc_old (b : Fin 3) (j : Fin 4) :
    (ProA.Site.ptc b j).old = Proof.ProA.ptcSite (4 * b.val + j.val) := by
  fin_cases b <;> fin_cases j <;> rfl

/-- The tensor copy a loader state fires names the `kv_desc` map. -/
theorem ld_copy_map {d : Proof.Loader.D} {pc a : Nat} {s : TensorCopy.Spec}
    (h : Proof.EvW.LdShapeW Q L g d ⟨pc, .tensorIssue a s⟩) : a = Q.kvMap := by
  unfold Proof.EvW.LdShapeW at h
  split at h <;> first
    | (obtain ⟨_, -, h⟩ := h
       simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at h
       exact h.2.1)
    | (exfalso; revert h; simp)

/-- **Every tensor copy names the `kv_desc` map** (`Safety.KvMapOnly`). -/
theorem kvMapOnly (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc a : Nat} {s : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a s⟩) : a = Q.kvMap := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨σ, t, ins, o, -, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hev := frag_ev hp hg hJ hat hi hc hf
    have hop : tensorOp ins.op = true := by
      cases hq : tensorOp ins.op
      · exact absurd rfl (fires_notTensor (eventTmpl_notTensor hq) hf a s)
      · rfl
    have hpc := OpPcsFast.mem kernel_copy_pcs hc hop
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r, d⟩
    · exact (startup_copy st.site hpc).elim
    · rename_i i
      cases i with
      | dp tm bw =>
        rcases d with d | ⟨_ | _, τ⟩
        · obtain ⟨b, j, hs⟩ := proA_copy d.site hpc
          have hx : d.site ≠ .exit := by rw [hs]; simp
          have hF := ProA.fired_old (P := Startup.inh L g Q tm) hx hat hi.1 hc hf
          obtain ⟨-, -, hP, -⟩ := (hJ : ProRef Q L g tm bw d n)
          have hmap : d.dt.pro.rest 1949 = .ptr 64 true (.param (param "1")) 0 := by
            rw [hP.pro]; rfl
          have he' := Proof.ProA.ptc_event_map hp (i := 4 * b.val + j.val) (by omega) hmap hF
            (by simp only [ProA.D.old, hs, ptc_old])
          simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at he'
          exact he'.2.1
        · cases τ with
          | sm d => exact (sm_copy d.site hpc).elim
          | epi d => exact (epi_copy d.site hpc).elim
        · exact hJ.elim
      | worker w =>
        cases d with
        | loader d P => exact ld_copy_map hev
        | worker w => exact (worker_copy w.site hpc).elim
        | idle d => exact (idle_copy d.site hpc).elim
        | mma d P => exact (mma_copy d.site hpc).elim
        | exit x => exact (exitsite_copy x.site hpc).elim
    · exact hJ.elim

end
end PTX.Kernels.InklingRelDecode.Proof2
