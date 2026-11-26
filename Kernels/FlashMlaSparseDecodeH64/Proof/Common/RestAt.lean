-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Table
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WfStep
public import Lemmas.Quiet.Progress.ReleasedU
public import Lemmas.Quiet.Progress.Other
public import Lemmas.Quiet.Progress.IssueU
public import Lemmas.Kernel.Progress.NextEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.AllocAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.AllocSteps
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegReq

@[expose] public section

/-! # A released lane at an ordinary instruction steps, from its state

`Descent.released_stepsUQ` and the library's steps of the other single-lane kinds
(`Descent.other_next_stepsUQ`, `Sched.tcStore_next_stepsUQ`, `Sched.reg_next_stepsUQ`,
`Sched.alloc_next_stepsUQ`) for the kernel's thread machines, at the state of a pending released
lane (`ordinary_at`, `other_at`, `reg_at`, `alloc_at`). A lane without events is at the startup's
first instruction, a warp collective, so it is never at these kinds; after lane 0's allocation
request the lane is at the allocation (`alloc_pc_at`), not at a store. The next-event forms of
`Common/Export/Quiet.lean` take the state from `next_state`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem init_pc : (thread P L g).pc (thread P L g).init = 6 := rfl

theorem code6_rest :
    ∀ ins, kernel.code[6]? = some ins → (Descent.opKind ins.op).Rest = true := by
  intro ins h
  have : kernel.code[6]?.map (fun i => (Descent.opKind i.op).Rest) = some true := by
    decide +kernel
  rw [h] at this
  simpa using this

theorem code91_alloc :
    ∀ ins, kernel.code[91]? = some ins → Descent.opKind ins.op = .alloc := by
  intro ins h
  have : kernel.code[91]?.map (fun i => Descent.opKind i.op) = some .alloc := by
    decide +kernel
  rw [h] at this
  simpa using this

theorem code6_other : ∀ ins, kernel.code[6]? = some ins →
    (Descent.otherOp ins.op || Sched.tcStoreOp ins.op) = false := by
  intro ins h
  have : kernel.code[6]?.map (fun i => Descent.otherOp i.op || Sched.tcStoreOp i.op) =
      some false := by
    decide +kernel
  rw [h] at this
  simpa using this

/-- A lane at the state of an instruction that the startup's first instruction is not has
events. -/
theorem ne_nil {Q : Instr → Prop} {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ))
    (h6 : ∀ ins, kernel.code[6]? = some ins → ¬ Q ins)
    (hk : ∀ ins, kernel.code[(thread P L g).pc σ]? = some ins → Q ins) : X.tr g ≠ [] := by
  intro h0
  have h0' : Frame.stateAt (thread P L) X g (X.tr g).length =
      some (some (thread P L g).init) := by
    rw [h0]; exact Frame.stateAt_zero
  rw [h0'] at hσ
  obtain rfl := Option.some.inj (Option.some.inj hσ)
  rw [init_pc] at hk
  obtain ⟨ins, hins⟩ : ∃ ins, kernel.code[6]? = some ins :=
    Option.isSome_iff_exists.mp (by decide +kernel)
  exact h6 ins hins (hk ins hins)

variable (hp : Pre P L m) (hc : Descent.NextEnvQ L kernel Assumptions.all m X)
  (hFw : Follow P L X) (hpd : Frame.Pending L X g) (hrel : Step.Released L X g)
  {σ : (thread P L g).D}
  (hσ : Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ))
include hp hc hFw hpd hrel hσ

/-- **A released pending lane at an instruction outside `Rest` steps**, when an exit's selected
stores have finished reading. -/
theorem ordinary_at
    (hk : ∀ ins, kernel.code[(thread P L g).pc σ]? = some ins →
      (Descent.opKind ins.op).Rest = false)
    (hexit : ∀ ins, kernel.code[(thread P L g).pc σ]? = some ins →
      Descent.opKind ins.op = .exit → TensorStore.Drained drainSel X g) :
    Sched.Steps (timed P L) m X (.thread g) := by
  have hlast : ∀ ins, kernel.code[(thread P L g).pc σ]? = some ins →
      Descent.opKind ins.op = .store → ∀ pc grp dst n, X.get (g, (X.tr g).length - 1) =
        some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ → PTX.laneOf L g ≠ 0 := by
    intro ins hins hst pc grp dst n ha hl
    have hlen : (X.tr g).length = (X.tr g).length - 1 + 1 := by
      have := (List.getElem?_eq_some_iff.mp (show (X.tr g)[(X.tr g).length - 1]? = _ from ha)).1
      omega
    have h91 := alloc_pc_at hp hc.max.1 hFw ha
      (alloc_pc hp hc.max.1 hFw (Frame.lt_of_get hc.max.1 ha) ha) hl hlen hσ
    rw [h91] at hins
    rw [code91_alloc ins hins] at hst
    cases hst
  have hne := ne_nil hσ (fun ins hins hr => by rw [code6_rest ins hins] at hr; cases hr)
    (hk := hk)
  exact Descent.released_stepsUQ hc hpd hne hrel (fun _ _ => thread_sound hp) hσ hk hlast
    fun ins hins hx _ _ => wf_snoc_exit hc.max.1 (hexit ins hins hx)

omit hFw in
/-- **A released pending lane at a non-coherent load, a `tcgen05` fence, copy or shift, a Tensor
Memory store or a store wait steps.** -/
theorem other_at
    (hk : ∀ ins, kernel.code[(thread P L g).pc σ]? = some ins →
      (Descent.otherOp ins.op || Sched.tcStoreOp ins.op) = true) :
    Sched.Steps (timed P L) m X (.thread g) := by
  have hne := ne_nil hσ (fun ins hins hr => by rw [code6_other ins hins] at hr; cases hr)
    (hk := hk)
  by_cases ho : ∀ ins, kernel.code[(thread P L g).pc σ]? = some ins →
      Descent.otherOp ins.op = true
  · exact Descent.other_next_stepsUQ hc (fun _ _ => thread_sound hp) hpd hσ hne hrel ho
      fun _ _ => wf_snoc_nc hc.max.1
  · rw [timed_eq]
    refine Sched.tcStore_next_stepsUQ (M := ⟨thread P L, time P L⟩) hc.wf hc.max hc.noUb
      (fun _ _ => thread_sound hp) hpd hσ hne hrel fun ins hins => ?_
    have h := hk ins hins
    rw [Bool.or_eq_true] at h
    refine h.resolve_left fun hi => ho fun ins' h' => ?_
    rw [hins] at h'
    cases h'
    exact hi

/-- **A released pending lane at a register request steps** (it is the lane's first). -/
theorem reg_at {J : (table P L).J g σ} {hi : (thread P L g).inv σ}
    (hk : ∀ ins, kernel.code[(thread P L g).pc σ]? = some ins → Sched.regOp ins.op = true)
    (hins : ∃ ins, kernel.code[(thread P L g).pc σ]? = some ins) :
    Sched.Steps (timed P L) m X (.thread g) := by
  obtain ⟨ins, hins⟩ := hins
  have hno := req_none_at hp hc.max.1 hFw hc.noUb hσ J hi hins (hk ins hins)
  have hne := ne_nil hσ (fun ins hins hr => by
    have : kernel.code[6]?.map (fun i => Sched.regOp i.op) = some false := by decide +kernel
    rw [hins] at this
    simp only [Option.map_some, Option.some.injEq] at this
    rw [this] at hr
    cases hr) (hk := hk)
  rw [timed_eq]
  exact Sched.reg_next_stepsUQ (M := ⟨thread P L, time P L⟩) hc.wf hc.max hc.noUb
    (fun _ _ => thread_sound hp) hpd hσ hne hrel hk hno

omit hFw in
/-- **A released pending lane at the allocation steps**, when every recorded allocation is at
column 0. -/
theorem alloc_at
    (hk : ∀ ins, kernel.code[(thread P L g).pc σ]? = some ins → Sched.allocOp ins.op = true)
    (hzero : ∀ {cta : Nat} {r : Tmem.Pair.Requests}, r ∈ X.tmemHistory cta →
      ∀ n col, r.action = .alloc n col → col = 0) :
    Sched.Steps (timed P L) m X (.thread g) := by
  have hne := ne_nil hσ (fun ins hins hr => by
    have : kernel.code[6]?.map (fun i => Sched.allocOp i.op) = some false := by decide +kernel
    rw [hins] at this
    simp only [Option.map_some, Option.some.injEq] at this
    rw [this] at hr
    cases hr) (hk := hk)
  rw [timed_eq]
  exact Sched.alloc_next_stepsUQ (M := ⟨thread P L, time P L⟩) hc.wf hc.max hc.noUb
    (fun _ _ => thread_sound hp) hpd hσ hne hrel hk hzero

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
