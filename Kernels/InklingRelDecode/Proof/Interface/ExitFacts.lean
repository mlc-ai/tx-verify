-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SyncFacts

@[expose] public section

/-!
# Exits

The `ret` instruction (the program's only exit) is the epilogue's last site for a default-partition
thread and the exit role's last site for a worker thread. An exit event of an execution fires from
one of those states (`exit_event_state`). The kernel has no cancellation request, so no thread is
cancelled (`no_canceled`), and in a complete execution every launched thread's last event is an
exit (`exit_of_complete`), fired from such a state.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Prove a statement about the sites of one machine at a list of positions: by cases on the
site, deciding each. -/
local macro "site_cls" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

/-- Instructions that exit the thread. -/
def isExitOp : Op → Bool
  | .ret => true
  | .exit => true
  | _ => false

/-- The position of the program's exit. -/
def exitPcs : List Nat := [Epi.Site.exit.pc]

/-- **The exits of the program are the epilogue's `ret`.** -/
theorem kernel_exit_pcs : OpPcsFast kernel.code isExitOp exitPcs = true := by decide +kernel

theorem dstart_exit_pc : ∀ s : DStart.Site, s.pc ∈ exitPcs → s ∈ ([] : List DStart.Site) := by
  site_cls
theorem pro_exit_pc : ∀ s : ProA.Site, s.pc ∈ exitPcs → s ∈ ([] : List ProA.Site) := by
  site_cls
theorem sm_exit_pc : ∀ s : Sm.Site, s.pc ∈ exitPcs → s ∈ ([] : List Sm.Site) := by site_cls
theorem epi_exit_pc : ∀ s : Epi.Site, s.pc ∈ exitPcs → s ∈ ([.exit] : List Epi.Site) := by
  site_cls
theorem worker_exit_pc : ∀ s : Worker.Site, s.pc ∈ exitPcs → s ∈ ([] : List Worker.Site) := by
  site_cls
theorem idle_exit_pc : ∀ s : Worker.Idle.Site, s.pc ∈ exitPcs →
    s ∈ ([] : List Worker.Idle.Site) := by site_cls
theorem loader_exit_pc : ∀ s : Loader.Site, s.pc ∈ exitPcs → s ∈ ([] : List Loader.Site) := by
  site_cls
theorem mma_exit_pc : ∀ s : Mma.Site, s.pc ∈ exitPcs → s ∈ ([] : List Mma.Site) := by site_cls
theorem exitsite_exit_pc : ∀ s : WComp.ExitSite, s.pc ∈ exitPcs →
    s ∈ ([.ret] : List WComp.ExitSite) := by site_cls

/-- **An exit event is the epilogue's or the exit role's `ret`.** -/
theorem exit_event_state (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {g k pc : Nat} (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    (∃ d : Epi.D, St Q L X g k = some (some (.d (.epi d))) ∧ d.site = .exit) ∨
    (∃ x : WComp.ExitD, St Q L X g k = some (some (.w (.exit x))) ∧ x.site = .ret) := by
  obtain ⟨s, hσ⟩ := Frame.event_state hS hX ht he (by intro pc f h; cases h)
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hop : isExitOp ins.op = true := by
    rcases fires_exit_op hf (rfl : (⟨pc, .exit⟩ : Event).kind = .exit) with h | h <;>
      simp [isExitOp, h]
  have hpw : TSt.pc s ∈ exitPcs := OpPcsFast.mem kernel_exit_pcs hc hop
  cases s with
  | w s =>
    cases s with
    | worker w => exact absurd hpw (fun h => by simpa using worker_exit_pc w.site h)
    | idle d => exact absurd hpw (fun h => by simpa using idle_exit_pc d.site h)
    | loader d _ => exact absurd hpw (fun h => by simpa using loader_exit_pc d.site h)
    | mma d _ => exact absurd hpw (fun h => by simpa using mma_exit_pc d.site h)
    | exit x => exact .inr ⟨x, hσ, by simpa using exitsite_exit_pc x.site hpw⟩
  | d s =>
    cases s with
    | dstart d => exact absurd hpw (fun h => by simpa using dstart_exit_pc d.site h)
    | pro d => exact absurd hpw (fun h => by simpa using pro_exit_pc d.site h)
    | sm d => exact absurd hpw (fun h => by simpa using sm_exit_pc d.site h)
    | epi d => exact .inl ⟨d, hσ, by simpa using epi_exit_pc d.site hpw⟩

/-- **No thread is cancelled**: the kernel issues no cancellation request. -/
theorem no_canceled (hX : Consistent L kernel asms mem0 X) :
    ∀ g < L.threads, ¬ ClcCanceled L X g := by
  rintro g - ⟨-, req, ho⟩
  obtain ⟨i, s, targets, -, ⟨pc, hi⟩, -⟩ := ClcOk.canceled_has_issue hX.clc ho
  exact no_clc hX hi

/-- **In a complete execution every launched thread exits**, from an exit state. -/
theorem exit_of_complete (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    (hc : Complete L X) {g : Nat} (hg : g < L.threads) :
    ∃ k pc, X.get (g, k) = some ⟨pc, .exit⟩ ∧
      ((∃ d : Epi.D, St Q L X g k = some (some (.d (.epi d))) ∧ d.site = .exit) ∨
      (∃ x : WComp.ExitD, St Q L X g k = some (some (.w (.exit x))) ∧ x.site = .ret)) := by
  rcases hc.1 g hg with hcan | ⟨pc, hl⟩
  · exact absurd hcan (no_canceled hX g hg)
  · have hlen : 0 < (X.tr g).length := by
      by_contra h0
      have : (X.tr g) = [] := List.length_eq_zero_iff.mp (by omega)
      rw [this] at hl
      simp at hl
    refine ⟨(X.tr g).length - 1, pc, ?_, ?_⟩
    · show (X.tr g)[(X.tr g).length - 1]? = _
      rw [← List.getLast?_eq_getElem?, hl]
    · exact exit_event_state hX hS ht (by
        show (X.tr g)[(X.tr g).length - 1]? = _
        rw [← List.getLast?_eq_getElem?, hl])

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
