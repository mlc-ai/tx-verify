-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingGateEvents
public import Lemmas.Step.CtaBarFinishExit

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The two full-CTA synchronization points. -/
inductive CtaGate where
  | launch
  | completion

def CtaGate.id : CtaGate → Nat
  | .launch => 0
  | .completion => 12

/-- Every warp of the CTA participates in each full-CTA gate. -/
def allWarps : Finset Nat := Finset.range 12

/-- A thread's trace ends at a full-CTA synchronization. -/
def AtCtaGate (X : Execution) (g : Nat) (gate : CtaGate) : Prop :=
  ∃ e, X.get (g, (X.tr g).length - 1) = some e ∧ e.kind = .bar gate.id none .sync

/-- Each lane of this CTA has made its arrival of the same ordinal. -/
def AllCtaArrived (L : Launch) (X : Execution) (g : Nat) (gate : CtaGate) : Prop :=
  ∀ y < L.block, ∃ j e, X.get (g / L.block * L.block + y, j) = some e ∧
    e.kind = .bar gate.id none .sync ∧
    ((X.tr (g / L.block * L.block + y)).take j).countP (Execution.isBarId gate.id) =
      ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId gate.id)

theorem all_wf_cta_history {L : Launch} {mem0 : Mem0} :
    Assumption.WfCtaHistory (L := L) (K := kernel) (mem0 := mem0) Assumptions.all := by
  intro X c suffix hX
  exact Interface.all_wf_effects hX (X.le_withCtaHistory c ⟨suffix, rfl⟩) rfl rfl rfl

private theorem full_gate_shape {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) (gate : CtaGate) : NamedBar.Shape L none allWarps gate.id := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [hpre.block]
    rfl
  · intro w hw
    rw [hpre.block]
    exact Finset.mem_range.mp hw
  · cases gate <;> decide

/-- Once every lane has arrived at a full-CTA gate, the barrier history can release a waiting
thread while preserving the execution's traces and its maximality. -/
theorem release_cta_gate {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hf : ∀ Y, Consistent L kernel Assumptions.all mem0 Y → ¬ CtaBarFault L Y) (hg : g < L.threads)
    {gate : CtaGate} (hsrc : NamedBar.Sources L X none allWarps gate.id)
    (hgate : AtCtaGate X g gate) (harrived : AllCtaArrived L X g gate) :
    ∃ Y, Maximal L kernel Assumptions.all mem0 Y ∧ Y.tr = X.tr ∧ PTX.Step.Released L Y g := by
  obtain ⟨⟨site, kind⟩, hget, hkind⟩ := hgate
  change kind = _ at hkind
  subst kind
  refine NamedBar.sync_release_of_wf hmax all_wf_cta_history hf
    (full_gate_shape hpre gate) hsrc hg hget ?_
  intro y hy _
  obtain ⟨j, ⟨site', kind⟩, he, hk, ho⟩ := harrived y hy
  change kind = _ at hk
  subst kind
  exact ⟨j, site', .sync, he, ho⟩

/-- The launch gate's arrival operands follow from the concrete prologue executions. -/
theorem launch_gate_sources {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    NamedBar.Sources L X none allWarps CtaGate.launch.id := by
  intro e site cnt he hg
  obtain ⟨mode, he⟩ := he
  have h0 : e.1 % L.block / 32 ∈ allWarps := by
    rw [hpre.block]
    exact Finset.mem_range.mpr (by have := Nat.mod_lt e.1 (by decide : 0 < 384); omega)
  refine ⟨h0, ?_⟩
  obtain ⟨d, hd⟩ := Frame.event_state hs hX ht he (by simp)
  obtain ⟨o, ho⟩ := RingEvents.fired_of_trace hX (hs e.1 hg).machine he hd
  exact (RingGateEvents.gate_source ho rfl).2.1

/-- The actual prologue gate can release a waiting thread after every CTA lane has arrived. -/
theorem release_launch_gate {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hf : ∀ Y, Consistent L kernel Assumptions.all mem0 Y → ¬ CtaBarFault L Y) (hg : g < L.threads)
    (hgate : AtCtaGate X g .launch) (harrived : AllCtaArrived L X g .launch) :
    ∃ Y, Maximal L kernel Assumptions.all mem0 Y ∧ Y.tr = X.tr ∧ PTX.Step.Released L Y g :=
  release_cta_gate hpre hmax hf hg (launch_gate_sources hpre hmax.1 hs ht) hgate harrived

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
