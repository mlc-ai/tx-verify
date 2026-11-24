-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsOrigin
public import Kernels.FlashAttn4Fwd.Proof.Interface.Exit
public import Kernels.FlashAttn4Fwd.Proof.Interface.Async
public import Kernels.FlashAttn4Fwd.Proof.Interface.Older
public import Lemmas.Flow.AccessLocal
public import Lemmas.Flow.NotRmw

@[expose] public section

/-! # The threads' memory accesses and polls (fields of `AsyncFacts`, `OlderFacts`, `ExitFacts`)

These facts need only that every event fires from its site's instruction (`event_origin`):

* a poll is on an mbarrier of its thread's CTA (`fires_wait_local`: the kernel's polls use no
  cluster addressing; `ExitFacts_wait_own`);
* the kernel's generic loads and stores all name shared memory (`kernel_no_global`), so every
  access of a thread is shared (`OlderFacts_access_shared`) and, its address computed without
  cluster addressing, of the thread's own CTA (`AsyncFacts_access_own`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A poll names a barrier of its thread's CTA.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.ExitFacts_wait_own
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g k pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}, g < L.threads →
      X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ → m.cta = ctaOf L g := by
  intro g k pc p m ok acq sc _ he
  obtain ⟨d, t, ins, o, -, -, -, -, -, hf⟩ :=
    event_origin hpre hX ht (J := fun _ _ _ => True) (fun g _ => trueJ_run L g) he nofun
  exact (fires_wait_local hf rfl).2

/-- The kernel has no generic load or store of global memory. -/
theorem kernel_no_global : OpPcsFast kernel.code globalMemOp [] = true := by
  decide +kernel

/-- The kernel has no atomic memory instruction. -/
theorem access_noAtomic : kernel.code.all (fun ins => !atomicOp ins.op) = true := by
  decide +kernel

/-- **A thread's access is a read or a write**: the kernel has no atomic read-modify-write. -/
theorem access_rw (hX : Consistent L kernel asms mem0 X) {e : EvId} {a : Acc} {w : Bool}
    (h : X.Access e a w) :
    (∃ bs, X.Reads e a bs ∧ w = false) ∨ (∃ bs, X.Writes e a bs ∧ w = true) :=
  (Execution.access_iff_of_not_rmw fun _ _ _ _ he => no_kind_of_code hX atomicOp
    (fun k => ∃ a o n, k = .rmw a o n) (fun _ ⟨_, _, _, h⟩ => by cases h)
    (fun hf ⟨_, _, _, hk⟩ => fires_rmw_op hf hk) access_noAtomic he ⟨_, _, _, rfl⟩).mp h

/-- **A thread's access is in shared memory, of its own CTA.** -/
theorem access_local (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k : Nat} {a : Acc} {w : Bool}
    (h : X.Access (g, k) a w) : a.loc.space = .shared ∧ a.loc.cta = ctaOf L g := by
  have hglob : ∀ {pc : Nat} {ins : Instr}, kernel.code[pc]? = some ins →
      globalMemOp ins.op = false := by
    intro pc ins hc
    by_contra hne
    simpa using OpPcsFast.mem kernel_no_global hc (by simpa using hne)
  rcases access_rw hX h with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩
  · obtain ⟨d, t, ins, o, -, -, -, -, hc, hf⟩ :=
      event_origin hpre hX ht (J := fun _ _ _ => True) (fun g _ => trueJ_run L g) he nofun
    rcases fires_read_loc hf rfl with ⟨h1, h2⟩ | hd
    · have hs := globalMemOp_space (hglob hc) (.inl h1)
      exact ⟨hs, h2 hs⟩
    · simp [globalMemOp_dynamic (hglob hc)] at hd
  · obtain ⟨d, t, ins, o, -, -, -, -, hc, hf⟩ :=
      event_origin hpre hX ht (J := fun _ _ _ => True) (fun g _ => trueJ_run L g) he nofun
    rcases fires_write_loc hf rfl with ⟨h1, h2⟩ | hd
    · have hs := globalMemOp_space (hglob hc) (.inr h1)
      exact ⟨hs, h2 hs⟩
    · simp [globalMemOp_dynamic (hglob hc)] at hd

/-- **A thread's memory access is of shared memory.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.OlderFacts_access_shared
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g k : Nat} {a : Acc} {w : Bool}, X.Access (g, k) a w → a.loc.space = .shared :=
  fun h => (access_local hpre hX ht h).1

/-- **A thread's shared accesses are of its own CTA.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.AsyncFacts_access_own
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g k : Nat} {a : Acc} {w : Bool}, X.Access (g, k) a w → a.loc.space = .shared →
      a.loc.cta = ctaOf L g :=
  fun h _ => (access_local hpre hX ht h).2

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
