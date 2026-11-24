-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0Election
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Lemmas.Step.WarpShfl

@[expose] public section

/-! # Full-warp launch broadcasts and producer dispatch -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof

/-- The two common broadcasts and the producer warp's dispatch broadcast. -/
inductive StartupShuffle where
  | group | warp | dispatch

def StartupShuffle.state : StartupShuffle → Machine.ThreadD
  | .group => .prologue .shfl0
  | .warp => .prologue .shfl1
  | .dispatch => .head

private def StartupShuffle.site : StartupShuffle → Nat
  | .group => Site.shfl0.pc
  | .warp => Site.shfl1.pc
  | .dispatch => Wg1Mma.Site.head.pc

private def StartupShuffle.word (L : Launch) (s : StartupShuffle) (g : Nat) : Value :=
  b32 (match s with | .group => wgOf L g | _ => warpOf L g)

private theorem startup_shuffle_template
    {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {u : TState} {ins : Instr}
    (hpre : Pre P L mem0) (s : StartupShuffle)
    (ha : (Machine.code P L g).AtD s.state u)
    (hc : kernel.code[(Machine.code P L g).pc s.state]? = some ins) :
    u.pc = s.site ∧
      ∃ k, eventTmpl Assumptions.all L g u ins.op = .shfl .idx (s.word L g) 0 31 k := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  cases s
  case group =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0)
    have hr : u.regs 519 = some (b32 (wgOf L g)) :=
      holds_mem ha.2.2.2.2 (mem_factsFrom (by table_decide : 519 ∈ liveAll 6))
    refine ⟨ha.1, fun recv ok => PTX.next (setReg (setReg u 462 recv) 2 (.pred ok)), ?_⟩
    simp only [eventTmpl, warpTmpl_shfl_idx, shflTmpl, readBits, readValue, readReg, hr, b32,
      Value.bytes, hb, pure, Except.pure]
    rw [ite_eq_left (by decide), ite_eq_left trivial]
    rfl
  case warp =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_1)
    have hr : u.regs 464 = some (b32 (warpOf L g)) :=
      holds_mem ha.2.2.2.2 (mem_factsFrom (by table_decide : 464 ∈ liveAll 9))
    refine ⟨ha.1, fun recv ok => PTX.next (setReg (setReg u 465 recv) 3 (.pred ok)), ?_⟩
    simp only [eventTmpl, warpTmpl_shfl_idx, shflTmpl, readBits, readValue, readReg, hr, b32,
      Value.bytes, hb, pure, Except.pure]
    rw [ite_eq_left (by decide), ite_eq_left trivial]
    rfl
  case dispatch =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_2)
    exact ⟨ha.1, _, Wg1Mma.event_head P L g ha hb⟩

/-- The lanes at one startup broadcast can issue its complete shuffle batch. -/
theorem startup_shuffle_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads) (hub : ¬ HasUb X)
    (s : StartupShuffle) (hall : ∀ h, SameWarp L g h →
      Frame.Pending L X h ∧ PTX.Step.Released L X h ∧
        Frame.stateAt (Machine.code P L) X h (X.tr h).length = some (some s.state)) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  refine PTX.Step.shfl_counted_extension_with_assumptions (pc := s.site) (m := .idx) hX
    (by rw [hpre.block]) (s.word L) (fun _ => 0) (fun _ => 31) hg
    (fun _ _ => .inr (fun ⟨i, sp, tg, hi⟩ =>
      (GlobalWrites.no_clc (i := i) (s := sp) (tg := tg) hX hi).elim))
    (fun h hw => (hall h hw).2.1) ?_ ?_
  · intro h hw recv ok
    obtain ⟨hp, _, hState⟩ := hall h hw
    obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
    obtain ⟨u, _, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hState
    obtain ⟨hPc, k, hTemplate⟩ := startup_shuffle_template hpre s ha hc
    rw [hTemplate] at hout
    exact ⟨t, u, some (k recv ok), hRun, hTau, _, hout, recv, ok, by rw [hPc], rfl⟩
  · apply all_wf_collective_batch hX (PTX.Step.warpThreads L g)
    · intro _ _ _ h
      exact Kind.noConfusion h
    · intro _ _ _ h
      exact Kind.noConfusion h
    · intro _ h
      exact Kind.noConfusion h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
