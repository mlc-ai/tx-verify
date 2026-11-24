-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.MmaCounts
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaLeader
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerExit
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleWarp
public import Kernels.Fp16Gemm8192.Proof.Thread.Tracked

@[expose] public section

/-! # An exited MMA warp thread's accumulator commits

A warp-8 or warp-9 thread whose trace ends with its exit made every task's accumulator commit: the
exit event is fired from the MMA role's exit site (`mma_not_exit`), where the counting invariant
(`threadCounts_run`, `Mma.Counts.accRound`) gives the accumulator commits of the thread's own buffer
as its tasks (its input commits over 128). The exit event commits nothing. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow MBarrier AsyncCopy

noncomputable section

set_option maxRecDepth 100000

/-- **An exited MMA thread's accumulator commits are its tasks.** -/
theorem mma_exit_acc_count {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads)
    (hw : g % L.block / 32 = 8 ∨ g % L.block / 32 = 9) {pc : Nat}
    (hlast : (X.tr g).getLast? = some ⟨pc, .exit⟩) :
    (X.tr g).countP (commitsTo (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩)) =
      mmaCount L g (X.tr g) / 128 := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
  have hlen : (X.tr g).length - 1 = ys.length := by
    rw [hys]
    simp
  have htake : (X.tr g).take ((X.tr g).length - 1) = ys := by
    rw [hlen, hys, List.take_left' rfl]
  have hget : X.get (g, (X.tr g).length - 1) = some ⟨pc, .exit⟩ := by
    change (X.tr g)[(X.tr g).length - 1]? = _
    rw [← List.getLast?_eq_getElem?, hlast]
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  -- the state before the exit event is a live role state
  obtain ⟨σ, hσ⟩ : ∃ σ, Frame.stateAt (code L) X g ((X.tr g).length - 1) = some σ := by
    rcases htr.fired hget with ⟨τ, -, ha, -⟩ | ⟨-, hub⟩
    · exact ⟨τ, ha⟩
    · obtain ⟨pc', f, hf⟩ := hub
      cases hf
  obtain ⟨d, hd⟩ : ∃ d, Frame.stateAt (code L) X g ((X.tr g).length - 1) = some (some d) := by
    cases σ with
    | none => exact absurd hσ (tracked hpre hX g _ hg)
    | some d => exact ⟨d, hσ⟩
  obtain ⟨r, rfl⟩ := exit_role hpre hX hg hget hd rfl
  have hrw := role_warp hpre hX hg ((X.tr g).length - 1) (Nat.sub_le _ _) _ hd
  cases r with
  | loader l =>
    simp only [roleWarp, Prologue.warpOf] at hrw
    omega
  | sched s =>
    simp only [roleWarp, Prologue.warpOf] at hrw
    omega
  | cons c =>
    simp only [roleWarp, Prologue.warpOf] at hrw
    omega
  | mma m =>
    simp only [roleWarp, Prologue.warpOf] at hrw
    have hmw : m.w = g % L.block / 32 := hrw.1
    have hsite : m.site = .exit := by
      by_contra hne
      exact mma_not_exit hpre hX hget hd hne rfl
    have hC : Mma.Counts L g m ((X.tr g).take ((X.tr g).length - 1)) :=
      threadCounts_run hpre hg htr _ _ hd
    have hacc := hC.accRound
    rw [htake, hsite] at hacc
    simp only [show Mma.Site.exit ≠ Mma.Site.accCommit from by simp, ↓reduceIte, add_zero] at hacc
    rw [hys]
    rw [← hmw]
    simp only [List.countP_append, List.countP_singleton, commitsTo, mmaCount, List.countP_append]
    unfold mcount at hacc
    simpa [Bar.loc, Bar.off, emptyAt, inputEmpty, Mma.accBar, Nat.add_assoc] using hacc

end
end PTX.Kernels.Fp16Gemm8192.Proof
