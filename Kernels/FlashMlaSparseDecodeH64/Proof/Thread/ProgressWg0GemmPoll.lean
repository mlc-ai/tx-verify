-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressPoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRingSources

public section

/-! # The softmax lane's actual QK and final PV completion polls -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof MBarrier

/-- The two completion waits of the softmax role. -/
inductive SoftmaxGemmWait where
  | qk
  | pv

/-- The softmax site of the selected GEMM completion wait. -/
@[expose] def SoftmaxGemmWait.site : SoftmaxGemmWait → Wg0.Site
  | .qk => .qkDone
  | .pv => .svDone

/-- The completion object of the selected wait and block's double-buffered slot. -/
@[expose] def SoftmaxGemmWait.object (w : SoftmaxGemmWait) (L : Launch) (g block : Nat) : Loc :=
  let obj : Protocol.GemmRing.Object := match w with
    | .qk => .qkDone
    | .pv => .svDone
  obj.loc L (ctaOf L g) ⟨block % 2, Nat.mod_lt _ (by decide)⟩

private theorem gemm_wait_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {t : TState} {d : Wg0.D} {ins : Instr} (hpre : Pre P L mem0)
    (w : SoftmaxGemmWait) (hd : d.site = w.site) (ha : (Wg0.code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins) :
    ∃ k, eventTmpl Assumptions.all L g t ins.op =
      .wait (w.object L g d.block) (d.block / 2 % 2) k true .cta := by
  rw [hd] at hc
  cases w with
  | qk =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_272)
    exact poll_regs_template (off := 222904 + 8 * (d.block % 2)) hpre
      (Wg0.reg977 ha hd) (Wg0.reg978 ha hd)
      (by omega) (by omega) (by omega)
  | pv =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1184)
    exact poll_regs_template (off := 222936 + 8 * (d.block % 2)) hpre
      (Wg0.reg1736 ha hd) (Wg0.reg2954_sv ha hd)
      (by omega) (by omega) (by omega)

/-- The pending softmax completion poll executes the selected slot and parity. -/
theorem softmax_gemm_poll_out {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg0.D} {t : TState} (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hg : g < L.threads) (hr : Run kernel Assumptions.all L g {} (X.tr g) (some t))
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (w : SoftmaxGemmWait) (hd : d.site = w.site) :
    ∃ u k, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u ∧
      out kernel Assumptions.all L g u =
        .ev (.wait (w.object L g d.block) (d.block / 2 % 2) k true .cta) := by
  obtain ⟨u, ins, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hg hr hσ
  obtain ⟨k, hTemplate⟩ := gemm_wait_template hpre w hd ha hc
  rw [hTemplate] at hout
  exact ⟨u, k, hTau, hout⟩

/-- If its object has reached the matching generation, the softmax GEMM poll extends the run. -/
theorem softmax_gemm_poll_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg0.D} {before : State}
    (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (w : SoftmaxGemmWait) (hd : d.site = w.site)
    (hstate : stateBefore (X.objects (w.object L g d.block))
      (X.objects (w.object L g d.block)).length = some before)
    (hready : before.phase % 2 ≠ d.block / 2 % 2) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, k, hTau, hout⟩ := softmax_gemm_poll_out hpre hs hp.1 hRun hσ w hd
  exact poll_extension hX hp.1 hne hrel hRun hTau hout hstate (by simpa using hready)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
