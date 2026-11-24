-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
public import Lemmas.Kernel.NextReads
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
import Lemmas.Step.TcLoad

import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressGuard
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions

public section

/-! # Softmax release fences and bulk commit progress -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof

/-- The softmax proxy fences and output bulk commit. -/
inductive SoftmaxQuietSite : Wg0.Site → Prop where
  | soFence : SoftmaxQuietSite .soFence
  | stageFence (j : Fin 4) : SoftmaxQuietSite (.stageFence j)
  | commit : SoftmaxQuietSite .commit

private theorem wg0_quiet_fire {L : Launch} {g : Nat} {site : Wg0.Site}
    {u : TState} {ins : Instr} (hd : SoftmaxQuietSite site)
    (hc : kernel.code[site.pc]? = some ins) :
    ∃ k, Fires u.pc (eventTmpl Assumptions.all L g u ins.op) ⟨u.pc, k⟩
      (some (PTX.next u)) ∧ ((∃ f s, k = .fenceProxy f s) ∨ k = .bulkCommit) := by
  cases hd with
  | soFence =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1120)
    exact ⟨_, ⟨rfl, rfl⟩, .inl ⟨_, _, rfl⟩⟩
  | stageFence j =>
    obtain rfl := Option.some.inj (hc.symm.trans (Wg0.stageFence_code j))
    exact ⟨_, ⟨rfl, rfl⟩, .inl ⟨_, _, rfl⟩⟩
  | commit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1832)
    exact ⟨_, ⟨rfl, rfl⟩, .inr rfl⟩

/-- Tensor Memory control events of softmax, through the last output load's wait. -/
inductive SoftmaxTcSite : Wg0.Site → TcKind → Prop where
  | fenceLoad : SoftmaxTcSite .fenceLoad .fenceAfter
  | fenceBefore : SoftmaxTcSite .fenceBefore .fenceBefore
  | scoreWait : SoftmaxTcSite .scoreWait .waitLd
  | rescaleFence : SoftmaxTcSite .rescaleFence .fenceAfter
  | rescaleWait (j : Fin 4) : SoftmaxTcSite (.rescaleWait j) .waitLd
  | rescaleWaitSt (j : Fin 4) : SoftmaxTcSite (.rescaleWaitSt j) .waitSt
  | rescaleFenceB : SoftmaxTcSite .rescaleFenceB .fenceBefore
  | fenceEpilogue : SoftmaxTcSite .fenceEpilogue .fenceAfter
  | oWait (j : Fin 4) : SoftmaxTcSite (.oWait j) .waitLd

private theorem wg0_tc_fire {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {site : Wg0.Site} {k : TcKind} {u : TState} {ins : Instr} (hpre : Pre P L mem0)
    (hd : SoftmaxTcSite site k) (hc : kernel.code[site.pc]? = some ins) :
    Fires u.pc (eventTmpl Assumptions.all L g u ins.op)
      ⟨u.pc, .tc k⟩ (some (PTX.next u)) := by
  have hwaitLd : eventTmpl Assumptions.all L g u .tcWaitLd = .tc .waitLd (PTX.next u) := by
    simp [eventTmpl, tcTmpl, hpre.block, ofExec, pure, Except.pure]
  have hwaitSt : eventTmpl Assumptions.all L g u .tcWaitSt = .tc .waitSt (PTX.next u) := by
    simp [eventTmpl, tcTmpl, hpre.block, ofExec, pure, Except.pure]
  cases hd with
  | fenceLoad =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_275)
    exact ⟨rfl, rfl⟩
  | fenceBefore =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_287)
    exact ⟨rfl, rfl⟩
  | scoreWait =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_286)
    rw [hwaitLd]
    exact ⟨rfl, rfl⟩
  | rescaleFence =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_711)
    exact ⟨rfl, rfl⟩
  | rescaleWait j =>
    have hcode : kernel.code[(Wg0.Site.rescaleWait j).pc]? = some ⟨none, .tcWaitLd⟩ := by
      fin_cases j <;> kernel_rfl
    obtain rfl := Option.some.inj (hc.symm.trans hcode)
    rw [hwaitLd]
    exact ⟨rfl, rfl⟩
  | rescaleWaitSt j =>
    have hcode : kernel.code[(Wg0.Site.rescaleWaitSt j).pc]? = some ⟨none, .tcWaitSt⟩ := by
      fin_cases j <;> kernel_rfl
    obtain rfl := Option.some.inj (hc.symm.trans hcode)
    rw [hwaitSt]
    exact ⟨rfl, rfl⟩
  | rescaleFenceB =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1119)
    exact ⟨rfl, rfl⟩
  | fenceEpilogue =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1187)
    exact ⟨rfl, rfl⟩
  | oWait j =>
    obtain rfl := Option.some.inj (hc.symm.trans (Wg0.outputWait_code j))
    rw [hwaitLd]
    exact ⟨rfl, rfl⟩

private theorem SoftmaxTcSite.not_load {s : Wg0.Site} {k : TcKind}
    (h : SoftmaxTcSite s k) : ∀ ta words shape, k ≠ .ld ta words shape := by
  cases h <;> nofun

/-- A released softmax lane can issue its next Tensor Memory fence or wait. -/
theorem softmax_tc_control_extension {P : Params} {L : Launch} {mem0 : Mem0}
    {X : Execution} {g : Nat} {d : Wg0.D} {k : TcKind} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hord : ReadsOrdered L X) (hsg : SyncGuarded L kernel X)
    (hnr : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false)
    (hnrmw : ∀ e pc a old new, X.get e = some ⟨pc, .rmw a old new⟩ → a.release = false)
    (hnf : ∀ e sem scope, ¬ X.ThreadFence e sem scope)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hd : SoftmaxTcSite d.site k) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, _, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hσ
  let ev : Event := ⟨u.pc, .tc k⟩
  have hf := wg0_tc_fire (g := g) (u := u) hpre hd hc
  have hStep : EStep kernel Assumptions.all L g u ev (some (PTX.next u)) := ⟨_, hout, hf⟩
  have hAsms := Interface.all_wf_snoc_of_not_nc (g := g) (event := ev)
    (rf := fun _ => none) hX (by simp [ev]) (by simp [ev])
  cases hcoll : isTcColl ev
  · refine PTX.Step.tc_counted_extension_reads hX hord hp.1 hne hrel hRun hTau hStep hcoll
      hAsms (hsg.snoc hnr hnrmw hnf ?_ ?_ ?_ ?_)
    all_goals simp
  · exact PTX.Step.tccoll_counted_extension hX hp.1 (.inl hne) hrel hRun hTau hStep hcoll
      (hX.tmemPairResult.snoc_not_wr nofun) (hX.tcRead_snoc_tc hd.not_load) hAsms

/-- A released softmax lane can append its proxy fence or output bulk commit. -/
theorem softmax_quiet_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg0.D} (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hord : ReadsOrdered L X) (hSafe : ¬ Unsafe L kernel Assumptions.all mem0 X)
    (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hSigma : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hd : SoftmaxQuietSite d.site) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hn : X.tr g ≠ [] := by
    intro hNil
    rw [hNil, List.length_nil, Frame.stateAt_zero] at hSigma
    cases hSigma
  obtain ⟨t, hRun⟩ := Frame.run_some hX (fun hub => hSafe (.inl hub)) hp
  obtain ⟨u, ins, hTau, _, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hSigma
  obtain ⟨k, hf, hk⟩ := wg0_quiet_fire (L := L) (g := g) (u := u) hd hc
  refine PTX.Step.quiet_counted_extension_reads hX hord hp.1 (.inl hn) hrel hRun hTau
    ⟨_, hout, hf⟩ ?_ ?_ (Step.objectAction_snoc_new ?_ ?_ ?_ ?_ ?_)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ((sync_guarded hX hSafe).snoc (fun _ _ _ _ he => write_no_release hX he)
      (fun _ tag _ _ _ he => (GlobalWrites.no_rmw hX ⟨tag, he⟩).elim)
      (no_thread_fence hX) ?_ ?_ ?_ ?_) <;>
  rcases hk with ⟨f, s, rfl⟩ | rfl <;> first
    | exact Interface.all_wf_snoc_of_not_nc hX (fun _ _ h => Kind.noConfusion h)
        (fun h => Kind.noConfusion h)
    | trivial
    | (intros; simp_all)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
