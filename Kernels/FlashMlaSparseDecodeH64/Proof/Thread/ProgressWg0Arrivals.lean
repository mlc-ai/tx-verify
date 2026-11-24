-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
public import Lemmas.Kernel.NextReads

import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressGuard
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions

public section

/-! # Pending softmax release arrivals -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof

/-- The softmax role's three ordinary release arrivals. -/
inductive SoftmaxArrival where
  | lastStore
  | validFree
  | soReady

/-- The softmax site of the selected arrival. -/
@[expose] def SoftmaxArrival.site : SoftmaxArrival → Wg0.Site
  | .lastStore => .lastStore
  | .validFree => .validFree
  | .soReady => .soReady

/-- The object named by the selected arrival. -/
@[expose] def SoftmaxArrival.object (w : SoftmaxArrival) (L : Launch) (g block : Nat) : Loc :=
  ⟨.shared, g / L.block, L.sharedBase + match w with
    | .lastStore => Wg0.lastStoreOff
    | .validFree => Wg0.validFreeOff (block % 4)
    | .soReady => Wg0.soReadyOff (block % 2)⟩

private theorem unit_arrive_template {L : Launch} {g base : Nat} {t : TState} {m : Loc}
    (hm : mbarLoc L g t base 0 = .ok m) :
    eventTmpl Assumptions.all L g t
        (.mbarArrive base 0 (.imm 0) (.imm 1) false true .cta none) =
      .arrive m 0 (PTX.next t) 1 true .cta := by
  have hscope : Assumptions.all.any (·.clusterScopeMbar t.pc) = false := rfl
  simp only [eventTmpl, widenMbarScope, hscope, Bool.false_eq_true, ↓reduceIte, tmaTmpl,
    hm, readBits, pure, Except.pure, bind, Except.bind, ofExec, mbarStateDest]
  rfl

private theorem softmax_arrival_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {t : TState} {d : Wg0.D} {ins : Instr} (hpre : Pre P L mem0) (w : SoftmaxArrival)
    (hd : d.site = w.site) (ha : (Wg0.code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins) :
    eventTmpl Assumptions.all L g t ins.op =
      .arrive (w.object L g d.block) 0 (PTX.next t) 1 true .cta := by
  rw [hd] at hc
  cases w with
  | lastStore =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_0)
    have hbase : t.regs 938 = some (sb L Wg0.lastStoreOff) := by
      have hr := Wg0.reg_value ha (r := 938) (by rw [hd]; decide +kernel)
      simpa [Wg0.valueOf, Wg0.table, Wg0.lastStoreOff, PTX.Flow.lookupLit, Option.getD_some]
        using hr
    have hb : L.sharedBase + Wg0.lastStoreOff < 2 ^ 32 := by
      have := sharedBase_lt hpre
      unfold Wg0.lastStoreOff
      omega
    have halign := Wg0.ringAddr_mod8 hpre (off := Wg0.lastStoreOff) (buf := 0) (by decide)
    exact unit_arrive_template (mbarLoc_b32 hbase hb halign)
  | validFree =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_1)
    exact unit_arrive_template (mbarLoc_b32 (Wg0.reg1000 ha hd)
      (Wg0.ringAddr_lt hpre (buf := d.block % 4) (by omega))
      (Wg0.ringAddr_mod8 hpre (off := 222872) (by decide)))
  | soReady =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_2)
    have hbase : t.regs 1717 = some (sb L (Wg0.soReadyOff (d.block % 2))) :=
      Wg0.reg_value ha (by rw [hd]; decide +kernel)
    exact unit_arrive_template (mbarLoc_b32 hbase
      (Wg0.ringAddr_lt hpre (off := 222920) (buf := d.block % 2) (by omega))
      (Wg0.ringAddr_mod8 hpre (off := 222920) (by decide)))

/-- A pending softmax release arrives on the selected object with unit count. -/
theorem softmax_arrival_out {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg0.D} {t : TState} (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hg : g < L.threads) (hr : Run kernel Assumptions.all L g {} (X.tr g) (some t))
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (w : SoftmaxArrival) (hd : d.site = w.site) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u ∧
      out kernel Assumptions.all L g u =
        .ev (.arrive (w.object L g d.block) 0 (PTX.next u) 1 true .cta) := by
  obtain ⟨u, ins, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hg hr hσ
  rw [softmax_arrival_template hpre w hd ha hc] at hout
  exact ⟨u, hTau, hout⟩

/-- Issue a softmax release notification using the same checked template as its trace rule. -/
theorem softmax_arrival_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg0.D} (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hord : ReadsOrdered L X) (hSafe : ¬ Unsafe L kernel Assumptions.all mem0 X)
    (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hSigma : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (w : SoftmaxArrival) (hd : d.site = w.site) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hn : X.tr g ≠ [] := by
    intro hNil
    rw [hNil, List.length_nil, Frame.stateAt_zero] at hSigma
    cases hSigma
  obtain ⟨t, hRun⟩ := Frame.run_some hX (fun hub => hSafe (.inl hub)) hp
  obtain ⟨u, hTau, hout⟩ := softmax_arrival_out hpre hs hp.1 hRun hSigma w hd
  exact role_arrival_extension hX hord (sync_guarded hX hSafe)
    (fun _ _ _ _ he => write_no_release hX he)
    (fun _ tag _ _ _ he => (GlobalWrites.no_rmw hX ⟨tag, he⟩).elim)
    (no_thread_fence hX) hp.1 hn hrel hRun hTau hout

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
