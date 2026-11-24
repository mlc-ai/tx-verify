-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Defs
public import Lemmas.Flow.NotBulkGroup
public import Lemmas.Kernel.Progress.Blocked
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Mma.Export.AllocNext
import Kernels.TmlFa4Fwd.Proof.Progress.OutputDrain
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Ops
import Kernels.TmlFa4Fwd.Proof.Top.Prog.Issue
import Lemmas.Kernel.Progress.TcColl
import Lemmas.Tmem.AllocResult
import Lemmas.Tmem.Tmem1Ready
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A lane blocked at a Tensor Memory resource operation or a bulk-group wait steps

A resource operation is a warp-collective `tcgen05` event. When a lane of the warp has not made the
collective, the template `Sched.tc_steps` applies, from the time table's facts for these events.
When every lane has, the operation is not performed and the allocator can perform it
(`Tmem.One.entry_ready`), or it is performed and the event waits for the allocation's result: lane 0
has not stored it, so it is at the store, earlier than the blocked lane. A bulk-group wait waits for
the output warp's tensor stores (`Progress.drain_steps`): the kernel has no bulk-group copy. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

theorem kernel_noBulkGroup :
    kernel.code.all (fun ins => !Flow.bulkGroupOp ins.op) = true := by decide +kernel

/-- **A lane whose allocation is performed but not published steps**: lane 0 of its warp is at the
store. -/
theorem publish_steps (hp : Pre p L m)
    (hmax : Maximal L kernel Assumptions.all m X) {g pc n : Nat} {grp : CtaGroup}
    {dst : Option Loc} (hg : Frame.Pending L X g) (hrel : ¬ Step.Released L X g)
    (he : X.get (g, (X.tr g).length - 1) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩)
    (hperf : Tmem.Pair.Performed L X (g, (X.tr g).length - 1)) (hl : laneOf L g ≠ 0)
    (hmiss : ¬ ∃ store out, Tmem.Pair.AllocResult L X store (g, (X.tr g).length - 1) out) :
    StepsAt p L m X (.thread g) := by
  have hX := hmax.1
  have hto := tmem1Ops hp hX (launchFollow hp hX)
  obtain ⟨cta, r, hr, lane, hlane⟩ := hperf
  have hv := ((hX.tmemPair.1 cta).1 r hr).2.2
  have hlen : 0 < (X.tr g).length := by
    have : (X.tr g).length - 1 < (X.tr g).length := len_of_get he
    omega
  have hgw : Prologue.warpIndex L g = 12 := (hto.event hg.1 he).1
  -- the leader's event
  have hget := hv.2.2.1 lane
  rw [hlane, he] at hget
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hget
  obtain ⟨rfl, rfl, rfl, hact⟩ := hget
  have hl0 := hv.2.2.1 0
  rw [← hact] at hl0
  have hprop := Tmem.Pair.WarpRequest.event_props hv 0
  have hlt := hprop.2.2
  have hlw : Prologue.warpIndex L (r.own.event L 0).1 = 12 := (hto.event hlt hl0).1
  have hzero : laneOf L (r.own.event L 0).1 = 0 := by
    have hwl : r.own.warp * 32 < L.block := by have := hv.2.1; omega
    simp only [laneOf, Tmem.Pair.WarpRequest.event, Fin.val_zero, Nat.add_zero]
    rw [Nat.mul_comm r.own.cta, Nat.mul_add_mod, Nat.mod_eq_of_lt hwl]
    simp
  obtain ⟨-, hdst, nl, hσl⟩ := Mma.alloc_after hp hX hlw (g := (r.own.event L 0).1)
    (k := (r.own.event L 0).2) hl0
  have hcta : (r.own.event L 0).1 / L.block = r.own.cta := hprop.1
  have hll := len_of_get hl0
  by_cases hlater : (r.own.event L 0).2 + 1 < (X.tr (r.own.event L 0).1).length
  · exfalso
    obtain ⟨bytes, hs⟩ := Mma.alloc_store hp hX hlw hzero hl0
      (List.getElem?_eq_getElem hlater :
        X.get ((r.own.event L 0).1, (r.own.event L 0).2 + 1) = some _)
    have hst : X.get ((r.own.event L 0).1, (r.own.event L 0).2 + 1) = some _ :=
      List.getElem?_eq_getElem hlater
    rw [hs] at hst
    have hres := Tmem.Pair.AllocResult.of_warpRequest hv hact.symm hdst rfl hcta hst lane
    rw [hlane] at hres
    exact hmiss ⟨_, _, hres⟩
  · have hsw : SameWarp L (r.own.event L 0).1 g := by
      have := Tmem.Pair.WarpRequest.event_sameWarp hv 0 lane
      rwa [hlane] at this
    have hlast : (r.own.event L 0).2 + 1 = (X.tr (r.own.event L 0).1).length := by omega
    have hph : Frame.Pending L X (r.own.event L 0).1 := by
      refine ⟨hlt, Sched.not_canceled_of_peer hX hg.1 (List.ne_nil_of_length_pos hlen)
        (Sched.cluster_of_sameWarp (sameWarp_symm hsw)), fun _ hExit => ?_⟩
      have h1 := Sched.exit_get hExit
      rw [show (X.tr (r.own.event L 0).1).length - 1 = (r.own.event L 0).2 by omega] at h1
      rw [show X.get ((r.own.event L 0).1, (r.own.event L 0).2) = _ from hl0] at h1
      cases h1
    refine Sched.earlier_steps hmax hrel hph ?_
    obtain ⟨-, -, ng, hσg⟩ := Mma.alloc_after hp hX hgw he
    rw [Nat.sub_add_cancel hlen] at hσg
    rw [hlast] at hσl
    rw [Sched.threadTime_of hσl, Sched.threadTime_of hσg]
    simp only [hzero, hl, ↓reduceIte]
    simp [Progress.timed, Progress.time, Progress.roleTime, Progress.Mm.startT, Progress.Mm.time,
      Mma.Site.pipe, Progress.Mm.endOff]

/-- **A lane blocked at a Tensor Memory resource operation steps.** -/
theorem tmem_steps (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X)
    (htw : ∀ {g : Nat}, Frame.Pending L X g → ¬ Step.Released L X g → Sched.TcWait L X g →
      StepsAt p L m X (.thread g)) {g : Nat} (hpd : Frame.Pending L X g)
    (hrel : ¬ Step.Released L X g) (h : Sched.TmemWait L X g) :
    StepsAt p L m X (.thread g) := by
  have hX := hmax.1
  have hto := tmem1Ops hp hX (launchFollow hp hX)
  obtain ⟨pc, grp, dst, act, he, hnr⟩ := h
  have hlen : 0 < (X.tr g).length := by
    have : (X.tr g).length - 1 < (X.tr g).length := len_of_get he
    omega
  by_cases hperf : Tmem.Pair.Performed L X (g, (X.tr g).length - 1)
  · have hm : ∃ n, act = .alloc n ∧ laneOf L g ≠ 0 ∧
        ¬ ∃ store out, Tmem.Pair.AllocResult L X store (g, (X.tr g).length - 1) out := by
      by_contra hn
      refine hnr (Tmem.Pair.ReturnReady.ready hX.tmemPair he
        ⟨hperf, fun _ => Tmem.One.covered_of_performed hX hto hperf⟩ fun n hna hl => ?_)
      by_contra hmiss
      exact hn ⟨n, hna, hl, hmiss⟩
    obtain ⟨n, rfl, hl, hmiss⟩ := hm
    exact publish_steps hp hmax hpd hrel he hperf hl hmiss
  · have hk : X.TcK (g, (X.tr g).length - 1)
        (((X.tr g).take ((X.tr g).length - 1)).countP isTcColl) := ⟨⟨_, he, rfl⟩, rfl⟩
    by_cases hall : ∀ h, h < L.threads → SameWarp L g h →
        ∃ j, X.TcK (h, j) (((X.tr g).take ((X.tr g).length - 1)).countP isTcColl)
    · have hsafe := hs.2 X hX
      obtain ⟨c, r, hR⟩ := Tmem.One.entry_ready hX hto
        ⟨hp.cluster.2.2, by rw [hp.cluster.1, Nat.mod_one]⟩
        (fun h => hsafe (by simp [Unsafe, h])) hpd.1 he hperf hk hall
      obtain ⟨Y, hY, hle, hsize, -⟩ := Step.entry_counted hX hR
        (wfStepAll.quiet hX Tmem.Pair.le_recordEntry rfl (Execution.noNewRead_of_tr rfl))
      exact .inl ⟨Y, hY, hle, hsize⟩
    · exact htw hpd hrel ⟨_, hlen, hk, hall⟩

/-- **A lane blocked at a bulk-group wait steps.** -/
theorem bulk_steps (hmax : Maximal L kernel Assumptions.all m X) {g : Nat}
    (hrel : ¬ Step.Released L X g) (h : Sched.BulkWait L X g) : StepsAt p L m X (.thread g) :=
  Progress.drain_steps hmax (fun _ _ hi => Flow.no_bulkGroup hmax.1 kernel_noBulkGroup hi) hrel h

end PTX.Kernels.TmlFa4Fwd.Proof.Top
