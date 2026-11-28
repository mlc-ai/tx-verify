-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Classes
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemResource
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.AllocSteps
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.TcSteps
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WfStep
import Lemmas.Tmem.AllocResult
import Lemmas.Tmem.Tmem1Ready
import Lemmas.Tmem.Tmem1ReadyG
import Lemmas.Tmem.TmemPairHistory
import Lemmas.Tcgen05.TcExtend

@[expose] public section

/-! # A lane blocked at a Tensor Memory resource operation steps

The template is tml-fa4's `Top/Prog/TmemBulk.lean`. A resource operation is a warp-collective
`tcgen05` event (warp 0 of the CTA, `Safe.tmemOne`). When a lane of the warp has not made the
collective, `tc_steps` applies. When every lane has, the operation is not performed and the
allocator can perform it (`Tmem.One.entry_readyG`), or it is performed and the event waits for
the allocation's result: lane 0 has not stored it (its event after the allocation is the store,
`alloc_next_wr`), so its last event is the allocation and it is earlier than the blocked lane
(`alloc_earlier`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A lane whose allocation is performed but not published steps**: lane 0 of its warp is
at the store, earlier. -/
theorem Prog.publish_steps (hp : Pre P L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X) (hFw : Follow P L X) {g pc n : Nat}
    {grp : CtaGroup} {dst : Option Loc} (hg : Frame.Pending L X g) (hrel : ¬ Step.Released L X g)
    (he : X.get (g, (X.tr g).length - 1) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩)
    (hperf : Tmem.Pair.Performed L X (g, (X.tr g).length - 1)) (hl : PTX.laneOf L g ≠ 0)
    (hmiss : ¬ ∃ store out, Tmem.Pair.AllocResult L X store (g, (X.tr g).length - 1) out) :
    Sched.Steps (timed P L) m X (.thread g) := by
  have hX := hmax.1
  have hnu := Sched.safe_noUb (hs.2 X hX)
  obtain ⟨cta, r, hr, lane, hlane⟩ := hperf
  have hv := ((hX.tmemPair.1 cta).1 r hr).2.2
  have hlen : 0 < (X.tr g).length := by
    have := (List.getElem?_eq_some_iff.mp
      (show (X.tr g)[(X.tr g).length - 1]? = some _ from he)).1
    omega
  have hget := hv.2.2.1 lane
  rw [hlane, he] at hget
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hget
  obtain ⟨rfl, rfl, rfl, hact⟩ := hget
  have hl0 := hv.2.2.1 0
  rw [← hact] at hl0
  have hprop := Tmem.Pair.WarpRequest.event_props hv 0
  have hlt := hprop.2.2
  have hzero : PTX.laneOf L (r.own.event L 0).1 = 0 := by
    have hwl : r.own.warp * 32 < L.block := by have := hv.2.1; omega
    simp only [PTX.laneOf, Tmem.Pair.WarpRequest.event, Fin.val_zero, Nat.add_zero]
    rw [Nat.mul_comm r.own.cta, Nat.mul_add_mod, Nat.mod_eq_of_lt hwl]
    simp
  have hpc0 := alloc_pc hp hX hFw hlt hl0
  have hcta : (r.own.event L 0).1 / L.block = r.own.cta := hprop.1
  have hll := (List.getElem?_eq_some_iff.mp hl0).1
  by_cases hlater : (r.own.event L 0).2 + 1 < (X.tr (r.own.event L 0).1).length
  · exfalso
    have hst : X.get ((r.own.event L 0).1, (r.own.event L 0).2 + 1) = some _ :=
      List.getElem?_eq_getElem hlater
    obtain ⟨h91, bytes, hs⟩ := alloc_next_wr hp hX hFw hnu hl0 hpc0 hzero hst
    rw [hs] at hst
    obtain ⟨-, hc⟩ := startup_tc hp hX hFw hl0 hpc0 rfl
    rcases hc with hc | hc
    · simp only [TcKind.resource.injEq] at hc
      obtain ⟨-, hdst, -⟩ := hc
      rw [← h91] at hst
      have hres := Tmem.Pair.AllocResult.of_warpRequest hv hact.symm hdst rfl
        (by simpa [wsLoc, Tmem.Pair.WarpRequest.event] using hcta) hst lane
      rw [hlane] at hres
      exact hmiss ⟨_, _, hres⟩
    · simp at hc
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
    exact Sched.earlier_steps hmax hrel hph (alloc_earlier hp hX hFw hl0 hpc0 hlast.symm hzero
      he (alloc_pc hp hX hFw hg.1 he) (by omega) hl)

/-- **A lane blocked at a Tensor Memory resource operation steps.** -/
theorem Prog.tmem_steps (hp : Pre P L m) (hIn : Top.Inputs P L m)
    (hs : SafeGoal kernel Assumptions.all L m) (hmax : Maximal L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g : Nat} (hpd : Frame.Pending L X g) (hrel : ¬ Step.Released L X g)
    (h : Sched.TmemWait L X g) : Sched.Steps (timed P L) m X (.thread g) := by
  have hX := hmax.1
  have hto := (Safe.tmemOne hp hIn hX hFw).toTmem1Ops
  obtain ⟨pc, grp, dst, act, he, hnr⟩ := h
  have hlen : 0 < (X.tr g).length := by
    have := (List.getElem?_eq_some_iff.mp
      (show (X.tr g)[(X.tr g).length - 1]? = some _ from he)).1
    omega
  by_cases hperf : Tmem.Pair.Performed L X (g, (X.tr g).length - 1)
  · have hm : ∃ n, act = .alloc n ∧ PTX.laneOf L g ≠ 0 ∧
        ¬ ∃ store out, Tmem.Pair.AllocResult L X store (g, (X.tr g).length - 1) out := by
      by_contra hn
      refine hnr (Tmem.Pair.ReturnReady.ready hX.tmemPair he
        ⟨hperf, fun _ => Tmem.One.covered_of_performed hX hto hperf⟩ fun n hna hl => ?_)
      by_contra hmiss
      exact hn ⟨n, hna, hl, hmiss⟩
    obtain ⟨n, rfl, hl, hmiss⟩ := hm
    exact Prog.publish_steps hp hs hmax hFw hpd hrel he hperf hl hmiss
  · have hk : X.TcK (g, (X.tr g).length - 1)
        (((X.tr g).take ((X.tr g).length - 1)).countP isTcColl) := ⟨⟨_, he, rfl⟩, rfl⟩
    by_cases hall : ∀ h, h < L.threads → SameWarp L g h →
        ∃ j, X.TcK (h, j) (((X.tr g).take ((X.tr g).length - 1)).countP isTcColl)
    · have hsafe := hs.2 X hX
      obtain ⟨c, r, hR⟩ := Tmem.One.entry_readyG hX hto hp.launchValid.1
        (fun h => hsafe (by simp [Unsafe, h])) hpd.1 he hperf hk hall
      obtain ⟨Y, hY, hle, hsize, -⟩ := Step.entry_counted hX hR
        (wfQuiet_all.quiet hX Tmem.Pair.le_recordEntry rfl (Execution.quietExt_of_tr rfl))
      exact .inl ⟨Y, hY, hle, hsize⟩
    · exact tc_steps hp hs hmax hFw hpd hrel ⟨_, hlen, hk, hall⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
