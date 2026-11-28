-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Prog.Classes
import Kernels.InklingRelDecode.Proof.Common.Export.Tmem
import Kernels.InklingRelDecode.Proof.Top.Prog.CollSteps
import Kernels.InklingRelDecode.Proof.Startup.Export.AllocSteps
import Kernels.InklingRelDecode.Proof.Lib.AssumptionStep
import Lemmas.Tmem.AllocResult
import Lemmas.Tmem.Tmem1Ready
import Lemmas.Tmem.Tmem1ReadyG
import Lemmas.Tmem.TmemPairHistory
import Lemmas.Tcgen05.TcExtend

/-! # A lane blocked at a Tensor Memory resource operation steps

A resource operation is a warp-collective `tcgen05` event of warp 0 of the CTA. When a lane of
the warp has not made the collective, the collective class applies (`htc`). When every lane has,
the operation is not performed and the allocator can perform it (`Tmem.One.entry_readyG`), or it
is performed and the event waits for the allocation's result: lane 0 has not stored it (its event
after the allocation is the store), so its last event is the allocation and it is earlier than
the blocked lane. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem kind_ne {e : Event} {i : EvId} (hnu : ¬ HasUb X) (he : X.get i = some e) :
    ∀ u, e.kind ≠ .ub u := by
  intro u hk
  apply hnu
  obtain ⟨pc, k⟩ := e
  simp only at hk
  subst hk
  exact ⟨i, pc, u, he⟩

/-- **A lane whose allocation is performed but not published steps**: lane 0 of its warp is
at the store, earlier. -/
public theorem Prog.publish_steps (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X) (hFw : Follow Q L X) {g pc n : Nat}
    {grp : CtaGroup} {dst : Option Loc} (hg : Frame.Pending L X g) (hrel : ¬ Step.Released L X g)
    (he : X.get (g, (X.tr g).length - 1) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩)
    (hperf : Tmem.Pair.Performed L X (g, (X.tr g).length - 1)) (hl : PTX.laneOf L g ≠ 0)
    (hmiss : ¬ ∃ store out, Tmem.Pair.AllocResult L X store (g, (X.tr g).length - 1) out) :
    Sched.Steps (schedule Q L) m X (.thread g) := by
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
  have hcta : (r.own.event L 0).1 / L.block = r.own.cta := hprop.1
  have hll := (List.getElem?_eq_some_iff.mp hl0).1
  by_cases hlater : (r.own.event L 0).2 + 1 < (X.tr (r.own.event L 0).1).length
  · exfalso
    have hst : X.get ((r.own.event L 0).1, (r.own.event L 0).2 + 1) = some _ :=
      List.getElem?_eq_getElem hlater
    obtain ⟨bytes, hs'⟩ := Startup.Export.alloc_next_wr hp hX hFw hl0 hzero hst
      (kind_ne hnu hst)
    obtain ⟨-, -, hdst, -⟩ := Startup.Export.alloc_event hp hX hFw hl0
    rw [hs'] at hst
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
    exact Sched.earlier_steps hmax hrel hph (Startup.Export.alloc_earlier hp hX hFw hl0
      hlast.symm hzero he (by omega) hl)

/-- **A Tensor Memory operation not performed, whose warp's lanes have all made it, is recorded**:
a counted extension. -/
public theorem Prog.tmem_ext (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow Q L X) {g pc : Nat}
    {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request} (hg : g < L.threads)
    (he : X.get (g, (X.tr g).length - 1) = some ⟨pc, .tc (.resource grp dst act)⟩)
    (hperf : ¬ Tmem.Pair.Performed L X (g, (X.tr g).length - 1))
    (hall : ∀ h, h < L.threads → SameWarp L g h →
      ∃ j, X.TcK (h, j) (((X.tr g).take ((X.tr g).length - 1)).countP isTcColl)) :
    ∃ Y, Consistent L kernel Assumptions.all m Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hto := Export.tmem_ops hp hX hFw
  have hk : X.TcK (g, (X.tr g).length - 1)
      (((X.tr g).take ((X.tr g).length - 1)).countP isTcColl) := ⟨⟨_, he, rfl⟩, rfl⟩
  have hsafe := hs.2 X hX
  obtain ⟨c, r, hR⟩ := Tmem.One.entry_readyG hX hto hp.launchValid.1
    (fun h => hsafe (by simp [Unsafe, h])) hg he hperf hk hall
  obtain ⟨Y, hY, hle, hsize, -⟩ := Step.entry_counted hX hR
    (Lib.assumptions_step.wfQuiet.quiet hX Tmem.Pair.le_recordEntry rfl
      (Execution.quietExt_of_tr rfl))
  exact ⟨Y, hY, hle, hsize⟩

/-- **A Tensor Memory operation other than an allocation, whose warp's lanes have all made it,
is released or recorded.** -/
public theorem Prog.tmem_rel_or_ext (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow Q L X) {g pc : Nat}
    {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request} (hg : g < L.threads)
    (he : X.get (g, (X.tr g).length - 1) = some ⟨pc, .tc (.resource grp dst act)⟩)
    (hna : ∀ n, act ≠ .alloc n)
    (hall : ∀ h, h < L.threads → SameWarp L g h →
      ∃ j, X.TcK (h, j) (((X.tr g).take ((X.tr g).length - 1)).countP isTcColl)) :
    Step.Released L X g ∨ ∃ Y, Consistent L kernel Assumptions.all m Y ∧ X.le Y ∧
      X.size L < Y.size L := by
  by_cases hperf : Tmem.Pair.Performed L X (g, (X.tr g).length - 1)
  · left
    have hto := Export.tmem_ops hp hX hFw
    exact ⟨fun _ _ hget _ => by
      rw [he] at hget
      cases hget
      exact Tmem.Pair.ReturnReady.ready hX.tmemPair he
        ⟨hperf, fun _ => Tmem.One.covered_of_performed hX hto hperf⟩
        fun n hn _ => absurd hn (hna n)⟩
  · exact .inr (Prog.tmem_ext hp hs hX hFw hg he hperf hall)

/-- **A lane blocked at a Tensor Memory resource operation steps**, by the collective class. -/
public theorem Prog.tmem_steps (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X) (hFw : Follow Q L X)
    {g : Nat} (hpd : Frame.Pending L X g) (hrel : ¬ Step.Released L X g)
    (h : Sched.TmemWait L X g) : Sched.Steps (schedule Q L) m X (.thread g) := by
  have hX := hmax.1
  have hto := Export.tmem_ops hp hX hFw
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
    · obtain ⟨Y, hY, hle, hsize⟩ := Prog.tmem_ext hp hs hX hFw hpd.1 he hperf hall
      exact .inl ⟨Y, hY, hle, hsize⟩
    · exact Prog.tc_steps hp hs hmax hFw hpd hrel ⟨_, hlen, hk, hall⟩

end PTX.Kernels.InklingRelDecode.Proof.Top
