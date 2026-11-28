-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
import Kernels.InklingRelDecode.Proof.Common.EpilogueEvent
import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
import Kernels.InklingRelDecode.Proof.Epilogue.Export.WaitValue
import Kernels.InklingRelDecode.Proof.Lib.WinEvent
import Kernels.InklingRelDecode.Proof.Lib.LanePre
import Kernels.InklingRelDecode.Proof.Lib.WinLane
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
import Kernels.InklingRelDecode.Flow.Code.Part040
import Lemmas.Kernel.PostEvent

@[expose] public section

/-! # The state after the epilogue's wait

A state of the lane at pc 2566 follows the epilogue's poll (pc 2565), whose state carries the
entry's skip flag in register 173 (the launch has no block) and the zero word in register 1760;
the poll writes neither. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Proof

private theorem pre_ok : Lib.predOk 2566 [] = true := by decide +kernel
private theorem ev_ok : Lib.evPre 2566 = true := by decide +kernel

private theorem keep2565 : (match kernel.code[2565]? with
    | some ins => [173, 1760].all (fun r => !(EventFrame.eventWrites ins.op).contains r)
    | none => true) = true := by decide +kernel

private theorem site_wait (s : Epilogue.Site) (h : s.pc = 2565) : s = .wait := by
  cases s <;> first | rfl | (exfalso; revert h; decide) |
    (simp only [Epilogue.Site.pc, Epilogue.storePc] at h; omega)

/-- **The registers 173 and 1760 after the poll** of the epilogue: the launch has no block, and
the zero word. -/
public theorem epi_wait {Q L m X g} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) {c : TState}
    (hc : Iface.LaneState L X g c) (hpc : c.pc = 2566) :
    c.regs 173 = some (.pred (decide (Lib.blocksOf Q L (g / L.block) = 0))) ∧
      c.regs 1760 = some (b32 0) := by
  obtain ⟨k, e, hk, hepc, hr⟩ := Lib.ev_before pre_ok ev_ok (by omega) hc hpc
  obtain ⟨s0, -, hes0⟩ := Lib.lane_pre hk hr
  obtain ⟨m0, -, hfire0⟩ := hes0
  have nu : ∀ f, e.kind ≠ .ub f := fun f h => by
    obtain ⟨p, kd⟩ := e
    subst h
    exact fires_some_not_ub hfire0 p f rfl
  have he : X.get (g, k) = some e := hk
  have hg := Frame.lt_of_get hX he
  obtain ⟨w, ent, d, n, -, -, -, hs, -, -, pcd, -⟩ :=
    epilogue_event_entry hp hX hf he nu (by omega) (by omega)
  obtain ⟨s, ins, ⟨_, -, -, -, regs⟩, -, -, hes⟩ :=
    Frame.post_event (fun g hg => thread_sound hp hg) hX he hr hs
  have hsite : d.site = .wait := site_wait _ (by rw [← pcd]; omega)
  have hk' : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨hlim, hskip⟩ := reached_loop hp hX hg hk' hs
  have r1 := holds_mem regs (mem_factsFrom (by rw [hsite]; exact Epilogue.Export.wait_live.1))
  have r2 := holds_mem regs (mem_factsFrom (by rw [hsite]; exact Epilogue.Export.wait_live.2))
  rw [Epilogue.Export.value_skip] at r1
  rw [Epilogue.Export.value_zero] at r2
  have hspc := EventFrame.estep_source_pc hes
  obtain ⟨ins', hci, -, -⟩ := EventFrame.estep_event_source hes
  have hs2565 : s.pc = 2565 := by omega
  rw [hs2565, Flow.code_2565] at hci
  obtain rfl := (Option.some.inj hci).symm
  have kp := keep2565
  rw [Flow.code_2565] at kp
  have kp1 := List.all_eq_true.mp kp 173 (by simp)
  have kp2 := List.all_eq_true.mp kp 1760 (by simp)
  refine ⟨?_, ?_⟩
  · rw [Lib.estep_keeps hes _ (by rw [hs2565, Flow.code_2565]) 173 (by simpa using kp1), r1]
    change some (Value.pred (decide (ent.blocks = 0 ∨ 2 ^ 31 ≤ ent.blocks))) = _
    rw [hskip, hlim]
  · rw [Lib.estep_keeps hes _ (by rw [hs2565, Flow.code_2565]) 1760 (by simpa using kp2), r2]

end PTX.Kernels.InklingRelDecode.Proof.Export
