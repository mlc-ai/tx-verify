-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.WarpColl
public import Kernels.InklingRelDecode.Proof.Common.StartupEvents
public import Lemmas.Kernel.Progress.WarpCls
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Common.Sound

@[expose] public section

/-! # The collectives a data lane has made

A lane of the first four warps runs the startup and then the data roles, none of which holds a
warp barrier or a ballot: its warp collectives are its shuffles and its elections. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame PTX.Descent

private theorem tag_ck : kernel.code.zipIdx.all (fun x => opKind x.1.op != .warp ||
    decide (2344 < x.2 ∧ x.2 < 2557 ∧ x.2 ≠ 2422) ||
    decide ((Sched.CollShape.tag (pcShape x.2)) ≤ 1)) = true := by
  decide +kernel

/-- **An event of a data lane is a warp collective** exactly when it is a shuffle or an
election. -/
theorem data_event {Q L m X g j ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (lane : g % L.block < 128)
    (get : X.get (g, j) = some ev) (nu : ∀ f, ev.kind ≠ .ub f) :
    Sched.isWarpColl ev = (Execution.isShfl ev || isElectEv ev) := by
  have hg := lt_of_get hX get
  obtain ⟨s, hs, -⟩ := good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX get (fun pc f h => nu f (by rw [h])) ⟨control_tracked hp hX g j hg, fun _ _ => trivial⟩
  have pos := event_pcU (fun g hg => thread_sound hp hg) hX get hs nu
  have off : ¬ (2344 < ev.pc ∧ ev.pc < 2557 ∧ ev.pc ≠ 2422) := by
    rintro ⟨a, b, c⟩
    obtain ⟨w, x, r, d, n, rfl⟩ := (pos ▸ state_role s).worker a b c
    have := (worker_warp hp hX (List.getElem?_eq_some_iff.mp get).1.le hs).1
    simp only at this
    omega
  cases hc : Sched.isWarpColl ev
  · obtain ⟨pc, k⟩ := ev
    cases k <;> simp_all [Sched.isWarpColl, Execution.isShfl, isElectEv]
  · have hk := warp_kind hX get hc
    have hw := warp_event hX get nu
    unfold isWarpAt at hw
    rw [hc] at hw
    cases hco : kernel.code[ev.pc]? with
    | none => rw [hco] at hw; simp at hw
    | some ins =>
      rw [hco] at hw
      simp only [Option.any_some] at hw
      have ck := List.all_eq_true.mp tag_ck (ins, ev.pc) (List.mem_zipIdx_iff_getElem?.mpr hco)
      have tag : (Sched.CollShape.tag (pcShape ev.pc)) ≤ 1 := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at ck
        rcases ck with (h | h) | h
        · exact absurd (beq_iff_eq.mp hw.symm) h
        · exact absurd h off
        · exact h
      rw [Sched.shfl_tag ev _ hk, Sched.elect_tag ev _ hk]
      generalize Sched.CollShape.tag (pcShape ev.pc) = t at tag
      interval_cases t <;> rfl

private theorem not_both (e : Event) :
    ¬ (Execution.isShfl e = true ∧ isElectEv e = true) := by
  obtain ⟨pc, kd⟩ := e
  cases kd <;> simp [Execution.isShfl, isElectEv]

private theorem count_or (l : List Event)
    (h : ∀ e ∈ l, Sched.isWarpColl e = (Execution.isShfl e || isElectEv e)) :
    l.countP Sched.isWarpColl = l.countP Execution.isShfl + l.countP isElectEv := by
  induction l with
  | nil => rfl
  | cons e t ih =>
    have he := h e (List.mem_cons_self ..)
    have ih := ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    simp only [List.countP_cons, ih, he]
    cases hs : Execution.isShfl e <;> cases hl : isElectEv e
    · simp
    · simp; omega
    · simp; omega
    · exact absurd ⟨hs, hl⟩ (not_both e)

/-- **A data lane's collectives** are its shuffles and its elections. -/
theorem data_collCount {Q L m X g k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (lane : g % L.block < 128)
    (nu : NoUbBefore X g k) :
    Sched.collCount X g k = ((X.tr g).take k).countP Execution.isShfl +
      ((X.tr g).take k).countP isElectEv := by
  refine count_or _ fun e he => ?_
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
  rw [List.getElem?_take] at hi
  split_ifs at hi with hik
  exact data_event hp hX lane hi (nu i hik e hi)

end PTX.Kernels.InklingRelDecode.Proof
