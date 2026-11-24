-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Joint

@[expose] public section

/-! # A thread's acknowledgements are at most its selector's notifications

The acknowledgement barrier of a cluster records the arrivals of its selected threads, counted per
selector (`selectedArrival`). A thread of a selector arrives on the barrier only with records of
that selector: each of its arrivals is a record of the barrier whose thread is selected. So its
arrivals over its whole trace are at most the selector's records on the barrier. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace ClcRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The acknowledgements of a selected thread are its selector's notifications.** A thread `b` of
selector `f` of cluster `c` has at most as many arrivals on the acknowledgement barrier, over its
whole trace, as the barrier records for selector `f`. -/
theorem ack_arrivals_le (hX : Consistent L kernel Prod mem0 X) {c b : Nat} {f : Fin 10}
    (hb : consumerSel L c f b = true) :
    arrivals ((slot L c).empty 0) (X.tr b) ≤
      (X.objects ((slot L c).empty 0)).countP (selectedArrival (consumerSel L c f)) := by
  have hnodup : ((X.objects ((slot L c).empty 0)).map Record.id).Nodup := (hX.tma.2.2.1 _).1.1
  have hwin : ∀ q j, q ∈ X.objects ((slot L c).empty 0) → q.id = .thread (b, j) →
      (q ∈ X.objects ((slot L c).empty 0) ↔ j < (X.tr b).length) := by
    intro q j hq hid
    refine ⟨fun _ => ?_, fun _ => hq⟩
    have ha := ((hX.tma.2.2.1 _).2.1 q hq).1
    rw [hid] at ha
    cases he : X.get (b, j) with
    | none => simp [objectAction, he] at ha
    | some ev => exact len_of_get he
  have hcount := hX.object_thread_arrival_count_window (g := b) (k := (X.tr b).length)
    (X.objects ((slot L c).empty 0)) (fun _ hq => hq) hnodup hwin
  rw [List.take_length] at hcount
  unfold arrivals arrivesOn
  rw [← hcount]
  apply List.countP_mono_left
  intro q _ hthr
  obtain ⟨hsel, _, _, hact⟩ := threadArrival_iff.mp hthr
  obtain ⟨j, hqid⟩ := objectThreadSelected_iff.mp hsel
  simp only [selectedArrival, hqid, hact]
  exact hb

end ClcRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
