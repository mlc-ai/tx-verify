-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Production

@[expose] public section

/-! # A loader reuses a slot only after the MMA reads of its earlier productions

A loader's successful empty poll with `q + 1` earlier successful polls is its poll for use
`q + 1`: it found phase `q + 1` and observed phase `q`, and both MMA threads' notifications of
the uses `0, …, q` are before it (`producer_poll`, by `PairTmaRing.producer_poll` with the slot's
notification selector, `notification_iff`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace InputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A loader's empty poll.** A successful poll of slot `s`'s empty barrier by producer `a`'s
thread, with `q + 1` earlier successful polls, has a fault-free record that observes the
barrier's phase `q`, with at least `q + 1` notifications of each MMA thread before it. -/
theorem producer_poll (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {s : Fin 4} {a : Fin 2} {gl jl pc p : Nat} {acq : Bool}
    {sc : MbarScope} (hprod : producerThread L c a gl = true)
    (hwl : X.get (gl, jl) = some ⟨pc, .wait ((slot L c s).empty a) p true acq sc⟩) {q : Nat}
    (hq : okPolls ((slot L c s).empty a) ((X.tr gl).take jl) = q + 1) :
    ∃ jr w, (X.objects ((slot L c s).empty a))[jr]? = some w ∧ w.id = .thread (gl, jl) ∧
      w.fault = none ∧ w.reply.waited = some true ∧
      observedAt (X.objects ((slot L c s).empty a)) jr = some q ∧
      ∀ b, q + 1 ≤ ((X.objects ((slot L c s).empty a)).take jr).countP
        ((slot L c s).notification a b) := by
  have hg := producerOf_eq hX ht hprod hwl
  subst hg
  obtain ⟨jr, w, hjr, hwid, hwf, hww, ho, hnot⟩ :=
    PairTmaRing.producer_poll hX (hyp hpre hX ht c s) hwl hq
  refine ⟨jr, w, hjr, hwid, hwf, hww, ho, fun b => ?_⟩
  rw [List.countP_congr (fun x hx => by
    rw [notification_iff hpre hX ht (List.mem_of_mem_take hx)])]
  exact hnot b

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
