-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemReach
public import Lemmas.Protocol.UnitReachBlocker

@[expose] public section

/-! # Who blocks the MMA warp at a P-ready poll

Stage `st`'s P-ready object of the pair led by CTA `c` (`pReadyBar`) is a unit object of its 512
producers (`pObj`), whose arrivals the MMA warp's polls enable (`pReadyReach`, from the routes'
context `RouteCtx`). So when its final phase has the parity of an MMA thread's next poll, the
phase is the thread's successful polls of it, and some producer (`pThread`: a softmax thread of
the stage or a correction thread, of either CTA of the pair) has made no more arrivals on it than
that phase (`pReady_blocked`, by `MbarRing.Unit.Obj.reach_short`, when no record faults).

`pThread_spec` places each producer: a launched thread of the pair, of the stage's softmax warps
or of the correction warps. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof
open AsyncCopy MBarrier

noncomputable section

namespace Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- A P-ready producer is a launched thread of the pair: a softmax thread of the stage or a
correction thread. -/
theorem pThread_spec (hpre : Pre P L mem0) {c st : Nat} (hc : leadCta c = c) (hcg : c < L.grid)
    (hst : st < 2) (a : Fin 512) :
    pThread L c st a < L.threads ∧ leadCta (ctaOf L (pThread L c st a)) = c ∧
      ((warpOf L (pThread L c st a) < 8 ∧ warpOf L (pThread L c st a) / 4 = st) ∨
        (8 ≤ warpOf L (pThread L c st a) ∧ warpOf L (pThread L c st a) < 12)) := by
  have hb := hpre.block
  have hgr := hpre.grid
  have ha := a.isLt
  unfold leadCta at hc ⊢
  unfold pThread ctaOf warpOf
  simp only [Launch.threads]
  rw [hb] at ⊢
  split_ifs with h
  · exact ⟨by omega, by omega, .inl ⟨by omega, by omega⟩⟩
  · exact ⟨by omega, by omega, .inr ⟨by omega, by omega⟩⟩

/-- **The P-ready blocker.** When the final phase of stage `st`'s P-ready object of the pair led
by `c` has the parity of an MMA thread's next poll, the phase is the thread's successful polls of
it, and some producer has made no more arrivals on it than the phase. -/
theorem pReady_blocked (H : RouteCtx P L mem0 K A X) {c st h : Nat} (hc : leadCta c = c)
    (hst : st < 2) (hh : mmaIn L c h) (hff : ∀ r ∈ X.objects (pReadyBar L c st), r.fault = none)
    {before : State}
    (hb : stateBefore (X.objects (pReadyBar L c st)) (X.objects (pReadyBar L c st)).length =
      some before)
    (hpar : before.phase % 2 = okPolls (pReadyBar L c st) (X.tr h) % 2) :
    before.phase = okPolls (pReadyBar L c st) (X.tr h) ∧
      ∃ a, arrivals (pReadyBar L c st) (X.tr (pThread L c st a)) ≤ before.phase := by
  have O := pObj H.pre H.cons H.pf H.tm H.pinit hc hst
  obtain ⟨h1, h2⟩ := O.reach_short H.cons (pReadyReach H c st hc hst h hh) hff hb
    (Nat.zero_le _) (by simpa using hpar)
  exact ⟨by simpa using h1, h2⟩

end Score

end
end PTX.Kernels.FlashAttn4Fwd.Proof
