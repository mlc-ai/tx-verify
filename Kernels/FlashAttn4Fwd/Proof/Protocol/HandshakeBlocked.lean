-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemAllocHandshake

@[expose] public section

/-! # Who blocks an MMA lane at its deallocation handshake poll

The handshake barrier of a CTA is a one-phase barrier whose arrivals are the 32 lanes of the
other CTA's warp 12 (`TmemAlloc.table`). Its final state is phase 1 exactly when every one of these
arrivals is recorded, and phase 0 otherwise (`MbarOneShot.Hist.final_state`). An arrival
event on the barrier is its lane's first (`arriveIdx_eq`) and is recorded (OBJ-MBAR-STATE: every
object operation has its record). So when the final phase is even, it is phase 0, and some lane of
the other CTA's warp 12 has made no arrival on the barrier (`handshake_short`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.TmemAlloc
open PTX PTX.Proof AsyncCopy MBarrier

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Some lane of the other CTA's warp 12 has not arrived on a handshake barrier in an even
phase.** -/
theorem handshake_short (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : TmemFacts L X) {cta : Nat} (hi : HsInit L X cta) {before : State}
    (hs : stateBefore (X.objects (hsLoc L cta)) (X.objects (hsLoc L cta)).length = some before)
    (h0 : before.phase % 2 = 0) :
    ∃ l < 32, Flow.arrivals (hsLoc L cta) (X.tr (lane0 L (pairCta cta) + l)) = 0 := by
  have hne : X.objects (hsLoc L cta) ≠ [] := by
    intro he
    rw [he] at hs
    simp [stateBefore] at hs
  obtain ⟨s, hs', hle, hiff⟩ := (table hpre hX ht hi).final_state hX hne
  rw [hs] at hs'
  cases hs'
  by_contra hall
  push Not at hall
  have h1 : before.phase = 1 := by
    refine hiff.mpr ⟨fun a ha => ?_, fun c hc => by simp at hc⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    have hcnt := hall l (List.mem_range.mp hl)
    generalize lane0 L (pairCta cta) + l = y at hcnt ⊢
    obtain ⟨e, hmem, hp⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero hcnt)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
    have hget : X.get (y, j) = some (X.tr y)[j] := List.getElem?_eq_getElem hj
    revert hp hget
    generalize (X.tr y)[j] = ev
    intro hp hget
    obtain ⟨pc, k⟩ := ev
    cases k with
    | arrive m' tx c rel sc =>
      simp only [Flow.arrivesOn, sourceArrive, decide_eq_true_eq] at hp
      subst hp
      rw [arriveIdx_eq hX ht hget]
      obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 (hsLoc L cta)).2.2 (.thread (y, j)) (.arrive c tx)
        (by simp [objectAction, hget])
      exact ⟨r, hr, hid⟩
    | _ => simp [Flow.arrivesOn, sourceArrive] at hp
  omega

end

end PTX.Kernels.FlashAttn4Fwd.Proof.TmemAlloc
