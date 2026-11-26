-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.NextEv
public import Kernels.TmlFa4Fwd.Proof.Protocol.Ld.Blk
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Kernels.TmlFa4Fwd.Proof.Mma.Export.CommitLag
import Kernels.TmlFa4Fwd.Proof.Progress.Order
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Target
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Winner
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Handoff
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A channel blocker without the waiter's state: tml-fa4's empty K/V slots

tml-fa4's `kvE_lag` (`Protocol/Ld/Blk.lean`) states the blocker of a loader lane at an empty-slot
wait with the lane's machine state (`Frame.stateAt … = some (some (.inr ⟨.loader b, d⟩, n))`),
which it uses for two things: the lane's trace is not empty, and the lane's time
(`Progress.time p L g σ`). `kvE_blkN` states the same blocker on the trace: the lane's trace is not
empty, and the wait's counts and lateness (`KvWait`) are taken at the lane's `threadTime`. The
proof is `kvE_lag`'s with `Sched.blk_of_lagsN` for `Sched.blk_of_lags`. `kvE_waitBlk` is the
channel's export in the shape `Sched.wait_site_stepsN` consumes, and `kvE_lag_of_N` recovers the
old statement. -/

namespace PTX.Tests.NextEvLag
open PTX PTX.Flow PTX.Kernels.TmlFa4Fwd PTX.Kernels.TmlFa4Fwd.Proof

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A blocked wait for empty K/V slot `i % 3` has an earlier blocker**, stated on the trace. -/
theorem kvE_blkN (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hff : ∀ l, ∀ r ∈ X.objects l, r.fault = none) (hub : ¬ HasUb X)
    (hg : g < L.threads) (hne : X.tr g ≠ [])
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {i : Nat}
    (hi : KvWait p L X g (Sched.threadTime (Progress.timed p L) X g) i) {f : MBarrier.State}
    (hst : Final X (obj L g (56 + 8 * (i % 3))) f)
    (hpar : f.phase % 2 = (i / 3 + 1) % 2) : Sched.Blk (Progress.timed p L) X g := by
  obtain ⟨hok, hlate⟩ := hi
  have hmod := Nat.mod_lt i (show 0 < 3 by decide)
  obtain ⟨hph, hcm⟩ := kvE_blocked hp hX hFw hff g hg ⟨i % 3, hmod⟩ ⟨rfl, hw⟩ hst
    (by rw [show okPolls (kvE L g ⟨i % 3, hmod⟩) (X.tr g) = i / 3 from hok, hpar])
  rw [show okPolls (kvE L g ⟨i % 3, hmod⟩) (X.tr g) = i / 3 from hok] at hph
  obtain ⟨R, hR, hi5, htime⟩ := hlate (by omega)
  rcases hcm with h | h
  swap
  · exact .inl ⟨.commit, .inl rfl, h⟩
  obtain ⟨z, hzt, hzc, hzw, hwin⟩ := warp_winner hp hX hg (w := 12) (by omega)
  have hRz := hR.cta hzc.symm
  have hcnt : (X.tr z).countP (commitsTo (obj L z (56 + 8 * (i % 3)))) + 1 ≤ i / 3 := by
    rw [obj_cta hzc]
    by_contra hgt
    obtain ⟨e, he, hea⟩ := List.countP_pos_iff.mp
      (show 0 < (X.tr z).countP (commitsTo (obj L g (56 + 8 * (i % 3)))) by omega)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    have hget : X.get (z, j) = some ((X.tr z)[j]) := List.getElem?_eq_getElem hj
    generalize (X.tr z)[j] = e at hget hea
    obtain ⟨pc, kd⟩ := e
    unfold commitsTo at hea
    split at hea
    · rename_i sp hk
      obtain rfl : kd = .tc (.commit sp) := hk
      obtain ⟨rank, ht⟩ := commit_self hp hX hget
      rw [of_decide_eq_true hea] at ht
      have hz := commitLane_eq hp hX hFw hget ht
      simp only at h
      rw [← hz] at h
      have h' : (X.tr z).countP (commitsTo (obj L g (56 + 8 * (i % 3)))) ≤ f.phase := h
      omega
    · cases hea
  have hbm := mma_rounds_bmax hp hg hR
  have h3 : 3 ≤ i := by omega
  refine Sched.blk_of_lagsN hX hub hg hne hzt (by rw [hzc]) fun _ => ⟨fun k pc hx => ?_, ?_⟩
  · have h1 := mma_exit_commits hp hX hFw hub hzt hzw hwin hRz hx (56 + 8 * (i % 3))
    have h2 := commitAt_kv_total h3 hi5
    omega
  · refine (kv_commit_early hp hX hFw hub hzt hzw hwin hRz h3 hi5 hcnt).trans_le ?_
    rcases htime with ht | ⟨hi2, ht⟩
    · refine le_trans (le_of_lt (Progress.drain_order p ?_ (by decide))) ht
      omega
    · refine le_trans ?_ ht
      rw [Progress.slotOf_eq (by omega)]
      have : min ((i - 2) / 2) (R + 1) = (i - 2) / 2 := by omega
      rw [this]
      unfold Progress.clk Progress.bandL
      omega

/-- **The channel's export in the consumer's shape**: a lane whose next event is a failed poll of
empty slot `i % 3` with the parity of `i / 3 + 1` is blocked as `Sched.WaitBlk` states it, given
the slot's final state and the wait's counts at the lane's time. -/
theorem kvE_waitBlk (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hff : ∀ l, ∀ r ∈ X.objects l, r.fault = none) (hub : ¬ HasUb X)
    (hne : X.tr g ≠ []) (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
    {i pc q : Nat} {sc : MbarScope}
    (hN : Sched.NextEv L kernel Assumptions.all m X g
      ⟨pc, .wait (obj L g (56 + 8 * (i % 3))) q false true sc⟩)
    (hq : q % 2 = (i / 3 + 1) % 2)
    (hi : KvWait p L X g (Sched.threadTime (Progress.timed p L) X g) i) {f : MBarrier.State}
    (hst : Final X (obj L g (56 + 8 * (i % 3))) f) :
    Sched.WaitBlk (Progress.timed p L) X g (obj L g (56 + 8 * (i % 3))) q :=
  ⟨f, hst, fun hpar => kvE_blkN hp hX hFw hff hub hN.lt hne hw hi hst (hpar.trans hq)⟩

/-- The state-level statement follows: the lane's time is its state's time. -/
theorem kvE_lag_of_N (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hff : ∀ l, ∀ r ∈ X.objects l, r.fault = none) (hub : ¬ HasUb X)
    (hg : g < L.threads) {b : Bool} {d : Loader.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (.inr ⟨.loader b, d⟩, n)))
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {i : Nat}
    (hi : KvWait p L X g (Progress.time p L g (.inr ⟨.loader b, d⟩, n)) i) {f : MBarrier.State}
    (hst : Final X (obj L g (56 + 8 * (i % 3))) f)
    (hpar : f.phase % 2 = (i / 3 + 1) % 2) : Sched.Blk (Progress.timed p L) X g := by
  have hne : X.tr g ≠ [] := by
    intro h0
    rw [show (X.tr g).length = 0 by rw [h0]; rfl, Frame.stateAt_zero] at hσ
    simp [thread, glued, Code.glue, Code.counted, Code.enter, Startup.code, exit] at hσ
  have ht : Sched.threadTime (Progress.timed p L) X g =
      Progress.time p L g (.inr ⟨.loader b, d⟩, n) :=
    Sched.threadTime_of (M := Progress.timed p L) hσ
  exact kvE_blkN hp hX hFw hff hub hg hne hw (ht ▸ hi) hst hpar

end
end PTX.Tests.NextEvLag
