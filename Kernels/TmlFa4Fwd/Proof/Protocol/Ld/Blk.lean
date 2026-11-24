-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.LdKvWait
public import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Channels
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Kernels.TmlFa4Fwd.Proof.Mma.Export.CommitLag
import Kernels.TmlFa4Fwd.Proof.Progress.Order
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Target
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Winner
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Handoff
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Progress at the loader's waits for an empty K/V slot

`kvE_lag`: a blocked wait for packet `i` has the MMA warp's committing lane short of its release of
packet `i - 3`, in an earlier slot or band M of the wait's slot. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem kvE_lag (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
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
  refine Sched.blk_of_lags hX hub hg hne hσ hzt (by rw [hzc]) fun _ => ⟨fun k pc hx => ?_, ?_⟩
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

end
end PTX.Kernels.TmlFa4Fwd.Proof
