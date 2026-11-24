-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WkLdLag

@[expose] public section

/-!
# The KV ring's polls: the loader's half proved

`Wy.WorkerPollsRest` is the blocker clause of the loader's `kv_empty` poll and of the MMA warp's
`kv_ready` poll. The loader's half is proved (`workerPollsRest_of`): when the polled object's
final phase has the poll's parity, the committing MMA lane has not committed the block three
before the loader's, or a commit's notification is undelivered (`Wk.loader_empty_blocked`, for
every lane of the loader warp); in the first case the committing lane lags the loader lane
(`loader_lag`), so it is a blocker (`Wy.blk_of_lags`). The MMA warp's half is the premise
`MmaKvPollsRest`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wk
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Progress

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0}

/-- **The blocker clause of the MMA warp's `kv_ready` poll.** -/
def MmaKvPollsRest (T : Nat → TSt → Nat) (Q : Params) (L : Launch) (mem0 : Mem0) : Prop :=
  ∀ X g (d : Mma.D) (P : Loader.Pro) m par before, Maximal L kernel asms mem0 X →
    Frame.Pending L X g → Step.Released L X g →
    St Q L X g (X.tr g).length = some (some (.w (.mma d P))) → d.site = .kvWait →
    PollAt L g (.w (.mma d P)) m par →
    MBarrier.stateBefore (X.objects m) (X.objects m).length = some before →
    before.phase % 2 = par % 2 → Sched.Blk (timed T Q L) X g

/-- **`Wy.WorkerPollsRest`** from the loader's half and the premise of the MMA warp's half. -/
theorem workerPollsRest_of (hpre : Pre Q L mem0)
    (hF : ∀ X, Consistent L kernel asms mem0 X → ThreadFacts Q L mem0 X)
    (hR : ∀ X, Consistent L kernel asms mem0 X → RoleReads L X)
    (hB : ∀ X, Consistent L kernel asms mem0 X → BaseWordRead L X)
    (hN : ∀ X, Consistent L kernel asms mem0 X → NumWordRead Q L X)
    (hNP : ∀ X, Consistent L kernel asms mem0 X → NumPreRead Q L X)
    (hMB : ∀ X, Consistent L kernel asms mem0 X → Mma.MmaBcast L X)
    (hub : ∀ X, Consistent L kernel asms mem0 X → ¬ HasUb X)
    (hP : ∀ X, Consistent L kernel asms mem0 X →
      ∃ P : Sr.SrPkg L kernel asms mem0 X, ∀ c, P.cm c = Hs.cmOf L X c)
    (hm : MmaKvPollsRest Wt.time Q L mem0) : Wy.WorkerPollsRest Wt.time Q L mem0 := by
  intro X g s m par before hmax hp hrel hσ hnp hat hst hpar
  have hX := hmax.1
  have hg := hp.1
  cases s with
  | loader d P =>
    obtain ⟨G, hcm⟩ := hP X hX
    have hw : d.site = .wait := hat.1
    rcases Wk.loader_empty_blocked hpre hX (hF X hX) (hR X hX) (hNP X hX) G hg hσ hat hst hpar
      with h | h
    · obtain ⟨-, rfl, -⟩ := hat
      rw [hcm] at h
      exact Wy.blk_of_lags hX hσ (Hs.cm_mma hpre (by
          unfold Launch.threads at hg
          exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg))).1
        (loader_lag hpre hX (hF X hX) (hR X hX) (hB X hX) (hN X hX) (hMB X hX) (hub X hX) hg hσ
          hw h)
    · exact .inl ⟨.commit, .inl rfl, h⟩
  | mma d P =>
    rcases hat with hat' | hat'
    · exact hm X g d P m par before hmax hp hrel hσ hat'.1 (.inl hat') hst hpar
    · exact (hnp hat'.1).elim
  | _ => exact hat.elim

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wk
