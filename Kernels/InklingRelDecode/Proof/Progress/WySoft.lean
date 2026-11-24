-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WyPolls
public import Kernels.InklingRelDecode.Proof.Interface.WyMma

@[expose] public section

/-!
# The blocker of the default partition's polls

The default partition polls three commit objects of its CTA's committing MMA lane `cm`: the softmax
region `s_ready (i % 2)` and `o_done`, the epilogue `o_final`. When the polled object's final phase
has the poll's parity, `cm` has made no more commits to it than the thread's successful polls of
it, or a commit's notification is undelivered, an open `.commit` obligation
(`Interface.soft_poll_blocked`, `Interface.epi_poll_blocked`). In the first case `cm` is a blocker
once it lags the polling thread (`Lags`: it has not exited and its time is earlier). That `cm`
lags is a statement about the MMA warp's machine (its commits as a function of its state, and its
time), the premise `CmLag`.

The MMA warp's poll of `p_ready b` is blocked by thread 0 of the CTA: `p_ready b` is a unit object
of that thread, and when its final phase has the parity of the lane's successful polls of it,
thread 0 has made no more arrivals than those polls (`Interface.mma_p_blocked`). The parity of
the lane's polls at its end state (`MmaParity`) and the lag of thread 0 behind the lane (`P0Lag`)
are statements about the MMA warp's machine, premises here.

The KV ring's polls (the loader's `kv_empty`, the MMA warp's `kv_ready`) are the premise
`WorkerPollsRest`, the blocker clause restricted to those states. `pollsRest_of` assembles
`PollsRest`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wy
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Progress

noncomputable section

variable {T : Nat → TSt → Nat} {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Thread `y` lags the state `d` of thread `g`**: `y` has not exited, and its time is earlier
than `d`'s. -/
def Lags (T : Nat → TSt → Nat) (Q : Params) (L : Launch) (X : Execution) (y g : Nat) (d : TSt) :
    Prop :=
  (∀ k pc, X.get (y, k) ≠ some ⟨pc, .exit⟩) ∧ Sched.threadTime (timed T Q L) X y < T g d

/-- **The committing MMA lane lags a default-partition thread at its poll** of `s_ready`,
`o_done` or `o_final` while it has made no more commits to the polled object than the thread's
successful polls of it. -/
def CmLag (T : Nat → TSt → Nat) (Q : Params) (L : Launch) (mem0 : Mem0) : Prop :=
  ∀ X g s m par, Consistent L kernel asms mem0 X → ¬ HasUb X → g < L.threads →
    St Q L X g (X.tr g).length = some (some (.d s)) → PollAt L g (.d s) m par →
    (X.tr (Hs.cmOf L X (g / L.block))).countP (commitsTo m) ≤ okPolls m (X.tr g) →
    Lags T Q L X (Hs.cmOf L X (g / L.block)) g (.d s)

/-- **The MMA warp's polls have the parity of its successful polls**: at a poll state at the end
of its trace (`kv_ready` or `p_ready`), a lane's successful polls of the polled object have the
poll's parity. -/
def MmaParity (Q : Params) (L : Launch) (mem0 : Mem0) : Prop :=
  ∀ X g (d : Mma.D) (P : Loader.Pro) m par, Consistent L kernel asms mem0 X → g < L.threads →
    St Q L X g (X.tr g).length = some (some (.w (.mma d P))) →
    PollAt L g (.w (.mma d P)) m par → okPolls m (X.tr g) % 2 = par % 2

/-- **Thread 0 of the CTA lags an MMA lane at its poll of `p_ready`** while it has made no more
arrivals on the polled object than the lane's successful polls of it. -/
def P0Lag (T : Nat → TSt → Nat) (Q : Params) (L : Launch) (mem0 : Mem0) : Prop :=
  ∀ X g (d : Mma.D) (P : Loader.Pro) m par, Consistent L kernel asms mem0 X → ¬ HasUb X →
    g < L.threads → St Q L X g (X.tr g).length = some (some (.w (.mma d P))) →
    d.site = .pWait → PollAt L g (.w (.mma d P)) m par →
    arrivals m (X.tr (Hs.p0Of L (g / L.block))) ≤ okPolls m (X.tr g) →
    Lags T Q L X (Hs.p0Of L (g / L.block)) g (.w (.mma d P))

/-- The MMA warp's `p_ready` poll state. -/
def IsPWait : WComp.WSt → Prop
  | .mma d _ => d.site = .pWait
  | _ => False

/-- **The blocker clause of the KV ring's polls** (the loader's `kv_empty`, the MMA warp's
`kv_ready`). -/
def WorkerPollsRest (T : Nat → TSt → Nat) (Q : Params) (L : Launch) (mem0 : Mem0) : Prop :=
  ∀ X g (s : WComp.WSt) m par before, Maximal L kernel asms mem0 X → Frame.Pending L X g →
    Step.Released L X g → St Q L X g (X.tr g).length = some (some (.w s)) → ¬ IsPWait s →
    PollAt L g (.w s) m par →
    MBarrier.stateBefore (X.objects m) (X.objects m).length = some before →
    before.phase % 2 = par % 2 → Sched.Blk (timed T Q L) X g

/-- **A lagging thread is a blocker.** -/
theorem blk_of_lags (hX : Consistent L kernel asms mem0 X) {g y : Nat} {d : TSt}
    (hσ : St Q L X g (X.tr g).length = some (some d)) (hy : y < L.threads)
    (hl : Lags T Q L X y g d) : Sched.Blk (timed T Q L) X g :=
  .inr ⟨y, pending_of_noExit hX hy hl.1, by rw [threadTime_eq hσ]; exact hl.2⟩

/-- **`PollsRest` from the lag of the committing lane and the workers' blocker clause.** -/
theorem pollsRest_of (hpre : Pre Q L mem0)
    (hF : ∀ X, Consistent L kernel asms mem0 X → ThreadFacts Q L mem0 X)
    (hR : ∀ X, Consistent L kernel asms mem0 X → RoleReads L X)
    (hub : ∀ X, Consistent L kernel asms mem0 X → ¬ HasUb X)
    (hP : ∀ X, Consistent L kernel asms mem0 X →
      ∃ P : Sr.SrPkg L kernel asms mem0 X, (∀ c, P.cm c = Hs.cmOf L X c) ∧
        (∀ c, P.p0 c = Hs.p0Of L c) ∧ ∀ c h, Hs.MmaOf L c h → P.Mma c h)
    (hlag : CmLag T Q L mem0) (hpar0 : MmaParity Q L mem0) (hp0 : P0Lag T Q L mem0)
    (hw : WorkerPollsRest T Q L mem0) : PollsRest T Q L mem0 := by
  intro X g s m par before hmax hp hrel hσ hat hst hpar
  have hX := hmax.1
  have hf := hF X hX
  cases s with
  | w s =>
    by_cases hpw : IsPWait s
    · obtain ⟨P, -, hp0e, hmma⟩ := hP X hX
      cases s with
      | mma d P' =>
        have hs : d.site = .pWait := hpw
        have hg := hp.1
        have hgrid : g / L.block < L.grid := by
          unfold Launch.threads at hg
          exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
        have hpm := hpar0 X g d P' m par hX hg hσ hat
        rcases hat with ⟨hs', -, -⟩ | ⟨-, rfl, rfl⟩
        · rw [hs] at hs'; cases hs'
        have hle := mma_p_blocked P hX hgrid (hmma _ _ (mma_lane hf.roleWarp hg hσ))
          (Nat.mod_lt _ (by omega)) hst (by omega)
        rw [hp0e] at hle
        exact blk_of_lags hX hσ (Hs.p0_soft hpre hgrid).1
          (hp0 X g d P' _ _ hX (hub X hX) hg hσ hs (.inr ⟨hs, rfl, rfl⟩) hle)
      | _ => exact hpw.elim
    · exact hw X g s m par before hmax hp hrel hσ hpw hat hst hpar
  | d s =>
    obtain ⟨P, hcm, -⟩ := hP X hX
    have hg := hp.1
    have hgrid : g / L.block < L.grid := by
      unfold Launch.threads at hg
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
    have hcmt : Hs.cmOf L X (g / L.block) < L.threads := by
      have := (P.lane _ hgrid).cm_ok.1
      rwa [hcm] at this
    have hcase : (X.tr (Hs.cmOf L X (g / L.block))).countP (commitsTo m) ≤ okPolls m (X.tr g) ∨
        Descent.Obl L X .commit := by
      rw [← hcm]
      cases s with
      | sm d => exact soft_poll_blocked P hpre hX hf hg hσ hat hst hpar
      | epi d =>
        rcases epi_poll_blocked P hpre hX hf (hR X hX) hg hσ hat hst hpar with h | h
        · exact .inl (by omega)
        · exact .inr h
      | _ => exact hat.elim
    rcases hcase with h | h
    · exact blk_of_lags hX hσ hcmt (hlag X g s m par hX (hub X hX) hg hσ hat h)
    · exact .inl ⟨.commit, .inl rfl, h⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wy
