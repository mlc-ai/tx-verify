-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Close.Obj
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.ObjNe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
public import Lemmas.Kernel.Progress.NextEv
public import Lemmas.Protocol.UnitReachBlocker
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar0
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Bar

@[expose] public section

/-! # The last store's barrier: progress row (`last_store_done`, wait at 2209)

The TMA lane waits once, at pc 2209, on `lastStoreDone` of its CTA with parity 0. Warpgroup 0's
128 lanes arrive on it once each at pc 200 (`wg0_lastArr`: an arrival is a lane's first), so the
object never completes a second phase and its reuse paths are vacuous (`lastReach`). On the glued
table (`Lib/Slots.lean`) a warpgroup-0 lane that has not arrived is at most at `lastArr + 1`
(`wg0_lastEarly`), one that exited has arrived (`wg0_lastExit`), and the TMA lane at its wait is
at `lastWait` with no earlier successful poll (`tma_lastWait`): the schedule `lastStore_lag`
(`Sched.LagN`, `τ _ = lastWait`, `δ = 0`, `U = 1`). At a blocked poll the object is in phase 0
and some warpgroup-0 lane has not arrived (`Unit.Obj.reach_short`); it lags the TMA lane
(`lastStore_blk`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A warpgroup-0 lane of CTA `c` is of warps 0–3 and of CTA `c`. -/
theorem wg0Lane_at (hp : Pre P L m) (c : Nat) (b : Fin 128) :
    MbarRow.warp L (wg0Lane L c b) < 4 ∧ wg0Lane L c b / L.block = c := by
  have hb := b.isLt
  simp only [MbarRow.warp, wg0Lane, tidOf_x_eq hp, hp.block]
  omega

/-- The producers of `lastStoreDone` of CTA `c` while they lag: its warpgroup-0 lanes that have
not arrived. -/
def LastProd (L : Launch) (X : Execution) (c : Nat) (y : Nat) : Prop :=
  (∃ b, y = wg0Lane L c b) ∧ arrivals (mbarLoc L c .lastStoreDone) (X.tr y) = 0

/-- Lane `g`'s next event is the wait at 2209 on `lastStoreDone` of CTA `c`. -/
def LastCons (L : Launch) (m : Mem0) (X : Execution) (c : Nat) (g : Nat) : Prop :=
  ∃ p ok acq sc, Sched.NextEv L kernel Assumptions.all m X g
    ⟨2209, .wait (mbarLoc L c .lastStoreDone) p ok acq sc⟩

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **The `lastStoreDone` schedule** of CTA `c`. -/
theorem lastStore_lag (hub : ¬ HasUb X) (c : Nat) :
    Sched.LagN (timed P L) X (mbarLoc L c .lastStoreDone) 0 (LastProd L X c) (LastCons L m X c)
      (fun _ => lastWait) 1 (arrivesOn (mbarLoc L c .lastStoreDone)) := by
  refine ⟨fun _ _ _ => Nat.le_refl _, fun g hg => ?_, fun y hy hyt => ?_,
    fun y k pc hy hx => ?_, fun g hg => ?_⟩
  · obtain ⟨p, ok, acq, sc, hn⟩ := hg
    exact (tma_lastWait hp hX hFw hn).2.2
  · obtain ⟨⟨b, rfl⟩, h0⟩ := hy
    obtain ⟨hw, hc⟩ := wg0Lane_at hp c b
    have h := wg0_lastEarly hp hX hFw hub hw hyt (by rw [MbarRow.loc, hc]; exact h0)
    have h1 : lastArr + 1 < lastWait := by decide
    omega
  · obtain ⟨⟨b, rfl⟩, -⟩ := hy
    obtain ⟨hw, hc⟩ := wg0Lane_at hp c b
    have h := wg0_lastExit hp hX hFw hw hx (startup_exit hp hX hFw hx)
    rw [MbarRow.loc, hc] at h
    exact h
  · obtain ⟨p, ok, acq, sc, hn⟩ := hg
    exact (tma_lastWait hp hX hFw hn).2.1

/-- **No reuse of `lastStoreDone`**: its reuse paths as lane `g` polls it are vacuous, every
warpgroup-0 arrival being the lane's first (`wg0_lastArr`). -/
theorem lastReach (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (c g : Nat) :
    Unit.Reach L kernel Assumptions.all X (mbarLoc L c .lastStoreDone) 128 (wg0Lane L c) 0 g := by
  intro x hx j hj
  obtain ⟨-, ⟨pc, sc, he⟩, hcnt⟩ := (lastStore_obj hp hX hFw hR hI hB c).S_rec hx
  have h0 : arrivals (mbarLoc L c .lastStoreDone) ((X.tr (wg0Lane L c x.1)).take
      (Unit.it X (mbarLoc L c .lastStoreDone) (wg0Lane L c) x.1 x.2).2) = 0 :=
    wg0_lastArr hp hX hFw x.1.isLt he
  omega

/-- **The TMA lane's wait on `lastStoreDone` is blocked** by a warpgroup-0 lane that has not
arrived, when the object's records do not fault. -/
theorem lastStore_blk (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hub : ¬ HasUb X) {g : Nat} {sc : MbarScope}
    (hff : ∀ r ∈ X.objects (MbarRow.loc L g .lastStoreDone), r.fault = none)
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨2209, .wait (MbarRow.loc L g .lastStoreDone) 0 false true sc⟩) :
    Sched.WaitBlk (timed P L) X g (MbarRow.loc L g .lastStoreDone) 0 := by
  simp only [MbarRow.loc] at hff hn ⊢
  obtain ⟨⟨k, e, he, hu, hon⟩, hlt, -⟩ := tma_lastWait hp hX hFw hn
  have hg := hn.lt
  have hb0 := bar0_before hp hX hFw he hu (by have := hon.2; omega)
  have O := lastStore_obj hp hX hFw hR hI hB (g / L.block)
  obtain ⟨st, hst⟩ := Unit.final_of_init hX O.init O.noInval
    (objects_ne hp hX hFw hI hg (.inl (List.getElem?_eq_some_iff.mp he).1) hb0 .lastStoreDone)
  refine ⟨st, hst, fun hpar => ?_⟩
  obtain ⟨hph, b, hb⟩ := O.reach_short hX (lastReach hp hX hFw hR hI hB _ g) hff hst
    (Nat.zero_le _) (by omega)
  obtain ⟨hw, hc⟩ := wg0Lane_at hp (g / L.block) b
  have hyl : wg0Lane L (g / L.block) b < L.threads := by
    have := b.isLt
    have h := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) (g := b.val)
      (by rw [hp.block]; omega)
    simp only [wg0Lane]
    omega
  have hne : X.tr g ≠ [] := by
    intro h
    simp [Execution.get, h] at he
  exact (lastStore_lag hp hX hFw hub (g / L.block)).blk hX hub hg ⟨_, _, _, _, hn⟩ hne
    ⟨⟨b, rfl⟩, by omega⟩ hyl (by rw [hc]) (by simp only [arrivals] at hb; omega)

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
