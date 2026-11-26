-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Coord.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Lemmas.Kernel.Progress.NextEv
public import Lemmas.Protocol.UnitReachBlocker
public import Lemmas.Protocol.NamedBarLedger
public import Lemmas.Protocol.NamedBarSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.ObjNe
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar0
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Time

@[expose] public section

/-! # The index ring's ready side: progress row (`valid_coord_ready`, waits at 264 and 2234)

The consumers of the index ring (warpgroup 0's lanes at pc 264, the TMA lane at pc 2234) wait on
`coordReady j` of their CTA with the parity of their successful polls. Block `r` of slot
`j = r % 4` is filled by the 32 index lanes' arrivals at `crArr r` and awaited by warpgroup 0 at
`crWaitW0 r` and by the TMA lane at `crWaitT r` (`cr_lt_w0`, `cr_lt_t`). The schedule
(`coordReady_lag`, `Sched.LagN`): `τ u = crArr (4 u + j) + 1`, `δ = 0`, producers the index lanes
short of the CTA's uses of the slot (`ix_crEarly`, `ix_crExit`: no election, every lane of warp 7
arrives), consumers the lanes whose next event is one of the two waits (`wg0_crWait`,
`tma_crWait`), `U` the CTA's uses of the slot.

At a blocked poll the final phase is the consumer's successful polls and some index lane has made
no more arrivals (`Unit.Obj.reach_short`, reuse paths `crReach` from the ring, `KRing.reachF`);
that lane is short of the uses the waiter still needs, so `LagN.blk` makes it a blocker
(`coordReady_blk`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- An index lane of CTA `c` is a lane of warp 7 of CTA `c`. -/
theorem idxLane_at (hp : Pre P L m) (c : Nat) (a : Fin 32) :
    MbarRow.warp L (idxLane L c a) = 7 ∧ idxLane L c a / L.block = c := by
  have ha := a.isLt
  simp only [MbarRow.warp, idxLane, tidOf_x_eq hp, hp.block]
  omega

/-- An index lane of a CTA of a lane `g` is a thread of the launch. -/
theorem idxLane_lt (hp : Pre P L m) {g : Nat} (hg : g < L.threads) (a : Fin 32) :
    idxLane L (g / L.block) a < L.threads := by
  have := a.isLt
  have h := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) (g := 224 + a.val)
    (by rw [hp.block]; omega)
  simp only [idxLane]
  omega

/-- The producers of `coordReady j` of CTA `c` while they lag: its index lanes short of the
uses of the slot. -/
def CrProd (P : Params) (L : Launch) (X : Execution) (c : Nat) (j : Fin 4) (y : Nat) : Prop :=
  (∃ a, y = idxLane L c a) ∧
    arrivals (mbarLoc L c (.coordReady j)) (X.tr y) < ringUses 4 j.val (blocksOf P L c)

/-- Lane `g`'s next event is a consumer's wait (pc 264 or 2234) on `coordReady j` of CTA `c`. -/
def CrCons (L : Launch) (m : Mem0) (X : Execution) (c : Nat) (j : Fin 4) (g : Nat) : Prop :=
  ∃ pc p ok acq sc, (pc = 264 ∨ pc = 2234) ∧ Sched.NextEv L kernel Assumptions.all m X g
    ⟨pc, .wait (mbarLoc L c (.coordReady j)) p ok acq sc⟩

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- A consumer's facts: a use below the CTA's uses, no earlier than the ready slot. -/
theorem crCons_wait {c : Nat} {j : Fin 4} {g : Nat} (hg : CrCons L m X c j g) :
    okPolls (mbarLoc L c (.coordReady j)) (X.tr g) < ringUses 4 j.val (blocksOf P L c) ∧
    crArr (4 * okPolls (mbarLoc L c (.coordReady j)) (X.tr g) + j.val) + 1 ≤
      Sched.threadTime (timed P L) X g := by
  obtain ⟨pc, p, ok, acq, sc, hpc, hn⟩ := hg
  rcases hpc with rfl | rfl
  · obtain ⟨-, hlt, hw, -⟩ := wg0_crWait hp hX hFw hn
    have := cr_lt_w0 (4 * okPolls (mbarLoc L c (.coordReady j)) (X.tr g) + j.val)
    exact ⟨hlt, by omega⟩
  · obtain ⟨-, hlt, hw⟩ := tma_crWait hp hX hFw hn
    have := cr_lt_t (4 * okPolls (mbarLoc L c (.coordReady j)) (X.tr g) + j.val)
    exact ⟨hlt, by omega⟩

/-- **The `coordReady` schedule** of slot `j` of CTA `c`. -/
theorem coordReady_lag (hub : ¬ HasUb X) (c : Nat) (j : Fin 4) :
    Sched.LagN (timed P L) X (mbarLoc L c (.coordReady j)) 0 (CrProd P L X c j)
      (CrCons L m X c j) (fun u => crArr (4 * u + j.val) + 1)
      (ringUses 4 j.val (blocksOf P L c)) (arrivesOn (mbarLoc L c (.coordReady j))) := by
  refine ⟨fun a b h => ?_, fun g hg => (crCons_wait hp hX hFw hg).2, fun y hy hyt => ?_,
    fun y k pc hy hx => ?_, fun g hg => (crCons_wait hp hX hFw hg).1⟩
  · simp only [crArr, frame, stride, loopBase, ixOff, ixArr]
    omega
  · obtain ⟨⟨a, rfl⟩, hlt⟩ := hy
    obtain ⟨hw, hc⟩ := idxLane_at hp c a
    have := ix_crEarly hp hX hFw hw hub hyt hc hlt
    simp only [arrivals, Nat.add_zero] at this ⊢
    omega
  · obtain ⟨⟨a, rfl⟩, -⟩ := hy
    obtain ⟨hw, hc⟩ := idxLane_at hp c a
    exact ix_crExit hp hX hFw hw hc hx

variable (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : CoordInputs L X)
include hR hI hB hN

/-- **The reuse paths of `coordReady s`** as consumer `b` polls it (`KRing.reachF`). -/
theorem crReach (c : Nat) (s : Fin 4) (b : Fin 129) :
    Unit.Reach L kernel Assumptions.all X (mbarLoc L c (.coordReady s)) 32 (idxLane L c) 0
      (coordCons L X c b) :=
  fun _ hx _ hj => (coordSlot hp hX hFw hR hI hB hN c s).reachF hX hx b hj

/-- **A consumer's wait on `coordReady s` is blocked** by a lagging index lane, when the object's
records do not fault. The consumer is warpgroup 0's lane (pc 264, warps 0–3) or the TMA lane
(pc 2234). -/
theorem coordReady_blk (hub : ¬ HasUb X) {g q pc : Nat} {s : Fin 4} {sc : MbarScope}
    (hpc : pc = 264 ∧ MbarRow.warp L g < 4 ∨ pc = 2234)
    (hff : ∀ r ∈ X.objects (MbarRow.loc L g (.coordReady s)), r.fault = none)
    (hq : q = okPolls (MbarRow.loc L g (.coordReady s)) (X.tr g) % 2)
    (hrel : Step.Released L X g)
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨pc, .wait (MbarRow.loc L g (.coordReady s)) q false true sc⟩) :
    Sched.WaitBlk (timed P L) X g (MbarRow.loc L g (.coordReady s)) q := by
  simp only [MbarRow.loc] at hff hq hn ⊢
  have hg := hn.lt
  -- the waiter is a consumer of its CTA's ring, past barrier 0
  have hcons : (∃ b, g = coordCons L X (g / L.block) b) ∧ 0 < (X.tr g).countP isBar0 := by
    rcases hpc with ⟨rfl, hw⟩ | rfl
    · obtain ⟨-, -, -, hb0⟩ := wg0_crWait hp hX hFw hn
      refine ⟨⟨⟨g % 384, by simp only [MbarRow.warp, tidOf_x_eq hp] at hw; omega⟩, ?_⟩, hb0⟩
      simp only [MbarRow.warp, tidOf_x_eq hp] at hw
      simp only [coordCons, hp.block, show g % 384 < 128 from by omega, ↓reduceIte]
      omega
    · obtain ⟨⟨k, e, he, hu, hon⟩, -, -⟩ := tma_crWait hp hX hFw hn
      have hb0 := bar0_before hp hX hFw he hu (by have := hon.2; omega)
      refine ⟨⟨⟨128, by omega⟩, ?_⟩, ?_⟩
      · simp only [coordCons, show ¬ (128 < 128) from by omega, ↓reduceIte]
        exact tma_thread_on hN.tmaOne he hu hon
      · exact Nat.lt_of_lt_of_le hb0 (List.take_sublist k _).countP_le
  obtain ⟨⟨b, hb⟩, hb0⟩ := hcons
  have hb0' : 0 < ((X.tr g).take (X.tr g).length).countP isBar0 := by
    rw [List.take_length]
    exact hb0
  have O := coordReady_obj hp hX hFw hR hI hB (g / L.block) s
  obtain ⟨st, hst⟩ := Unit.final_of_init hX O.init O.noInval
    (objects_ne hp hX hFw hI hg (.inr ⟨rfl, hrel⟩) hb0' (.coordReady s))
  refine ⟨st, hst, fun hpar => ?_⟩
  rw [hq, Nat.mod_mod] at hpar
  have hpar' : st.phase % 2 = (okPolls (mbarLoc L (g / L.block) (.coordReady s))
      (X.tr (coordCons L X (g / L.block) b)) + 0) % 2 := by
    rw [← hb]
    exact hpar
  obtain ⟨hph, a, ha⟩ := O.reach_short hX (crReach hp hX hFw hR hI hB hN (g / L.block) s b) hff
    hst (Nat.zero_le _) hpar'
  rw [← hb] at hph
  have hne : X.tr g ≠ [] := by
    intro h
    simp [h] at hb0
  have hcy := (idxLane_at hp (g / L.block) a).2
  exact (coordReady_lag hp hX hFw hub (g / L.block) s).blk hX hub hg
    ⟨_, _, _, _, _, (by rcases hpc with ⟨h, -⟩ | h <;> simp [h]), hn⟩ hne
    ⟨⟨a, rfl⟩, by have := (crCons_wait hp hX hFw ⟨_, _, _, _, _, (by rcases hpc with ⟨h, -⟩ | h <;>
      simp [h]), hn⟩).1; omega⟩ (idxLane_lt hp hg a) (by rw [hcy])
    (by simp only [arrivals] at ha; omega)

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
