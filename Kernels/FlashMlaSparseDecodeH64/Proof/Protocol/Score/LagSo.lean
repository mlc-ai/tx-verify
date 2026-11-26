-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Score.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Close.Lag
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Lemmas.Flow.Counted
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Bar

@[expose] public section

/-! # The softmax output's progress row (`so_ready`, wait at 2107)

The MMA lane waits at pc 2107 on `soReady j` of its CTA with the parity of its successful polls.
Block `r` of slot `j = r % 2` is filled by the 128 warpgroup-0 lanes' arrivals at `soArr r` and
awaited by the MMA lane at `soWait r = soArr r + 10`. The schedule (`soReady_lag`,
`Sched.LagN`): `τ u = soArr (2 u + j) + 2`, `δ = 0` (a warpgroup-0 lane short of a use is at most
one past the arrival's slot, `wg0_soEarly`: its last state may be the arrival site itself),
producers the warpgroup-0 lanes short of the CTA's uses of the slot (`wg0_soEarly`,
`wg0_soExit`), consumers the lanes whose next event is the wait (`mma_soWait`), `U` the CTA's uses
of the slot.

**The reuse paths** (`soReach`, `Protocol/Score/Observe.lean`): the arrival of use `t` of a
warpgroup-0 lane on `soReady s` follows the MMA lane's successful polls of `soReady s` for the uses
before `t`, from the score ring (full `qkDone s`, commits of the MMA lane; empty `soReady s`,
arrivals of warpgroup 0) as a `KRingOff` with empty-side offset 0. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The producers of `soReady j` of CTA `c` while they lag: its warpgroup-0 lanes short of the
uses of the slot. -/
def SoProd (P : Params) (L : Launch) (X : Execution) (c : Nat) (j : Fin 2) (y : Nat) : Prop :=
  (∃ b, y = wg0Lane L c b) ∧
    arrivals (mbarLoc L c (.soReady j)) (X.tr y) < ringUses 2 j.val (blocksOf P L c)

/-- Lane `g`'s next event is the wait at 2107 on `soReady j` of CTA `c`. -/
def SoCons (L : Launch) (m : Mem0) (X : Execution) (c : Nat) (j : Fin 2) (g : Nat) : Prop :=
  ∃ p ok acq sc, Sched.NextEv L kernel Assumptions.all m X g
    ⟨2107, .wait (mbarLoc L c (.soReady j)) p ok acq sc⟩

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **The `soReady` schedule** of slot `j` of CTA `c`. -/
theorem soReady_lag (hub : ¬ HasUb X) (c : Nat) (j : Fin 2) :
    Sched.LagN (timed P L) X (mbarLoc L c (.soReady j)) 0 (SoProd P L X c j) (SoCons L m X c j)
      (fun u => soArr (2 * u + j.val) + 2) (ringUses 2 j.val (blocksOf P L c))
      (arrivesOn (mbarLoc L c (.soReady j))) := by
  refine ⟨fun a b h => ?_, fun g hg => ?_, fun y hy hyt => ?_, fun y k pc hy hx => ?_,
    fun g hg => ?_⟩
  · simp only [soArr, frame, stride, loopBase, wg0Off, w0ArrS]
    omega
  · obtain ⟨p, ok, acq, sc, hn⟩ := hg
    obtain ⟨-, -, hw⟩ := mma_soWait hp hX hFw hn
    simp only [soArr, soWait, frame, stride, loopBase, wg0Off, w0ArrS, mmaOff, mmaSo] at hw ⊢
    omega
  · obtain ⟨⟨b, rfl⟩, hlt⟩ := hy
    obtain ⟨hw, hc⟩ := wg0Lane_at hp c b
    have := wg0_soEarly hp hX hFw hub hw hyt j (by rw [MbarRow.loc, hc]; exact hlt)
    rw [MbarRow.loc, hc] at this
    simp only [arrivals, Nat.add_zero] at this ⊢
    omega
  · obtain ⟨⟨b, rfl⟩, -⟩ := hy
    obtain ⟨hw, hc⟩ := wg0Lane_at hp c b
    have h := wg0_soExit hp hX hFw hw j hx (startup_exit hp hX hFw hx)
    rw [MbarRow.loc, hc] at h
    exact h
  · obtain ⟨p, ok, acq, sc, hn⟩ := hg
    exact (mma_soWait hp hX hFw hn).2.1

/-- **The MMA lane's wait on `soReady s` is blocked** by a lagging warpgroup-0 lane, when the
object's records do not fault. -/
theorem soReady_blk (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hub : ¬ HasUb X) {g q : Nat} {s : Fin 2} {sc : MbarScope}
    (hff : ∀ r ∈ X.objects (MbarRow.loc L g (.soReady s)), r.fault = none)
    (hq : q = okPolls (MbarRow.loc L g (.soReady s)) (X.tr g) % 2)
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨2107, .wait (MbarRow.loc L g (.soReady s)) q false true sc⟩) :
    Sched.WaitBlk (timed P L) X g (MbarRow.loc L g (.soReady s)) q := by
  simp only [MbarRow.loc] at hff hq hn ⊢
  obtain ⟨⟨k, e, he, hu, hon, hb0⟩, -, -⟩ := mma_soWait hp hX hFw hn
  have hg := hn.lt
  have hy : g = mmaLane L X (g / L.block) := laneOn_eq (mmaOne hp hX hFw) he hu hon
  have O := soReady_obj hp hX hFw hR hI hB (g / L.block) s
  obtain ⟨st, hst⟩ := Unit.final_of_init hX O.init O.noInval
    (objects_ne hp hX hFw hI hg (.inl (List.getElem?_eq_some_iff.mp he).1) hb0 (.soReady s))
  refine ⟨st, hst, fun hpar => ?_⟩
  rw [hq, Nat.mod_mod] at hpar
  have hpar' : st.phase % 2 = (okPolls (mbarLoc L (g / L.block) (.soReady s))
      (X.tr (mmaLane L X (g / L.block))) + 0) % 2 := by
    rw [← hy]
    exact hpar
  obtain ⟨hph, b, hb⟩ := O.reach_short hX (soReach hp hX hFw hR hI hB (g / L.block) s) hff hst
    (Nat.zero_le _) hpar'
  rw [← hy] at hph
  obtain ⟨-, hc⟩ := wg0Lane_at hp (g / L.block) b
  have hyl : wg0Lane L (g / L.block) b < L.threads := by
    have := b.isLt
    have h := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) (g := b.val)
      (by rw [hp.block]; omega)
    simp only [wg0Lane]
    omega
  have hne : X.tr g ≠ [] := by
    intro h
    simp [Execution.get, h] at he
  have hlt := (mma_soWait hp hX hFw hn).2.1
  exact (soReady_lag hp hX hFw hub (g / L.block) s).blk hX hub hg ⟨_, _, _, _, hn⟩ hne
    ⟨⟨b, rfl⟩, by simp only [arrivals] at hb ⊢; omega⟩ hyl (by rw [hc])
    (by simp only [arrivals] at hb; omega)

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
