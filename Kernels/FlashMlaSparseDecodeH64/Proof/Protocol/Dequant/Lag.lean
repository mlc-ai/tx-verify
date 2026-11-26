-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Lemmas.Kernel.Progress.NextEv
public import Lemmas.Flow.Counted
public import Lemmas.Protocol.NamedBarLedger
public import Lemmas.Protocol.NamedBarSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.ObjNe

@[expose] public section

/-! # The dequantized buffer's progress row (`dequant_ready`, wait at 2012)

The MMA lane waits at pc 2012 on `dequantReady j` of its CTA. On the glued time table (stride
128, `Lib/Slots.lean`) block `r` of slot `j = r % 2` is filled by the 128 dequant lanes' arrivals
at `drArr r` and awaited by the MMA lane at `drWait r` (`dr_lt`). The schedule
(`dequantReady_lag`, `Sched.LagN`): `τ u = drArr (2 u + j) + 1`, `δ = 0`, producers the dequant
lanes short of the CTA's uses of the slot, consumers the lanes whose next event is the wait,
`U` the CTA's uses of the slot `ringUses 2 j R`, counted events the arrivals.

At a blocked poll the final phase is the MMA lane's successful polls and some dequant lane has
made no more arrivals (`dequantReady_short`); that lane is short of the uses the waiter still
needs, so `LagN.blk` makes it a blocker (`dequantReady_blk`).

**The time facts (`DrTime`, for the CTA's block count `blocksOf P L c`):** the MMA lane at its
wait has an event after barrier 0 at an MMA pc (so it is its CTA's MMA lane), polls a use below
`ringUses 2 j (blocksOf P L c)`, and is no earlier than `drWait` of the block it waits for
(`mmaWait`, `mma_drWait`); a dequant lane short of its uses of the slot is no later than `drArr`
of its next use (`deqEarly`, `deq_drEarly`), and one that exited has made all of them
(`deqExit`, `deq_drExit`). Discharged at the top (`Top.Inputs.drTime`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The time and count facts of the dequantized buffer ring** for the CTAs' block counts
`blocksOf P L c`. -/
structure DrTime (P : Params) (L : Launch) (m : Mem0) (X : Execution) : Prop where
  /-- The MMA lane at its wait on `dequantReady j` (pc 2012): it has an event at an
  MMA pc after barrier 0, waits for a use below the CTA's uses of the slot, and is no earlier
  than the wait's slot of that use's block. -/
  mmaWait : ∀ {g c p : Nat} {j : Fin 2} {ok acq : Bool} {sc : MbarScope},
    Sched.NextEv L kernel Assumptions.all m X g
      ⟨2012, .wait (mbarLoc L c (.dequantReady j)) p ok acq sc⟩ →
    (∃ k e, X.get (g, k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧ MmaOn L g e.pc ∧
      0 < ((X.tr g).take k).countP isBar0) ∧
    okPolls (mbarLoc L c (.dequantReady j)) (X.tr g) < ringUses 2 j.val (blocksOf P L c) ∧
    drWait (2 * okPolls (mbarLoc L c (.dequantReady j)) (X.tr g) + j.val) ≤
      Sched.threadTime (timed P L) X g
  /-- A dequant lane short of the CTA's uses of slot `j` is no later than the arrival slot of its
  next use, in an execution without undefined behaviour. -/
  deqEarly : ¬ HasUb X → ∀ {c : Nat} {a : Fin 128} {j : Fin 2}, deqLane L c a < L.threads →
    arrivals (mbarLoc L c (.dequantReady j)) (X.tr (deqLane L c a)) <
      ringUses 2 j.val (blocksOf P L c) →
    Sched.threadTime (timed P L) X (deqLane L c a) ≤
      drArr (2 * arrivals (mbarLoc L c (.dequantReady j)) (X.tr (deqLane L c a)) + j.val)
  /-- A dequant lane that exited has made the CTA's uses of slot `j`. -/
  deqExit : ∀ {c k pc : Nat} {a : Fin 128} {j : Fin 2},
    X.get (deqLane L c a, k) = some ⟨pc, .exit⟩ →
    ringUses 2 j.val (blocksOf P L c) ≤
      arrivals (mbarLoc L c (.dequantReady j)) (X.tr (deqLane L c a))

/-- A dequant lane of CTA `c` is in CTA `c`. -/
theorem deqLane_cta (hp : Pre P L m) (c : Nat) (a : Fin 128) : deqLane L c a / L.block = c := by
  have := a.isLt
  simp only [deqLane, hp.block]
  omega

/-- The producers of `dequantReady j` of CTA `c` while they lag: its dequant lanes short of the
uses of the slot. -/
def DrProd (L : Launch) (X : Execution) (R : Nat → Nat) (c : Nat) (j : Fin 2) (y : Nat) :
    Prop :=
  (∃ a, y = deqLane L c a) ∧
    arrivals (mbarLoc L c (.dequantReady j)) (X.tr y) < ringUses 2 j.val (R c)

/-- Lane `g`'s next event is the wait at 2012 on `dequantReady j` of CTA `c`. -/
def DrCons (L : Launch) (m : Mem0) (X : Execution) (c : Nat) (j : Fin 2) (g : Nat) : Prop :=
  ∃ p ok acq sc, Sched.NextEv L kernel Assumptions.all m X g
    ⟨2012, .wait (mbarLoc L c (.dequantReady j)) p ok acq sc⟩

/-- **The `dequantReady` schedule** of slot `j` of CTA `c`. -/
theorem dequantReady_lag (hT : DrTime P L m X) (hub : ¬ HasUb X) (c : Nat) (j : Fin 2) :
    Sched.LagN (timed P L) X (mbarLoc L c (.dequantReady j)) 0 (DrProd L X (blocksOf P L) c j)
      (DrCons L m X c j) (fun u => drArr (2 * u + j.val) + 1) (ringUses 2 j.val (blocksOf P L c))
      (arrivesOn (mbarLoc L c (.dequantReady j))) := by
  refine ⟨fun a b h => ?_, fun g hg => ?_, fun y hy hyt => ?_, fun y k pc hy hx => ?_,
    fun g hg => ?_⟩
  · simp only [drArr, frame, stride, loopBase, deqOff, deqArrD]
    omega
  · obtain ⟨p, ok, acq, sc, hn⟩ := hg
    obtain ⟨-, -, hw⟩ := hT.mmaWait hn
    have := dr_lt (2 * okPolls (mbarLoc L c (.dequantReady j)) (X.tr g) + j.val)
    omega
  · obtain ⟨⟨a, rfl⟩, hlt⟩ := hy
    have := hT.deqEarly hub hyt hlt
    simp only [arrivals, Nat.add_zero] at this ⊢
    omega
  · obtain ⟨⟨a, rfl⟩, -⟩ := hy
    exact hT.deqExit hx
  · obtain ⟨p, ok, acq, sc, hn⟩ := hg
    exact (hT.mmaWait hn).2.1

/-- **The MMA lane's wait on `dequantReady j` is blocked** by a lagging dequant lane, when the
object's records do not fault. -/
theorem dequantReady_blk (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hN : DequantInputs L X) (hT : DrTime P L m X) (hub : ¬ HasUb X)
    {g q : Nat} {j : Fin 2} {sc : MbarScope}
    (hff : ∀ r ∈ X.objects (MbarRow.loc L g (.dequantReady j)), r.fault = none)
    (hq : q = okPolls (MbarRow.loc L g (.dequantReady j)) (X.tr g) % 2)
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨2012, .wait (MbarRow.loc L g (.dequantReady j)) q false true sc⟩) :
    Sched.WaitBlk (timed P L) X g (MbarRow.loc L g (.dequantReady j)) q := by
  simp only [MbarRow.loc] at hff hq hn ⊢
  obtain ⟨⟨k, e, he, hu, hon, hb0⟩, hlt, -⟩ := hT.mmaWait hn
  have hg := hn.lt
  have hy : g = mmaLane L X (g / L.block) := laneOn_eq (mmaOne hp hX hFw) he hu hon
  -- the object has its initialization record, hence a final state
  have hne := objects_ne hp hX hFw hI hg (.inl (List.getElem?_eq_some_iff.mp he).1) hb0
    (.dequantReady j)
  have O := dequantReady_obj hp hX hFw hR hI hB (g / L.block) j
  obtain ⟨st, hst⟩ := Unit.final_of_init hX O.init O.noInval hne
  refine ⟨st, hst, fun hpar => ?_⟩
  rw [hq, Nat.mod_mod] at hpar
  have hpar' : st.phase % 2 = okPolls (mbarLoc L (g / L.block) (.dequantReady j))
      (X.tr (mmaLane L X (g / L.block))) % 2 := by
    rw [← hy]
    exact hpar
  obtain ⟨hph, a, ha⟩ := dequantReady_short hp hX hFw hR hI hB hN (g / L.block) j hff hst hpar'
  rw [← hy] at hph
  have hcy := deqLane_cta hp (g / L.block) a
  have hyl : deqLane L (g / L.block) a < L.threads := by
    have := a.isLt
    have h := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) (g := 256 + a.val)
      (by rw [hp.block]; omega)
    simp only [deqLane]
    omega
  have hne' : X.tr g ≠ [] := by
    intro h
    simp [Execution.get, h] at he
  exact (dequantReady_lag hT hub (g / L.block) j).blk hX hub hg ⟨_, _, _, _, hn⟩ hne'
    ⟨⟨a, rfl⟩, by omega⟩ hyl (by rw [hcy]) (by simp only [arrivals] at ha; omega)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
