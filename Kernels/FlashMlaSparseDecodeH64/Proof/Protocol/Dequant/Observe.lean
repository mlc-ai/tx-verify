-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Count
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticPoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.Obj
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Score.Obj
public import Lemmas.Protocol.KindRing
public import Lemmas.Protocol.ReachJoint
public import Lemmas.Protocol.UnitCounted
public import Lemmas.Protocol.UnitReachBlocker

@[expose] public section

/-! # The dequantized buffer's ring: what its waits observe

Slot `s` of the dequantized buffer of CTA `c` is a slot of a one-CTA ring of kinds
(`MbarRing.KRing`, library pattern `KindRing`, as the K/V ring of `TmlFa4Fwd`): full barrier
`dequantReady s` (`dequantReady_obj`, 128 kinds: the dequant lanes' unit arrivals), empty barrier
`svDone s` (`svDone_obj`, a commit object: the notification of the MMA lane's commit), 128
producers (the dequant lanes, `deqLane`) and one consumer (the CTA's MMA lane). A dequant lane's
arrival of use `u` follows `u + 1` successful polls of `svDone s` (`dequant_readyArr`, proved by
lane D), the MMA lane's commit of use `u` follows `u + 1` successful polls of `dequantReady s`
(`DequantInputs.mmaSvArr`, lane B). Then:

* `dqReach`: the reuse paths of `dequantReady s` as the MMA lane polls it (`KRing.reachF`);
* `dequantReady_short`: when the final phase has the parity of the MMA lane's next poll, it is
  the lane's successful polls, and some dequant lane has made no more arrivals than that, when no
  record of the object faults (`Unit.Obj.reach_short`). -/

/-! # The dequantized buffer's ready barrier as an object

From `mbar_use` and the rows only. `dequantReady s` of CTA `c` is named by the startup's
initialization (count 128), the 128 dequant lanes' unit arrivals at pc 3597 and the MMA lane's
polls at pc 2012 with the parity of its earlier successful polls (`dequantReady_use`). It is a
`MbarRing.Unit.Obj` of the dequant lanes `deqLane L c b`, polled with offset 0
(`dequantReady_obj`; library pattern `UnitObject`).

**Observe / Lag** (not here): the reuse of slot `s` is gated not by a barrier of its own but by
`svDone s` (the dequant lanes wait at 2684 for the PV GEMM that read the buffer), so its observes
relation is a `Unit.Gate` (library `UnitGate`) whose `gate` field is the path from the MMA lane's
poll of use `u` through its commit to `svDone s` to the dequant lanes' poll at 2684 and their
arrival of use `u + 1`: inputs of lanes B (the MMA lane's commit to `svDone` of use `u` follows its
poll of `dequantReady` of use `u`) and D (the arrival of use `u + 1` follows the poll of `svDone`
of use `u`), with `svDone_obj`'s observes. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The uses of `dequantReady s` of CTA `c`**: the initialization, the MMA lane's poll with the
parity of its earlier successful polls, or a dequant lane's unit arrival. -/
theorem dequantReady_use (hR : MbarRows P L X) {c g k : Nat} {s : Fin 2} {e : Event}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hm : Frame.MbarOf e (mbarLoc L c (.dequantReady s))) :
    (∃ n, e.kind = .mbInit (mbarLoc L c (.dequantReady s)) n) ∨
      (MmaOn L g e.pc ∧ g / L.block = c ∧ MbarRow.Wait e (mbarLoc L c (.dequantReady s))
        (okPolls (mbarLoc L c (.dequantReady s)) ((X.tr g).take k) % 2)) ∨
      MbarRow.DequantAt L g e.pc ∧ g / L.block = c ∧
        MbarRow.Arrive e (mbarLoc L c (.dequantReady s)) 0 := by
  rcases mbar_use hR hg he hm with ⟨-, ⟨-, j, -, -, hk⟩⟩ | ⟨-, h⟩ | ⟨hw, h⟩ | ⟨-, h⟩ |
    ⟨-, h⟩ | ⟨hw, h⟩
  · exact .inl ⟨_, hk⟩
  · cases h with
    | lastStore _ hl _ | coordReady _ hl _ | qkDone _ hl _ | coordFree _ hl _ | soReady _ hl _
    | svDone _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qLoad _ hl _ | qArrive _ hl _ | qWait _ hl _ _ | qCommit _ hl _ | qCopyWait _ hl _ _
    | qkCommit _ hl _ | soWait _ hl _ | svCommit _ hl _ => nomatch (fam_eq hl).2
    | kvWait hpc hl hk => exact .inr (.inl ⟨⟨hw, by omega⟩, (fam_eq hl).1.symm, hk⟩)
  · cases h with
    | qWait _ hl _ _ | lastWait _ hl _ _ | coordWait _ hl _ | freeWait _ hl _ | rawLoad _ hl _
    | rawArrive _ hl _ | coordFree _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | freeWait _ hl _ | readyArrive _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qWait _ hl _ _ | rawWait _ hl _ | svWait _ hl _ | freeArrive _ hl _ =>
      nomatch (fam_eq hl).2
    | readyArrive _ hl hk => exact .inr (.inr ⟨hw, (fam_eq hl).1.symm, hk⟩)

/-- **`dequantReady s` of CTA `c` is a unit object of the CTA's 128 dequant lanes**, polled with
offset 0. -/
theorem dequantReady_obj (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (c : Nat) (s : Fin 2) :
    Unit.Obj X (mbarLoc L c (.dequantReady s)) 128 (deqLane L c) 0 :=
  unit_of_uses hX hR (by decide) (deqLane_inj L c) (Nat.zero_le _)
    (initFirst hp hX hFw hR hI hB c (.dequantReady s)) fun he hm => by
    rcases dequantReady_use hR (Frame.lt_of_get hX he) he hm with hk | ⟨-, -, hk⟩ |
      ⟨hw, hc, hk⟩
    · exact .inl hk
    · exact .inr (.inl ⟨_, hk, by omega⟩)
    · obtain ⟨b, hb⟩ := deq_lane hp hw
      rw [hc] at hb
      exact .inr (.inr ⟨⟨b, hb⟩, hk⟩)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy

noncomputable section
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The dequantized buffer ring's input** (lane B): the MMA lane's commit to `svDone s`
follows more successful polls of `dequantReady s` than its earlier commits to `svDone s`. -/
structure DequantInputs (L : Launch) (X : Execution) : Prop where
  /-- (lane B) The MMA lane's commit of use `u` to `svDone s` follows `u + 1` successful polls
  of `dequantReady s`. -/
  mmaSvArr : ∀ {c i pc : Nat} {s : Fin 2} {sp : TcCommit.Spec},
    X.get (mmaLane L X c, i) = some ⟨pc, .tc (.commit sp)⟩ →
    sp.mbar = mbarLoc L c (.svDone s) →
    ((X.tr (mmaLane L X c)).take i).countP (commitsTo (mbarLoc L c (.svDone s))) <
      okPolls (mbarLoc L c (.dequantReady s)) ((X.tr (mmaLane L X c)).take i)

/-- A dequant lane is in warps 8 to 11. -/
theorem deqLane_warp (hp : Pre P L m) (c : Nat) (a : Fin 128) :
    8 ≤ MbarRow.warp L (deqLane L c a) ∧ MbarRow.warp L (deqLane L c a) < 12 := by
  have ha := a.isLt
  simp only [MbarRow.warp, deqLane, tidOf_x_eq hp, hp.block]
  omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
include hp hX hFw hR hI hB hN

/-- **Slot `s` of the dequantized buffer ring of CTA `c`** as a ring of kinds. -/
def dqSlot (c : Nat) (s : Fin 2) : KRing L kernel X 128 1 128 :=
  have O := dequantReady_obj hp hX hFw hR hI hB c s
  have N := svDone_obj hp hX hFw hR hI hB (mmaOne hp hX hFw) c s
  { F := mbarLoc L c (.dequantReady s)
    E := mbarLoc L c (.svDone s)
    prod := deqLane L c
    cons := fun _ => mmaLane L X c
    ownF := id
    opF := Unit.it X (mbarLoc L c (.dequantReady s)) (deqLane L c)
    itF := Unit.itRef X (mbarLoc L c (.dequantReady s)) (deqLane L c)
    cm := fun _ t => (mmaLane L X c,
      Notify.cm X (mmaLane L X c) (mbarLoc L c (.svDone s)) t)
    note := fun _ t => Notify.it X (mbarLoc L c (.svDone s)) (mmaLane L X c)
      (mbarLoc L c (.svDone s)) t
    SF := Unit.S X (mbarLoc L c (.dequantReady s)) (deqLane L c)
    SE := Notify.S X (mbarLoc L c (.svDone s)) (mmaLane L X c) (mbarLoc L c (.svDone s))
    cover := fun a => ⟨a, rfl⟩
    cF := O.counted
    cE :=
      { record := fun x hx => by
          obtain ⟨⟨k, r, hk, hid, hf, ha⟩, -⟩ := N.S_rec hx
          exact ⟨k, r, hk, hid, hf, by rw [ha]; trivial⟩
        init := ⟨1, N.init⟩
        noInval := N.noInval }
    spins := fun _ _ _ _ _ _ he => poll_canonical hX he
    parF := fun _ _ _ _ _ _ he => O.parity he
    parE := fun a _ _ _ _ _ he => N.parityOf (by have := deqLane_warp hp c a; omega) he
    fullF := fun _ _ hj => O.card_phase hX (Nat.zero_le _) hj
    fullE := fun a _ hn hj => N.card_phase hX hn hj (by have := deqLane_warp hp c a; omega)
    polF := fun _ hx => O.pol (fun h => dequant_readyArr hp hX hFw (deqLane_warp hp c _) h) hx
    polE := fun y hy => by
      obtain ⟨-, pc, sp, hget, hb, -, hcnt⟩ := N.S_rec hy
      refine ⟨_, rfl, len_of_get hget, ?_⟩
      have h1 := hN.mmaSvArr hget hb
      rw [hcnt] at h1
      exact h1
    issueF := fun _ _ => .refl
    issueE := fun y hy => by
      obtain ⟨⟨k, r, hk, hid, -, -⟩, pc, sp, hget, -⟩ := N.S_rec hy
      obtain ⟨-, -, -, -, hr⟩ := Reach.notify_rec hX (List.mem_of_getElem? hk) hid
      exact .single (Reach.commit_notify hget hr) }

/-- **The reuse paths of `dequantReady s`** as the MMA lane polls it: a dequant lane's arrival of
use `t` follows the MMA lane's successful polls for the uses before `t`. -/
theorem dqReach (c : Nat) (s : Fin 2) :
    Unit.Reach L kernel Assumptions.all X (mbarLoc L c (.dequantReady s)) 128 (deqLane L c) 0
      (mmaLane L X c) :=
  fun _ hx _ hj => (dqSlot hp hX hFw hR hI hB hN c s).reachF hX hx 0 hj

/-- **A blocked MMA lane at `dequantReady s` is one use ahead and some dequant lane is short**:
when the final phase has the parity of the lane's successful polls, it is that count, and a dequant
lane has made no more arrivals than it, when no record of the object faults. -/
theorem dequantReady_short (c : Nat) (s : Fin 2)
    (hff : ∀ r ∈ X.objects (mbarLoc L c (.dequantReady s)), r.fault = none)
    {st : MBarrier.State}
    (hst : MBarrier.stateBefore (X.objects (mbarLoc L c (.dequantReady s)))
      (X.objects (mbarLoc L c (.dequantReady s))).length = some st)
    (hpar : st.phase % 2 =
      okPolls (mbarLoc L c (.dequantReady s)) (X.tr (mmaLane L X c)) % 2) :
    st.phase = okPolls (mbarLoc L c (.dequantReady s)) (X.tr (mmaLane L X c)) ∧
      ∃ a, arrivals (mbarLoc L c (.dequantReady s)) (X.tr (deqLane L c a)) ≤ st.phase := by
  obtain ⟨h1, h2⟩ := (dequantReady_obj hp hX hFw hR hI hB c s).reach_short hX
    (dqReach hp hX hFw hR hI hB hN c s) hff hst (Nat.zero_le _) (by simpa using hpar)
  exact ⟨by simpa using h1, h2⟩

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
