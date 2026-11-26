-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Score.Obj
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticPoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
public import Lemmas.Protocol.KindRingOff
public import Lemmas.Protocol.UnitCounted
public import Lemmas.Protocol.UnitReachBlocker
public import Lemmas.Protocol.ReachJoint
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Count

@[expose] public section

/-! # The score ring: its reuse paths

Slot `s` of the score ring of CTA `c` is a slot of a one-CTA ring of kinds whose producer polls
the empty barrier with offset 0 (`MbarRing.KRingOff … 0`, library pattern `KindRingOff`): full
barrier `qkDone s` (`qkDone_obj`, a commit object: the notification of the MMA lane's commit),
empty barrier `soReady s` (`soReady_obj`, one notification per warpgroup-0 lane: its unit
arrival), one producer (the CTA's MMA lane) and 128 consumers (the warpgroup-0 lanes). The MMA
lane's commit of use `u` to `qkDone s` follows `u` successful polls of `soReady s` (`mma_qkArr`),
a warpgroup-0 lane's arrival of use `u` on `soReady s` follows `u + 1` successful polls of
`qkDone s` (`wg0_soArr`). Then `soReach`: the reuse paths of `soReady s` as the MMA lane polls
it (`KRingOff.reachE`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy

noncomputable section
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

/-- **Slot `s` of the score ring of CTA `c`** as a ring of kinds with empty-side offset 0. -/
def scoreSlot (c : Nat) (s : Fin 2) : KRingOff L kernel X 1 128 1 0 :=
  have N := qkDone_obj hp hX hFw hR hI hB (mmaOne hp hX hFw) c s
  have O := soReady_obj hp hX hFw hR hI hB c s
  { F := mbarLoc L c (.qkDone s)
    E := mbarLoc L c (.soReady s)
    prod := fun _ => mmaLane L X c
    cons := wg0Lane L c
    ownF := fun _ => 0
    opF := fun _ t => (mmaLane L X c, Notify.cm X (mmaLane L X c) (mbarLoc L c (.qkDone s)) t)
    itF := fun _ t => Notify.it X (mbarLoc L c (.qkDone s)) (mmaLane L X c)
      (mbarLoc L c (.qkDone s)) t
    cm := Unit.it X (mbarLoc L c (.soReady s)) (wg0Lane L c)
    note := Unit.itRef X (mbarLoc L c (.soReady s)) (wg0Lane L c)
    SF := Notify.S X (mbarLoc L c (.qkDone s)) (mmaLane L X c) (mbarLoc L c (.qkDone s))
    SE := Unit.S X (mbarLoc L c (.soReady s)) (wg0Lane L c)
    dE_le := Nat.zero_le _
    cover := fun _ => ⟨0, Subsingleton.elim _ _⟩
    cF :=
      { record := fun x hx => by
          obtain ⟨⟨k, r, hk, hid, hf, ha⟩, -⟩ := N.S_rec hx
          exact ⟨k, r, hk, hid, hf, by rw [ha]; trivial⟩
        init := ⟨1, N.init⟩
        noInval := N.noInval }
    cE := O.counted
    spins := fun _ _ _ _ _ _ he => poll_canonical hX he
    parF := fun _ _ _ _ _ _ he => N.parity he
    parE := fun _ _ _ _ _ _ he => O.parity he
    fullF := fun _ _ hj => N.card_phase hX (Nat.zero_le _) hj
    fullE := fun _ _ hn hj => O.card_phase hX hn hj
    polF := fun x hx => by
      obtain ⟨-, pc, sp, hget, hb, -, hcnt⟩ := N.S_rec hx
      refine ⟨_, rfl, len_of_get hget, ?_⟩
      have h1 := mma_qkArr hp hX hFw (mma_commit_warp hp hX hFw hget) hget hb
      rw [hcnt] at h1
      omega
    polE := fun _ hy => O.pol (fun {a} _ _ _ h => wg0_soArr hp hX hFw a.isLt h) hy
    issueF := fun x hx => by
      obtain ⟨⟨k, r, hk, hid, -, -⟩, pc, sp, hget, -⟩ := N.S_rec hx
      obtain ⟨-, -, -, -, hr⟩ := Reach.notify_rec hX (List.mem_of_getElem? hk) hid
      exact .single (Reach.commit_notify hget hr)
    issueE := fun _ _ => .refl }

/-- **The reuse paths of `soReady s`** as the MMA lane polls it: a warpgroup-0 lane's arrival of
use `t` follows the MMA lane's successful polls for the uses before `t`. -/
theorem soReach (c : Nat) (s : Fin 2) :
    Unit.Reach L kernel Assumptions.all X (mbarLoc L c (.soReady s)) 128 (wg0Lane L c) 0
      (mmaLane L X c) :=
  fun _ hx _ hj => (scoreSlot hp hX hFw hR hI hB c s).reachE hX hx 0 (Nat.zero_le _) hj

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
