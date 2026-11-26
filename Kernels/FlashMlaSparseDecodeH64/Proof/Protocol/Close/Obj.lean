-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.InitFirst
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MbarUse.UnitObj
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch

@[expose] public section

/-! # The last store's barrier as an object

From `mbar_use` and the rows only. `lastStoreDone` of CTA `c` is named by the startup's
initialization (count 128), the unit arrivals of warpgroup 0's 128 lanes at pc 200 (`wg0Lane L c
b`, threads 0–127 of the CTA) and the TMA lane's first poll at pc 2209 with parity 0
(`lastStore_use`). It is a `MbarRing.Unit.Obj` of the warpgroup-0 lanes polled with offset 0
(`lastStore_obj`; library pattern `UnitObject`).

**Observe / Lag** (not here): the TMA lane's one poll observes phase 0, which holds every lane's
first arrival (`Unit.Obj.card_phase` and `phase_all`, no reuse: one arrival per lane, an input of
lane W1 like `QueryTime`'s counts); its Lag needs the TMA lane's waiter time against
warpgroup 0's time to pc 200. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- Lane `b` of warpgroup 0 of CTA `c`. -/
def wg0Lane (L : Launch) (c : Nat) (b : Fin 128) : Nat := c * L.block + b.val

theorem wg0Lane_inj (L : Launch) (c : Nat) : Function.Injective (wg0Lane L c) := by
  intro a b h
  simp only [wg0Lane] at h
  exact Fin.ext (by omega)

/-- **A warpgroup-0 lane is a lane `wg0Lane` of its CTA.** -/
theorem wg0_lane (hp : Pre P L m) {g pc : Nat} (hw : MbarRow.Wg0At L g pc) :
    ∃ b, g = wg0Lane L (g / L.block) b := by
  obtain ⟨h4, -, -⟩ := hw
  simp only [MbarRow.warp, tidOf_x_eq hp] at h4
  refine ⟨⟨g % 384, by omega⟩, ?_⟩
  simp only [wg0Lane, hp.block]
  omega

/-- **The uses of `lastStoreDone` of CTA `c`**: the initialization, the TMA lane's first poll
with parity 0, or a warpgroup-0 lane's unit arrival. -/
theorem lastStore_use (hR : MbarRows P L X) {c g k : Nat} {e : Event}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hm : Frame.MbarOf e (mbarLoc L c .lastStoreDone)) :
    (∃ n, e.kind = .mbInit (mbarLoc L c .lastStoreDone) n) ∨
      (MbarRow.TmaAt L g e.pc ∧ g / L.block = c ∧ MbarRow.Wait e (mbarLoc L c .lastStoreDone) 0 ∧
        okPolls (mbarLoc L c .lastStoreDone) ((X.tr g).take k) = 0) ∨
      MbarRow.Wg0At L g e.pc ∧ g / L.block = c ∧
        MbarRow.Arrive e (mbarLoc L c .lastStoreDone) 0 := by
  rcases mbar_use hR hg he hm with ⟨-, ⟨-, j, -, -, hk⟩⟩ | ⟨hw, h⟩ | ⟨-, h⟩ | ⟨hw, h⟩ |
    ⟨-, h⟩ | ⟨-, h⟩
  · exact .inl ⟨_, hk⟩
  · cases h with
    | coordReady _ hl _ | qkDone _ hl _ | coordFree _ hl _ | soReady _ hl _ | svDone _ hl _ =>
      nomatch (fam_eq hl).2
    | lastStore _ hl hk => exact .inr (.inr ⟨hw, (fam_eq hl).1.symm, hk⟩)
  · cases h with
    | qLoad _ hl _ | qArrive _ hl _ | qWait _ hl _ _ | qCommit _ hl _ | qCopyWait _ hl _ _
    | kvWait _ hl _ | qkCommit _ hl _ | soWait _ hl _ | svCommit _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qWait _ hl _ _ | coordWait _ hl _ | freeWait _ hl _ | rawLoad _ hl _ | rawArrive _ hl _
    | coordFree _ hl _ => nomatch (fam_eq hl).2
    | lastWait _ hl hk h0 => exact .inr (.inl ⟨hw, (fam_eq hl).1.symm, hk, h0⟩)
  · cases h with
    | freeWait _ hl _ | readyArrive _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qWait _ hl _ _ | rawWait _ hl _ | svWait _ hl _ | readyArrive _ hl _ | freeArrive _ hl _ =>
      nomatch (fam_eq hl).2

/-- **`lastStoreDone` of CTA `c` is a unit object of warpgroup 0's 128 lanes**, polled with
offset 0. -/
theorem lastStore_obj (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (c : Nat) : Unit.Obj X (mbarLoc L c .lastStoreDone) 128 (wg0Lane L c) 0 :=
  unit_of_uses hX hR (by decide) (wg0Lane_inj L c) (Nat.zero_le _)
    (initFirst hp hX hFw hR hI hB c .lastStoreDone) fun he hm => by
    rcases lastStore_use hR (Frame.lt_of_get hX he) he hm with hk | ⟨-, -, hk, h0⟩ |
      ⟨hw, hc, hk⟩
    · exact .inl hk
    · exact .inr (.inl ⟨_, hk, by rw [h0]⟩)
    · obtain ⟨b, hb⟩ := wg0_lane hp hw
      rw [hc] at hb
      exact .inr (.inr ⟨⟨b, hb⟩, hk⟩)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
