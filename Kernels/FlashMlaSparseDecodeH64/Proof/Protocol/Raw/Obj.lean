-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.TmaLane
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.InitFirst
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MbarUse.TmaObj
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MbarUse.UnitObj
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch

@[expose] public section

/-! # The raw KV ring's barriers as objects

From `mbar_use` and the rows only. Slot `s` of the two-slot raw ring of CTA `c` has two barriers:

* `rawReady s` is named by the startup's initialization (count 1), the TMA lane's sixteen gather4
  loads of 2304 bytes (pcs `rawLoadPcs`) and its arrival expecting 36864 bytes (pc 2305), and the
  dequant lanes' polls at pc 2677 with the parity of their earlier successful polls
  (`rawReady_use`). With one TMA lane per CTA (`TmaOne`) it is a `MbarRing.TmaUnits.Obj` of the
  CTA's `tmaThread` with sixteen loads of 2304 bytes (`rawReady_obj`; library pattern `TmaUnits`).
* `rawFree s` is named by the initialization (count 128), the TMA lane's polls at pc 2245 with
  the parity of its earlier successful polls plus one, and the dequant lanes' unit arrivals at pc
  3599 (`rawFree_use`). It is a `MbarRing.Unit.Obj` of the 128 dequant lanes `deqLane L c b`
  (threads 256–383 of the CTA), polled with offset 1 (`rawFree_obj`; library pattern
  `UnitObject`).

The objects' first record is their initialization (`initFirst`), whose inputs `InitRows` and
`Bar0Rows` they take. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- Dequant lane `b` of CTA `c` (warpgroup 2, threads 256–383). -/
def deqLane (L : Launch) (c : Nat) (b : Fin 128) : Nat := c * L.block + 256 + b.val

theorem deqLane_inj (L : Launch) (c : Nat) : Function.Injective (deqLane L c) := by
  intro a b h
  simp only [deqLane] at h
  exact Fin.ext (by omega)

/-- **A warpgroup-2 lane is a dequant lane of its CTA.** -/
theorem deq_lane (hp : Pre P L m) {g pc : Nat} (hw : MbarRow.DequantAt L g pc) :
    ∃ b, g = deqLane L (g / L.block) b := by
  obtain ⟨h8, h12, -, -⟩ := hw
  simp only [MbarRow.warp, tidOf_x_eq hp] at h8 h12
  refine ⟨⟨g % 384 - 256, by omega⟩, ?_⟩
  simp only [deqLane, hp.block]
  omega

/-- **The uses of `rawReady s` of CTA `c`**: the initialization, the CTA's TMA lane's loads of 2304
bytes and arrivals expecting 36864 bytes, or a dequant lane's poll with the parity of its earlier
successful polls. -/
theorem rawReady_use (hR : MbarRows P L X) {c g k : Nat} {s : Fin 2} {e : Event}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hm : Frame.MbarOf e (mbarLoc L c (.rawReady s))) :
    (∃ n, e.kind = .mbInit (mbarLoc L c (.rawReady s)) n) ∨
      MbarRow.TmaAt L g e.pc ∧ MbarRow.TmaUse L X g k e (mbarLoc L c (.rawReady s)) ∧
        g / L.block = c ∧ (MbarRow.Issue e (mbarLoc L c (.rawReady s)) 2304 ∨
          MbarRow.Arrive e (mbarLoc L c (.rawReady s)) 36864) ∨
      MbarRow.DequantAt L g e.pc ∧ g / L.block = c ∧
        MbarRow.Wait e (mbarLoc L c (.rawReady s))
          (okPolls (mbarLoc L c (.rawReady s)) ((X.tr g).take k) % 2) := by
  rcases mbar_use hR hg he hm with ⟨-, ⟨-, j, -, -, hk⟩⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨hw, h⟩ | ⟨-, h⟩ |
    ⟨hw, h⟩
  · exact .inl ⟨_, hk⟩
  · cases h with
    | lastStore _ hl _ | coordReady _ hl _ | qkDone _ hl _ | coordFree _ hl _ | soReady _ hl _
    | svDone _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qLoad _ hl _ | qArrive _ hl _ | qWait _ hl _ _ | qCommit _ hl _ | qCopyWait _ hl _ _
    | kvWait _ hl _ | qkCommit _ hl _ | soWait _ hl _ | svCommit _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qWait _ hl _ _ | lastWait _ hl _ _ | coordWait _ hl _ | freeWait _ hl _ | coordFree _ hl _ =>
      nomatch (fam_eq hl).2
    | rawLoad hpc hl hk =>
      exact .inr (.inl ⟨hw, .rawLoad hpc hl hk, (fam_eq hl).1.symm, .inl hk⟩)
    | rawArrive hpc hl hk =>
      exact .inr (.inl ⟨hw, .rawArrive hpc hl hk, (fam_eq hl).1.symm, .inr hk⟩)
  · cases h with
    | freeWait _ hl _ | readyArrive _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qWait _ hl _ _ | svWait _ hl _ | readyArrive _ hl _ | freeArrive _ hl _ =>
      nomatch (fam_eq hl).2
    | rawWait _ hl hk => exact .inr (.inr ⟨hw, (fam_eq hl).1.symm, hk⟩)

/-- **The uses of `rawFree s` of CTA `c`**: the initialization, the CTA's TMA lane's polls with
the parity of its earlier successful polls plus one, or a dequant lane's unit arrival. -/
theorem rawFree_use (hR : MbarRows P L X) {c g k : Nat} {s : Fin 2} {e : Event}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hm : Frame.MbarOf e (mbarLoc L c (.rawFree s))) :
    (∃ n, e.kind = .mbInit (mbarLoc L c (.rawFree s)) n) ∨
      MbarRow.TmaAt L g e.pc ∧ MbarRow.TmaUse L X g k e (mbarLoc L c (.rawFree s)) ∧
        g / L.block = c ∧ MbarRow.Wait e (mbarLoc L c (.rawFree s))
          ((okPolls (mbarLoc L c (.rawFree s)) ((X.tr g).take k) + 1) % 2) ∨
      MbarRow.DequantAt L g e.pc ∧ g / L.block = c ∧
        MbarRow.Arrive e (mbarLoc L c (.rawFree s)) 0 := by
  rcases mbar_use hR hg he hm with ⟨-, ⟨-, j, -, -, hk⟩⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨hw, h⟩ | ⟨-, h⟩ |
    ⟨hw, h⟩
  · exact .inl ⟨_, hk⟩
  · cases h with
    | lastStore _ hl _ | coordReady _ hl _ | qkDone _ hl _ | coordFree _ hl _ | soReady _ hl _
    | svDone _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qLoad _ hl _ | qArrive _ hl _ | qWait _ hl _ _ | qCommit _ hl _ | qCopyWait _ hl _ _
    | kvWait _ hl _ | qkCommit _ hl _ | soWait _ hl _ | svCommit _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qWait _ hl _ _ | lastWait _ hl _ _ | coordWait _ hl _ | rawLoad _ hl _ | rawArrive _ hl _
    | coordFree _ hl _ => nomatch (fam_eq hl).2
    | freeWait hpc hl hk =>
      exact .inr (.inl ⟨hw, .freeWait hpc hl hk, (fam_eq hl).1.symm, hk⟩)
  · cases h with
    | freeWait _ hl _ | readyArrive _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qWait _ hl _ _ | rawWait _ hl _ | svWait _ hl _ | readyArrive _ hl _ =>
      nomatch (fam_eq hl).2
    | freeArrive _ hl hk => exact .inr (.inr ⟨hw, (fam_eq hl).1.symm, hk⟩)

/-- **`rawReady s` of CTA `c` is a `TmaUnits` object of the CTA's TMA lane**: one arrival
expecting 36864 bytes per use and sixteen gather4 loads of 2304 bytes. -/
theorem rawReady_obj (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hO : TmaOne L X) (c : Nat) (s : Fin 2) :
    TmaUnits.Obj X (mbarLoc L c (.rawReady s)) (tmaThread L X c) 16 2304 :=
  tmaUnits_of_uses hX hR (initFirst hp hX hFw hR hI hB c (.rawReady s)) fun he hm => by
    rcases rawReady_use hR (Frame.lt_of_get hX he) he hm with hk | ⟨hat, hu, hc, hk⟩ |
      ⟨-, -, hk⟩
    · exact .inl hk
    · have hy := tma_thread_eq hO he (notUb_of_kind (mbar_kind hX hR he hm)) hat hu
      rw [hc] at hy
      exact .inr (.inr ⟨hy, hk⟩)
    · exact .inr (.inl ⟨_, hk⟩)

/-- **`rawFree s` of CTA `c` is a unit object of the CTA's 128 dequant lanes**, polled with
offset 1. -/
theorem rawFree_obj (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (c : Nat) (s : Fin 2) :
    Unit.Obj X (mbarLoc L c (.rawFree s)) 128 (deqLane L c) 1 :=
  unit_of_uses hX hR (by decide) (deqLane_inj L c) le_rfl
    (initFirst hp hX hFw hR hI hB c (.rawFree s)) fun he hm => by
    rcases rawFree_use hR (Frame.lt_of_get hX he) he hm with hk | ⟨-, -, -, hk⟩ | ⟨hw, hc, hk⟩
    · exact .inl hk
    · exact .inr (.inl ⟨_, hk, Nat.mod_mod _ _⟩)
    · obtain ⟨b, hb⟩ := deq_lane hp hw
      rw [hc] at hb
      exact .inr (.inr ⟨⟨b, hb⟩, hk⟩)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
