-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.RefNext

@[expose] public section

/-! # Warpgroup 2's arrivals against its polls

The inputs of the ring objects the dequant lanes arrive on (`Protocol/Raw/Observe.lean`'s
`RawInputs.deqArr`, the `dequantReady` gate of `Protocol/Dequant/Obj.lean`), for a lane of warps
8–11 (the protocol's `deqLane L c b`):

* `dequant_freeArr`: an arrival on `rawFree s` follows more successful polls of `rawReady s`
  than the lane's earlier arrivals on `rawFree s`;
* `dequant_readyArr`: an arrival on `dequantReady s` follows more successful polls of `svDone s`
  than the lane's earlier arrivals on `dequantReady s`.

Both from the reference invariant at the arrival (`dequant_at`): in block `j` the arrivals are at
the sites `arrD`, `arrF` on slot `j % 2`, whose barriers were used `uses s j` times before the
block, and the block's two polls of the slot are made. The prefix counts are the ledger's
(`wg2_okPolls`, `wg2_arrivals`, `Common/DequantLane.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem loc_fam {g c : Nat} {f f' : MbarFam} (h : mbarLoc L c f = loc L g f') :
    c = g / L.block ∧ f = f' := by
  simp only [loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff, true_and] at h
  exact ⟨h.1, MbarFam.off_inj h.2⟩

private theorem free_slot {g c j : Nat} {s : Fin 2}
    (h : mbarLoc L c (.rawFree s) = loc L g (.rawFree (slot2 j))) :
    c = g / L.block ∧ s = slot2 j := by
  obtain ⟨h1, h2⟩ := loc_fam h
  exact ⟨h1, MbarFam.rawFree.inj h2⟩

private theorem ready_slot {g c j : Nat} {s : Fin 2}
    (h : mbarLoc L c (.dequantReady s) = loc L g (.dequantReady (slot2 j))) :
    c = g / L.block ∧ s = slot2 j := by
  obtain ⟨h1, h2⟩ := loc_fam h
  exact ⟨h1, MbarFam.dequantReady.inj h2⟩

/-- An arrival of a warpgroup-2 lane is one of block `j`'s two arrivals, with the block's counts. -/
private theorem arrive_block (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g i pc tx cnt : Nat} {l : Loc} {rel : Bool} {sc : MbarScope}
    (hw : 8 ≤ warp L g ∧ warp L g < 12)
    (he : X.get (g, i) = some ⟨pc, .arrive l tx cnt rel sc⟩) :
    ∃ j, (∀ b, Dequant.SlotCounts L g (fun c => ((X.tr g).take i).countP (Dequant.cls c)) b
      (Dequant.uses b (j + 1)) (Dequant.uses b (j + 1)) (Dequant.uses b (j + 1))
      (Dequant.uses b j)) ∧ l = loc L g (.rawFree (slot2 j)) ∨
    (∀ b, Dequant.SlotCounts L g (fun c => ((X.tr g).take i).countP (Dequant.cls c)) b
      (Dequant.uses b (j + 1)) (Dequant.uses b (j + 1)) (Dequant.uses b j) (Dequant.uses b j)) ∧
      l = loc L g (.dequantReady (slot2 j)) := by
  have hin := wg2_inRole hp hX hFw hw he (.inr (.inr (.inr ⟨l, tx, cnt, rel, sc, rfl⟩)))
  simp only [Dequant.inRole, decide_eq_true_eq] at hin
  obtain ⟨d, hR, hev, -⟩ :=
    dequant_at hp hX hFw he (fun f h => by cases h) ⟨hin.1, by dsimp only; omega⟩
  have hc := hR (wg2_take_noUb hX he)
  obtain ⟨-, hk⟩ := hev
  obtain ⟨site, el, ac, l0, l1, cnt', sb, pb⟩ := d
  cases site with
  | arrD =>
    obtain ⟨j, -, hsb, -, hn⟩ := hc
    dsimp only at hsb
    simp only [Dequant.EvK, Kind.arrive.injEq] at hk
    refine ⟨j, .inr ⟨hn, ?_⟩⟩
    rw [hk.1, Dequant.ready_loc hp, hsb, Dequant.slotF_slot2]
  | arrF =>
    obtain ⟨j, -, hsb, -, hn⟩ := hc
    dsimp only at hsb
    simp only [Dequant.EvK, Kind.arrive.injEq] at hk
    refine ⟨j, .inl ⟨hn, ?_⟩⟩
    rw [hk.1, Dequant.free_loc hp, hsb, Dequant.slotF_slot2]
  | lenA | lenB | wq | wraw | wsv | scale _ | raw _ _ | store _ _ =>
    simp [Dequant.EvK, Dequant.PollEv, Dequant.LoadEv, Dequant.StoreEv] at hk
  | smr | fpx | bar | exit => simp [Dequant.EvK] at hk

/-- **A dequant lane's arrival on `rawFree s` follows more successful polls of `rawReady s`
than its earlier arrivals on `rawFree s`** (`RawInputs.deqArr`). -/
theorem dequant_freeArr (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g c i pc tx cnt : Nat} {s : Fin 2} {rel : Bool} {sc : MbarScope}
    (hw : 8 ≤ warp L g ∧ warp L g < 12)
    (he : X.get (g, i) = some ⟨pc, .arrive (mbarLoc L c (.rawFree s)) tx cnt rel sc⟩) :
    arrivals (mbarLoc L c (.rawFree s)) ((X.tr g).take i) <
      okPolls (mbarLoc L c (.rawReady s)) ((X.tr g).take i) := by
  obtain ⟨j, ⟨hn, hl⟩ | ⟨-, hl⟩⟩ := arrive_block hp hX hFw hw he
  · obtain ⟨rfl, rfl⟩ := free_slot hl
    obtain ⟨h1, -, -, h4⟩ := hn (slot2 j)
    rw [wg2_arrivals hp hX hFw hw, wg2_okPolls hp hX hFw hw]
    simp only [loc] at h1 h4
    rw [h1, h4, Dequant.uses_succ]
    simp
  · exact absurd (loc_fam hl).2 (by simp)

/-- **A dequant lane's arrival on `dequantReady s` follows more successful polls of `svDone s`
than its earlier arrivals on `dequantReady s`** (the `dequantReady` gate's input). -/
theorem dequant_readyArr (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g c i pc : Nat} {s : Fin 2} {sc : MbarScope}
    (hw : 8 ≤ warp L g ∧ warp L g < 12)
    (he : X.get (g, i) = some ⟨pc, .arrive (mbarLoc L c (.dequantReady s)) 0 1 true sc⟩) :
    arrivals (mbarLoc L c (.dequantReady s)) ((X.tr g).take i) <
      okPolls (mbarLoc L c (.svDone s)) ((X.tr g).take i) := by
  obtain ⟨j, ⟨-, hl⟩ | ⟨hn, hl⟩⟩ := arrive_block hp hX hFw hw he
  · exact absurd (loc_fam hl).2 (by simp)
  · obtain ⟨rfl, rfl⟩ := ready_slot hl
    obtain ⟨-, h2, h3, -⟩ := hn (slot2 j)
    rw [wg2_arrivals hp hX hFw hw, wg2_okPolls hp hX hFw hw]
    simp only [loc] at h2 h3
    rw [h2, h3, Dequant.uses_succ]
    simp

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
