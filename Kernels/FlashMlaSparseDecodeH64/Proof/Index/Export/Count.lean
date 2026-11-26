-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Index
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.RefNext

@[expose] public section

/-! # The index warp's arrivals against its polls

The input of the index ring (`Protocol/Coord/Observe.lean`'s `CoordInputs.idxArr`) for a lane
of warp 7: an arrival on `coordReady s` follows more successful polls of `coordFree s` than the
lane's earlier arrivals on `coordReady s` (`index_readyArr`; `index_idxArr` for the protocol's
`idxLane L c a = c * L.block + 224 + a`). From the reference invariant at the arrival
(`index_at`): in block `i` the arrival is at the site `arrA` or `arrB` on slot `i % 4`, whose
barriers were used `ringUses 4 s i` times before the block, and the block's poll of the slot is
made. The prefix counts are the ledger's (`ix_okPolls`, `ix_arrivals`,
`Common/IndexLane.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem ready_slot {g c i : Nat} {s : Fin 4}
    (h : mbarLoc L c (.coordReady s) = loc L g (.coordReady (slot4 i))) :
    c = g / L.block ∧ s = slot4 i := by
  simp only [loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff, true_and] at h
  exact ⟨h.1, MbarFam.coordReady.inj (MbarFam.off_inj h.2)⟩

/-- **An index lane's arrival on `coordReady s` follows more successful polls of `coordFree s`
than its earlier arrivals on `coordReady s`.** -/
theorem index_readyArr (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g c i pc : Nat} {s : Fin 4} {sc : MbarScope} (hw : warp L g = 7)
    (he : X.get (g, i) = some ⟨pc, .arrive (mbarLoc L c (.coordReady s)) 0 1 true sc⟩) :
    arrivals (mbarLoc L c (.coordReady s)) ((X.tr g).take i) <
      okPolls (mbarLoc L c (.coordFree s)) ((X.tr g).take i) := by
  have hin := ix_inRole hp hX hFw hw he (.inr (.inr (.inr ⟨_, 0, 1, true, sc, rfl⟩)))
  simp only [Index.inRole, decide_eq_true_eq] at hin
  obtain ⟨d, hR, hev, -⟩ :=
    index_at hp hX hFw he (fun f h => by cases h) ⟨hin.1, by dsimp only; omega⟩
  obtain ⟨j, -, hsl, -, hc, -⟩ := hR (ix_take_noUb hX he)
  simp only [Index.RingCounts] at hc
  obtain ⟨-, hk⟩ := hev
  rw [ix_arrivals hp hX hFw hw, ix_okPolls hp hX hFw hw]
  obtain ⟨site, el, ac, c'⟩ := d
  dsimp only at hsl hc
  cases site with
  | arrA | arrB =>
    simp only [Index.EvK, Kind.arrive.injEq] at hk
    have hl : mbarLoc L c (.coordReady s) = loc L g (.coordReady (slot4 j)) := by
      rw [hk.1, Index.ready_loc hp, hsl]
    obtain ⟨rfl, rfl⟩ := ready_slot hl
    obtain ⟨h1, h2⟩ := hc (slot4 j)
    simp only [loc] at h1 h2
    rw [h1, h2]
    simp only [Index.incW]
    rw [Index.ring_succ]
    simp
  | lenA | lenB | pre | pf | xpre | xpf | wA | wB | sA1 | sA2 | sB1 | sB2 | stA | stB | bA
    | bB =>
    simp [Index.EvK, Index.NcEv, Index.NcAt, Index.PollEv, Index.ShflEv, Index.StoreEv] at hk
  | bar | exit => simp [Index.EvK] at hk

/-- **`CoordInputs.idxArr`** for lane `a` of warp 7 of CTA `c` (thread `c * L.block + 224 + a`,
the protocol's `idxLane`). -/
theorem index_idxArr (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {c i pc : Nat} {s : Fin 4} {a : Fin 32} {sc : MbarScope}
    (he : X.get (c * L.block + 224 + a.val, i) =
      some ⟨pc, .arrive (mbarLoc L c (.coordReady s)) 0 1 true sc⟩) :
    arrivals (mbarLoc L c (.coordReady s)) ((X.tr (c * L.block + 224 + a.val)).take i) <
      okPolls (mbarLoc L c (.coordFree s)) ((X.tr (c * L.block + 224 + a.val)).take i) := by
  refine index_readyArr hp hX hFw ?_ he
  have ha := a.isLt
  simp only [warp, tidOf_x_eq hp, hp.block]
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
