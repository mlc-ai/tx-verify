-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Index
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLive
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Addr

@[expose] public section

/-! # The use of an index write

The per-use index of the index warp's shared writes (the ring regions `tmaCoord` and
`tokenValid`): a write of block `i` lies in slot `s = i % 4` (a coordinate pair element or the
validity byte of the slot, as in `MemRow.IxWr`), after the block's successful poll of
`coordFree s` and before its arrival on `coordReady s`, so the lane has made `u = i / 4`
arrivals on `coordReady s` and `u + 1` successful polls of `coordFree s` (`index_wrUse`); the
validity byte is written by lanes `0 mod 4` only (`IxSkip`, `Common/IndexLive.lean`). Read off
the reference invariant's ring counts at the store sites (`Index.RingCounts` with the poll's
success), the counts are the ledger's (`ix_arrivals`, `ix_okPolls`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The ring counts at a site after the block's poll, on the block's slot. -/
private theorem use_counts {g i : Nat} {n : Index.Cnt → Nat}
    (hc : Index.RingCounts L g n i 1) :
    n (.arrive (MbarRow.loc L g (.coordReady (MbarRow.slot4 i)))) = i / 4 ∧
      n (.acq (MbarRow.loc L g (.coordFree (MbarRow.slot4 i)))) = i / 4 + 1 := by
  obtain ⟨h1, h2⟩ := hc (MbarRow.slot4 i)
  rw [h1, h2, Index.ring_succ, Index.ring_here]
  simp

/-- A lane that does not skip the validity byte is a lane `0 mod 4`. -/
private theorem skip_tid (hp : Pre P L m) {g : Nat} (h : ixSkipB L g = false) :
    (L.tidOf g).x % 4 = 0 := by
  have ht := tidOf_lt hp g
  unfold ixSkipB at h
  rw [show (3 : Int) = ((2 ^ 2 - 1 : Nat) : Int) from rfl, show tw L g = W (tidOf L g) from rfl,
    andi_W_low ht (by norm_num), scmpi_ne_b_W (by omega) (by norm_num) (by norm_num)] at h
  have h2 := of_decide_eq_false h
  simp only [tidOf, Int.toNat_zero, ne_eq, not_not] at h2
  omega

/-- **The use of an index write**: a shared write of an index lane is at its pair or validity
places of a slot `s`, with `u` arrivals on `coordReady s` and `u + 1` successful polls of
`coordFree s` before it. -/
theorem index_wrUse (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hat : MbarRow.IndexAt L g pc) :
    ∃ s : Fin 4, ((∃ j < 2, MemRow.WsAcc L (g / L.block)
        (221728 + 256 * s.val + 8 * ((L.tidOf g).x % 32) + 4 * j) 4 a) ∨
      MemRow.WsAcc L (g / L.block) (221696 + 8 * s.val + (L.tidOf g).x % 32 / 4) 1 a ∧
        (L.tidOf g).x % 4 = 0) ∧
      ∃ u, arrivals (mbarLoc L (g / L.block) (.coordReady s)) ((X.tr g).take k) = u ∧
        okPolls (mbarLoc L (g / L.block) (.coordFree s)) ((X.tr g).take k) = u + 1 := by
  obtain ⟨hw, hr1, hr2⟩ := hat
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he (fun _ h => by cases h)
  obtain ⟨d, n, rfl, hR, ⟨-, hE⟩, -⟩ := index_state hJ hi hev hpc ⟨hr1, hr2⟩
  obtain ⟨-, hel, hsk⟩ := ix_ok hp hX hσ _ n rfl
  obtain ⟨i, -, hsl, -, hc, -⟩ := hR (state_ub hX hσ he)
    ((state_count hσ (.index .ub)).trans (ix_take_noUb hX he))
  have hA : ∀ l, arrivals l ((X.tr g).take k) = n (.index (.arrive l)) := fun l =>
    (ix_arrivals hp hX hFw hw k l).trans (state_count hσ (.index (.arrive l))).symm
  have hP : ∀ l, okPolls l ((X.tr g).take k) = n (.index (.acq l)) := fun l =>
    (ix_okPolls hp hX hFw hw k l).trans (state_count hσ (.index (.acq l))).symm
  obtain ⟨site, el, ac, c'⟩ := d
  dsimp only at hsl hc hel hsk
  have hpl := Index.pair_loc (g := g) hp c'
  have hbl := Index.byte_loc (g := g) hp c'
  simp only [tidOf] at hpl hbl
  have hcnt : ∀ (hw1 : Index.incW site = 1), ∃ u,
      arrivals (mbarLoc L (g / L.block) (.coordReady c'.slot)) ((X.tr g).take k) = u ∧
        okPolls (mbarLoc L (g / L.block) (.coordFree c'.slot)) ((X.tr g).take k) = u + 1 := by
    intro hw1
    rw [hw1] at hc
    obtain ⟨h1, h2⟩ := use_counts hc
    refine ⟨i / 4, ?_, ?_⟩
    · rw [hA, hsl]
      exact h1
    · rw [hP, hsl]
      exact h2
  cases site <;> simp [Index.EvK, Index.NcEv, Index.PollEv, Index.ShflEv, Index.StoreEv] at hE
  all_goals
    obtain ⟨hl, hsz⟩ := hE
    simp only [IxSite.elems] at hel
  · exact ⟨c'.slot, .inl ⟨el, hel, by
      rw [hl, hpl]; simp only [wsLoc, Loc.at, Loc.mk.injEq, true_and]; omega, hsz⟩,
      hcnt rfl⟩
  · exact ⟨c'.slot, .inr ⟨⟨by rw [hl, hbl]; simp [wsLoc, Loc.at], hsz⟩,
      skip_tid hp (hsk (by simp))⟩, hcnt rfl⟩
  · exact ⟨c'.slot, .inl ⟨el, hel, by
      rw [hl, hpl]; simp only [wsLoc, Loc.at, Loc.mk.injEq, true_and]; omega, hsz⟩,
      hcnt rfl⟩
  · exact ⟨c'.slot, .inr ⟨⟨by rw [hl, hbl]; simp [wsLoc, Loc.at], hsz⟩,
      skip_tid hp (hsk (by simp))⟩, hcnt rfl⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
