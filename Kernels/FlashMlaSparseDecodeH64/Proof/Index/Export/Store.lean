-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Index
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IdxStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLive
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Addr
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.SgTid

@[expose] public section

/-! # The index lane's writes in order

A lane of warp 7 makes, per block of the ring, two writes of its coordinate pair and, on lanes
`0 mod 4`, one of the validity byte (`Index.StEq`). So the lane's write of element `j` of its
block `4 u + s` (`u` arrivals on `coordReady s` before it; `j = 2` the validity byte) is preceded by
exactly `(2 + [lane % 4 = 0]) (4 u + s) + j` writes of the lane at the index warp's pcs
(`index_wrCount`). It is how the written word of a pair is told from the lane's other writes. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A lane that does not skip the validity byte is a lane `0 mod 4`. -/
private theorem skip_tid (hp : Pre P L m) {g : Nat} (h : ixSkipB L g = false) :
    (L.tidOf g).x % 4 = 0 := by
  by_contra hne
  have := sgB_tid hp g
  simp [Index.sgB, h, hne] at this

/-- **The write count of an index lane's write**: the lane's block `4 u + s` and element `j`. -/
theorem index_wrCount (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hat : MbarRow.IndexAt L g pc) :
    ∃ s : Fin 4, ∃ u j : Nat, ((∃ j' < 2, j = j' ∧ MemRow.WsAcc L (g / L.block)
        (221728 + 256 * s.val + 8 * ((L.tidOf g).x % 32) + 4 * j') 4 a) ∨
      j = 2 ∧ (L.tidOf g).x % 4 = 0 ∧
        MemRow.WsAcc L (g / L.block) (221696 + 8 * s.val + (L.tidOf g).x % 32 / 4) 1 a) ∧
      arrivals (mbarLoc L (g / L.block) (.coordReady s)) ((X.tr g).take k) = u ∧
      okPolls (mbarLoc L (g / L.block) (.coordFree s)) ((X.tr g).take k) = u + 1 ∧
      ((X.tr g).take k).countP idxWr =
        (2 + if (L.tidOf g).x % 4 = 0 then 1 else 0) * (4 * u + s.val) + j := by
  obtain ⟨hw, hr1, hr2⟩ := hat
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he (fun _ h => by cases h)
  obtain ⟨d, n, rfl, hR, ⟨-, hE⟩, -⟩ := index_state hJ hi hev hpc ⟨hr1, hr2⟩
  obtain ⟨-, hel, hsk⟩ := ix_ok hp hX hσ _ n rfl
  obtain ⟨i, -, hsl, -, hc, -, hst⟩ := hR (state_ub hX hσ he)
    ((state_count hσ (.index .ub)).trans (ix_take_noUb hX he))
  have hA : ∀ l, arrivals l ((X.tr g).take k) = n (.index (.arrive l)) := fun l =>
    (ix_arrivals hp hX hFw hw k l).trans (state_count hσ (.index (.arrive l))).symm
  have hP : ∀ l, okPolls l ((X.tr g).take k) = n (.index (.acq l)) := fun l =>
    (ix_okPolls hp hX hFw hw k l).trans (state_count hσ (.index (.acq l))).symm
  have hS : ((X.tr g).take k).countP idxWr = n (.index .st) := by
    refine Eq.trans ?_ (state_count hσ (.index .st)).symm
    refine List.countP_congr fun e _ => ?_
    simp only [cls, Index.cls, Index.inRole, Index.kindOf, idxWr]
    cases e with | mk pc kd =>
      cases kd with
      | wait l q ok a sc => cases ok <;> simp
      | _ => simp
  obtain ⟨site, el, ac, c'⟩ := d
  dsimp only at hsl hc hel hsk
  obtain ⟨hn, -, -⟩ := hst
  have hpl := Index.pair_loc (g := g) hp c'
  have hbl := Index.byte_loc (g := g) hp c'
  simp only [tidOf] at hpl hbl
  have hsg := sgB_tid hp g
  have hcnt : ∀ (hw1 : Index.incW site = 1), ∃ u,
      arrivals (mbarLoc L (g / L.block) (.coordReady c'.slot)) ((X.tr g).take k) = u ∧
        okPolls (mbarLoc L (g / L.block) (.coordFree c'.slot)) ((X.tr g).take k) = u + 1 ∧
        i = 4 * u + c'.slot.val := by
    intro hw1
    rw [hw1] at hc
    obtain ⟨h1, h2⟩ := hc (MbarRow.slot4 i)
    have a1 : n (.index (.arrive (MbarRow.loc L g (.coordReady (MbarRow.slot4 i))))) = i / 4 := by
      exact h2.trans (Index.ring_here i)
    have a2 : n (.index (.acq (MbarRow.loc L g (.coordFree (MbarRow.slot4 i))))) = i / 4 + 1 := by
      exact h1.trans (by rw [Index.ring_succ, Index.ring_here]; simp)
    refine ⟨i / 4, ?_, ?_, ?_⟩
    · rw [hA, hsl]; exact a1
    · rw [hP, hsl]; exact a2
    · rw [hsl]; simp only [MbarRow.slot4]; omega
  have hn' : n (.index .st) = (2 + Index.sgB L g) * i + Index.stDone L g site el := hn
  rw [hsg] at hn'
  cases site <;> simp [Index.EvK, Index.NcEv, Index.PollEv, Index.ShflEv, Index.StoreEv] at hE
  all_goals
    obtain ⟨hl, hsz⟩ := hE
    simp only [IxSite.elems] at hel
  · obtain ⟨u, h1, h2, h3⟩ := hcnt rfl
    refine ⟨c'.slot, u, el, .inl ⟨el, hel, rfl, by
      rw [hl, hpl]; simp only [wsLoc, Loc.at, Loc.mk.injEq, true_and]; omega, hsz⟩, h1, h2, ?_⟩
    rw [hS, hn', h3]; simp [Index.stDone]
  · obtain ⟨u, h1, h2, h3⟩ := hcnt rfl
    have hb := skip_tid hp (hsk (by simp))
    refine ⟨c'.slot, u, 2, .inr ⟨rfl, hb, by rw [hl, hbl]; simp [wsLoc, Loc.at], hsz⟩, h1, h2, ?_⟩
    rw [hS, hn', h3]; simp [Index.stDone, hb]
  · obtain ⟨u, h1, h2, h3⟩ := hcnt rfl
    refine ⟨c'.slot, u, el, .inl ⟨el, hel, rfl, by
      rw [hl, hpl]; simp only [wsLoc, Loc.at, Loc.mk.injEq, true_and]; omega, hsz⟩, h1, h2, ?_⟩
    rw [hS, hn', h3]; simp [Index.stDone]
  · obtain ⟨u, h1, h2, h3⟩ := hcnt rfl
    have hb := skip_tid hp (hsk (by simp))
    refine ⟨c'.slot, u, 2, .inr ⟨rfl, hb, by rw [hl, hbl]; simp [wsLoc, Loc.at], hsz⟩, h1, h2, ?_⟩
    rw [hS, hn', h3]; simp [Index.stDone, hb]

private theorem ready_slot' {g c i : Nat} {s : Fin 4}
    (h : mbarLoc L c (.coordReady s) = MbarRow.loc L g (.coordReady (MbarRow.slot4 i))) :
    c = g / L.block ∧ s = MbarRow.slot4 i := by
  simp only [MbarRow.loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff, true_and] at h
  exact ⟨h.1, MbarFam.coordReady.inj (MbarFam.off_inj h.2)⟩

/-- **The write count of an index lane's arrival**: the arrival on `coordReady s` that follows `u`
earlier ones ends block `4 u + s`, with all its writes made. -/
theorem index_arrCount (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g c i pc : Nat} {s : Fin 4} {sc : MbarScope} (hw : MbarRow.warp L g = 7)
    (he : X.get (g, i) = some ⟨pc, .arrive (mbarLoc L c (.coordReady s)) 0 1 true sc⟩) :
    c = g / L.block ∧ ((X.tr g).take i).countP idxWr =
      (2 + if (L.tidOf g).x % 4 = 0 then 1 else 0) *
        (4 * arrivals (mbarLoc L c (.coordReady s)) ((X.tr g).take i) + s.val + 1) := by
  have hin := ix_inRole hp hX hFw hw he (.inr (.inr (.inr ⟨_, 0, 1, true, sc, rfl⟩)))
  simp only [Index.inRole, decide_eq_true_eq] at hin
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he (fun f h => by cases h)
  obtain ⟨d, n, rfl, hR, ⟨hpcE, hk⟩, -⟩ := index_state hJ hi hev hpc ⟨hin.1, by dsimp only; omega⟩
  obtain ⟨j, -, hsl, -, hc, -, hst⟩ := hR (state_ub hX hσ he)
    ((state_count hσ (.index .ub)).trans (ix_take_noUb hX he))
  have hS : ((X.tr g).take i).countP idxWr = n (.index .st) := by
    refine Eq.trans ?_ (state_count hσ (.index .st)).symm
    refine List.countP_congr fun e _ => ?_
    simp only [cls, Index.cls, Index.inRole, Index.kindOf, idxWr]
    cases e with | mk pc kd =>
      cases kd with
      | wait l q ok a sc => cases ok <;> simp
      | _ => simp
  obtain ⟨site, el, ac, c'⟩ := d
  dsimp only at hsl hc
  obtain ⟨hn, -, -⟩ := hst
  rw [ix_arrivals hp hX hFw hw]
  have hsg := sgB_tid hp g
  cases site with
  | arrA | arrB =>
    simp only [Index.EvK, Kind.arrive.injEq] at hk
    have hl : mbarLoc L c (.coordReady s) = MbarRow.loc L g (.coordReady (MbarRow.slot4 j)) := by
      rw [hk.1, Index.ready_loc hp, hsl]
    obtain ⟨rfl, rfl⟩ := ready_slot' hl
    obtain ⟨-, h2⟩ := hc (MbarRow.slot4 j)
    have h3 : ((X.tr g).take i).countP (Index.cls (.arrive (MbarRow.loc L g
        (.coordReady (MbarRow.slot4 j))))) = j / 4 :=
      (state_count hσ (.index (.arrive (MbarRow.loc L g
        (.coordReady (MbarRow.slot4 j)))))).symm.trans (h2.trans (Index.ring_here j))
    have h4 : 4 * (j / 4) + (MbarRow.slot4 j).val = j := by simp only [MbarRow.slot4]; omega
    have hn' : n (.index .st) = (2 + Index.sgB L g) * j + (2 + Index.sgB L g) := hn
    refine ⟨rfl, ?_⟩
    rw [h3, hS, hn', h4, hsg]; ring
  | lenA | lenB | pre | pf | xpre | xpf | wA | wB | sA1 | sA2 | sB1 | sB2 | stA | stB | bA
    | bB =>
    simp [Index.EvK, Index.NcEv, Index.NcAt, Index.PollEv, Index.ShflEv, Index.StoreEv] at hk
  | bar | exit => simp [Index.EvK] at hk

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
