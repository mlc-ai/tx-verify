-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Index
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.GatherVocab
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.StoredFull
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IdxStore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLive
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexVal
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictIndexNoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StoreVal
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.SgTid
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexWord

@[expose] public section

/-! # The coordinate words the index lane stores

A coordinate store of the index warp (pc `2471`, the main cache's blocks, or `2560`, the extra
cache's) writes the 32-bit word of the lane's block `r` and element `el`: the coordinate of the
index word at position `64 r + 2 lane + el` of the lane's row (the extra row at position
`64 (r - M) + 2 lane + el`, `M` the main cache's blocks), as `StoredWord` says: `-1`, or the
physical row of the selected slot. `r` is the block the lane's write count names. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The coordinate word of an index lane's store**: block `r`, element `el`, a 32-bit word that
is `-1` or the row of the slot the position names, of the main cache below its blocks and of the
extra cache from them on. -/
theorem index_coordStore (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hat : MbarRow.IndexAt L g pc)
    (hsz : a.size = 4) :
    (pc = 2471 ∨ pc = 2560) ∧ ∃ r el z, el < 2 ∧
      ((X.tr g).take k).countP idxWr = (2 + if (L.tidOf g).x % 4 = 0 then 1 else 0) * r + el ∧
      bs = (Value.bits 32 z).toBytes ∧
      (pc = 2471 → r < FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g)) ∧
        StoredWordFull P (ctaidY L g) (ctaidX L g) false (64 * r + 2 * (tidOf L g % 32) + el) z) ∧
      (pc = 2560 → FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g)) ≤ r ∧
        StoredWordFull P (ctaidY L g) (ctaidX L g) true
          (64 * (r - FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g))) +
            2 * (tidOf L g % 32) + el) z) := by
  have hub : ∀ f, (⟨pc, .wr a bs⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  obtain ⟨hw, hr1, hr2⟩ := hat
  obtain ⟨d, n, rfl, hR, ⟨hpcE, hE⟩, -⟩ := index_state hJ hi hev hpcσ ⟨hr1, by dsimp only; omega⟩
  obtain ⟨hok, hel, hsk⟩ := ix_ok hp hX hσ _ n rfl
  obtain ⟨i0, -, hsl, -, hc, hct0, hst⟩ := hR (state_ub hX hσ he)
    ((state_count hσ (.index .ub)).trans (ix_take_noUb hX he))
  obtain ⟨iv, hctv, hV⟩ := ix_val hp hX hFw hσ
  have hS : ((X.tr g).take k).countP idxWr = n (.index .st) := by
    refine Eq.trans ?_ (state_count hσ (.index .st)).symm
    refine List.countP_congr fun e _ => ?_
    simp only [cls, Index.cls, Index.inRole, Index.kindOf, idxWr]
    cases e with | mk pc kd =>
      cases kd with
      | wait l q ok a sc => cases ok <;> simp
      | _ => simp
  obtain ⟨hn, -, -⟩ := hst
  have hn' : n (.index .st) = (2 + Index.sgB L g) * i0 + Index.stDone L g d.site d.el := hn
  rw [sgB_tid hp g] at hn'
  obtain ⟨-, -, -, t1, o', hgood, hq, hes⟩ := ix_strictAt hp hX hFw he hσ
  obtain ⟨ins, hc', hf⟩ := Code.fired_of_good (thread_sound hp) hgood hes
  obtain ⟨hat', hinv⟩ := hgood
  obtain ⟨site, el, ac, c⟩ := d
  dsimp only at hpcE hel hct0 hctv hV hn' hok
  have hlenA := (len_words hp (g / L.block)).1
  have hlenB := (len_words hp (g / L.block)).2.1
  rw [rowOf_cta] at hlenA hlenB
  cases site <;> simp [IxSite.pc] at hpcE <;>
    simp only [Index.EvK, Index.NcEv, Index.NcAt, Index.PollEv, Index.ShflEv,
      Index.StoreEv] at hE <;> try (exfalso; simp at hE; done)
  case stA => -- pc = 2471, the main cache's blocks
    have hpc2 : pc = 2471 := hpcE
    have hmw0 : Index.MainW P L g c i0 := hct0
    obtain rfl : iv = i0 := Index.mainW_inj hctv hmw0
    obtain ⟨hM, -⟩ := hV
    obtain ⟨h0, -⟩ := hok
    obtain ⟨a', ha'⟩ := Index.noUbq_pairVal hp ⟨.stA, el, ac, c⟩ rfl (.inl rfl) t1 ins _ o'
      hat' hinv.1 hc' hq hf
    have hbs : bs = (Value.bits 32 (Index.ixStW P ⟨.stA, el, ac, c⟩)).toBytes :=
      (Kind.wr.inj ha').2
    have hel2 : el < 2 := by simpa [IxSite.elems] using hel
    have hMn : Index.nMain c.l0 = FlashMlaSparseDecodeH64.numOrigBlocks
        (P.topkLen (ctaidY L g)) := nMain_lane hp h0
    have hbnd := (Index.nMain_bnd c.l0).2.1
    have hlt := hmw0.1
    have hmin : Index.nMin c.l0 c.l1 ≤ Index.nMain c.l0 := Nat.min_le_left _ _
    have hl2 : Index.lane2 L g < 64 := by
      have := Nat.mod_lt (tidOf L g) (show 0 < 32 by norm_num)
      simp only [Index.lane2]; omega
    refine ⟨.inl hpc2, iv, el, Index.ixStW P ⟨.stA, el, ac, c⟩, hel2, ?_, hbs,
      fun _ => ⟨by omega, ?_⟩,
      fun h => absurd h (by omega)⟩
    · rw [hS, hn']
      simp [Index.stDone]
    · rcases (show el = 0 ∨ el = 1 by omega) with rfl | rfl
      · simp only [Index.ixStW, ↓reduceIte]
        refine stored_main hp (hM.1) ?_ (h0.trans hlenA) (by omega)
        have e1 := addi_negW (a := Index.lane2 L g + 1 + 64 * iv) (k := 1) (by omega) (by omega)
        rw [show Index.lane2 L g + 1 + 64 * iv - 1 = 64 * iv + Index.lane2 L g by omega] at e1
        rw [hM.2.2]
        exact e1
      · simp only [Index.ixStW, show ¬ (1 = 0) by omega, ↓reduceIte]
        refine stored_main hp (hM.2.1) ?_ (h0.trans hlenA) (by omega)
        rw [hM.2.2, show Index.lane2 L g + 1 + 64 * iv = 64 * iv + Index.lane2 L g + 1 by omega]
  case stB => -- pc = 2560, the extra cache's blocks
    have hpc2 : pc = 2560 := hpcE
    have hxw0 : Index.XW L g c i0 := hct0
    obtain rfl : iv = i0 := Index.xw_inj hctv hxw0
    obtain ⟨hE0, -⟩ := hV
    obtain ⟨h0, h1⟩ := hok
    obtain ⟨hMR, hge, hlr, -, -, hxa⟩ := hxw0
    obtain ⟨a', ha'⟩ := Index.noUbq_pairVal hp ⟨.stB, el, ac, c⟩ rfl (.inr rfl) t1 ins _ o'
      hat' hinv.1 hc' hq hf
    have hbs : bs = (Value.bits 32 (Index.ixStW P ⟨.stB, el, ac, c⟩)).toBytes :=
      (Kind.wr.inj ha').2
    have hel2 : el < 2 := by simpa [IxSite.elems] using hel
    have hMn : Index.nMain c.l0 = FlashMlaSparseDecodeH64.numOrigBlocks
        (P.topkLen (ctaidY L g)) := nMain_lane hp h0
    have hrl := Index.rounds_lt c.l0 c.l1
    have hl2 : Index.lane2 L g < 64 := by
      have := Nat.mod_lt (tidOf L g) (show 0 < 32 by norm_num)
      simp only [Index.lane2]; omega
    have hxa' : c.xa = W (Index.lane2 L g + 64 + 64 * (iv - Index.nMain c.l0)) := by
      rw [hxa, ixXa0_val hp g, toNat_W (by omega)]
      show W _ = W _
      rw [Nat.mod_eq_of_lt (by simp only [Index.lane2] at hl2 ⊢; omega)]
      simp only [Index.lane2]
      rw [show tidOf L g % 32 * 2 = 2 * (tidOf L g % 32) by omega]
    refine ⟨.inr hpc2, iv, el, Index.ixStW P ⟨.stB, el, ac, c⟩, hel2, ?_, hbs,
      fun h => absurd h (by omega),
      fun _ => ⟨by omega, ?_⟩⟩
    · rw [hS, hn']
      simp [Index.stDone]
    · rw [← hMn]
      rcases (show el = 0 ∨ el = 1 by omega) with rfl | rfl
      · simp only [Index.ixStW, ↓reduceIte]
        refine stored_extra hp (hE0.1) ?_ (h1.trans hlenB) (by omega)
        have e1 := addi_negW (a := Index.lane2 L g + 64 + 64 * (iv - Index.nMain c.l0)) (k := 64)
          (by omega) (by omega)
        rw [show Index.lane2 L g + 64 + 64 * (iv - Index.nMain c.l0) - 64 =
          64 * (iv - Index.nMain c.l0) + Index.lane2 L g by omega] at e1
        rw [hxa']
        exact e1
      · simp only [Index.ixStW, show ¬ (1 = 0) by omega, ↓reduceIte]
        refine stored_extra hp (hE0.2) ?_ (h1.trans hlenB) (by omega)
        have e1 := addi_negW (a := Index.lane2 L g + 64 + 64 * (iv - Index.nMain c.l0)) (k := 63)
          (by omega) (by omega)
        rw [show Index.lane2 L g + 64 + 64 * (iv - Index.nMain c.l0) - 63 =
          64 * (iv - Index.nMain c.l0) + Index.lane2 L g + 1 by omega] at e1
        rw [hxa']
        exact e1

  all_goals
    exfalso
    rcases hE with ⟨a', bs', h, -, hs'⟩ | ⟨f, h⟩
    · obtain ⟨rfl, rfl⟩ := Kind.wr.inj h
      omega
    · cases h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
