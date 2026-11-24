-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryTmaHistory
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmQuery
public import Core.Memory.CommitOperandOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaWait
import Lemmas.Order.OrderWaits
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Sound
import Lemmas.Tensor.TensorCompleteConsistentRead

@[expose] public section

/-! # The selected query TMA byte precedes its Tensor Memory copy read -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaCopyOrder

open PTX AsyncCopy PTX.Flow MmaDataTrace Result

noncomputable section

/-- The actual query wait observes the selected tile. Its geometry and thread history give
the actual TMA write and its asynchronous order into the copy read at the same byte. -/
theorem actual_query_tma_write_before_copy
    {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {d : Wg1Mma.D} {cp : Fin 16} {e : Event} {u : TState}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .qCopy cp)
    (hf : (Machine.machine P L g).Fired (some (.mma d)) e (some u))
    (row : Fin 128) (feature : Fin 16) (b : Fin 2) :
    let n := 2 * (row.val * 16 + feature.val) + b.val
    ∃ (tile : Fin 8) (x h : Fin 64) (t w : Nat) (l : Loc) (value : Byte),
      t < w ∧ w < i ∧
      X.TensorIssue (g, t) (P.param1Base + Wg1Mma.qMapOff) (queryTmaSpec P L g tile) ∧
      X.MemWrites (.async (g, t) (.write (.load x.val h.val b.val)))
        { loc := l, size := 1 } [value] ∧
      X.MmaFootprint (g, i) false n l ∧
      AsyncChain L X l ((g, t), .write (.load x.val h.val b.val))
        ((g, i), .mmaRead false n) ∧
      ByteCausality L X l (.async (g, t) (.write (.load x.val h.val b.val)))
        (.async (g, i) (.mmaRead false n)) ∧
      Wg1Mma.qCoord tile + x.val = qkFeature cp row feature ∧ h.val = row.val % 64 := by
  dsimp only
  let n := 2 * (row.val * 16 + feature.val) + b.val
  have hg := Frame.lt_of_get hX he
  obtain ⟨w, hw, q, tag, hstate, hwaitSite, hwait⟩ :=
    QueryTmaHistory.wait_before_copy hpre hX (hs g hg).machine he hd hsite
  obtain ⟨tile, x, h, hFeat, hHead, hloc⟩ := queryCopy_tmaSlot hpre g cp row feature b
  obtain ⟨t, htw, hissue⟩ :=
    QueryTmaHistory.load_before_wait tile hpre hX (hs g hg).machine hwait hstate hwaitSite
  let l := (queryTmaSpec P L g tile).toTensorBox.sharedLoc (queryTileSlot P L g tile x h b)
  let a : Acc := { loc := l, size := 1 }
  let part := AsyncCopy.Part.write (.load x.val h.val b.val)
  let source := (g, t)
  let destination := (g, i)
  have hcompletion := QueryTmaWait.actual_tile_observed hpre hX hs hissue hwait
  have hnotify := hcompletion
  obtain ⟨r, m, hn, hwo⟩ := hnotify
  obtain ⟨hr, o, addr, hobs, hi, hm, hnotified⟩ :
      r = .async source (.notify .load) ∧ NotifyOn X source .load m := hn
  have hspec : o.spec = queryTmaSpec P L g tile := by
    obtain ⟨p, hi⟩ := hi
    obtain ⟨q, hq⟩ := hissue
    exact (Kind.tensorIssue.inj (congrArg Event.kind (Option.some.inj (hi.symm.trans hq)))).2
  have hquerySlot : TensorTransfer.slotAt (queryTmaSpec P L g tile).descriptor
      x.val h.val b.val = some (queryTileSlot P L g tile x h b) :=
    TensorCopy.slotAt_self (queryTileSlot P L g tile x h b)
  obtain ⟨address, hsrc, _⟩ := queryTile_initial hpre hg tile x h b
  have hslot : ∃ slot : TensorTransfer.Slot o.spec.descriptor,
      TensorTransfer.slotAt o.spec.descriptor x.val h.val b.val = some slot ∧
      TensorCopy.source o.spec slot = .global address := by
    rw [hspec]
    exact ⟨_, hquerySlot, hsrc⟩
  obtain ⟨slot, hslot, hsource⟩ := hslot
  have hwloc : TensorCopy.writeLoc o.spec x.val h.val b.val = some l := by
    rw [hspec, TensorCopy.writeLoc, hquerySlot]
    rfl
  have hok := (hX.tensor _ _ hobs).2.1
  obtain ⟨content, hcontent⟩ := hok.complete hnotified slot
  have hdata := hok.writes slot content hcontent
  rw [hsource] at hdata
  obtain ⟨value, _, rfl⟩ := hdata
  have hv : TensorCopy.writeByte o x.val h.val b.val = some value := by
    simp only [TensorCopy.writeByte, hslot, Option.bind_some, hcontent, TensorCopy.Content.byte]
  have hwrite : X.MemWrites (.async source part) a [value] :=
    ⟨o, addr, value, hobs, hi, hwloc, hv, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hwriteCover : AsyncCovers X source part l := by
    refine ⟨a, true, ⟨rfl, o.spec, addr, hi, hwloc, rfl⟩, ?_⟩
    simp [a, Acc.Covers, Loc.InRange]
  have hcp : X.CpIssue destination (queryCopySpec L g cp) := by
    have hkind := GemmReuseEndpoints.query_copy hpre hg hsite hf
    obtain ⟨tag, _⟩ := e
    exact ⟨tag, by rw [he]; cases hkind; rfl⟩
  have hnlt : n < (queryCopySpec L g cp).shape.sourceBytes := by
    have hr := row.isLt
    have hfeature := feature.isLt
    have hb := b.isLt
    change n < 4096
    dsimp only [n]
    omega
  have hread : X.MmaFootprint destination false n l := by
    refine .inr ⟨queryCopySpec L g cp, 0, ctaOf L g, hcp, rfl, rfl,
      Nat.div_eq_of_lt hnlt, ?_⟩
    rw [Nat.mod_eq_of_lt hnlt]
    exact hloc
  have hreadCover : AsyncCovers X destination (.mmaRead false n) l := by
    refine ⟨a, false, ⟨rfl, rfl, hread⟩, ?_⟩
    simp [a, Acc.Covers, Loc.InRange]
  have hfinish : AsyncFinished L X source part (g, w) :=
    .inr ⟨.cta, hcompletion, ⟨hg, hg, rfl⟩, ⟨hg, hg, rfl⟩⟩
  have hbefore : baseCausality L X (g, w) destination := .single (.inl
    (po_of_source_not_access rfl hw (PTX.len_of_get he) (by rw [hwait]; rfl)))
  have hchain : AsyncChain L X l (source, part) (destination, .mmaRead false n) :=
    .direct ⟨hwriteCover, hreadCover, .inl ⟨(g, w), hfinish, hbefore⟩⟩
  exact ⟨tile, x, h, t, w, l, value, htw, hw, hissue, hwrite, hread, hchain,
    .direct ⟨.inl ⟨hg, hg, rfl⟩, hchain⟩, hFeat, hHead⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaCopyOrder
