-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GlobalWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputStageReuse
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.DequantByteGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RawSharedWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.OrdinaryReadWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0StageUnique
import Lemmas.Order.Order

@[expose] public section

/-! # Ordinary writes sharing the dequantization and output staging storage -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedTileWrites

open PTX PTX.Flow AsyncCopy Protocol OutputStageReuse

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem producer_lane {g i cta : Nat} {d : Wg2.D} {a : Acc} {bytes : List Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hw : X.Writes (g, i) a bytes)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hc : ctaOf L g = cta) : ∃ lane, g = GemmRing.producer L cta lane := by
  have hg := Frame.lt_of_get hX hw.choose_spec
  have hRole : wgOf L g = 2 := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
  exact RawRing.consumer_of_wg2 hpre hc hRole

private theorem dequant_byte {cta i : Nat} {lane : Fin 128} {r : Fin 4} {s : Fin 8}
    {d : Wg2.D} {a : Acc} {bytes : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (hw : X.Writes (GemmRing.producer L cta lane, i) a bytes)
    (hd : Frame.stateAt (Machine.code P L) X (GemmRing.producer L cta lane) i =
      some (some (.wg2 d))) (hSite : d.site = .store r s) (hc : a.Covers l) :
    ∃ (tag : Nat) (u : TState) (b : Fin 16),
      X.get (GemmRing.producer L cta lane, i) = some ⟨tag, .wr a bytes⟩ ∧
      (Wg2.machine P L (GemmRing.producer L cta lane)).Fired
        (some (.inr d)) ⟨tag, .wr a bytes⟩ (some u) ∧
      Wg2.Inv P L (GemmRing.producer L cta lane) d ∧
      l = dequantStoreByte L cta lane d.buf r s b := by
  obtain ⟨tag, he⟩ := hw
  obtain ⟨o, hf⟩ := (Frame.trace hs hX (Frame.lt_of_get hX he)).fired_at he hd
  cases o with
  | none =>
    obtain ⟨_, _, hfire⟩ := hf
    rcases fires_none_ends hfire with ⟨_, h⟩ | h <;> cases h
  | some u =>
    have hFire : (Wg2.machine P L (GemmRing.producer L cta lane)).Fired
        (some (.inr d)) ⟨tag, .wr a bytes⟩ (some u) := hf
    obtain ⟨b, hLoc⟩ := dequantStoreByte_of_cover hpre hSite hFire he ⟨tag, he⟩ hc
    exact ⟨tag, u, b, he, hFire, hFire.choose_spec.1.2, hLoc⟩

private theorem same_dequant_lane {cta block block' : Nat} {lane lane' : Fin 128}
    {r r' : Fin 4} {s s' : Fin 8} {b b' : Fin 16}
    (hpre : Pre P L mem0)
    (hSame : dequantStoreByte L cta lane (block % 2) r s b =
      dequantStoreByte L cta lane' (block' % 2) r' s' b') :
    lane = lane' := by
  let g := GemmRing.producer L cta lane
  let slot : Fin 64 := ⟨Wg2.rawRow L g r.val, Wg2.rawRow_lt r.isLt⟩
  let feat : Fin 512 := ⟨Wg2.logicalElem L g s.val (b.val / 2), by
    have hi : Wg2.idxInGroup L g < 8 := Wg2.idxInGroup_lt L g
    have hs := s.isLt
    have hb := b.isLt
    simp only [Wg2.logicalElem, Wg2.elemsPerStep, Wg2.rawBytesPerThread]
    omega⟩
  let byte : Fin 2 := ⟨b.val % 2, Nat.mod_lt _ (by decide)⟩
  let loc : Loc := ⟨.shared, cta, TensorSwizzle.offset .b128 0
    (MmaDataTrace.kvLinearByte L block slot.val feat.val byte.val)⟩
  have hLeft : dequantStoreByte L cta lane (block % 2) r s b = loc := by
    have hAddr := Result.logical_store_byte hpre cta lane block r s b
    change (dequantStoreByte L cta lane (block % 2) r s b).addr = loc.addr at hAddr
    simp only [dequantStoreByte, loc] at hAddr ⊢
    rw [hAddr]
  have hA := (Result.dequant_store_coordinates hpre hLeft).2.1
  have hB := (Result.dequant_store_coordinates hpre (hSame.symm.trans hLeft)).2.1
  exact hA.trans hB.symm

private theorem dequant_before_stage {g j w i : Nat} {d : Wg2.D} {q : Wg0.D}
    {r tile : Fin 4} {s chunk : Fin 8} {a b : Acc} {bytes raw : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hg : X.Writes (g, j) a bytes) (hw : X.Writes (w, i) b raw)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 d)))
    (hq : Frame.stateAt (Machine.code P L) X w i = some (some (.wg0 q)))
    (hD : d.site = .store r s) (hQ : q.site = .oStage tile chunk)
    (hcg : ctaOf L g = l.cta) (hcw : ctaOf L w = l.cta)
    (ha : a.Covers l) (hb : b.Covers l) (hLo : L.sharedBase + 65536 ≤ l.addr) :
    ByteCausality L X l (.thread (g, j)) (.thread (w, i)) := by
  have hMachine (k : Nat) (hk : k < L.threads) := (hs k hk).machine
  obtain ⟨lane, hLane⟩ := producer_lane hpre hX hs hg hd hcg
  have hwLt := Frame.lt_of_get hX hw.choose_spec
  have hwg : wgOf L w = 0 := RingRoleGeometry.of_trace hX hwLt (hMachine w hwLt) hq
  obtain ⟨softmaxLane, hSoft⟩ := GemmRing.softmax_thread hpre hcw hwg
  rw [hLane] at hg hd ⊢
  rw [hSoft] at hw hq ⊢
  obtain ⟨tag, u, v, he, hFired, hInv, hLoc⟩ := dequant_byte hpre hX hs hg hd hD ha
  have hBuf : d.buf = 1 := by
    have hLt : d.buf < 2 := hInv.bufLt
    by_contra hn
    have hz : d.buf = 0 := by omega
    have hB := v.isLt
    have hFit := Wg2.tile_fit (L := L) (g := GemmRing.producer L l.cta lane) r.isLt s.isLt
    have hAddr := congrArg Loc.addr hLoc
    simp only [dequantStoreByte, Wg2.tileBase, hz, Nat.mul_zero, Nat.add_zero] at hAddr
    change _ ≤ 65536 at hFit
    omega
  rw [hLoc] at hb ⊢
  exact dequant_store_before_stage hpre hX hs ht he hd hD hBuf hFired hq hQ hw v hb

/-- Any two distinct ordinary writes touching a byte of the dequantization/output tile area
are ordered in that byte's causality relation. -/
theorem writes_ordered {e f : EvId} {a b : Acc} {bytes raw : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.Writes e a bytes) (hf : X.Writes f b raw) (hne : e ≠ f)
    (ha : a.Covers l) (hb : b.Covers l) (hSh : l.space = .shared)
    (hHi : l.addr < L.sharedBase + 131072) :
    ByteCausality L X l (.thread e) (.thread f) ∨
      ByteCausality L X l (.thread f) (.thread e) := by
  obtain ⟨g, i⟩ := e
  obtain ⟨w, j⟩ := f
  obtain ⟨hCta, ⟨d, r, s, hd, hD⟩ | ⟨hLo, d, r, s, hd, hD⟩⟩ :=
    RawSharedWrites.tile_writer_role hpre hX hs ht he ha hSh hHi
  all_goals obtain ⟨hCta', ⟨q, t, k, hq, hQ⟩ | ⟨hLo', q, t, k, hq, hQ⟩⟩ :=
    RawSharedWrites.tile_writer_role hpre hX hs ht hf hb hSh hHi
  · obtain ⟨lane, hG⟩ := producer_lane hpre hX hs he hd hCta.symm
    obtain ⟨lane', hW⟩ := producer_lane hpre hX hs hf hq hCta'.symm
    have hWriters : g = w := by
      have hw := hf
      have hg := he
      rw [hG] at hg hd
      rw [hW] at hw hq
      obtain ⟨_, _, v, _, _, hInv, hA⟩ := dequant_byte hpre hX hs hg hd hD ha
      obtain ⟨_, _, v', _, _, hInv', hB⟩ := dequant_byte hpre hX hs hw hq hQ hb
      rw [hInv.bufBlock] at hA
      rw [hInv'.bufBlock] at hB
      have hEq := same_dequant_lane hpre (hA.symm.trans hB)
      rw [hG, hW, hEq]
    have hI : i ≠ j := fun h => hne (Prod.ext hWriters h)
    rcases Nat.lt_or_gt_of_ne hI with hLt | hLt
    · exact .inl (.direct (.inl (.single (.inl
        (po_of_overlap he.access hf.access hWriters hLt ⟨l, ha, hb⟩)))))
    · exact .inr (.direct (.inl (.single (.inl
        (po_of_overlap hf.access he.access hWriters.symm hLt ⟨l, hb, ha⟩)))))
  · exact .inl (dequant_before_stage hpre hX hs ht he hf hd hq hD hQ
      hCta.symm hCta'.symm ha hb hLo')
  · exact .inr (dequant_before_stage hpre hX hs ht hf he hq hd hQ hD
      hCta'.symm hCta.symm hb ha hLo)
  · exact (hne (Wg0StageUnique.sameByte hpre hX (fun k hk => (hs k hk).machine) ht
      he.choose_spec hf.choose_spec rfl rfl hd hq hD hQ ha hb)).elim

/-- Any ordinary conflict in the tile window is between two causally ordered stores. -/
theorem ordinary_conflict_ordered {e f : EvId} {a b : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hConflict : Conflict X (.thread e) (.thread f) a b)
    (ha : a.Covers l) (hb : b.Covers l) (hSh : l.space = .shared)
    (hHi : l.addr < L.sharedBase + 131072) :
    ByteCausality L X l (.thread e) (.thread f) ∨
      ByteCausality L X l (.thread f) (.thread e) := by
  obtain ⟨hne, ea, fb, hA, hB, _, _⟩ := hConflict
  have write {i : EvId} {a : Acc} {w : Bool}
      (h : X.Access i a w) (hCover : a.Covers l) : ∃ bytes, X.Writes i a bytes := by
    have hNoRmw : ∀ tag access old bytes, X.get i ≠ some ⟨tag, .rmw access old bytes⟩ :=
      fun tag _ _ _ he => GlobalWrites.no_rmw hX ⟨tag, he⟩
    rcases (Execution.access_iff_of_not_rmw hNoRmw).mp h with ⟨_, hRead, _⟩ | ⟨bytes, hw, _⟩
    · obtain ⟨g, j⟩ := i
      have hLo := OrdinaryReadWindow.read_above_tiles hpre hX hs ht hRead hCover
      exact (Nat.not_lt_of_ge hLo hHi).elim
    · exact ⟨bytes, hw⟩
  obtain ⟨bytes, hWa⟩ := write hA ha
  obtain ⟨raw, hWb⟩ := write hB hb
  exact writes_ordered hpre hX hs ht hWa hWb
    (fun h => hne (congrArg Ref.thread h)) ha hb hSh hHi

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedTileWrites
