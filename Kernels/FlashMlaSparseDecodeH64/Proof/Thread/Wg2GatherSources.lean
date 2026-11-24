-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2GatherInput
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRingOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawTmaDequant

@[expose] public section

/-! # Published gather records for the dequantizer's raw loads -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2

open PTX PTX.Flow PTX.AsyncCopy PTX.MbarRing
open Protocol Protocol.RawRing Result.RawGather

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The successful raw-ready acquire before an access identifies the actual gather of the
same block and tile, including the already-notified observation. -/
theorem published_gather_with_acquires {cta issuer j : Nat} {lane : Fin 128} {d : D} {e : Event}
    (tile : Fin 16) (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hAcquires : GatherAcquires L X cta issuer)
    (he : X.get (consumer L cta lane, j) = some e)
    (hState : Frame.stateAt (Machine.code P L) X (consumer L cta lane) j = some (some (.wg2 d)))
    (hd : Wg2RawTrace.RawAccess d.site) :
    let m := ready L cta (rawSlot d.block)
    let i := nthEv X (issuesTo m) issuer (16 * (d.block / 2) + tile.val)
    ∃ t o address,
      Frame.stateAt (Machine.code P L) X issuer i = some (some (.tma t)) ∧
      t.site = .issue tile ∧ t.block = d.block ∧ ctaOf L issuer = cta ∧
      o.spec.sharedBase =
        ⟨.shared, cta, L.sharedBase + Wg1Tma.issueDst (d.block % 2) tile.val⟩ ∧
      X.tensor (issuer, i) = some o ∧ X.TensorIssue (issuer, i) address o.spec ∧
      o.effects.notified = true := by
  intro m i
  let g := consumer L cta lane
  have hgc : ctaOf L g = cta := by
    have hlane := lane.isLt
    simp only [g, consumer, ctaOf, hpre.block]
    omega
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, hcount⟩ := Wg2RawTrace.composed_raw_access_counts hpre
    ((hs g hg).machine.produces (hX.thr g hg)) hState hd
  rw [hgc] at hcount
  change okPolls m ((X.tr g).take j) = d.block / 2 + 1 at hcount
  obtain ⟨p, pc, parity, acq, sc, _, hp, huses⟩ :=
    MbarRing.Poll.exists_nth (le_of_eq hcount.symm)
  have hObs := hAcquires tile hp rfl
  change AsyncObserved X (issuer,
    nthEv X (issuesTo m) issuer (16 * okPolls m ((X.tr g).take p) + tile.val))
    (.notify .load) (g, p) true .cta at hObs
  rw [huses] at hObs
  change AsyncObserved X (issuer, i) (.notify .load) (g, p) true .cta at hObs
  obtain ⟨o, address, ho, hi, hn, hw⟩ := hObs.tensor
  obtain ⟨site, flag, hget⟩ := hw.1
  have hm : o.spec.mbar = m := by
    have hEq := Event.mk.inj (Option.some.inj (hget.symm.trans hp))
    exact (Kind.wait.inj hEq.2).1
  obtain ⟨a, _, record, _, _, hra, hId, _⟩ := hw.2
  have hr : record ∈ X.objects m := by
    rw [← hm]
    exact List.mem_of_getElem? hra
  obtain ⟨tag, hiss⟩ := hi
  have hAct := (hX.tma.2.2.1 m).2.1 record hr
  rw [hId] at hAct
  have ha : record.action = .completeTx (TensorTransfer.bytes o.spec.descriptor) := by
    simpa [AsyncCopy.objectAction, hiss, ho, hm, hn] using hAct.1.symm
  obtain ⟨_, h, j', v, a', sp, t, k, href, hget', hkind, _, hcta, htSite, hslot, hdst, _, hst⟩ :=
    actual_gather_record hpre hX hs hr ha
  have hid := (Ref.async.inj (href.symm.trans hId)).1
  have ⟨hh, hj⟩ := Prod.mk.inj hid
  subst h
  subst j'
  rw [hiss] at hget'
  obtain rfl := Option.some.inj hget'
  have hspec := (Kind.tensorIssue.inj hkind).2
  subst sp
  have hIssuerLt := Frame.lt_of_get hX hiss
  have hCnt := TmaGatherCounts.composed_issue_count hpre
    ((hs issuer hIssuerLt).machine.produces (hX.thr issuer hIssuerLt)) hst htSite
  rw [hcta, hslot] at hCnt
  change ((X.tr issuer).take i).countP (issuesTo m) = _ at hCnt
  have hNth := (nthEv_spec_of_get (p := issuesTo m) hiss).2
  change ((X.tr issuer).take i).countP (issuesTo m) = 16 * (d.block / 2) + tile.val at hNth
  have hkl := k.isLt
  have htl := tile.isLt
  have hGen : t.block / 2 = d.block / 2 := by omega
  have hk : k = tile := Fin.ext (by omega)
  have hblock : t.block = d.block := by
    change t.block % 2 = d.block % 2 at hslot
    omega
  subst k
  exact ⟨t, o, address, hst, htSite, hblock, hcta, hdst, ho, ⟨tag, hiss⟩, hn⟩

/-- A read of a published gather byte must select that write if older and newer writers are
ordered on the corresponding sides. This uses read axioms directly, without global safety. -/
theorem read_from_published_gather {L : Launch} {mem0 : Mem0} {X : Execution}
    {load : EvId} {a : Acc} {bs : List (Option Byte)}
    {k : Nat} {source : Ref} {written : Acc} {values : List Byte}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hRead : X.Reads load a bs)
    (hk : k < a.size) (hWrite : X.MemWrites source written values)
    (hCovers : written.Covers (a.loc.at k))
    (hPublished : ByteCausality L X (a.loc.at k) source (.thread load))
    (hCompeting : ∀ w b data, X.MemWrites w b data → b.Covers (a.loc.at k) →
      w = source ∨ ByteCausality L X (a.loc.at k) w source ∨
        ByteCausality L X (a.loc.at k) (.thread load) w) :
    X.rf (.thread load) k = some source := by
  have hHidden := hX.hidden (.thread load) a bs k source written values (.inl hRead) hk
    hWrite hCovers hPublished
  cases hrf : X.rf (.thread load) k with
  | none =>
    rw [hrf] at hHidden
    exact hHidden.elim
  | some w =>
    have hrfWf := (hX.rf (.thread load) a bs (.inl hRead)).2 k hk
    rw [hrf] at hrfWf hHidden
    obtain ⟨b, data, hw, hc, _⟩ := hrfWf
    rcases hCompeting w b data hw hc with rfl | hOld | hNew
    · rfl
    · exact (hHidden hOld).elim
    · exact (hX.noFuture (.thread load) a bs k w (.inl hRead) hk hrf hNew).elim

private theorem present_box_slot {L : Launch} {mem0 : Mem0} {X : Execution}
    {issue : EvId} {o : TensorCopy.Observation}
    {base blocks stride : Nat} {cls : TensorDescriptor.AllocationClass}
    {dst : Loc} {oy : Int} {rows : Fin 4 → Int}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (ho : X.tensor issue = some o) (hn : o.effects.notified = true)
    (hBox : o.spec.toTensorBox = Result.RawGather.box base blocks stride cls dst oy rows)
    (row : Fin 4) (col : Fin 144) (byte : Fin 4) :
    TensorCopy.writeLoc o.spec col.val row.val byte.val =
      some (dst.at (576 * row.val + 4 * col.val + byte.val)) ∧
      ∃ value, TensorCopy.writeByte o col.val row.val byte.val = some value := by
  have hc : ∃ s : TensorTransfer.Slot o.spec.descriptor,
      TensorTransfer.slotAt o.spec.descriptor col.val row.val byte.val = some s ∧
      o.spec.sharedLoc s = dst.at (576 * row.val + 4 * col.val + byte.val) ∧
      ((∃ addr, TensorCopy.source o.spec s = .global addr) ∨
        TensorCopy.source o.spec s = .fill .zero .u32 byte.val) := by
    change ∃ s : TensorTransfer.Slot o.spec.toTensorBox.descriptor,
      TensorTransfer.slotAt o.spec.toTensorBox.descriptor col.val row.val byte.val = some s ∧
      o.spec.toTensorBox.sharedLoc s = dst.at (576 * row.val + 4 * col.val + byte.val) ∧
      ((∃ addr, (match o.spec.toTensorBox.globalAddress s with
          | some a => TensorTransfer.Source.global a
          | none => .fill o.spec.toTensorBox.descriptor.fill o.spec.toTensorBox.descriptor.format
              s.2.2.val) = .global addr) ∨
        (match o.spec.toTensorBox.globalAddress s with
          | some a => TensorTransfer.Source.global a
          | none => .fill o.spec.toTensorBox.descriptor.fill o.spec.toTensorBox.descriptor.format
              s.2.2.val) = .fill .zero .u32 byte.val)
    rw [hBox]
    refine ⟨slot base blocks stride cls row col byte,
      Result.RawGather.slotAt base blocks stride cls row col byte,
      sharedLoc dst oy rows row col byte, ?_⟩
    split
    · exact .inl ⟨_, rfl⟩
    · exact .inr rfl
  obtain ⟨s, hslot, hloc, hsource⟩ := hc
  refine ⟨?_, ?_⟩
  · simp [TensorCopy.writeLoc, hslot, hloc]
  · have hok := (hX.tensor issue o ho).2.1
    obtain ⟨content, hcontent⟩ := hok.complete hn s
    have hwrite := hok.writes s content hcontent
    rcases hsource with ⟨addr, h⟩ | h
    · rw [h] at hwrite
      obtain ⟨value, _, rfl⟩ := hwrite
      exact ⟨value, by simp [TensorCopy.writeByte, hslot, hcontent, TensorCopy.Content.byte]⟩
    · rw [h] at hwrite
      have hfill : content = .filled .zero .u32 byte.val := hwrite
      exact ⟨(PTX.Proof.b32 0, byte.val), by
        simp [TensorCopy.writeByte, hslot, hcontent, hfill, TensorCopy.Content.byte,
          TensorCopy.zeroValue, TensorDescriptor.Format.bytes, PTX.Proof.b32, Value.byteAt]⟩

/-- The decoded descriptor of the selected gather maps this byte to its intended raw row. -/
theorem published_gather_slot {issuer i address : Nat} {t : Wg1Tma.D} {tile : Fin 16}
    {o : TensorCopy.Observation} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hst : Frame.stateAt (Machine.code P L) X issuer i = some (some (.tma t)))
    (hsite : t.site = .issue tile) (ho : X.tensor (issuer, i) = some o)
    (hi : X.TensorIssue (issuer, i) address o.spec) (hn : o.effects.notified = true) (row : Fin 4)
    (off : Fin 528) :
    let col : Fin 144 := ⟨off.val / 4, by have := off.isLt; omega⟩
    let byte : Fin 4 := ⟨off.val % 4, Nat.mod_lt _ (by decide)⟩
    TensorCopy.writeLoc o.spec col.val row.val byte.val =
      some (o.spec.sharedBase.at (576 * row.val + off.val)) ∧
      ∃ value, TensorCopy.writeByte o col.val row.val byte.val = some value := by
  intro col byte
  obtain ⟨pc, he⟩ := hi
  obtain ⟨_, _, rows, hfirst, hcoord, hdesc⟩ :=
    RawGatherTrace.gather_operands hpre hs hX hst hsite he rfl
  have hOff : 576 * row.val + 4 * col.val + byte.val = 576 * row.val + off.val := by
    dsimp [col, byte]
    omega
  have hWitness {base blocks stride : Nat} {cls : TensorDescriptor.AllocationClass}
      (hd : (⟨o.spec.outer, o.spec.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
        ⟨1, (encodeKv base blocks stride cls).fourRows⟩) :
      TensorCopy.writeLoc o.spec col.val row.val byte.val =
          some (o.spec.sharedBase.at (576 * row.val + off.val)) ∧
        ∃ value, TensorCopy.writeByte o col.val row.val byte.val = some value := by
    obtain ⟨oy, hb⟩ := Result.RawGather.canonicalBox (s := o.spec.toTensorBox) hd hfirst hcoord
    have h := present_box_slot hX ho hn hb row col byte
    rw [hOff] at h
    exact h
  exact hdesc.elim hWitness (fun h => hWitness h.2)

/-- Every competing write at a read byte must either be that byte's current gather, precede it,
or follow the load. This is the remaining cross-generation and footprint condition of the ring. -/
def GatherReadOrder (L : Launch) (X : Execution) (load : EvId) (a : Acc) (issuer i pos off : Nat) :
    Prop :=
  ∀ k < a.size, ∀ w b values, X.MemWrites w b values → b.Covers (a.loc.at k) →
    let source : Ref :=
      .async (issuer, i) (.write (.load ((off + k) / 4) (pos % 4) ((off + k) % 4)))
    w = source ∨ ByteCausality L X (a.loc.at k) w source ∨
      ByteCausality L X (a.loc.at k) (.thread load) w

/-- The current acquire publishes the gather at every byte of this load. Ordered competing writes
then determine all its read-from choices. -/
theorem gather_sources_with_acquires {cta issuer j off : Nat} {lane : Fin 128} {row : Fin 4} {d : D}
    {e : Event} {a : Acc} {bs : List (Option Byte)} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hAcquires : GatherAcquires L X cta issuer)
    (he : X.get (consumer L cta lane, j) = some e)
    (hState : Frame.stateAt (Machine.code P L) X (consumer L cta lane) j = some (some (.wg2 d)))
    (hd : Wg2RawTrace.RawAccess d.site) (hRead : X.Reads (consumer L cta lane, j) a bs)
    (hLoc : a.loc = ⟨.shared, cta, L.sharedBase + rawBase (d.block % 2) +
      rawRowOff L (consumer L cta lane) row.val + off⟩) (hBound : off + a.size ≤ 528) :
    let pos := rawRow L (consumer L cta lane) row.val
    let m := ready L cta (rawSlot d.block)
    let i := nthEv X (issuesTo m) issuer (16 * (d.block / 2) + pos / 4)
    GatherReadOrder L X (consumer L cta lane, j) a issuer i pos off →
      GatherSources P L X (consumer L cta lane, j) issuer d.block row off a.size := by
  intro pos m i hOrder
  let g := consumer L cta lane
  have hMachine : ∀ h < L.threads, (Machine.machine P L h).Sound :=
    fun h hh => (hs h hh).machine
  let tile : Fin 16 := ⟨pos / 4, by
    have hb := rawRow_lt (L := L) (g := g) (lr := row.val) row.isLt
    change pos < 64 at hb
    omega⟩
  let outRow : Fin 4 := ⟨pos % 4, Nat.mod_lt _ (by decide)⟩
  obtain ⟨t, o, address, hst, hsite, hblock, hcta, hdst, ho, hi, hn⟩ :=
    published_gather_with_acquires tile hpre hX hs hAcquires he hState hd
  refine ⟨i, t, hst, hsite, hblock, ?_⟩
  intro k hk
  let off' : Fin 528 := ⟨off + k, by omega⟩
  obtain ⟨hwriteLoc, value, hvalue⟩ :=
    published_gather_slot hpre hX hs hst hsite ho hi hn outRow off'
  have hrow := RawTmaDequant.rawRow_addr_eq L g (d.block % 2) row.val
  change Wg1Tma.issueDst (d.block % 2) tile.val + 576 * outRow.val =
    rawBase (d.block % 2) + rawRowOff L g row.val at hrow
  have haddr : o.spec.sharedBase.at (576 * outRow.val + off'.val) = a.loc.at k := by
    rw [hdst, hLoc]
    simp only [Loc.at]
    congr 1
    change _ = L.sharedBase + rawBase (d.block % 2) + rawRowOff L g row.val + off + k
    have hOff : off'.val = off + k := rfl
    omega
  let part := Part.write (.load ((off + k) / 4) outRow.val ((off + k) % 4))
  let written : Acc := { loc := a.loc.at k, size := 1 }
  have hWrite : X.MemWrites (.async (issuer, i) part) written [value] :=
    ⟨o, address, value, ho, hi, hwriteLoc.trans (congrArg some haddr), hvalue,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hCovers : written.Covers (a.loc.at k) := by
    simpa [written, Loc.at] using (Acc.covers_at (a := written) (k := 0) (show 0 < 1 by decide))
  have hCover : AsyncCovers X (issuer, i) part (a.loc.at k) :=
    ⟨written, true, hWrite.intent, hCovers⟩
  have hPublished :=
    gather_at_generation_with_acquires tile hpre hX hMachine hAcquires hcta
      he hState hd le_rfl hCover
  exact read_from_published_gather hX hRead hk hWrite hCovers (.direct hPublished) (hOrder k hk)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2
