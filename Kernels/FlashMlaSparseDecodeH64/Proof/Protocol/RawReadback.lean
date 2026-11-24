-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2GatherSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.CtaRings
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawTmaDequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RawSharedWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorSharedBounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2RawWriteKinds
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRawNoOrdinary
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantRawOrigin
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaCoordinate
import Lemmas.Tensor.BoxWrite
import Lemmas.TensorStore.StoreWrite

@[expose] public section

/-! # Shared raw-ring writes supplying dequantizer reads -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawReadback

open PTX PTX.Flow PTX.AsyncCopy PTX.MbarRing RawRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The old generation's ready observation reaches a later same-buffer issue through one
consumer's raw-free release. This orders the two actual asynchronous writes on their common byte. -/
theorem actual_earlier_gather_before_issue {cta issuer i block : Nat} {t : Wg1Tma.D} {e : Event}
    {l : Loc} {x y b x' y' b' : Nat} {current : Fin 16} (tile : Fin 16) (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hIssuer : Issuer P L X cta issuer)
    (hCta : ctaOf L issuer = cta) (he : X.get (issuer, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X issuer i = some (some (.tma t)))
    (hSite : t.site = .issue current) (hSlot : block % 2 = t.block % 2)
    (hOld : block / 2 < t.block / 2) :
    let m := ready L cta (rawSlot block)
    let old := (issuer, nthEv X (issuesTo m) issuer (16 * (block / 2) + tile.val))
    let part := Part.write (.load x y b)
    let next := Part.write (.load x' y' b')
    AsyncCovers X old part l → AsyncCovers X (issuer, i) next l →
    modelCausality L X l (.async old part) (.async (issuer, i) next) := by
  intro m old part next hCover hNext
  let lane : Fin 128 := 0
  let g := consumer L cta lane
  let f := free L cta (rawSlot block)
  have hIssuerLt := Frame.lt_of_get hX he
  have hFreeCount := TmaRawTrace.composed_gather_reuse_count hpre
    ((hs issuer hIssuerLt).machine.produces (hX.thr issuer hIssuerLt)) hState hSite
  rw [hCta, ← hSlot] at hFreeCount
  change okPolls f ((X.tr issuer).take i) = t.block / 2 + 1 at hFreeCount
  obtain ⟨iw, _, _, _, _, hwi, hw, hOrdinal⟩ :=
    MbarRing.Poll.exists_nth (show block / 2 + 1 + 1 ≤ okPolls f ((X.tr issuer).take i) by
      rw [hFreeCount]
      omega)
  have hWarp := RingRoleGeometry.of_trace hX hIssuerLt (hs issuer hIssuerLt).machine hState
  obtain ⟨relScope, hRel, acqScope, hSync, hScope⟩ :=
    actual_free_release_sync lane hpre hX hs hWarp hIssuer hCta hw rfl hOrdinal
  let r := (Unit.it X f (consumer L cta) lane (block / 2)).2
  obtain ⟨tx, n, tag, hGetRelease⟩ := hRel
  change X.get (g, r) = some ⟨tag, .arrive f tx n true relScope⟩ at hGetRelease
  have hg := Frame.lt_of_get hX hGetRelease
  obtain ⟨hgCta, hWg⟩ := actual_consumer_geometry hpre cta lane
  have hKind : (⟨tag, .arrive f tx n true relScope⟩ : Event).kind =
      .arrive (free L (ctaOf L g) (rawSlot block)) tx n true relScope := by rw [show ctaOf L g =
        cta from hgCta]
  have hReady := MachineTracking.actual_raw_release_counts hpre hX hs hWg hGetRelease hKind
  rw [hgCta] at hReady
  change okPolls m ((X.tr g).take r) = arrivals f ((X.tr g).take r) + 1 at hReady
  have hArrival := (nthEv_spec_of_get (p := arrivesOn f) hGetRelease).2
  change arrivals f ((X.tr g).take r) = block / 2 at hArrival
  rw [hArrival] at hReady
  obtain ⟨j, _, _, _, _, hjr, hj, hjOrdinal⟩ :=
    MbarRing.Poll.exists_nth (le_of_eq hReady.symm)
  have hObserve := actual_gather_acquired tile hpre hX hs hWarp hIssuer hj rfl
  change AsyncObserved X
    (issuer, nthEv X (issuesTo m) issuer (16 * okPolls m ((X.tr g).take j) + tile.val))
    (.notify .load) (g, j) true .cta at hObserve
  rw [hjOrdinal] at hObserve
  have hFinished : AsyncFinished L X old part (g, j) :=
    .inr ⟨.cta, hObserve, Unit.Gate.scopesMeet ⟨hIssuerLt, hg, hCta.trans hgCta.symm⟩
      .cluster .cta⟩
  have hBefore : baseCausality L X (g, j) (issuer, i) :=
    Staging.baseCausality_of_handoff ⟨tx, n, tag, hGetRelease⟩ hSync hScope
      ⟨rfl, hjr.le⟩ ⟨rfl, hwi, PTX.len_of_get he⟩
  exact ⟨.inl ⟨hIssuerLt, hIssuerLt, rfl⟩, .direct
    ⟨hCover, hNext, .inl ⟨(g, j), hFinished, hBefore⟩⟩⟩

private theorem canonical_write_address {s : TensorCopy.Spec} {dst l : Loc}
    {base blocks stride : Nat} {cls : TensorDescriptor.AllocationClass}
    {oy : Int} {rows : Fin 4 → Int} {x y b : Nat}
    (hBox : s.toTensorBox = Result.RawGather.box base blocks stride cls dst oy rows)
    (hLoc : TensorCopy.writeLoc s x y b = some l) :
    x < 144 ∧ y < 4 ∧ b < 4 ∧ l = dst.at (576 * y + 4 * x + b) := by
  open Result.RawGather in
  have hShape :
      let d := (encodeKv base blocks stride cls).fourRows
      TensorTile.count d.box 0 = 144 ∧ TensorTile.rows d.box = 4 ∧ d.format.bytes = 4 := by
    norm_num [encodeKv, TensorDescriptor.Descriptor.fourRows, TensorTile.count, TensorTile.step,
      TensorTile.rows, TensorTile.rowsOf, Fin.cases, TensorDescriptor.Format.bytes]
  have hBounds := TensorCopy.writeLoc_bounds hLoc
  change x < TensorTile.count s.toTensorBox.descriptor.box 0 ∧
    y < TensorTile.rows s.toTensorBox.descriptor.box ∧ b < s.toTensorBox.descriptor.format.bytes
    at hBounds
  rw [hBox] at hBounds
  change x < TensorTile.count (encodeKv base blocks stride cls).fourRows.box 0 ∧
    y < TensorTile.rows (encodeKv base blocks stride cls).fourRows.box ∧
    b < (encodeKv base blocks stride cls).fourRows.format.bytes at hBounds
  obtain ⟨hCol, hRow, hBytes⟩ := hShape
  rw [hCol, hRow, hBytes] at hBounds
  obtain ⟨hx, hy, hb⟩ := hBounds
  let col : Fin 144 := ⟨x, hx⟩
  let row : Fin 4 := ⟨y, hy⟩
  let byte : Fin 4 := ⟨b, hb⟩
  change ((TensorTransfer.slotAt s.toTensorBox.descriptor x y b).map s.toTensorBox.sharedLoc) =
    some l at hLoc
  rw [hBox] at hLoc
  have hSlot := Result.RawGather.slotAt base blocks stride cls row col byte
  change TensorTransfer.slotAt
      (Result.RawGather.box base blocks stride cls dst oy rows).descriptor x y b =
    some (Result.RawGather.slot base blocks stride cls row col byte) at hSlot
  rw [hSlot] at hLoc
  change some ((Result.RawGather.box base blocks stride cls dst oy rows).sharedLoc
    (Result.RawGather.slot base blocks stride cls row col byte)) = some l at hLoc
  rw [Result.RawGather.sharedLoc] at hLoc
  exact ⟨hx, hy, hb, (Option.some.inj hLoc).symm⟩

/-- A raw-window write footprint comes from the elected gather issue, even while pending. -/
theorem actual_gather_at_write_location {cta issuer address : Nat} {j : EvId} {x y b : Nat}
    {l : Loc} {spec : TensorCopy.Spec} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hIssuer : Issuer P L X cta issuer)
    (hlCta : l.cta = cta) (hRaw : L.sharedBase + 131072 ≤ l.addr ∧ l.addr < L.sharedBase + 204800)
    (hi : X.TensorIssue j address spec) (hWrite : TensorCopy.writeLoc spec x y b = some l) :
    ∃ (i : Nat) (t : Wg1Tma.D) (tile : Fin 16) (e : Event),
      j = (issuer, i) ∧ X.get (issuer, i) = some e ∧ ctaOf L issuer = cta ∧
      Frame.stateAt (Machine.code P L) X issuer i = some (some (.tma t)) ∧
      t.site = .issue tile ∧ x < 144 ∧ y < 4 ∧ b < 4 ∧
      l.addr = L.sharedBase + Wg1Tma.issueDst (t.block % 2) tile.val + (576 * y + 4 * x + b) ∧
      i = nthEv X (issuesTo (ready L cta (rawSlot t.block))) issuer
        (16 * (t.block / 2) + tile.val) := by
  obtain ⟨g, i⟩ := j
  obtain ⟨tag, he⟩ := hi
  have hFollow := MachineTracking.actual_tensor_issue_followed hpre hX hs he rfl
  obtain ⟨_, hCta, hWindow⟩ :=
    TensorSharedBounds.write_loc_windows_at_followed hpre hX hs hFollow ⟨tag, he⟩ hWrite
  have hgCta := hCta.symm.trans hlCta
  have hg := Frame.lt_of_get hX he
  obtain ⟨s, u, hState, hf⟩ :=
    RingSourceSites.fired_at_followed hX (hs g hg).machine hFollow he (by simp)
  rcases RingTensorEvents.issue_source hpre hf rfl with
    hQuery | ⟨t, tile, rfl, hSite, _, hDst, hm, _⟩
  · rcases hWindow with ⟨hq, _⟩ | ⟨_, block, hRawMbar⟩
    · exact (TensorSharedBounds.query_raw_disjoint hq hRaw).elim
    · have h := congrArg Loc.addr (hQuery.symm.trans hRawMbar)
      simp only [Wg1Tma.rawReadyOff] at h
      omega
  · have hThread := hIssuer g i t hgCta hState (.inr ⟨tile, hSite⟩)
    subst g
    obtain ⟨_, _, rows, hFirst, hCoord, hDesc⟩ :=
      RawGatherTrace.gather_operands hpre hs hX hState hSite he rfl
    have hExact {base blocks stride : Nat} {cls : TensorDescriptor.AllocationClass}
        (hDesc : (⟨spec.outer, spec.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
          ⟨1, (encodeKv base blocks stride cls).fourRows⟩) :
        x < 144 ∧ y < 4 ∧ b < 4 ∧
          l = spec.sharedBase.at (576 * y + 4 * x + b) := by
      obtain ⟨_, hBox⟩ :=
        Result.RawGather.canonicalBox (s := spec.toTensorBox) hDesc hFirst hCoord
      exact canonical_write_address hBox hWrite
    obtain ⟨hx, hy, hb, hl⟩ := hDesc.elim hExact (fun h => hExact h.2)
    have hAddr := congrArg Loc.addr (hl.trans (congrArg (·.at (576 * y + 4 * x + b)) hDst))
    have hCount := TmaGatherCounts.composed_issue_count hpre
      ((hs issuer hg).machine.produces (hX.thr issuer hg)) hState hSite
    rw [hgCta] at hCount hm
    let m := ready L cta (rawSlot t.block)
    change ((X.tr issuer).take i).countP (issuesTo m) = _ at hCount
    change spec.mbar = m at hm
    have hIssue : issuesTo m ⟨tag, .tensorIssue address spec⟩ = true := by
      simp [issuesTo, hm]
    have hNth := nthEv_eq he hIssue
    rw [hCount] at hNth
    exact ⟨i, t, tile, _, rfl, he, hgCta, hState, hSite, hx, hy, hb, hAddr, hNth.symm⟩

private theorem competing_gather {cta issuer : Nat} {j : EvId} {x y b : Nat} {l : Loc} {a : Acc}
    {bs : List Byte} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hIssuer : Issuer P L X cta issuer)
    (hlCta : l.cta = cta) (hRaw : TensorSharedBounds.RawWindow L l)
    (hw : X.MemWrites (.async j (.write (.load x y b))) a bs) (hCover : a.Covers l) :
    ∃ (i : Nat) (t : Wg1Tma.D) (tile : Fin 16) (e : Event),
      j = (issuer, i) ∧ X.get (issuer, i) = some e ∧ ctaOf L issuer = cta ∧
      Frame.stateAt (Machine.code P L) X issuer i = some (some (.tma t)) ∧
      t.site = .issue tile ∧ x < 144 ∧ y < 4 ∧ b < 4 ∧
      l.addr = L.sharedBase + Wg1Tma.issueDst (t.block % 2) tile.val + (576 * y + 4 * x + b) ∧
      i = nthEv X (issuesTo (ready L cta (rawSlot t.block))) issuer
        (16 * (t.block / 2) + tile.val) := by
  obtain ⟨o, address, value, ho, hi, hWrite, hByte, hSize, _⟩ := hw
  rw [Acc.loc_of_one hCover hSize] at hWrite
  exact actual_gather_at_write_location hpre hX hs hIssuer hlCta hRaw hi hWrite

/-- A byte address fixes its physical raw buffer, transfer tile, row, column and byte. -/
theorem raw_address_match {a b u v x y k x' y' k' : Nat}
    (hu : u < 16) (hv : v < 16) (hx : x < 144) (hy : y < 4) (hk : k < 4)
    (hx' : x' < 144) (hy' : y' < 4) (hk' : k' < 4)
    (he : Wg1Tma.issueDst a u + (576 * y + 4 * x + k) =
      Wg1Tma.issueDst b v + (576 * y' + 4 * x' + k')) :
    a = b ∧ u = v ∧ x = x' ∧ y = y' ∧ k = k' := by
  unfold Wg1Tma.issueDst Wg1Tma.rawBase at he
  have hSlot : a = b := by omega
  have hTile : u = v := by omega
  have hRow : y = y' := by omega
  have hCol : x = x' := by omega
  exact ⟨hSlot, hTile, hCol, hRow, by omega⟩

/-- Each tensor write covering a raw read byte either is its current gather, precedes that
gather via an older use of the raw slot, or follows the reader's release of this slot. -/
theorem tensor_write_order {cta issuer j off : Nat} {lane : Fin 128} {row : Fin 4} {d : Wg2.D}
    {e : Event} {a : Acc} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hIssuer : Issuer P L X cta issuer)
    (he : X.get (consumer L cta lane, j) = some e) (hAccess : e.acc.isSome = true)
    (hState : Frame.stateAt (Machine.code P L) X (consumer L cta lane) j = some (some (.wg2 d)))
    (hd : Wg2RawTrace.RawAccess d.site)
    (hLoc : a.loc = ⟨.shared, cta, L.sharedBase + Wg2.rawBase (d.block % 2) +
      Wg2.rawRowOff L (consumer L cta lane) row.val + off⟩) (hBound : off + a.size ≤ 528) :
    let g := consumer L cta lane
    let pos := Wg2.rawRow L g row.val
    let m := ready L cta (rawSlot d.block)
    let i := nthEv X (issuesTo m) issuer (16 * (d.block / 2) + pos / 4)
    ∀ k < a.size, ∀ src x y b fp bs, X.MemWrites (.async src (.write (.load x y b))) fp bs →
      fp.Covers (a.loc.at k) →
      let w := Ref.async src (.write (.load x y b))
      let current := Ref.async (issuer, i)
        (.write (.load ((off + k) / 4) (pos % 4) ((off + k) % 4)))
      w = current ∨ ByteCausality L X (a.loc.at k) w current ∨
        ByteCausality L X (a.loc.at k) (.thread (g, j)) w := by
  intro g pos m i k hk src x y b fp bs hWrite hCover w current
  change a.loc = ⟨.shared, cta, L.sharedBase + Wg2.rawBase (d.block % 2) +
    Wg2.rawRowOff L g row.val + off⟩ at hLoc
  let l := a.loc.at k
  have hpos : pos < 64 := Wg2.rawRow_lt (L := L) (g := g) (lr := row.val) row.isLt
  let tile : Fin 16 := ⟨pos / 4, by omega⟩
  let r : Fin 4 := ⟨pos % 4, Nat.mod_lt _ (by decide)⟩
  let n : Fin 528 := ⟨off + k, by omega⟩
  have hByteSpace : l.space = .shared := by simp [l, Loc.at, hLoc]
  have hByteCta : l.cta = cta := by simp [l, Loc.at, hLoc]
  have hRowAddr := RawTmaDequant.rawRow_addr_eq L g (d.block % 2) row.val
  change Wg1Tma.issueDst (d.block % 2) (pos / 4) + 576 * (pos % 4) =
    Wg2.rawBase (d.block % 2) + Wg2.rawRowOff L g row.val at hRowAddr
  have hByteAddr : l.addr = L.sharedBase + Wg1Tma.issueDst (d.block % 2) (pos / 4) +
      (576 * (pos % 4) + (off + k)) := by
    simp only [l, Loc.at, hLoc]
    omega
  have hRaw : TensorSharedBounds.RawWindow L l := by
    unfold TensorSharedBounds.RawWindow
    rw [hByteAddr]
    unfold Wg1Tma.issueDst Wg1Tma.rawBase
    omega
  obtain ⟨i', t, tile', event', hSource, hEvent, hIssuerCta, hTma, hSite', hx, hy, hb,
    hAddr, hNth⟩ := competing_gather hpre hX hs hIssuer hByteCta hRaw hWrite hCover
  subst src
  have hAt : Wg1Tma.issueDst (t.block % 2) tile'.val + (576 * y + 4 * x + b) =
      Wg1Tma.issueDst (d.block % 2) (pos / 4) +
        (576 * (pos % 4) + 4 * ((off + k) / 4) + ((off + k) % 4)) := by omega
  obtain ⟨hSlot, hTile, hCol, hRow, hByte⟩ :=
    raw_address_match tile'.isLt tile.isLt hx hy hb (by omega) r.isLt (by omega) hAt
  rcases lt_trichotomy (t.block / 2) (d.block / 2) with hOld | hSame | hNew
  · right
    left
    have hWarp := RingRoleGeometry.of_trace hX (Frame.lt_of_get hX hEvent)
      (hs issuer (Frame.lt_of_get hX hEvent)).machine hTma
    obtain ⟨d', o, addr, hCurrent, hSite, hBlock, hCta, hDst, ho, hi, hn⟩ :=
      Wg2.published_gather_with_acquires tile hpre hX hs
        (fun tile he hk => actual_gather_acquired tile hpre hX hs hWarp hIssuer he hk) he hState hd
    obtain ⟨hCurrentLoc, val, hVal⟩ :=
      Wg2.published_gather_slot hpre hX hs hCurrent hSite ho hi hn r n
    have hSameLoc : o.spec.sharedBase.at (576 * r.val + n.val) = l := by
      rw [hDst]
      simp only [l, hLoc, Loc.at]
      congr 1
      have hRow : Wg1Tma.issueDst (d.block % 2) tile.val + 576 * r.val =
          Wg2.rawBase (d.block % 2) + Wg2.rawRowOff L g row.val := hRowAddr
      have hn : n.val = off + k := rfl
      omega
    let byteAcc : Acc := { loc := l, size := 1 }
    have hCurrentWrite : X.MemWrites current byteAcc [val] :=
      ⟨o, addr, val, ho, hi, hCurrentLoc.trans (congrArg some hSameLoc), hVal,
        rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hCurrentCover : byteAcc.Covers l := by
      simpa [byteAcc, Loc.at] using (Acc.covers_at (a := byteAcc) (k := 0) (show 0 < 1 by decide))
    obtain ⟨tag, hGet⟩ := hi
    change ByteCausality L X l (.async (issuer, i') (.write (.load x y b))) current
    rw [hNth] at hWrite ⊢
    exact .direct (actual_earlier_gather_before_issue tile' hpre hX hs hIssuer hCta hGet
      hCurrent hSite (by rwa [hBlock]) (by rwa [hBlock]) ⟨fp, true, hWrite.intent, hCover⟩
      ⟨byteAcc, true, hCurrentWrite.intent, hCurrentCover⟩)
  · left
    have hSameBlock : t.block = d.block := by omega
    have hEq : i' = i := by simpa only [hSameBlock, hTile] using hNth
    simp only [w, current, hEq, hCol, hRow, hByte, r]
  · exact .inr (.inr (.direct (actual_raw_access_before_reuse hpre hX hs
      hIssuer hIssuerCta he hEvent hAccess hState hTma hd hSite' hSlot.symm hNew hByteSpace hByteCta
      ⟨fp, true, hWrite.intent, hCover⟩)))

/-- The actual ready/free ring determines reads-from for every byte of a dequantizer load. -/
theorem gather_sources {cta issuer j off : Nat} {lane : Fin 128} {row : Fin 4} {d : Wg2.D}
    {e : Event} {a : Acc} {bs : List (Option Byte)} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hWarp : warpOf L issuer = 5)
    (hIssuer : Issuer P L X cta issuer) (he : X.get (consumer L cta lane, j) = some e)
    (hState : Frame.stateAt (Machine.code P L) X (consumer L cta lane) j = some (some (.wg2 d)))
    (hd : Wg2RawTrace.RawAccess d.site) (hRead : X.Reads (consumer L cta lane, j) a bs)
    (hLoc : a.loc = ⟨.shared, cta, L.sharedBase + Wg2.rawBase (d.block % 2) +
      Wg2.rawRowOff L (consumer L cta lane) row.val + off⟩) (hBound : off + a.size ≤ 528) :
    Wg2.GatherSources P L X (consumer L cta lane, j) issuer d.block row off a.size := by
  apply Wg2.gather_sources_with_acquires hpre hX hs
    (fun tile he hk => actual_gather_acquired tile hpre hX hs hWarp hIssuer he hk)
    he hState hd hRead hLoc hBound
  intro k hk w b values hWrite hCover
  have hSpace : (a.loc.at k).space = .shared := by simp [Loc.at, hLoc]
  rcases Wg2.raw_read_competing_kinds hX hWrite hCover hSpace with
    ⟨thread, rfl, hw⟩ | ⟨src, x, y, byte, rfl⟩
  · exfalso
    have hpos : Wg2.rawRow L (consumer L cta lane) row.val < 64 :=
      Wg2.rawRow_lt (L := L) (g := consumer L cta lane) (lr := row.val) row.isLt
    have hAddr : (a.loc.at k).addr =
        L.sharedBase + 131072 + 36864 * (d.block % 2) +
          576 * Wg2.rawRow L (consumer L cta lane) row.val + off + k := by
      simp only [Loc.at, hLoc, Wg2.rawBase, Wg2.rawBufBytes, Wg2.rawRowOff, Wg2.rawRowStride]
      omega
    exact MachineTracking.no_actual_ordinary_raw_write hpre hX hs hw hCover hSpace
      (by rw [hAddr]; omega) (by rw [hAddr]; omega)
  · obtain ⟨tag, hGet⟩ := hRead
    have heq := Option.some.inj (he.symm.trans hGet)
    have hAccess : e.acc.isSome = true := by rw [heq]; rfl
    exact tensor_write_order hpre hX hs hIssuer he hAccess hState hd hLoc hBound
      k hk src x y byte b values hWrite hCover

/-- The active TMA issuer supplies the current generation of every actual dequantizer load. -/
theorem actual_dequant_load_sources {g i : Nat} {d : Wg2.D} {e : Event} {u : TState}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hf : (Machine.machine P L g).Fired (some (.wg2 d)) e (some u)) :
    ∃ issuer < L.threads, ctaOf L issuer = ctaOf L g ∧
      (∀ row scale, d.site = .scale row scale →
        Wg2.GatherSources P L X (g, i) issuer d.block row (512 + 4 * scale.val) 4) ∧
      (∀ row word, d.site = .raw row word →
        Wg2.GatherSources P L X (g, i) issuer d.block row (Wg2.elemByte L g word.val 0) 8) := by
  let cta := ctaOf L g
  have hg := Frame.lt_of_get hX he
  have hcta : cta < L.grid := NamedBar.cta_lt hg
  have hMachine (t : Nat) (h : t < L.threads) := (hs t h).machine
  have hGroup : wgOf L g = 2 := RingRoleGeometry.of_trace hX hg (hMachine g hg) hState
  obtain ⟨lane, hgEq⟩ := consumer_of_wg2 hpre (show ctaOf L g = cta from rfl) hGroup
  obtain ⟨producerLane, _, hIssuer⟩ := selected_tma (cta := cta) hpre hX hMachine
  let issuer := cta * L.block + 160 + producerLane.val
  have hIssuerLt : issuer < L.threads := by
    have hp := producerLane.isLt
    have hmul := Nat.mul_le_mul_right L.block (Nat.succ_le_of_lt hcta)
    simp only [Nat.succ_mul, hpre.block] at hmul
    simp only [issuer, Launch.threads, hpre.block]
    omega
  have hWarp : warpOf L issuer = 5 := by
    have hp := producerLane.isLt
    simp only [warpOf, tidOf_eq hpre, issuer, hpre.block]
    omega
  have hIssuerCta : ctaOf L issuer = cta := by
    have hp := producerLane.isLt
    simp only [ctaOf, issuer, hpre.block]
    omega
  have hinv : Wg2.Inv P L g d := (Exists.choose_spec hf).1.2
  have hf' : (Wg2.machine P L g).Fired (some (.inr d)) e (some u) := hf
  have read (a : Acc) (bs : List (Option Byte)) (h : e.kind = .rd a bs) :
      X.Reads (g, i) a bs := by
    obtain ⟨tag, kind⟩ := e
    cases h
    exact ⟨tag, he⟩
  refine ⟨issuer, hIssuerLt, hIssuerCta, ?_, ?_⟩
  · intro row scale hSite
    obtain ⟨a, bs, hKind, hLoc, hWidth⟩ := Wg2.fired_scale_event hpre hSite hf'
    have hRead := read a bs hKind
    rw [hinv.bufBlock] at hLoc
    change a.loc = ⟨.shared, cta, L.sharedBase + Wg2.rawBase (d.block % 2) +
      Wg2.scaleRowOff L g row.val + 4 * scale.val⟩ at hLoc
    have hLoc' : a.loc = ⟨.shared, cta, L.sharedBase + Wg2.rawBase (d.block % 2) +
        Wg2.rawRowOff L g row.val + (512 + 4 * scale.val)⟩ := by
      rw [hLoc]
      simp [Wg2.scaleRowOff, Wg2.quantBytes, Nat.add_assoc]
    rw [hgEq] at he hState hRead hLoc' ⊢
    have hBound : 512 + 4 * scale.val + a.size ≤ 528 := by
      have := scale.isLt
      omega
    simpa only [hWidth] using gather_sources hpre hX hs hWarp hIssuer he hState
      (.inl ⟨row, scale, hSite⟩) hRead hLoc' hBound
  · intro row word hSite
    obtain ⟨a, bs, hKind, hLoc, hWidth⟩ := Wg2.fired_raw_event hpre hSite hf'
    have hRead := read a bs hKind
    rw [hinv.bufBlock] at hLoc
    change a.loc = ⟨.shared, cta, L.sharedBase + Wg2.rawBase (d.block % 2) +
      Wg2.rawWordOff L g row.val word.val⟩ at hLoc
    have hLoc' : a.loc = ⟨.shared, cta, L.sharedBase + Wg2.rawBase (d.block % 2) +
        Wg2.rawRowOff L g row.val + Wg2.elemByte L g word.val 0⟩ := by
      rw [hLoc]
      simp [Wg2.rawWordOff, Wg2.elemByte, Wg2.rawBytesPerStep, Wg2.elemsPerStep,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [hgEq] at he hState hRead hLoc' ⊢
    have hBound : Wg2.elemByte L (consumer L cta lane) word.val 0 + a.size ≤ 528 := by
      have hlim := Wg2.elemByte_lt (L := L) (g := consumer L cta lane) (s := word.val) (e := 7)
        word.isLt (by decide)
      simp only [Wg2.elemByte, Wg2.quantBytes, Nat.add_zero] at hlim ⊢
      omega
    simpa only [hWidth] using gather_sources hpre hX hs hWarp hIssuer he hState
      (.inr ⟨row, word, hSite⟩) hRead hLoc' hBound

/-- Order an older gather before a new issue in a fully followed execution. -/
theorem earlier_gather_before_issue {cta issuer i block : Nat} {t : Wg1Tma.D} {e : Event} {l : Loc}
    {x y b x' y' b' : Nat} {current : Fin 16} (tile : Fin 16) (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (_hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) (hIssuer : Issuer P L X cta issuer)
    (hCta : ctaOf L issuer = cta) (he : X.get (issuer, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X issuer i = some (some (.tma t)))
    (hSite : t.site = .issue current) (hSlot : block % 2 = t.block % 2)
    (hOld : block / 2 < t.block / 2) :
    let m := ready L cta (rawSlot block)
    let old := (issuer, nthEv X (issuesTo m) issuer (16 * (block / 2) + tile.val))
    let part := Part.write (.load x y b)
    let next := Part.write (.load x' y' b')
    AsyncCovers X old part l → AsyncCovers X (issuer, i) next l →
    modelCausality L X l (.async old part) (.async (issuer, i) next) :=
  actual_earlier_gather_before_issue tile hpre hX (fun _ hg => Machine.code_sound hpre hg)
    hIssuer hCta he hState hSite hSlot hOld

/-- Locate the gather writing a raw byte in a fully followed execution. -/
theorem gather_at_write_location {cta issuer address : Nat} {j : EvId} {x y b : Nat} {l : Loc}
    {spec : TensorCopy.Spec} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (_ht : Frame.Tracked (Machine.code P L) X)
    (hIssuer : Issuer P L X cta issuer) (hlCta : l.cta = cta)
    (hRaw : L.sharedBase + 131072 ≤ l.addr ∧ l.addr < L.sharedBase + 204800)
    (hi : X.TensorIssue j address spec) (hWrite : TensorCopy.writeLoc spec x y b = some l) :
    ∃ (i : Nat) (t : Wg1Tma.D) (tile : Fin 16) (e : Event),
      j = (issuer, i) ∧ X.get (issuer, i) = some e ∧ ctaOf L issuer = cta ∧
      Frame.stateAt (Machine.code P L) X issuer i = some (some (.tma t)) ∧
      t.site = .issue tile ∧ x < 144 ∧ y < 4 ∧ b < 4 ∧
      l.addr = L.sharedBase + Wg1Tma.issueDst (t.block % 2) tile.val + (576 * y + 4 * x + b) ∧
      i = nthEv X (issuesTo (ready L cta (rawSlot t.block))) issuer
        (16 * (t.block / 2) + tile.val) :=
  actual_gather_at_write_location hpre hX hs hIssuer hlCta hRaw hi hWrite

/-- The exact decoded scale and quantized words are finite at every tracked dequantizer load. -/
theorem actual_finite_input {g i : Nat} {d : Wg2.D} {e : Event} {u : TState} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hf : (Machine.machine P L g).Fired (some (.wg2 d)) e (some u)) :
    Wg2.FiniteInput d e := by
  obtain ⟨issuer, hIssuer, _, hScale, hRaw⟩ := actual_dequant_load_sources hpre hX hs he hState hf
  exact Wg2.finiteInput_of_gather_sources hpre hX hs
    (Wg1Mma.batchOf_lt hpre hIssuer) (Wg1Mma.queryOf_lt hpre hIssuer) he hf hScale hRaw

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawReadback
