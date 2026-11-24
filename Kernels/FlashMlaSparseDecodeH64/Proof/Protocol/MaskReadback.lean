-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexTmaReadback
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.CtaRings
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingAccessOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.IndexCoordinateTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Tracking
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.StageWriteClasses
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorSharedBounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingMaskWrites
import Lemmas.Order.OrderWaits

@[expose] public section

/-! # Validity-mask bytes of the active index ring use -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MaskReadback

open PTX PTX.Flow PTX.Proof PTX.MbarRing IndexRingThreads

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem lane_of_producer (hpre : Pre P L mem0) (cta : Nat) (p : Fin 32) :
    laneOf L (producerThread L cta p) = p.val := by
  have := p.isLt
  simp only [producerThread, laneOf, tidOf_eq hpre, hpre.block]
  omega

/-- The four byte stores of the current mask use follow the index producer ring and supply the
actual bytes returned to a softmax thread. -/
private theorem actual_mask_byte (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    {g i : Nat} {d : Wg0.D} {e : Event}
    (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ MachineTracking.Dismisses P L X t)
    (he : X.get (g, i) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .maskRead) {a : Acc} {bs : List (Option Byte)}
    (hk : e.kind = .rd a bs) (k : Fin 4) :
    let quad := 4 * Wg0.half L g + k.val
    let p : Fin 32 := ⟨4 * (quad % 8), by have := Nat.mod_lt quad (by decide : 0 < 8); omega⟩
    bs[k.val]? = some (some
      (.bits 8 (BitVec.ofNat 64
        (Wg1Index.quadByte P L (producerThread L (ctaOf L g) p) d.block (4 * quad))), 0)) := by
  dsimp only
  let cta := ctaOf L g
  have hSound (h : Nat) (hh : h < L.threads) := (hs h hh).machine
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX (hSound g hg) he hst
  obtain ⟨a', data, hk', hsize, hhalf, hloc⟩ :=
    Wg0.composed_mask_footprint hpre hsite hf ⟨a, bs, hk⟩
  obtain ⟨rfl, rfl⟩ := Kind.rd.inj (hk.symm.trans hk')
  let quad := 4 * Wg0.half L g + k.val
  have hklt := k.isLt
  have hquad : quad < 8 := by unfold quad; omega
  let p : Fin 32 := ⟨4 * quad, by omega⟩
  let h := producerThread L cta p
  have hLane : laneOf L h = 4 * quad := lane_of_producer hpre cta p
  have hGrid : cta < L.grid := NamedBar.cta_lt hg
  have ⟨hh, hCtaProducer, _⟩ := producerThread_facts hpre hGrid p
  let byte := a.loc.at k.val
  have hAddr : byte = ⟨.shared, cta, L.sharedBase + 221696 + 8 * (d.block % 4) + quad⟩ := by
    rw [show byte = a.loc.at k.val from rfl, hloc]
    simp [Loc.at, Wg0.shLoc, Wg0.maskBase, Wg0.maskStride, quad, cta, Nat.add_assoc]
  have hShared : byte.space = .shared := by rw [hAddr]
  have hSlotLt := Nat.mod_lt d.block (by decide : 0 < 4)
  have hlo : L.sharedBase + 221696 ≤ byte.addr := by
    rw [hAddr]; change L.sharedBase + 221696 ≤ L.sharedBase + 221696 + _ + _; omega
  have hhi : byte.addr < L.sharedBase + 221728 := by
    rw [hAddr]; change L.sharedBase + 221696 + 8 * (d.block % 4) + quad < _; omega
  obtain ⟨n, release, r, extra, hRelease, hState, hReady, hBlock, hBefore⟩ :=
    MachineTracking.mask_publication hpre hX hs he hst hsite hPrior p
  obtain ⟨_, hReadyFire⟩ := RingEvents.fired_of_trace hX (hSound h hh) hRelease hState
  have hRelKind := RingEvents.validReady_arrive hpre hReady hReadyFire
  obtain ⟨t, wr, s, aw, raw, htN, hGet, hKind, hStore, hStoreBlock, hValid⟩ :=
    IndexCoordinateTrace.valid_before_publish (PTX.len_of_get hRelease).le hState hReady
      (by rw [hLane]; omega)
  obtain ⟨_, hFire⟩ := RingEvents.fired_of_trace hX (hSound h hh) hGet hStore
  obtain ⟨hWidth, hLoc⟩ := IndexCoordinateTrace.written_validity hpre hValid hFire hKind
  have hFoot : aw.loc = byte := by
    rw [hLoc, hAddr, hStoreBlock, hBlock, hCtaProducer, hLane]
    congr 1
    omega
  have hCovered : aw.Covers byte := by
    rw [← hFoot]
    exact ⟨rfl, rfl, Nat.le_refl _, by omega⟩
  have hWr : X.Writes (h, t) aw raw := by
    obtain ⟨tag, _⟩ := wr
    cases hKind
    exact ⟨tag, hGet⟩
  have hPublished : baseCausality L X (h, t) (g, i) := by
    have hr : (X.get (h, n)).bind Event.acc = none := by
      rw [hRelease, Option.bind_some]
      obtain ⟨tag, kind⟩ := release
      change kind = _ at hRelKind
      subst kind
      rfl
    have hp : baseCausality L X (h, t) (h, n) :=
      .single (.inl (po_of_not_access rfl htN (PTX.len_of_get hRelease) hr))
    exact hp.trans hBefore
  have hMemRead : X.MemReads (.thread (g, i)) a bs := by
    obtain ⟨tag, _⟩ := e
    cases hk
    exact .inl ⟨tag, he⟩
  have hOffset : k.val < a.size := by omega
  have hHidden := hX.hidden (.thread (g, i)) a bs k.val (.thread (h, t)) aw raw
    hMemRead hOffset (.inl hWr) hCovered (.direct (.inl hPublished))
  have hRf := (hX.rf (.thread (g, i)) a bs hMemRead).2 k.val hOffset
  cases hSrc : X.rf (.thread (g, i)) k.val with
  | none => rw [hSrc] at hHidden; exact hHidden.elim
  | some src =>
    rw [hSrc] at hRf hHidden
    obtain ⟨fp, data, hData, hCover, hVal⟩ := hRf
    obtain ⟨producer, j, event, ds, xtra, q, rfl, hw, hKind, hAt, hSite, hInv, hQLane,
      hFp, hLoc', _, hRaw⟩ :=
      MachineTracking.actual_validity_source hpre hX hs hData hCover hShared hlo hhi
    have hProducer := Frame.lt_of_get hX hw
    have hCta : ctaOf L producer = cta := congrArg Loc.cta (hLoc'.symm.trans hAddr)
    have hWarp : warpOf L producer = 7 :=
      RingRoleGeometry.of_trace hX hProducer (hSound producer hProducer) hAt
    obtain ⟨srcLane, hProd⟩ := producer_of_warp hpre hCta hWarp
    have hPhase := hInv.phase_block (by rw [hSite]; intro hz; cases hz)
    have hMatch := congrArg Loc.addr (hLoc'.symm.trans hAddr)
    change L.sharedBase + 221696 + 8 * ds.phase + q.val =
      L.sharedBase + 221696 + 8 * (d.block % 4) + quad at hMatch
    have hq := q.isLt
    have hSlot : ds.block % 4 = d.block % 4 := by omega
    have hQuad : q.val = quad := by omega
    have hSource : producer = h := by
      rw [hProd]
      congr 1
      apply Fin.ext
      rw [hProd, lane_of_producer hpre] at hQLane
      rw [hQLane, hQuad]
    rcases lt_trichotomy (ds.block / 4) (d.block / 4) with hEarlier | hSame | hLater
    · exfalso
      let m := IndexRing.ready L cta (indexSlot d.block)
      have hcnt := (IndexRingTrace.composed_write_counts hpre
        ((hSound producer hProducer).produces (hX.thr _ hProducer)) hAt (.inr ⟨xtra, hSite⟩)).1
      have hcnt' := (IndexRingTrace.composed_write_counts hpre
        ((hSound h hh).produces (hX.thr _ hh)) hStore (.inr ⟨extra, hValid⟩)).1
      have hObj : indexSlot ds.block = indexSlot d.block := Fin.ext hSlot
      change arrivals (IndexRing.ready L (ctaOf L producer) (indexSlot ds.block))
        ((X.tr producer).take j) = ds.block / 4 at hcnt
      change arrivals (IndexRing.ready L (ctaOf L h) (indexSlot s.block))
        ((X.tr h).take t) = s.block / 4 at hcnt'
      rw [hCta, hObj, hSource] at hcnt
      rw [hCtaProducer, hStoreBlock, hBlock] at hcnt'
      have hord : arrivals m ((X.tr h).take j) < arrivals m ((X.tr h).take t) := by
        change arrivals m ((X.tr h).take j) = _ at hcnt
        change arrivals m ((X.tr h).take t) = _ at hcnt'
        omega
      rw [hSource] at hw hHidden
      exact hHidden (.direct (.inl (IndexTma.prior_coordinate_write hw hGet hKind hord)))
    · have hEq : ds.block = d.block := by omega
      have hSub : byte.addr - fp.loc.addr = 0 := by rw [hFp]; exact Nat.sub_self _
      change bs[k.val]? = some (data[byte.addr - fp.loc.addr]?) at hVal
      rw [hSub, hRaw, hEq, hQuad, hSource] at hVal
      change bs[k.val]? = some (some
        (.bits 8 (BitVec.ofNat 64 (Wg1Index.quadByte P L h d.block (4 * quad))), 0)) at hVal
      simpa only [quad, Nat.mod_eq_of_lt hquad] using hVal
    · exfalso
      exact hX.noFuture _ a bs k.val _ hMemRead hOffset hSrc (.direct (.inl
        (MachineTracking.mask_before_future_producer hpre hX hs he hst hsite hw hAt
          (.inr (.inr ⟨xtra, hSite⟩)) hCta hSlot hLater)))

private theorem rebuild_four_integers (a b c d : BitVec 64) :
    rebuild 3 [some (.bits 8 a, 0), some (.bits 8 b, 0), some (.bits 8 c, 0),
      some (.bits 8 d, 0)] = .ok (.bits 32 (BitVec.ofNat 64
        (a.toNat % 256 + 256 *
          (b.toNat % 256 + 256 * (c.toNat % 256 + 256 * (d.toNat % 256)))))) := by
  simp [rebuild, rebuild.halves, rebuildBits, littleEndianBits, intByte, byteBits,
    Value.bytes, Value.bitPattern, Bind.bind, Pure.pure, Except.pure]

/-- Each of the four quad leaders contributes one byte to the actual mask load. -/
def maskByte (P : Params) (L : Launch) (g block : Nat) (k : Fin 4) : Nat :=
  let quad := 4 * Wg0.half L g + k.val
  let p : Fin 32 := ⟨4 * (quad % 8), by
    have := Nat.mod_lt quad (by decide : 0 < 8)
    omega⟩
  Wg1Index.quadByte P L (producerThread L (ctaOf L g) p) block (4 * quad)

/-- The mask word as read by the softmax lane, in little-endian order. -/
def maskWord (P : Params) (L : Launch) (g block : Nat) : BitVec 64 :=
  let byte (k : Fin 4) := maskByte P L g block k
  BitVec.ofNat 64 (byte 0 + 256 * (byte 1 + 256 * (byte 2 + 256 * byte 3)))

/-- Four published validity bytes decode to their little-endian mask word. -/
theorem rebuild_of_mask_bytes {g block : Nat} {bs : List (Option Byte)}
    (hLen : bs.length = 4)
    (hByte : ∀ k : Fin 4, bs[k.val]? = some (some
      (.bits 8 (BitVec.ofNat 64 (maskByte P L g block k)), 0))) :
    rebuild 3 bs = .ok (.bits 32 (maskWord P L g block)) := by
  let wordFor (k : Fin 4) := BitVec.ofNat 64 (maskByte P L g block k)
  let actual : List (Option Byte) :=
    [some (.bits 8 (wordFor 0), 0), some (.bits 8 (wordFor 1), 0),
      some (.bits 8 (wordFor 2), 0), some (.bits 8 (wordFor 3), 0)]
  have hEq : bs = actual := by
    apply List.ext_getElem?
    intro k
    by_cases hb : k < 4
    · interval_cases k
      · exact hByte 0
      · exact hByte 1
      · exact hByte 2
      · exact hByte 3
    · rw [List.getElem?_eq_none (by omega : bs.length ≤ k),
        List.getElem?_eq_none (by change 4 ≤ k; omega)]
  rw [hEq]
  have hbyte (k : Fin 4) : (wordFor k).toNat % 256 = maskByte P L g block k := by
    have h := Wg1Index.quadByte_lt P L
    have hSmall : maskByte P L g block k < 256 := h _ _ _
    simp only [wordFor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show
      maskByte P L g block k < 2 ^ 64 from hSmall.trans (by decide)),
      Nat.mod_eq_of_lt hSmall]
  rw [show actual = _ from rfl, rebuild_four_integers, hbyte, hbyte, hbyte, hbyte]
  rfl

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
include hpre hX hs

/-- The actual returned mask uses the current generation of the validity ring. -/
theorem rebuild_actual_mask {g i : Nat} {d : Wg0.D} {e : Event} (he : X.get (g, i) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .maskRead)
    (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ MachineTracking.Dismisses P L X t) {a : Acc}
    {bs : List (Option Byte)} (hk : e.kind = .rd a bs) :
    rebuild 3 bs = .ok (.bits 32 (maskWord P L g d.block)) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hst
  obtain ⟨a', _, hk', hSize, _⟩ := Wg0.composed_mask_footprint hpre hsite hf ⟨a, bs, hk⟩
  have hEq := (Kind.rd.inj (hk.symm.trans hk')).1
  have hRead : X.MemReads (.thread (g, i)) a bs := by
    obtain ⟨tag, _⟩ := e
    cases hk
    exact .inl ⟨tag, he⟩
  have hLen := (hX.rf _ a bs hRead).1.trans (hEq ▸ hSize)
  exact rebuild_of_mask_bytes hLen (actual_mask_byte hpre hX hs hPrior he hst hsite hk)


/-- The actual mask read rebuilds the word published by the four quad leaders of its slot. -/
theorem rebuild_mask_exact (ht : Frame.Tracked (Machine.code P L) X) {g i : Nat} {d : Wg0.D}
    {e : Event} (he : X.get (g, i) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .maskRead) {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .rd a bs) :
    rebuild 3 bs = .ok (.bits 32 (maskWord P L g d.block)) := by
  apply rebuild_actual_mask hpre hX hs he hst hsite ?_ hk
  rintro ⟨t, j⟩ _ ⟨z, f, hf, hState, hNext⟩
  have hAfter := Frame.stateAt_succ (C := Machine.code P L) hf
  rw [hState] at hAfter
  exact ht t (j + 1) (Frame.lt_of_get hX hf) (hAfter.trans hNext)

private theorem next_of_mask_word {g i : Nat} {d : Wg0.D} {e : Event} (he : X.get (g, i) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .maskRead) (hScores : Wg0.exchangeReady d = true)
    (hWord : ∀ a bs, e.kind = .rd a bs → ∃ w, rebuild 3 bs = .ok (.bits 32 w)) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hst
  cases o with
  | none => simp [Wg0.composed_ending_next hf]
  | some u =>
    obtain ⟨_, hn, _, _⟩ := Wg0.composed_mask_next hpre hsite hf hScores hWord
    rw [hn]
    intro h
    cases h

/-- The actual QK and mask data preserve tracking using only causally prior tracking. -/
theorem next_of_actual_scores {g i : Nat} {d : Wg0.D} {e : Event} (he : X.get (g, i) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .maskRead)
    (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ MachineTracking.Dismisses P L X t)
    (hScores : Wg0.exchangeReady d = true) :
    Machine.next P L g (.wg0 d) e ≠ some none :=
  next_of_mask_word hpre hX hs he hst hsite hScores
    (fun _ _ hk => ⟨_, rebuild_actual_mask hpre hX hs he hst hsite hPrior hk⟩)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MaskReadback
