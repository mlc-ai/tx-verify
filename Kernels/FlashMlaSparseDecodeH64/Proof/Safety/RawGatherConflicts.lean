-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawReadback
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorSharedBounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.CtaRings
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.OrdinaryReadWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Events
import Lemmas.TensorStore.StoreWrite

@[expose] public section

/-! # Conflicting raw TMA writes and dequantizer loads use the ready/free ring -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.RawGatherConflicts

open PTX PTX.Flow AsyncCopy MbarRing Protocol RawRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem write_location {i : EvId} {x y b : Nat} {a : Acc} {l : Loc}
    (hi : X.Intent (.async i (.write (.load x y b))) a true) (ha : a.Covers l) :
    ∃ address spec, X.TensorIssue i address spec ∧ TensorCopy.writeLoc spec x y b = some l := by
  obtain ⟨_, spec, address, hIssue, hLoc, hSize⟩ := hi
  rw [Acc.loc_of_one ha hSize] at hLoc
  exact ⟨address, spec, hIssue, hLoc⟩

private theorem byte_in_gather_slot {buf : Nat} {tile : Fin 16} {x y b : Nat} {l : Loc}
    (hx : x < 144) (hy : y < 4) (hb : b < 4)
    (hl : l.addr = L.sharedBase + Wg1Tma.issueDst buf tile.val + (576 * y + 4 * x + b)) :
    L.sharedBase + Wg2.rawBase buf ≤ l.addr ∧
      l.addr < L.sharedBase + Wg2.rawBase buf + Wg2.rawBufBytes := by
  have hTile := tile.isLt
  simp only [hl, Wg1Tma.issueDst, Wg1Tma.rawBase, Wg2.rawBase, Wg2.rawBufBytes]
  omega

private theorem same_raw_slot {l : Loc} {a b : Nat}
    (ha : L.sharedBase + Wg2.rawBase a ≤ l.addr ∧
      l.addr < L.sharedBase + Wg2.rawBase a + Wg2.rawBufBytes)
    (hb : L.sharedBase + Wg2.rawBase b ≤ l.addr ∧
      l.addr < L.sharedBase + Wg2.rawBase b + Wg2.rawBufBytes) : a = b := by
  simp only [Wg2.rawBase, Wg2.rawBufBytes] at ha hb
  omega

/-- Each covered byte of an actual scale/raw read belongs to the active raw buffer. -/
theorem byte_in_read_slot {g j : Nat} {d : Wg2.D} {a : Acc} {values : List (Option Byte)} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hr : X.Reads (g, j) a values)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 d)))
    (hSite : Wg2RawTrace.RawAccess d.site) (ha : a.Covers l) :
    l.space = .shared ∧ l.cta = ctaOf L g ∧
      L.sharedBase + Wg2.rawBase (d.block % 2) ≤ l.addr ∧
      l.addr < L.sharedBase + Wg2.rawBase (d.block % 2) + Wg2.rawBufBytes := by
  obtain ⟨tag, he⟩ := hr
  obtain ⟨u, hf⟩ := (Frame.trace hs hX (Frame.lt_of_get hX he)).fired_at he hd
  cases u with
  | none =>
    obtain ⟨_, _, hfire⟩ := hf
    rcases fires_none_ends hfire with ⟨_, h⟩ | h <;> cases h
  | some u =>
    have hFire : (Wg2.machine P L g).Fired (some (.inr d)) ⟨tag, .rd a values⟩ (some u) := hf
    have hInv : Wg2.Inv P L g d := hFire.choose_spec.1.2
    have hIn {off : Nat} (hLoc : a.loc = ⟨.shared, ctaOf L g,
        L.sharedBase + Wg2.rawBase (d.block % 2) + off⟩)
        (hSize : off + a.size ≤ Wg2.rawBufBytes) :
        l.space = .shared ∧ l.cta = ctaOf L g ∧
          L.sharedBase + Wg2.rawBase (d.block % 2) ≤ l.addr ∧
          l.addr < L.sharedBase + Wg2.rawBase (d.block % 2) + Wg2.rawBufBytes := by
      obtain ⟨hSpace, hCta, hLo, hHi⟩ := ha
      rw [hLoc] at hSpace hCta hLo hHi
      change L.sharedBase + Wg2.rawBase (d.block % 2) + off ≤ l.addr at hLo
      change l.addr < L.sharedBase + Wg2.rawBase (d.block % 2) + off + a.size at hHi
      exact ⟨hSpace, hCta, by omega, by omega⟩
    rcases hSite with ⟨row, scale, hSite⟩ | ⟨row, word, hSite⟩
    · obtain ⟨_, _, hKind, hLoc, hSize⟩ := Wg2.fired_scale_event hpre hSite hFire
      obtain rfl := (Kind.rd.inj hKind).1
      rw [hInv.bufBlock, Nat.add_assoc (L.sharedBase + Wg2.rawBase (d.block % 2))] at hLoc
      apply hIn hLoc
      have hBound := Wg2.scaleRow_fit (L := L) (g := g) row.isLt
      have hScale := scale.isLt
      simp only [Wg2.scaleLoadBytes, hSize] at hBound ⊢
      omega
    · obtain ⟨_, _, hKind, hLoc, hSize⟩ := Wg2.fired_raw_event hpre hSite hFire
      obtain rfl := (Kind.rd.inj hKind).1
      rw [hInv.bufBlock] at hLoc
      exact hIn hLoc (by rw [hSize]; exact Wg2.rawWord_fit (L := L) (g := g) row.isLt word.isLt)

/-- An actual WG2 scale/raw read and an overlapping raw TMA write have order in either
direction. The TMA endpoint needs only its issue footprint. -/
theorem read_write_ordered {g j : Nat} {d : Wg2.D} {i : EvId} {x y b : Nat}
    {a fp : Acc} {values : List (Option Byte)} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hr : X.Reads (g, j) a values)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 d)))
    (hSite : Wg2RawTrace.RawAccess d.site)
    (hw : X.Intent (.async i (.write (.load x y b))) fp true)
    (ha : a.Covers l) (hf : fp.Covers l) :
    ByteCausality L X l (.async i (.write (.load x y b))) (.thread (g, j)) ∨
      ByteCausality L X l (.thread (g, j)) (.async i (.write (.load x y b))) := by
  let cta := ctaOf L g
  have hMachine (s : Nat) (hs' : s < L.threads) := (hs s hs').machine
  obtain ⟨hSh, hCta, hlo, hhi⟩ := byte_in_read_slot hpre hX hs hr hd hSite ha
  have hRaw : TensorSharedBounds.RawWindow L l := by
    have hBuf : d.block % 2 < 2 := Nat.mod_lt _ (by decide)
    simp only [Wg2.rawBase, Wg2.rawBufBytes] at hlo hhi
    exact ⟨by omega, by omega⟩
  have hg := Frame.lt_of_get hX hr.choose_spec
  have hwg : wgOf L g = 2 := RingRoleGeometry.of_trace hX hg (hMachine g hg) hd
  obtain ⟨lane, hgEq⟩ := consumer_of_wg2 hpre (show ctaOf L g = cta from rfl) hwg
  obtain ⟨producerLane, _, hIssuer⟩ := selected_tma (cta := cta) hpre hX hMachine
  let issuer := cta * L.block + 160 + producerLane.val
  obtain ⟨address, spec, hIssue, hWrite⟩ := write_location hw hf
  obtain ⟨k, t, tile, e, rfl, he, hProducerCta, hState, hSiteT,
    hx, hy, hb, hAddr, hNth⟩ :=
    RawReadback.gather_at_write_location hpre hX hs ht hIssuer hCta hRaw hIssue hWrite
  have hSlot : d.block % 2 = t.block % 2 :=
    same_raw_slot ⟨hlo, hhi⟩ (byte_in_gather_slot hx hy hb hAddr)
  obtain ⟨readTag, hReaderEq⟩ := hr
  rw [hgEq] at hReaderEq hd ⊢
  have hAsync : AsyncCovers X (issuer, k) (.write (.load x y b)) l := ⟨fp, true, hw, hf⟩
  by_cases hLater : d.block / 2 < t.block / 2
  · exact .inr (.direct (raw_access_before_reuse hpre hX hMachine ht hIssuer
      hProducerCta hReaderEq he hd hState hSite hSiteT hSlot hLater hSh hCta hAsync))
  · have hOld : t.block / 2 ≤ d.block / 2 := by omega
    have hOrder := gather_at_generation_before_raw_access (l := l) (generation := t.block / 2)
      (row := x) (col := y) (byte := b) tile hpre hX hMachine ht hIssuer hProducerCta
      hReaderEq hd hSite hOld
    change AsyncCovers X (issuer, nthEv X (issuesTo (ready L cta (rawSlot d.block))) issuer
        (16 * (t.block / 2) + tile.val)) (.write (.load x y b)) l →
      modelCausality L X l (.async (issuer, nthEv X (issuesTo (ready L cta (rawSlot d.block)))
        issuer (16 * (t.block / 2) + tile.val)) (.write (.load x y b)))
        (.thread (consumer L cta lane, j)) at hOrder
    have hSlotEq : rawSlot d.block = rawSlot t.block := Fin.ext hSlot
    rw [hSlotEq, ← hNth] at hOrder
    exact .inl (.direct (hOrder hAsync))

/-- Any two distinct overlapping raw TMA write intents are ordered, including a pending
write of the later generation. -/
theorem writes_ordered {i j : EvId} {x y b x' y' b' : Nat} {a fp : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.Intent (.async i (.write (.load x y b))) a true)
    (hj : X.Intent (.async j (.write (.load x' y' b'))) fp true)
    (hne : Ref.async i (.write (.load x y b)) ≠ .async j (.write (.load x' y' b')))
    (ha : a.Covers l) (hf : fp.Covers l) (hRaw : TensorSharedBounds.RawWindow L l) :
    ByteCausality L X l (.async i (.write (.load x y b))) (.async j (.write (.load x' y' b'))) ∨
    ByteCausality L X l (.async j (.write (.load x' y' b'))) (.async i (.write (.load x y b))) := by
  let cta := l.cta
  have hMachine (s : Nat) (hs' : s < L.threads) := (hs s hs').machine
  obtain ⟨producerLane, _, hIssuer⟩ := selected_tma (cta := cta) hpre hX hMachine
  let issuer := cta * L.block + 160 + producerLane.val
  obtain ⟨_, _, hIssue, hWrite⟩ := write_location hi ha
  obtain ⟨_, _, hIssue', hWrite'⟩ := write_location hj hf
  obtain ⟨k, t, tile, e, rfl, he, hCta, hState, hSite, hx, hy, hb, hAddr, hNth⟩ :=
    RawReadback.gather_at_write_location hpre hX hs ht hIssuer rfl hRaw hIssue hWrite
  obtain ⟨k', t', tile', e', rfl, he', hCta', hState', hSite', hx', hy', hb',
      hAddr', hNth'⟩ :=
    RawReadback.gather_at_write_location hpre hX hs ht hIssuer rfl hRaw hIssue' hWrite'
  have hSameByte : Wg1Tma.issueDst (t.block % 2) tile.val + (576 * y + 4 * x + b) =
      Wg1Tma.issueDst (t'.block % 2) tile'.val + (576 * y' + 4 * x' + b') := by omega
  obtain ⟨hSlot, hTile, hXeq, hYeq, hBeq⟩ :=
    RawReadback.raw_address_match tile.isLt tile'.isLt hx hy hb hx' hy' hb' hSameByte
  have hA : AsyncCovers X (issuer, k) (.write (.load x y b)) l := ⟨a, true, hi, ha⟩
  have hB : AsyncCovers X (issuer, k') (.write (.load x' y' b')) l := ⟨fp, true, hj, hf⟩
  rcases lt_trichotomy (t.block / 2) (t'.block / 2) with hLess | hEqual | hGreater
  · rw [hNth] at hA ⊢
    exact .inl (.direct (RawReadback.earlier_gather_before_issue tile hpre hX hMachine
      ht hIssuer hCta' he' hState' hSite' hSlot hLess hA hB))
  · have hBlock : t.block = t'.block := by omega
    have hIndex : k = k' := by
      rw [hNth, hNth', hBlock, hTile]
    exact (hne (by rw [hIndex, hXeq, hYeq, hBeq])).elim
  · rw [hNth'] at hB ⊢
    exact .inr (.direct (RawReadback.earlier_gather_before_issue tile' hpre hX hMachine
      ht hIssuer hCta he hState hSite hSlot.symm hGreater hB hA))

/-- An actual ordinary read and a pending raw TMA write are ordered at every common byte. -/
theorem ordinary_read_ordered {r i : EvId} {x y b : Nat} {a fp : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hr : X.Intent (.thread r) a false) (hw : X.Intent (.async i (.write (.load x y b))) fp true)
    (ha : a.Covers l) (hf : fp.Covers l) (hRaw : TensorSharedBounds.RawWindow L l) :
    ByteCausality L X l (.async i (.write (.load x y b))) (.thread r) ∨
      ByteCausality L X l (.thread r) (.async i (.write (.load x y b))) := by
  have hNoRmw : ∀ tag access old bytes, X.get r ≠ some ⟨tag, .rmw access old bytes⟩ :=
    fun tag _ _ _ he => GlobalWrites.no_rmw hX ⟨tag, he⟩
  rcases (Execution.access_iff_of_not_rmw hNoRmw).mp hr with ⟨values, hRead, _⟩ | ⟨_, _, h⟩
  · obtain ⟨g, j⟩ := r
    obtain ⟨d, hd, hSite⟩ :=
      OrdinaryReadWindow.raw_read_of_cover hpre hX hs ht hRead ha hRaw.1 hRaw.2
    exact read_write_ordered hpre hX hs ht hRead hd hSite hw ha hf
  · cases h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.RawGatherConflicts
