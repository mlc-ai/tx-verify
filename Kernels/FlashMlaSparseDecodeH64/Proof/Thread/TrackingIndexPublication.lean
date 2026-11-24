-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexTmaCoordinates
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingReadGuards

@[expose] public section

/-! # Coordinate publication at a followed TMA read -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.MbarRing PTX.AsyncCopy
open Protocol IndexRingThreads

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A followed coordinate read has a successful poll at the ordinal for its own ring use. -/
theorem coordinate_ready_poll {g i : Nat} {d : Wg1Tma.D} {e : Event} {k : Fin 16} {j : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hsite : d.site = .coord k j) :
    let ready := IndexRing.ready L (ctaOf L g) (indexSlot d.block)
    ∃ q tag parity acq scope, q < i ∧
      X.get (g, q) = some ⟨tag, .wait ready parity true acq scope⟩ ∧
      okPolls ready ((X.tr g).take q) = d.block / 4 := by
  have hcount :=
    (TmaIndexTrace.composed_coord_counts hpre (hs.produces (hX.thr g (Frame.lt_of_get hX he)))
      hd hsite).2
  change okPolls (IndexRing.ready L (ctaOf L g) (indexSlot d.block)) ((X.tr g).take i) =
    d.block / 4 + 1 at hcount
  exact UnitHandoff.exists_poll hcount.ge

/-- A selected producer's observed release at the expected ordinal exposes the actual
same-block coordinate store. Only the selected handoff is needed. -/
theorem coordinate_write_before_read {g i n q : Nat} {d : Wg1Tma.D} {e : Event}
    {k : Fin 16} {j : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hsite : d.site = .coord k j)
    (p : Fin 32) (hp : p.val = Wg1Tma.coordPos k.val j.val / 2)
    (hq : q < i) (rs ws : MbarScope)
    (hRelease : MbarRelease X (producerThread L (ctaOf L g) p, n)
      (IndexRing.ready L (ctaOf L g) (indexSlot d.block)) rs)
    (hUse : arrivals (IndexRing.ready L (ctaOf L g) (indexSlot d.block))
      ((X.tr (producerThread L (ctaOf L g) p)).take n) = d.block / 4)
    (hObserve : WaitObserves X (.thread (producerThread L (ctaOf L g) p, n)) (g, q)
      (IndexRing.ready L (ctaOf L g) (indexSlot d.block)) true ws)
    (hScopes : ScopesMeet L rs (producerThread L (ctaOf L g) p) ws g) :
    ∃ a bs w aw, e.kind = .rd a bs ∧ a.size = 4 ∧ a.loc = aw.loc ∧ aw.size = 4 ∧
      X.MemWrites (.thread w) aw (b32 (Wg1Tma.coordAt P L g d.block
        (Wg1Tma.coordPos k.val j.val))).toBytes ∧ baseCausality L X w (g, i) ∧
      ∃ (z : Wg1Index.D) (extra high : Bool),
        Frame.stateAt (Machine.code P L) X w.1 w.2 = some (some (.index z)) ∧
        z.site = .coord extra high ∧ z.block = d.block := by
  let pos := Wg1Tma.coordPos k.val j.val
  let cta := ctaOf L g
  let h := producerThread L cta p
  have hg := Frame.lt_of_get hX he
  have hgrid : cta < L.grid := NamedBar.cta_lt hg
  obtain ⟨_, hc, hwarp⟩ := producerThread_facts hpre hgrid p
  obtain ⟨tx, cnt, tag, hrelease⟩ := hRelease
  have hh := Frame.lt_of_get hX hrelease
  obtain ⟨⟨hc', z, hslot, ⟨extra, hz⟩, hst⟩, _⟩ :=
    IndexRing.publish_source_at_tracked_event hpre hX (hs h hh)
      (tracked_nonconsumer_warp hpre hX hs (.inr (.inr hwarp)) n) hrelease rfl
  have hcount := IndexRingTrace.composed_ready_counts hpre
    ((hs h hh).produces (hX.thr h hh)) hst hz
  change h / L.block = cta at hc'
  rw [hc', hslot] at hcount
  have hm : z.block % 4 = d.block % 4 := hslot
  have hcUse : z.block / 4 = d.block / 4 := hcount.1.symm.trans hUse
  have hb : z.block = d.block := by omega
  obtain ⟨_, hread⟩ := RingEvents.fired_of_trace hX (hs g hg) he hd
  obtain ⟨a, bs, hkind, ha, hloc⟩ := IndexCoordinateTrace.read_word hpre hsite hread
  let high : Bool := decide (pos % 2 = 1)
  have hhigh : (if high then 1 else 0) = pos % 2 := by
    unfold high
    have hlt := Nat.mod_lt pos (by decide : 0 < 2)
    by_cases hv : pos % 2 = 1
    · simp [hv]
    · simp [show pos % 2 = 0 by omega]
  obtain ⟨l, store, z', aw, bytes, hl, hstore, hstoreKind, hst', hb', hwriteSite⟩ :=
    IndexCoordinateTrace.writes_before_publish (high := high) (PTX.len_of_get hrelease).le hst hz
  obtain ⟨_, hwrite⟩ := RingEvents.fired_of_trace hX (hs h hh) hstore hst'
  obtain ⟨hbytes, hwidth, hwriteLoc⟩ :=
    IndexCoordinateTrace.written_word hpre hwriteSite hwrite hstoreKind
  rw [hb', hb, hhigh] at hbytes hwriteLoc
  have hlane : laneOf L h = pos / 2 := by
    rw [← hp]
    have hlt := p.isLt
    simp only [h, producerThread, laneOf, tidOf_eq hpre, hpre.block]
    omega
  rw [hlane, IndexTma.coord_same_cta hc, ← IndexTma.coordAt_eq_coordValue] at hbytes
  have hsame : a.loc = aw.loc := by
    rw [hloc, hwriteLoc, hc, hlane]
    change Loc.mk .shared cta (_ + 4 * pos) = Loc.mk .shared cta (_ + 8 * (pos / 2) + 4 * (pos % 2))
    congr 1
    omega
  have hw : X.MemWrites (.thread (h, l)) aw (b32 (Wg1Tma.coordAt P L g d.block pos)).toBytes := by
    obtain ⟨tag', kind⟩ := store
    change kind = _ at hstoreKind
    subst kind
    rw [hbytes] at hstore
    exact .inl ⟨tag', hstore⟩
  exact ⟨a, bs, (h, l), aw, hkind, ha, hsame, hwidth, hw,
    Staging.baseCausality_of_handoff (w := (g, q)) ⟨tx, cnt, tag, hrelease⟩ hObserve hScopes
      ⟨rfl, hl.le⟩ ⟨rfl, hq, PTX.len_of_get he⟩,
    z', extra, high, hst', hwriteSite, hb'.trans hb⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
