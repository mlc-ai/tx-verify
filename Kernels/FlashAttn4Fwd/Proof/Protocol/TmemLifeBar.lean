-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.TmemLife
public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemAllocHandshake
public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsGen
public import Kernels.FlashAttn4Fwd.Proof.Protocol.PReadyObj
public import Lemmas.Protocol.NamedBarMember
public import Lemmas.Tcgen05.TcExtend

@[expose] public section

/-! # Barrier 2 and the deallocation handshake

Barrier 2 is a named barrier of the warps 0-12 of each CTA with the operand 416 (`shape`,
`sources`: `TmemLifeFacts.bar2_warp`, `StatsFacts.bar_form`). From it:

* **Every member arrives** (`member`): once a thread of a CTA has passed its `bar.sync 2` of
  ordinal `o < 2`, every thread of warps 0-12 of the CTA has its barrier-2 event of ordinal `o`
  (`NamedBar.Sources.member_arrival_any`; a thread that exits has two such events before its
  exit, `TmemLifeFacts.exit_bar2`).
* **Barrier 2 orders** (`bar2_baseCausality`): what a thread did before its barrier-2 event of
  ordinal `o` happens before what a thread of its CTA does after its `bar.sync 2` of ordinal `o`
  (`NamedBar.Sources.arrive_sync_baseCausality`).
* **The `tcgen05` events precede the second generation** (`wait_lt`): a softmax or correction
  `tcgen05` event (a load, a store, a `wait::ld` or a `wait::st`) comes before the thread's
  barrier-2 event of ordinal 1.
* **The handshake** (`peer_chain`): a deallocation of a thread of CTA `c` follows its successful
  poll of `c`'s handshake barrier, which observes the release arrival of lane 0 of warp 12 of the
  other CTA (`TmemAlloc.observes`); that arrival follows the lane's `bar.sync 2` of ordinal 1
  (`TmemLifeFacts.hs_release`), and the arrival and the poll synchronize (MEM-MBAR-SYNCHRONIZES, at
  the cluster scope of the assumption `clusterMbar`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

namespace TmemLife

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Barrier 2's group: the warps 0-12 of a CTA, with the operand 416. -/
theorem shape (hpre : Pre P L mem0) : NamedBar.Shape L (some 416) (Finset.range 13) 2 where
  pos := by simp
  target := by simp [CtaBarrier.target]
  bound w hw := by
    rw [hpre.block]
    have := Finset.mem_range.mp hw
    omega
  id_lt := by decide

/-- The operand of a barrier-2 event is 416. -/
theorem bar2_cnt (hst : StatsFacts L X) {g i pc : Nat} {cnt : Option Nat} {m : BarMode}
    (hg : g < L.threads) (he : X.get (g, i) = some ⟨pc, .bar 2 cnt m⟩) : cnt = some 416 := by
  rcases hst.bar_form hg he with ⟨-, h⟩ | ⟨-, ⟨-, h, -⟩ | ⟨h8, -, h | h, -⟩⟩
  · exact h
  all_goals omega

/-- Barrier 2's arrivals are its group's. -/
theorem sources (hst : StatsFacts L X) (hl : TmemLifeFacts L X) :
    NamedBar.Sources L X (some 416) (Finset.range 13) 2 := by
  rintro ⟨g, i⟩ pc cnt ⟨m, he⟩ hg
  exact ⟨Finset.mem_range.mpr (hl.bar2_warp hg he), bar2_cnt hst hg he⟩

/-- **Every member arrives**: once a thread has passed its `bar.sync 2` of ordinal `o < 2`, every
thread of warps 0-12 of its CTA has its barrier-2 event of ordinal `o`. -/
theorem member (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hst : StatsFacts L X) (hl : TmemLifeFacts L X) {g b o after : Nat} (hs : Bar2Sync X g b o)
    (hba : b < after) (hal : after < (X.tr g).length) (ho : o < 2) {h : Nat}
    (hcta : ctaOf L h = ctaOf L g) (hw : warpOf L h < 13) :
    ∃ i pc m, X.get (h, i) = some ⟨pc, .bar 2 (some 416) m⟩ ∧ barOrd X h i 2 = o := by
  obtain ⟨pc, hget, hord⟩ := hs
  obtain ⟨i, pc', m, hi, hc⟩ := NamedBar.Sources.member_arrival_any hX (sources hst hl)
    (shape hpre) (f := (g, b)) hget (by dsimp only; omega) (g := h) hcta
    (Finset.mem_range.mpr hw) (fun ⟨j, pcx, hx⟩ => by
      have hh := Frame.lt_of_get hX hx
      have h2 := hl.exit_bar2 hh hw hx
      obtain ⟨y, pcy, cnt, my, -, hy, hyo⟩ :=
        Stats.exists_bar (X := X) (g := h) (x := j) (c := o) (id := 2) (by omega)
      rw [bar2_cnt hst hh hy] at hy
      exact ⟨y, pcy, my, hy, hyo.trans hord.symm⟩)
  exact ⟨i, pc', m, hi, hc.trans hord⟩

/-- **Barrier 2 orders**: what a thread did before its barrier-2 event of ordinal `o` happens
before what a thread of its CTA does after its `bar.sync 2` of ordinal `o`. -/
theorem bar2_baseCausality (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hst : StatsFacts L X) (hl : TmemLifeFacts L X) {h i pc g b o before after : Nat}
    {cnt : Option Nat} {m : BarMode} (hi : X.get (h, i) = some ⟨pc, .bar 2 cnt m⟩)
    (hio : barOrd X h i 2 = o) (hs : Bar2Sync X g b o) (hcta : ctaOf L h = ctaOf L g)
    (hbefore : before < i) (hba : b < after) (hal : after < (X.tr g).length) :
    baseCausality L X (h, before) (g, after) := by
  obtain ⟨pcb, hget, hord⟩ := hs
  exact NamedBar.Sources.arrive_sync_baseCausality hX (sources hst hl) (shape hpre)
    ⟨Frame.lt_of_get hX hi, Frame.lt_of_get hX hget, hcta⟩ hi hget (by omega)
    (hio.trans hord.symm) hbefore hba hal

/-- **The `tcgen05` events precede the second generation**: a softmax or correction `tcgen05`
event comes before the thread's barrier-2 event of ordinal 1. -/
theorem wait_lt (hl : TmemLifeFacts L X) {h k pc i pci : Nat} {wk : TcKind}
    {cnt : Option Nat} {m : BarMode} (hh : h < L.threads) (h12 : warpOf L h < 12)
    (hk : X.get (h, k) = some ⟨pc, .tc wk⟩)
    (hi : X.get (h, i) = some ⟨pci, .bar 2 cnt m⟩) (hio : barOrd X h i 2 = 1) : k < i := by
  have hw := hl.wait_bar2 hh h12 hk
  rcases Nat.lt_trichotomy k i with hlt | rfl | hgt
  · exact hlt
  · rw [hk] at hi
    cases hi
  · have := Stats.barOrd_lt hi hgt
    omega

/-- The CTA of lane 0 of warp 12 of CTA `c`. -/
theorem lane0_cta (hpre : Pre P L mem0) (c : Nat) : ctaOf L (TmemAlloc.lane0 L c) = c := by
  unfold ctaOf TmemAlloc.lane0
  rw [hpre.block]
  omega

/-- The warp of lane 0 of warp 12 of CTA `c`. -/
theorem lane0_warp (hpre : Pre P L mem0) (c : Nat) : warpOf L (TmemAlloc.lane0 L c) = 12 := by
  unfold warpOf TmemAlloc.lane0
  rw [hpre.block]
  omega

/-- **The handshake**: a deallocation of a thread of CTA `c` happens after an event, past its
`bar.sync 2` of ordinal 1, of lane 0 of warp 12 of the other CTA of the pair. -/
theorem peer_chain (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (htm : TmemFacts L X) (hl : TmemLifeFacts L X) {g k pc a n : Nat} {grp : CtaGroup}
    {dst : Option Loc} (hd : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩)
    (hi : TmemAlloc.HsInit L X (ctaOf L g)) :
    ∃ y b, Bar2Sync X (TmemAlloc.lane0 L (pairCta (ctaOf L g))) b 1 ∧ b < y ∧
      y < (X.tr (TmemAlloc.lane0 L (pairCta (ctaOf L g)))).length ∧
      baseCausality L X (TmemAlloc.lane0 L (pairCta (ctaOf L g)), y) (g, k) := by
  have hg := Frame.lt_of_get hX hd
  obtain ⟨w, hwk, pcw, p, hw⟩ := hl.dealloc_wait hg hd
  obtain ⟨-, -, rfl⟩ := htm.hs_wait hg hw rfl
  have hu := TmemAlloc.observes hpre hX htm hi hw (l := 0) (by decide)
  simp only [Nat.add_zero] at hu
  have hxl := update_thread_old hX.tma.2.2.1 hu
  dsimp only at hxl
  have hev : X.get (_, _) = some _ := List.getElem?_eq_getElem hxl
  obtain ⟨pcx, tx, cx, rel, sc, hx⟩ := TmemAlloc.get_arriveIdx hev
  rw [hx] at hev
  have hxg := Frame.lt_of_get hX hev
  obtain ⟨rfl, rfl, b, hby, hbs⟩ := hl.hs_release hxg hev
  have hlead : leadCta (ctaOf L (TmemAlloc.lane0 L (pairCta (ctaOf L g)))) =
      leadCta (ctaOf L g) := by
    rw [lane0_cta hpre]
    unfold leadCta pairCta
    omega
  refine ⟨_, b, hbs, hby, hxl, .single (.inr (.inr (.inl ⟨_, (g, w), _, .cluster, .cluster,
    ⟨tx, cx, pcx, hev⟩, ⟨⟨pcw, 0, hw⟩, hu⟩, ⟨Score.sameCluster_of_pair hpre hxg hg hlead,
      Score.sameCluster_of_pair hpre hg hxg hlead.symm⟩, rfl, hwk, len_of_get hd, rfl,
    le_refl _⟩)))⟩

end TmemLife

end
end PTX.Kernels.FlashAttn4Fwd.Proof
