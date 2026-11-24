-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.NcAllocationTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueAllocationTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteInput
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Lse
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Events
import Lemmas.Flow.NotRead
import Lemmas.Flow.OpPcsFast

public section

/-! # Ordinary reads are within their issuing CTA's shared window -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.OrdinaryReadWindow

open PTX PTX.Flow

private inductive SoftmaxReadSite : Wg0.Site → Prop
  | mask : SoftmaxReadSite .maskRead
  | peer (j : Fin 8) : SoftmaxReadSite (.peerRead j)
  | max : SoftmaxReadSite .maxRead
  | lse : SoftmaxReadSite .lseRead

private def readRole : Machine.ThreadD → Prop
  | .prologue s => s = .allocRead
  | .wg0 d => SoftmaxReadSite d.site
  | .tma d => ∃ k j, d.site = .coord k j
  | .wg2 d => (∃ r k, d.site = .raw r k) ∨ ∃ r j, d.site = .scale r j
  | _ => False

private def readSites : List Nat :=
  [Flow.load_0, Wg0.Site.maskRead.pc, Wg0.Site.maxRead.pc, Wg0.Site.lseRead.pc] ++
    (List.finRange 8).map (Wg0.Site.peerRead · |>.pc) ++
    (List.finRange 16).map (Wg1Tma.Site.coord · 0 |>.pc) ++
    (List.finRange 4).map (Wg2.Site.scale · 0 |>.pc) ++
    (List.finRange 4).flatMap (fun r => (List.finRange 8).map (Wg2.Site.raw r · |>.pc))

set_option maxRecDepth 100000 in
private theorem read_sites_cover :
    OpPcsFast kernel.code (fun op => readOp op && !isNcLoad op && !op.isLocal)
      readSites = true := by
  decide +kernel

local macro "exclude_read_site " h:ident : tactic => `(tactic| (
  exfalso
  revert $h
  first
  | decide
  | rename_i a; revert a; decide
  | rename_i a b; revert a b; decide
  | rename_i a b c; revert a b c; decide
  ))

private theorem read_role {P : Params} {L : Launch} {g : Nat} {d : Machine.ThreadD}
    (h : (Machine.code P L g).pc d ∈ readSites) : readRole d := by
  cases d with
  | prologue s =>
    change s.pc ∈ readSites at h
    change s = .allocRead
    cases s <;> first | rfl | exclude_read_site h
  | wg0 d =>
    change d.site.pc ∈ readSites at h
    change SoftmaxReadSite d.site
    generalize d.site = s at h ⊢
    clear d
    cases s with
    | maskRead => exact .mask
    | peerRead j => exact .peer j
    | maxRead => exact .max
    | lseRead => exact .lse
    | _ => all_goals exclude_read_site h
  | tma d =>
    change d.site.pc ∈ readSites at h
    change ∃ k j, d.site = .coord k j
    generalize d.site = s at h ⊢
    clear d
    cases s with
    | coord k j => exact ⟨k, j, rfl⟩
    | _ => all_goals exclude_read_site h
  | wg2 d =>
    change d.site.pc ∈ readSites at h
    change (∃ r k, d.site = .raw r k) ∨ ∃ r j, d.site = .scale r j
    generalize d.site = s at h ⊢
    clear d
    cases s with
    | raw r k => exact .inl ⟨r, k, rfl⟩
    | scale r j => exact .inr ⟨r, j, rfl⟩
    | _ => all_goals exclude_read_site h
  | head => exact absurd h (by change 1843 ∉ readSites; decide)
  | done => exact absurd h (by change 3611 ∉ readSites; decide)
  | idle d =>
    change d.pc ∈ readSites at h
    cases d <;> exclude_read_site h
  | mma d =>
    change False
    change d.site.pc ∈ readSites at h
    generalize d.site = s at h
    clear d
    cases s <;> exclude_read_site h
  | index d =>
    change False
    change d.site.pc ∈ readSites at h
    generalize d.site = s at h
    clear d
    cases s <;> exclude_read_site h

private def Fits (L : Launch) (g : Nat) (a : Acc) : Prop :=
  a.loc.space = .shared ∧ a.loc.cta = ctaOf L g ∧
    L.sharedBase + 131072 ≤ a.loc.addr ∧ a.loc.addr + a.size ≤ L.sharedBase + sharedBytes

private theorem fits_offset {L : Launch} {g off : Nat} {a : Acc}
    (hLoc : a.loc = ⟨.shared, ctaOf L g, L.sharedBase + off⟩)
    (hEnd : off + a.size ≤ sharedBytes) (hStart : 131072 ≤ off) : Fits L g a := by
  unfold Fits
  rw [hLoc]
  dsimp only
  exact ⟨rfl, rfl, by omega, by omega⟩

private def OutsideSoftmax (L : Launch) (a : Acc) : Prop :=
  a.loc.addr + a.size ≤ L.sharedBase + 204800 ∨ L.sharedBase + 221696 ≤ a.loc.addr

private def OutsideRaw (L : Launch) (a : Acc) : Prop :=
  a.loc.addr + a.size ≤ L.sharedBase + 131072 ∨ L.sharedBase + 204800 ≤ a.loc.addr

private def OutsideIndex (L : Launch) (a : Acc) : Prop :=
  a.loc.addr + a.size ≤ L.sharedBase + 221696 ∨ L.sharedBase + 222752 ≤ a.loc.addr

private def IndexReader (P : Params) (L : Launch) (X : Execution) (g i : Nat) : Prop :=
  (∃ d : Wg1Tma.D, Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)) ∧
    ∃ k j, d.site = .coord k j) ∨
  ∃ d : Wg0.D, Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) ∧
    d.site = .maskRead

private def SoftmaxReuseSite (L : Launch) (a : Acc) (d : Wg0.D) : Prop :=
  ((∃ j, d.site = .peerRead j) ∧ a.loc.addr + a.size ≤ L.sharedBase + 221184) ∨
    ((d.site = .maxRead ∨ d.site = .lseRead) ∧ L.sharedBase + 221184 ≤ a.loc.addr)

private theorem fit_wg0 {P : Params} {L : Launch} {mem0 : Mem0} {g tag : Nat}
    {a : Acc} {bs : List (Option Byte)} {d : Wg0.D} {t u : TState} {ins : Instr}
    (hpre : Pre P L mem0) (hRole : SoftmaxReadSite d.site) (hat : (Wg0.code P L g).AtD d t)
    (hinv : Wg0.Inv P L g d) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Wg0.asms L g t ins.op) ⟨tag, .rd a bs⟩ (some u)) :
    Fits L g a ∧ (OutsideSoftmax L a ∨ SoftmaxReuseSite L a d) ∧
      L.sharedBase + 204800 ≤ a.loc.addr ∧
      (a.loc.addr + a.size ≤ L.sharedBase + 221696 ∨ d.site = .maskRead) ∧
      a.loc.addr + a.size ≤ L.sharedBase + 222752 := by
  generalize hSite : d.site = s at hRole
  cases hRole with
  | mask =>
    obtain ⟨fp, _, hk, hl, hSize, _⟩ := Wg0.fires_maskRead hpre hSite hat hinv hc hf
    obtain rfl := (Kind.rd.inj hk).1
    simp only [hSite, Wg0.siteLoc, Option.some.injEq] at hl
    have hHalf := Wg0.halfLt hinv.warpLt
    refine ⟨fits_offset hl.symm ?_ ?_, .inl (.inr ?_), ?_, .inr rfl, ?_⟩
    · simp only [Wg0.maskBase, Wg0.maskStride, hSize, sharedBytes]
      omega
    · simp only [Wg0.maskBase]
      omega
    · rw [← hl]
      simp only [Wg0.shLoc, Wg0.maskBase]
      omega
    · rw [← hl]
      simp only [Wg0.shLoc, Wg0.maskBase]
      omega
    · rw [← hl, hSize]
      simp only [Wg0.shLoc, Wg0.maskBase, Wg0.maskStride]
      omega
  | peer j =>
    obtain ⟨fp, _, hk, hl, hSize, _⟩ := Wg0.fires_peerRead_at hpre hSite hinv hat hc hf
    obtain rfl := (Kind.rd.inj hk).1
    simp only [hSite, Wg0.siteLoc, Option.some.injEq] at hl
    have hSub := hinv.subLt
    simp only [hSite, Wg0.Site.elems] at hSub
    have hWarp := hinv.warpLt
    have hLane := hinv.laneLt
    have hJ := j.isLt
    have hEnd : a.loc.addr + a.size ≤ L.sharedBase + 221184 := by
      rw [← hl]
      simp only [Wg0.shLoc, hSize, hSite, Wg0.Site.elemBytes, Wg0.exchangeBase,
        Wg0.exchangeQuad, Wg0.exchangeChunk]
      omega
    refine ⟨fits_offset hl.symm ?_ ?_, .inr (.inl ⟨⟨j, hSite⟩, hEnd⟩), ?_,
      .inl (by omega), by omega⟩
    · simp only [hSize, hSite, Wg0.Site.elemBytes, Wg0.exchangeBase, Wg0.exchangeQuad,
        Wg0.exchangeChunk, sharedBytes]
      omega
    · simp only [Wg0.exchangeBase]
      omega
    · rw [← hl]
      simp only [Wg0.shLoc, Wg0.exchangeBase]
      omega
  | max | lse =>
    first
    | obtain ⟨fp, _, hk, hl, hSize, _, _⟩ := Wg0.fires_maxRead hpre hSite hat hinv hc hf
    | obtain ⟨fp, _, hk, hl, hSize, _, _⟩ := Wg0.fires_lseRead hpre hSite hat hinv hc hf
    obtain rfl := (Kind.rd.inj hk).1
    have hLane : (tidOf L g % 128 ^^^ 64) < 128 :=
      Nat.xor_lt_two_pow (n := 7) (Nat.mod_lt _ (by decide)) (by decide)
    refine ⟨fits_offset hl ?_ ?_, .inr (.inr ⟨?_, ?_⟩), ?_, .inl ?_, ?_⟩
    · simp only [hSize, Wg0.rowMaxBase, sharedBytes]
      omega
    · simp only [Wg0.rowMaxBase]
      omega
    · first | exact .inl hSite | exact .inr hSite
    · rw [hl]
      simp only [Wg0.shLoc, Wg0.rowMaxBase]
      omega
    · rw [hl]
      simp only [Wg0.shLoc, Wg0.rowMaxBase]
      omega
    · rw [hl, hSize]
      simp only [Wg0.shLoc, Wg0.rowMaxBase]
      omega
    · rw [hl, hSize]
      simp only [Wg0.shLoc, Wg0.rowMaxBase]
      omega

private theorem read_profile {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {a : Acc} {bs : List (Option Byte)}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hRead : X.Reads (g, i) a bs) :
    Fits L g a ∧ (OutsideSoftmax L a ∨
      ∃ d, Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) ∧
        SoftmaxReuseSite L a d) ∧
      (OutsideRaw L a ∨ ∃ d, Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)) ∧
        ((∃ r j, d.site = .scale r j) ∨ ∃ r j, d.site = .raw r j)) ∧
      (OutsideIndex L a ∨ IndexReader P L X g i) ∧
      (a.loc.addr + a.size ≤ L.sharedBase + 222752 ∨
        Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .allocRead))) := by
  obtain ⟨tag, he⟩ := hRead
  obtain ⟨d, hd⟩ := Frame.event_state hs hX ht he (by simp)
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ := Frame.fired_site hs hX he hd
  have hPc := fires_pc hf
  change tag = (Machine.code P L g).pc d at hPc
  have hCode : kernel.code[tag]? = some ins := hPc ▸ hc
  have hFired : Fires tag (eventTmpl Assumptions.all L g t ins.op) ⟨tag, .rd a bs⟩ o := hPc ▸ hf
  have hOp := fires_read_op hf rfl
  have hNotNc := NcInputTrace.ordinary_read_op_not_nc hCode hFired
  have hg := Frame.lt_of_get hX he
  obtain ⟨ins', hCode', hNonlocal, _⟩ := ((hs g hg).steps d).site hi
  obtain rfl := Option.some.inj (hc.symm.trans hCode')
  have hr : readRole d :=
    read_role (OpPcsFast.mem read_sites_cover hc (by simp [hOp, hNotNc, hNonlocal]))
  cases d with
  | prologue s =>
    change s = .allocRead at hr
    subst s
    obtain ⟨_, hk⟩ := PrologueAllocation.alloc_read hpre hX hs hd he
    obtain rfl := (Kind.rd.inj hk).1
    exact ⟨fits_offset rfl (by change 222752 + 4 ≤ sharedBytes; decide)
        (by decide),
      .inl (.inr (by change L.sharedBase + 221696 ≤ L.sharedBase + 222752; omega)),
      .inl (.inr (by change L.sharedBase + 204800 ≤ L.sharedBase + 222752; omega)),
      .inl (.inr (Nat.le_refl _)), .inr hd⟩
  | wg0 d =>
    cases o with
    | none => rcases fires_none_ends hf with ⟨_, h⟩ | h <;> cases h
    | some u =>
      obtain ⟨hFit, hSoft, hLo, hTail, hEnd⟩ := fit_wg0 hpre hr hat hi hc hf
      refine ⟨hFit, hSoft.imp id (fun h => ⟨d, hd, h⟩), .inl (.inr hLo), ?_, .inl hEnd⟩
      rcases hTail with hEnd | hMask
      · exact .inl (.inl hEnd)
      · exact .inr (.inr ⟨d, hd, hMask⟩)
  | tma d =>
    obtain ⟨k, j, hj⟩ := hr
    have hc' : kernel.code[(Wg1Tma.Site.coord k j).pc]? = some ins := by
      change kernel.code[d.site.pc]? = some ins at hc
      rwa [hj] at hc
    obtain rfl := Option.some.inj (hc'.symm.trans (Wg1Tma.coordLoad_code k j))
    obtain ⟨_, h, _⟩ := Wg1Tma.fires_coord hpre hj hat hi hf
    obtain rfl := (Kind.rd.inj (congrArg Event.kind h)).1
    have hPhase := (show Wg1Tma.Inv P L g d from hi).phase_lt
    have hK := k.isLt
    have hJ := j.isLt
    refine ⟨fits_offset (off := Wg1Tma.coordBase d.phase + 16 * k.val + 4 * j.val)
      (by simp only [Nat.add_assoc]) ?_ ?_, .inl (.inr ?_), .inl (.inr ?_),
      .inr (.inl ⟨d, hd, k, j, hj⟩), .inl ?_⟩
    · simp only [Wg1Tma.coordBase, sharedBytes]
      omega
    all_goals
      simp only [Wg1Tma.coordBase]
      omega
  | wg2 d =>
    cases o with
    | none => rcases fires_none_ends hf with ⟨_, h⟩ | h <;> cases h
    | some u =>
      have hLocal : (Wg2.machine P L g).Fired (some (.inr d)) ⟨tag, .rd a bs⟩ (some u) := by
        refine ⟨t, ⟨hat, hi⟩, ?_⟩
        change Fires t.pc (match kernel.code[d.site.pc]? with
          | some ins' => eventTmpl Assumptions.all L g t ins'.op
          | none => .ub .pcOutOfRange) _ (some u)
        have hpc : t.pc = d.site.pc := hat.1
        change kernel.code[d.site.pc]? = some ins at hc
        rw [hpc, hc]
        exact hf
      have hBuf := (show Wg2.Inv P L g d from hi).bufLt
      rcases hr with ⟨r, k, hSite⟩ | ⟨r, j, hSite⟩
      · obtain ⟨fp, _, hk, hl, hSize⟩ := Wg2.fired_raw_event hpre hSite hLocal
        obtain rfl := (Kind.rd.inj hk).1
        have hFit := Wg2.rawWord_fit (L := L) (g := g) r.isLt k.isLt
        refine ⟨fits_offset (off := Wg2.rawBase d.buf + Wg2.rawWordOff L g r.val k.val)
          (by simpa only [Nat.add_assoc] using hl) ?_ ?_, .inl (.inl ?_),
          .inr ⟨d, hd, .inr ⟨r, k, hSite⟩⟩, .inl (.inl ?_), .inl ?_⟩
        all_goals simp only [hl, Wg2.rawBase, Wg2.rawBufBytes, Wg2.rawBytesPerThread,
          sharedBytes, hSize] at hFit ⊢
        all_goals omega
      · obtain ⟨fp, _, hk, hl, hSize⟩ := Wg2.fired_scale_event hpre hSite hLocal
        obtain rfl := (Kind.rd.inj hk).1
        have hFit := Wg2.scaleRow_fit (L := L) (g := g) r.isLt
        have hJ := j.isLt
        refine ⟨fits_offset (off := Wg2.rawBase d.buf + Wg2.scaleRowOff L g r.val + 4 * j.val)
          (by simpa only [Nat.add_assoc] using hl) ?_ ?_, .inl (.inl ?_),
          .inr ⟨d, hd, .inl ⟨r, j, hSite⟩⟩, .inl (.inl ?_), .inl ?_⟩
        all_goals simp only [hl, Wg2.rawBase, Wg2.rawBufBytes, Wg2.scaleLoadBytes, sharedBytes,
          hSize] at hFit ⊢
        all_goals omega
  | head | done | mma _ | index _ | idle _ => exact hr.elim

/-- A tracked ordinary read covers bytes only within its issuing CTA's allocated window. -/
theorem read_window {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {a : Acc} {bs : List (Option Byte)}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hRead : X.Reads (g, i) a bs) :
    a.loc.space = .shared ∧ a.loc.cta = ctaOf L g ∧
      L.sharedBase ≤ a.loc.addr ∧ a.loc.addr + a.size ≤ L.sharedBase + sharedBytes := by
  obtain ⟨hSpace, hCta, hLo, hHi⟩ := (read_profile hpre hX hs ht hRead).1
  exact ⟨hSpace, hCta, by omega, hHi⟩

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat} {a : Acc}
    {bs : List (Option Byte)} {l : Loc} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

/-- Ordinary reads do not cover the query, dequantization or output staging tile bytes. -/
theorem read_above_tiles (hRead : X.Reads (g, i) a bs) (hCover : a.Covers l) :
    L.sharedBase + 131072 ≤ l.addr :=
  ((read_profile hpre hX hs ht hRead).1.2.2.1).trans hCover.2.2.1

/-- Only the peer exchange, maximum or half-sum reads touch the reused softmax window. -/
theorem softmax_read_of_cover (hRead : X.Reads (g, i) a bs) (hCover : a.Covers l)
    (hLo : L.sharedBase + 204800 ≤ l.addr) (hHi : l.addr < L.sharedBase + 221696) :
    ∃ d, Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) ∧
      (((∃ j, d.site = .peerRead j) ∧ l.addr < L.sharedBase + 221184) ∨
        ((d.site = .maxRead ∨ d.site = .lseRead) ∧ L.sharedBase + 221184 ≤ l.addr)) := by
  rcases (read_profile hpre hX hs ht hRead).2.1 with hOutside | hFound
  · obtain ⟨_, _, ha, hb⟩ := hCover
    rcases hOutside with hEnd | hStart <;> omega
  · obtain ⟨d, hd, hSite | hSite⟩ := hFound
    · exact ⟨d, hd, .inl ⟨hSite.1, by have := hCover.2.2.2; have := hSite.2; omega⟩⟩
    · exact ⟨d, hd, .inr ⟨hSite.1, by have := hCover.2.2.1; have := hSite.2; omega⟩⟩

/-- An ordinary read covering a raw-buffer byte belongs to the dequantizer's raw or scale path. -/
theorem raw_read_of_cover (hr : X.Reads (g, i) a bs) (hc : a.Covers l)
    (hLo : L.sharedBase + 131072 ≤ l.addr) (hHi : l.addr < L.sharedBase + 204800) :
    ∃ d, Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)) ∧
      ((∃ r j, d.site = .scale r j) ∨ ∃ r j, d.site = .raw r j) := by
  rcases (read_profile hpre hX hs ht hr).2.2.1 with hOutside | hFound
  · obtain ⟨_, _, ha, hb⟩ := hc
    rcases hOutside with hEnd | hStart <;> omega
  · exact hFound

/-- Every ordinary read of the index footprint is a TMA coordinate or a WG0 validity load. -/
theorem index_read_of_cover (hr : X.Reads (g, i) a bs) (hc : a.Covers l)
    (hLo : L.sharedBase + 221696 ≤ l.addr) (hHi : l.addr < L.sharedBase + 222752) :
    (∃ d : Wg1Tma.D, Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)) ∧
      ∃ k j, d.site = .coord k j) ∨
    ∃ d : Wg0.D, Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) ∧
      d.site = .maskRead := by
  rcases (read_profile hpre hX hs ht hr).2.2.2.1 with hOutside | hFound
  · obtain ⟨_, _, ha, hb⟩ := hc
    rcases hOutside with hEnd | hStart <;> omega
  · exact hFound

/-- Only the allocator result read-back can cover a byte at or above the shared tail. -/
theorem alloc_read_of_cover (hr : X.Reads (g, i) a bs) (hc : a.Covers l)
    (hLo : L.sharedBase + 222752 ≤ l.addr) :
    Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .allocRead)) := by
  exact (read_profile hpre hX hs ht hr).2.2.2.2.resolve_left
    (fun hEnd => (Nat.not_lt_of_ge (hEnd.trans hLo)) hc.2.2.2)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.OrdinaryReadWindow
