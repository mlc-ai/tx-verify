-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Dequant
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Lemmas.Flow.Counted
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Objs
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.ChunkLoc
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.MemLoc
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.RefNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantWords

@[expose] public section

/-! # Warpgroup 2's memory accesses

`memRow_dequant` (`MemRow.Dequant`): from the event table (`Dequant/Ev.lean`), whose addresses
are the control machine's registers: the chunk store `(r, s)` writes the 16 bytes at
`%r2014 + 2048 r + 8192 s` (`store_loc`: `dequant b`'s chunk `dqChunk i r s`, `i` the lane's
index in its warpgroup), the scale read element `j` of row `r` reads 4 bytes at
`%r2338 + 512 + 9216 r + 4 j`, the raw read `(r, s)` 8 bytes at `%r2338 + %r59 + 9216 r + 64 s`,
all in `raw b` (`scale_in`, `raw_in`); `%r2338` is `raw b`'s row `i / 8` (576 bytes a row),
`%r59` the lane's word `8 (i % 8)` in its row. The lane's registers `%r58`, `%r59`, `%r60` as
numbers: `lane_tab` (evaluated for the 384 thread indices). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MemRow Dequant

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

open Dequant in
private theorem not_mem {e : Event} {K : Kind} (h : e.kind = K)
    (h1 : ∀ a bs, K ≠ .rd a bs := by simp) (h2 : ∀ a bs, K ≠ .nc a bs := by simp)
    (h3 : ∀ a bs, K ≠ .wr a bs := by simp) (h4 : ∀ a o n, K ≠ .rmw a o n := by simp) :
    ¬ MemEvent e := by
  rintro (⟨a, bs, h'⟩ | ⟨a, bs, h'⟩ | ⟨a, bs, h'⟩ | ⟨a, o, n, h'⟩)
  · exact h1 a bs (h ▸ h')
  · exact h2 a bs (h ▸ h')
  · exact h3 a bs (h ▸ h')
  · exact h4 a o n (h ▸ h')

/-- **Row `MemRow.Dequant`**: a memory event of a warpgroup-2 lane at a pc of its code is a
length read (`.nc`), a shared read in a raw buffer of its CTA, or the 16-byte store of one of
its chunks of a dequantized tile of its CTA. -/
theorem memRow_dequant (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MemRow.Dequant P L X := by
  intro g k e _ he hat hmem
  obtain ⟨-, -, hlo, hhi⟩ := hat
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => (not_mem h) hmem
  obtain ⟨σ, -, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, ⟨-, hk⟩, -⟩ := dequant_state hp hJ hi hev hpc ⟨hlo, hhi⟩
  have hc : g % 128 / 8 * 576 ≤ 15 * 576 := Nat.mul_le_mul_right _ (by omega)
  have h8 : g % 8 * 8 ≤ 56 := by omega
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases site with
  | lenA | lenB =>
    rcases hk with ⟨a, bs, hk⟩ | ⟨f, hk⟩
    · exact .inl ⟨a, bs, hk⟩
    · exact absurd hk (hub f)
  | scale r =>
    have hel : el < 4 := hi
    have hr := r.isLt
    rcases hk with ⟨a, bs, hk, hl, hs⟩ | ⟨f, hk⟩
    · rw [Dequant.scale_loc hp] at hl
      refine .inr (.inl ⟨a, bs, slotF sb, hk, wsAcc_in ⟨hl, hs⟩ ?_ ?_⟩) <;>
        simp only [Region.lo, Region.size] <;> omega
    · exact absurd hk (hub f)
  | raw r s =>
    have hr := r.isLt
    have hs' := s.isLt
    rcases hk with ⟨a, bs, hk, hl, hs⟩ | ⟨f, hk⟩
    · rw [Dequant.rawRd_loc hp] at hl
      refine .inr (.inl ⟨a, bs, slotF sb, hk, wsAcc_in ⟨hl, hs⟩ ?_ ?_⟩) <;>
        simp only [Region.lo, Region.size] <;> omega
    · exact absurd hk (hub f)
  | store r s =>
    rcases hk with ⟨a, bs, hk, hl, hs⟩ | ⟨f, hk⟩
    · rw [Dequant.store_loc hp] at hl
      exact .inr (.inr ⟨a, bs, slotF sb, r, s, hk, hl, hs⟩)
    · exact absurd hk (hub f)
  | smr => obtain ⟨_, hk⟩ := hk; exact absurd hmem (not_mem hk)
  | wq | wraw | wsv =>
    rcases hk with ⟨_, hk⟩ | ⟨f, hk⟩
    · exact absurd hmem (not_mem hk)
    · exact absurd hk (hub f)
  | fpx | arrD | arrF | bar | exit => exact absurd hmem (not_mem hk)

/-- **No access of the dequantizer covers an mbarrier's bytes** (the dequantizer part of
`bytes`): it is a non-coherent read, or a shared access in a raw block or a dequantized tile,
below the first mbarrier of the lane's CTA. -/
theorem dq_mem_noMbar (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hat : MbarRow.DequantAt L g e.pc) (hm : MemRow.MemEvent e) :
    (∃ a bs, e.kind = .nc a bs) ∨ ∃ a : Acc, ((∃ bs, e.kind = .rd a bs) ∨ ∃ bs, e.kind = .wr a bs) ∧
      a.loc.space = .shared ∧ a.loc.cta = g / L.block ∧ L.sharedBase ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ L.sharedBase + Region.mbars.lo := by
  rcases memRow_dequant hp hX hFw hg he hat hm with h | ⟨a, bs, b, hk, hs, hc, hlo, hhi⟩ |
    ⟨a, bs, b, r, s, hk, hl, hsz⟩
  · exact .inl h
  · refine .inr ⟨a, .inl ⟨bs, hk⟩, hs, hc, by omega, ?_⟩
    fin_cases b <;> simp only [Region.lo, Region.size] at hhi ⊢ <;> omega
  · have hb := dqChunk_lt (i := g % 128) (Nat.mod_lt _ (by decide)) r.isLt s.isLt
    refine .inr ⟨a, .inr ⟨bs, hk⟩, by rw [hl]; rfl, by rw [hl]; rfl, by rw [hl]; simp [wsLoc], ?_⟩
    rw [hl, hsz]
    fin_cases b <;> simp only [wsLoc, Region.lo] <;> omega

/-- The slot counts of a loop state of block `i` past its raw-ready poll: `uses b i + 1`
successful polls of `rawReady b` and `uses b i` arrivals on `rawFree b`, `b` the block's slot. -/
private theorem rd_counts (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k i : Nat} {d : Control.D}
    (hw : 8 ≤ MbarRow.warp L g ∧ MbarRow.warp L g < 12)
    (h : LoopCounts L g d (fun c => ((X.tr g).take k).countP (Dequant.cls c)) i)
    (hinc : incR d.site = 1) :
    okPolls (mbarLoc L (g / L.block) (.rawReady (slotF d.sb))) ((X.tr g).take k) =
        uses (slotF d.sb) i + 1 ∧
      arrivals (mbarLoc L (g / L.block) (.rawFree (slotF d.sb))) ((X.tr g).take k) =
        uses (slotF d.sb) i := by
  obtain ⟨hsb, -, hn⟩ := h
  obtain ⟨h1, -, -, h4⟩ := hn (slotF d.sb)
  rw [wg2_okPolls hp hX hFw hw, wg2_arrivals hp hX hFw hw]
  simp only [MbarRow.loc] at h1 h4
  rw [h1, h4, hinc, uses_succ]
  simp [incF, hsb, slotF_slot2]

/-- **The use of a raw read, with its place**: a shared read of a dequant lane covers bytes of
`raw b` of its CTA, tile row `R` (576 bytes each) from column `c0` with `c0 + size ≤ 528` (a raw
word, size 8, ends by 512; a scale element, size 4, starts at 512 or later), after
`v + 1` successful polls of `rawReady b` and `v` arrivals on `rawFree b` (block `i` of the read
uses slot `b = i % 2`, after its poll and before its release). -/
theorem dequant_rd (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hat : MbarRow.DequantAt L g pc) :
    ∃ b : Fin 2, MemRow.SharedIn L (g / L.block) (.raw b) a ∧
      (∃ R c0, a.loc.addr = L.sharedBase + (Region.raw b).lo + (576 * R + c0) ∧
        c0 + a.size ≤ 528 ∧ (a.size = 8 → c0 + 8 ≤ 512) ∧ (a.size = 4 → 512 ≤ c0)) ∧ ∃ v,
      okPolls (mbarLoc L (g / L.block) (.rawReady b)) ((X.tr g).take k) = v + 1 ∧
      arrivals (mbarLoc L (g / L.block) (.rawFree b)) ((X.tr g).take k) = v := by
  obtain ⟨hw1, hw2, hlo, hhi⟩ := hat
  have hub : ∀ f, Kind.rd a bs ≠ .ub f := fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, ⟨-, hk⟩, -⟩ := dequant_state hp hJ hi hev hpc ⟨hlo, hhi⟩
  have hc := hR (state_ub hX hσ he)
  rw [show (fun c => n (.dequant c)) = fun c => ((X.tr g).take k).countP (Dequant.cls c) from
    funext fun c => state_count hσ (.dequant c)] at hc
  have hc := hc (wg2_take_noUb hX he)
  have hci : g % 128 / 8 * 576 ≤ 15 * 576 := Nat.mul_le_mul_right _ (by omega)
  have h8 : g % 8 * 8 ≤ 56 := by omega
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases site with
  | scale r =>
    have hel : el < 4 := hi
    have hr := r.isLt
    obtain ⟨i, -, hi⟩ := hc
    obtain ⟨h1, h2⟩ := rd_counts hp hX hFw ⟨hw1, hw2⟩ hi rfl
    rcases hk with ⟨a', bs', hk, hl, hs⟩ | ⟨f, hk⟩
    · simp only [Kind.rd.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rw [Dequant.scale_loc hp] at hl
      refine ⟨slotF sb, wsAcc_in ⟨hl, hs⟩ ?_ ?_, ⟨g % 128 / 8 + 16 * r.val, 512 + 4 * el,
        ?_, ?_, ?_, ?_⟩, _, h1, h2⟩
      · simp only [Region.lo]; omega
      · simp only [Region.lo, Region.size]; omega
      · rw [hl]; simp only [wsLoc, Region.lo]; omega
      · rw [hs]; omega
      · intro h8; rw [hs] at h8; omega
      · intro _; omega
    · cases hk
  | raw r s =>
    have hr := r.isLt
    have hs' := s.isLt
    obtain ⟨i, -, hi⟩ := hc
    obtain ⟨h1, h2⟩ := rd_counts hp hX hFw ⟨hw1, hw2⟩ hi rfl
    rcases hk with ⟨a', bs', hk, hl, hs⟩ | ⟨f, hk⟩
    · simp only [Kind.rd.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rw [Dequant.rawRd_loc hp] at hl
      refine ⟨slotF sb, wsAcc_in ⟨hl, hs⟩ ?_ ?_, ⟨g % 128 / 8 + 16 * r.val,
        g % 8 * 8 + 64 * s.val, ?_, ?_, ?_, ?_⟩, _, h1, h2⟩
      · simp only [Region.lo]; omega
      · simp only [Region.lo, Region.size]; omega
      · rw [hl]; simp only [wsLoc, Region.lo]; omega
      · rw [hs]; omega
      · intro _; omega
      · intro h4; rw [hs] at h4; omega
    · cases hk
  | lenA | lenB => rcases hk with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  | store r s => rcases hk with ⟨_, _, hk, -⟩ | ⟨_, hk⟩ <;> cases hk
  | wq | wraw | wsv => rcases hk with ⟨_, hk⟩ | ⟨_, hk⟩ <;> cases hk
  | smr => obtain ⟨_, hk⟩ := hk; cases hk
  | fpx | arrD | arrF | bar | exit => cases hk

/-- **The use of a raw read**: a shared read of a dequant lane covers bytes of `raw b` of its
CTA, after `v + 1` successful polls of `rawReady b` and `v` arrivals on `rawFree b`. -/
theorem dequant_rdUse (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hat : MbarRow.DequantAt L g pc) :
    ∃ b : Fin 2, MemRow.SharedIn L (g / L.block) (.raw b) a ∧ ∃ v,
      okPolls (mbarLoc L (g / L.block) (.rawReady b)) ((X.tr g).take k) = v + 1 ∧
      arrivals (mbarLoc L (g / L.block) (.rawFree b)) ((X.tr g).take k) = v := by
  obtain ⟨b, h, -, v, h1, h2⟩ := dequant_rd hp hX hFw he hat
  exact ⟨b, h, v, h1, h2⟩

/-- The slot counts of a loop state of block `i` at a store: `uses b i + 1` successful polls of
`svDone b` and `uses b i` arrivals on `dequantReady b`, `b` the block's slot. -/
private theorem wr_counts (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k i : Nat} {d : Control.D}
    (hw : 8 ≤ MbarRow.warp L g ∧ MbarRow.warp L g < 12)
    (h : LoopCounts L g d (fun c => ((X.tr g).take k).countP (Dequant.cls c)) i)
    (hS : incS d.site = 1) (hD : incD d.site = 0) :
    okPolls (mbarLoc L (g / L.block) (.svDone (slotF d.sb))) ((X.tr g).take k) =
        uses (slotF d.sb) i + 1 ∧
      arrivals (mbarLoc L (g / L.block) (.dequantReady (slotF d.sb))) ((X.tr g).take k) =
        uses (slotF d.sb) i := by
  obtain ⟨hsb, -, hn⟩ := h
  obtain ⟨-, h2, h3, -⟩ := hn (slotF d.sb)
  rw [wg2_okPolls hp hX hFw hw, wg2_arrivals hp hX hFw hw]
  simp only [MbarRow.loc] at h2 h3
  rw [h2, h3, hS, hD, uses_succ]
  simp [hsb, slotF_slot2]

/-- **The use of a chunk store**: a dequant lane's write is a 16-byte chunk of the dequantized
tile `b` of its CTA, after `u + 1` successful polls of `svDone b` and `u` arrivals on
`dequantReady b`. -/
theorem dequant_wrUse (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hat : MbarRow.DequantAt L g pc) :
    ∃ (b : Fin 2) (r : Fin 4) (s : Fin 8) (u : Nat),
      MemRow.WsAcc L (g / L.block) ((Region.dequant b).lo + MemRow.dqChunk (g % 128) r s) 16 a ∧
      okPolls (mbarLoc L (g / L.block) (.svDone b)) ((X.tr g).take k) = u + 1 ∧
      arrivals (mbarLoc L (g / L.block) (.dequantReady b)) ((X.tr g).take k) = u ∧
      u < ringUses 2 b.val (blocksOf P L (g / L.block)) := by
  obtain ⟨hw1, hw2, hlo, hhi⟩ := hat
  have hub : ∀ f, Kind.wr a bs ≠ .ub f := fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, ⟨-, hk⟩, -⟩ := dequant_state hp hJ hi hev hpc ⟨hlo, hhi⟩
  have hc := hR (state_ub hX hσ he)
  rw [show (fun c => n (.dequant c)) = fun c => ((X.tr g).take k).countP (Dequant.cls c) from
    funext fun c => state_count hσ (.dequant c)] at hc
  have hc := hc (wg2_take_noUb hX he)
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases site with
  | store r s =>
    obtain ⟨i, hwd, hi'⟩ := hc
    obtain ⟨h1, h2⟩ := wr_counts hp hX hFw ⟨hw1, hw2⟩ hi' rfl rfl
    have hR' := deq_rounds hp hX hσ rfl
    have hlt := hwd.1
    rw [hR'] at hlt
    have hsl := hi'.1
    have hu : uses (slotF sb) i = i / 2 := by
      simp only at hsl
      rw [hsl, slotF_slot2, uses_slot]
    rcases hk with ⟨a', bs', hk, hl, hs⟩ | ⟨f, hk⟩
    · simp only [Kind.wr.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rw [Dequant.store_loc hp] at hl
      refine ⟨slotF sb, r, s, _, ⟨hl, hs⟩, h1, h2, ?_⟩
      simp only at hsl
      rw [hu, hsl, slotF_slot2]
      simp only [MbarRow.slot2, ringUses]
      omega
    · cases hk
  | lenA | lenB => rcases hk with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  | scale r => rcases hk with ⟨_, _, hk, -⟩ | ⟨_, hk⟩ <;> cases hk
  | raw r s => rcases hk with ⟨_, _, hk, -⟩ | ⟨_, hk⟩ <;> cases hk
  | wq | wraw | wsv => rcases hk with ⟨_, hk⟩ | ⟨_, hk⟩ <;> cases hk
  | smr => obtain ⟨_, hk⟩ := hk; cases hk
  | fpx | arrD | arrF | bar | exit => cases hk

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
