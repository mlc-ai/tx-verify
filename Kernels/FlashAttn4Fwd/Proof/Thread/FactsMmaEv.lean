-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaEvents
public import Kernels.FlashAttn4Fwd.Proof.Interface.MmaSmem

@[expose] public section

/-! # The data of the MMA warp's MMAs

The MMA at site `.mma b j` of a state is one event whose every operand is a function of the
state (`MmaEv`): the accumulator column `mmaCol b` (S of stage 0 or 1 at columns 0 and 128, O of
stage 0 or 1 at 256 and 384), the operand specification `mmaSpec` and the enable-input-D flag
`mmaAcc`, with the eight zero lane masks.

* A QK block (`b` = 0, 1, 3, 5) reads Q stage `mmaStage b` and the K block of an even ring slot
  (the item's first use for blocks 0 and 1, use `2 + 2 t` for blocks 3 and 5) from shared memory,
  K step `j` of each (`qStepStart`, `kStepStart`, K-major); its instruction descriptor is the QK
  one (`qkDesc`). It accumulates from step 1 on.
* A PV block (`b` = 2, 4, 6, 7) reads A from Tensor Memory at column `128 st + 64 + 8 j` and the
  V block of the odd ring slot of use `1 + 2 t` from shared memory, rows `16 j` on
  (`vStepStart`, MN-major); its instruction descriptor is the PV one (`pvDesc`). It accumulates
  from step 1 on, and at step 0 from trip 1 on.
* Both CTAs of the thread's pair take part: the even one is `pairLo L g`.

This file holds the definitions and the issue lemmas of one MMA instruction (`qk_ev`, `pv_ev`,
from the template lemmas `tc_mma_en` and `tc_mmaTs`); the per-site instances are in
`FactsMmaEvQk.lean` and `FactsMmaEvPv.lean`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-! ### Descriptors -/

/-- The decoded QK instruction descriptor: `kind::f16` FP16 inputs, FP32 accumulator,
M = 256 over the pair, N = 128, K-major A and B. -/
def qkDesc : TcMma.Descriptor := ⟨.two, .f16 .f16 .f32, 256, 128, false, false, false, false, false⟩

/-- The decoded PV instruction descriptor: as `qkDesc`, with B transposed (MN-major). -/
def pvDesc : TcMma.Descriptor := ⟨.two, .f16 .f16 .f32, 256, 128, false, false, false, true, false⟩

theorem qkIdesc_decode : TcMma.decode .two false .f16 qkIdesc = some qkDesc := by decide

theorem pvIdesc_decode : TcMma.decode .two false .f16 pvIdesc = some pvDesc := by decide

/-- The shared-memory descriptor that the word `lo + 0x40004040 · 2^32` decodes to. -/
def sdesc (lo : Nat) : TcShared.Descriptor :=
  ⟨lo % 32768 * 16, lo / 65536 % 32768 * 16, 1024, 0, false, false, .b128⟩

/-- A word whose swizzle, reserved and version fields are those of the 128-byte swizzle
decodes to its fields. -/
theorem decode_b128 {x : Nat} (hs : x / 2 ^ 61 % 8 = 2)
    (hc : x < 2 ^ 64 ∧ x / 2 ^ 15 % 2 = 0 ∧ x / 2 ^ 31 % 2 = 0 ∧ x / 2 ^ 46 % 8 = 1 ∧
      x / 2 ^ 54 % 128 = 0) :
    TcShared.decode x = some ⟨x % 2 ^ 15 * 16, x / 2 ^ 16 % 2 ^ 15 * 16, x / 2 ^ 32 % 2 ^ 14 * 16,
      x / 2 ^ 49 % 8, x / 2 ^ 52 % 2 = 1, x / 2 ^ 53 % 2 = 1, .b128⟩ := by
  unfold TcShared.decode
  rw [hs]
  simp only [TcShared.decodeSwizzle, hc, and_self, ↓reduceIte]

/-- A descriptor `lo + hi · 2^32` with the high word's fields of `0x40004040`. -/
theorem sdesc_decode_of {lo hi : Nat} (hlo : lo < 2 ^ 31) (h15 : lo / 2 ^ 15 % 2 = 0)
    (hhi : hi < 2 ^ 32) (h61 : hi / 2 ^ 29 % 8 = 2) (h46 : hi / 2 ^ 14 % 8 = 1)
    (h54 : hi / 2 ^ 22 % 128 = 0) (h49 : hi / 2 ^ 17 % 8 = 0) (h52 : hi / 2 ^ 20 % 2 = 0)
    (h53 : hi / 2 ^ 21 % 2 = 0) (h32 : hi % 2 ^ 14 = 64) :
    TcShared.decode (lo + hi * 2 ^ 32) = some (sdesc lo) := by
  rw [decode_b128 (by omega) ⟨by omega, by omega, by omega, by omega, by omega⟩]
  have e1 : (lo + hi * 2 ^ 32) % 2 ^ 15 * 16 = lo % 32768 * 16 := by omega
  have e2 : (lo + hi * 2 ^ 32) / 2 ^ 16 % 2 ^ 15 * 16 = lo / 65536 % 32768 * 16 := by omega
  have e3 : (lo + hi * 2 ^ 32) / 2 ^ 32 % 2 ^ 14 * 16 = 1024 := by omega
  have e4 : (lo + hi * 2 ^ 32) / 2 ^ 49 % 8 = 0 := by omega
  have e5 : ¬ (lo + hi * 2 ^ 32) / 2 ^ 52 % 2 = 1 := by omega
  have e6 : ¬ (lo + hi * 2 ^ 32) / 2 ^ 53 % 2 = 1 := by omega
  simp only [e1, e2, e3, e4, e5, e6, decide_false, sdesc]

theorem sdesc_decode {lo : Nat} (hlo : lo < 2 ^ 31) (h15 : lo / 2 ^ 15 % 2 = 0) :
    TcShared.decode (lo + descHi * 2 ^ 32) = some (sdesc lo) :=
  sdesc_decode_of hlo h15 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-! ### The MMA of a site -/

/-- The even CTA of the thread's pair. -/
def pairLo (L : Launch) (g : Nat) : Nat := g / L.block / 2 * 2

/-- The stage of block `b`: the S stage of a QK block, the O stage of a PV block. -/
def mmaStage : Fin 8 → Fin 2
  | 0 | 2 | 3 | 6 => 0
  | _ => 1

/-- The accumulator column of block `b`: S of its stage, or O of its stage. -/
def mmaCol (b : Fin 8) : Nat := (if isPv b then 256 else 0) + 128 * (mmaStage b).val

/-- The K slot a QK block reads: the item's first use (blocks 0, 1) or use `2 + 2 t`. -/
def kSlot (L : Launch) (d : D) (b : Fin 8) : Fin 6 :=
  if b.val < 2 then slotOf L d.i 0 else slotOf L d.i (2 + 2 * d.t)

/-- The V slot a PV block reads: use `1 + 2 t`. -/
def vSlot (L : Launch) (d : D) : Fin 6 := slotOf L d.i (1 + 2 * d.t)

/-- The operand specification of MMA `j` of block `b` at state `d`. -/
def mmaSpec (L : Launch) (g : Nat) (d : D) (b j : Fin 8) : TcMma.OperandSpec :=
  if isPv b then
    ⟨pvDesc, mnMajorDesc (vStepStart L (vSlot L d) j), mnMajorDesc (vStepStart L (vSlot L d) j),
      pairLo L g, pairLo L g + 1, some (128 * (mmaStage b).val + 64 + 8 * j.val), {}⟩
  else
    ⟨qkDesc, kMajorDesc (qStepStart L (mmaStage b) j), kMajorDesc (kStepStart L (kSlot L d b) j),
      pairLo L g, pairLo L g + 1, none, {}⟩

/-- The enable-input-D flag of MMA `j` of block `b`: from step 1 on, and at step 0 of a PV
block from trip 1 on. -/
def mmaAcc (d : D) (b j : Fin 8) : Bool :=
  if j.val = 0 then isPv b && decide (d.t ≠ 0) else true

/-! ### Descriptor words -/

/-- The descriptor-word offset of K step `j` in a Q stage. -/
def qOff (j : Fin 8) : Nat := 2 * (j.val % 4) + 1024 * (j.val / 4)

/-- The descriptor-word offset of K step `j` in a K block. -/
def kOff (j : Fin 8) : Nat := 2 * (j.val % 4) + 512 * (j.val / 4)

/-- The Q stage of the descriptor toggle. -/
def qst (low : Bool) : Fin 2 := if low then 0 else 1

/-- The K-major descriptor word of a 16-byte aligned start below `2^18`. -/
theorem sdesc_k_of {S : Nat} (h16 : S % 16 = 0) (hS : S < 2 ^ 18) :
    sdesc (S / 16 + 65536) = kMajorDesc S := by
  have h1 : (S / 16 + 65536) / 65536 = 1 := by omega
  simp only [sdesc, kMajorDesc, TcShared.Descriptor.mk.injEq, h1]
  exact ⟨by omega, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- The MN-major descriptor word of a 16-byte aligned start below `2^18`. -/
theorem sdesc_mn_of {S : Nat} (h16 : S % 16 = 0) (hS : S < 2 ^ 18) :
    sdesc (S / 16) = mnMajorDesc S := by
  have h1 : S / 16 / 65536 = 0 := by omega
  simp only [sdesc, mnMajorDesc, TcShared.Descriptor.mk.injEq, h1]
  exact ⟨by omega, trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem qWord_eq (hpre : Pre P L mem0) (low : Bool) (j : Fin 8) :
    qLo L low + qOff j = qStepStart L (qst low) j / 16 + 65536 ∧
      qStepStart L (qst low) j % 16 = 0 ∧ qStepStart L (qst low) j < 2 ^ 18 := by
  have hb := hpre.sharedRange
  have ha := hpre.sharedAlignment
  unfold sharedBytes at hb
  have hj := j.isLt
  cases low <;> simp only [qStepStart, qLo, qOff, qst, FBar.regionOff, Bool.false_eq_true,
    ↓reduceIte, Fin.isValue, Fin.val_zero, Fin.val_one] <;> omega

theorem kWord_eq (hpre : Pre P L mem0) (s : Fin 6) (j : Fin 8) :
    kLo L s + kOff j = kStepStart L s j / 16 + 65536 ∧ kStepStart L s j % 16 = 0 ∧
      kStepStart L s j < 2 ^ 18 := by
  have hb := hpre.sharedRange
  have ha := hpre.sharedAlignment
  unfold sharedBytes at hb
  have hj := j.isLt
  have hs := s.isLt
  simp only [kStepStart, kLo, kOff, FBar.regionOff]
  omega

theorem vWord_eq (hpre : Pre P L mem0) (s : Fin 6) (j : Fin 8) :
    vLo L s + 128 * j.val = vStepStart L s j / 16 ∧ vStepStart L s j % 16 = 0 ∧
      vStepStart L s j < 2 ^ 18 := by
  have hb := hpre.sharedRange
  have ha := hpre.sharedAlignment
  unfold sharedBytes at hb
  have hj := j.isLt
  have hs := s.isLt
  simp only [vStepStart, vLo, FBar.regionOff]
  omega

theorem sdesc_q (hpre : Pre P L mem0) (low : Bool) (j : Fin 8) :
    sdesc (qLo L low + qOff j) = kMajorDesc (qStepStart L (qst low) j) := by
  obtain ⟨h, h16, hS⟩ := qWord_eq hpre low j
  rw [h, sdesc_k_of h16 hS]

theorem sdesc_k (hpre : Pre P L mem0) (s : Fin 6) (j : Fin 8) :
    sdesc (kLo L s + kOff j) = kMajorDesc (kStepStart L s j) := by
  obtain ⟨h, h16, hS⟩ := kWord_eq hpre s j
  rw [h, sdesc_k_of h16 hS]

theorem sdesc_v (hpre : Pre P L mem0) (s : Fin 6) (j : Fin 8) :
    sdesc (vLo L s + 128 * j.val) = mnMajorDesc (vStepStart L s j) := by
  obtain ⟨h, h16, hS⟩ := vWord_eq hpre s j
  rw [h, sdesc_mn_of h16 hS]

/-- The CTAs of an MMA over the pair: the thread's pair. -/
theorem makeOperands_two (hpre : Pre P L mem0) (hg : g < L.threads) (dsc : TcMma.Descriptor)
    (da db : TcShared.Descriptor) (hd : dsc.group = .two) :
    TcMma.makeOperands L (g / L.block) dsc da db =
      some ⟨dsc, da, db, pairLo L g, pairLo L g + 1, none, {}⟩ := by
  have hcta := cta_lt hg
  have hcl := hpre.cluster
  have hgr := hpre.grid
  have hone := hpre.oneDimLaunch.1
  unfold ctaOf at hcta
  have hrank : L.rankOfCta (g / L.block) = (g / L.block) % 2 := by
    rw [Launch.oneDim_rankOfCta hone, hcl]
  have hsz : L.clusterSizeOf (g / L.block) = 2 := by
    rw [Launch.oneDim_clusterSizeOf hone, hcl]
  have hbase : L.clusterStart (L.clusterOfCta (g / L.block)) = pairLo L g := by
    rw [Launch.oneDim_clusterStart hone, Launch.oneDim_clusterOfCta hone, hcl]
    rfl
  have hr0 : L.rankOfCta (g / L.block) / 2 * 2 = 0 := by rw [hrank]; omega
  have hpl : pairLo L g + 1 < L.grid := by unfold pairLo; omega
  have hlo : L.peerCta (g / L.block) (L.rankOfCta (g / L.block) / 2 * 2) =
      some (pairLo L g) := by
    have hc : g / L.block < L.grid ∧ 0 < L.clusterSizeOf (g / L.block) ∧ pairLo L g < L.grid :=
      ⟨hcta, by rw [hsz]; omega, by omega⟩
    rw [hr0]
    simp only [Launch.peerCta, Nat.add_zero, hbase, ite_eq_left hc]
  have hhi : L.peerCta (g / L.block) (L.rankOfCta (g / L.block) / 2 * 2 + 1) =
      some (pairLo L g + 1) := by
    have hc : g / L.block < L.grid ∧ 1 < L.clusterSizeOf (g / L.block) ∧
        pairLo L g + 1 < L.grid := ⟨hcta, by rw [hsz]; omega, hpl⟩
    rw [hr0]
    simp only [Launch.peerCta, hbase, ite_eq_left hc]
  rw [TcMma.makeOperands, hd, Launch.ctaGroup_two, hlo, hhi]
  rfl

/-! ### One MMA instruction -/

/-- **A QK MMA's event**: its accumulator column, Q descriptor of stage `qst low` and K
descriptor of slot `s` at K step `j`, the QK instruction descriptor, the enable flag. -/
theorem qk_ev (hpre : Pre P L mem0) (hg : g < L.threads) {t : TState} {pc dst ra rb c : Nat}
    {low : Bool} {s : Nat} (hs : s < 6) (j : Fin 8) {en : Opnd} {acc : Bool} {e : Event}
    {o : Option TState}
    (hd : t.regs dst = some (b32 c)) (hc : c < 2 ^ 32)
    (hA : t.regs ra = some (desc (qLo L low + qOff j)))
    (hB : t.regs rb = some (desc (kLo L s + kOff j)))
    (hI : t.regs 5351 = some (b32 qkIdesc)) (he : mmaEnable t en = .ok acc)
    (hf : Fires pc (eventTmpl asms L g t
      (.tcMma (.dense .two false .f16 dst (.smem (.reg ra)) (.reg rb) (.reg 5351) masks0 en)))
      e o) :
    e.kind = .tc (.mma c ⟨qkDesc, kMajorDesc (qStepStart L (qst low) j),
      kMajorDesc (kStepStart L ⟨s, hs⟩ j), pairLo L g, pairLo L g + 1, none, {}⟩ acc
      (List.replicate 8 0)) := by
  have hb := hpre.sharedRange
  have hal := hpre.sharedAlignment
  unfold sharedBytes at hb
  have hj := j.isLt
  obtain ⟨hqa, -, hqs⟩ := qWord_eq hpre low j
  obtain ⟨hka, -, hks⟩ := kWord_eq hpre ⟨s, hs⟩ j
  have hla : qLo L low + qOff j < 2 ^ 31 := by omega
  have hla' : (qLo L low + qOff j) / 2 ^ 15 % 2 = 0 := by omega
  have hlb : kLo L s + kOff j < 2 ^ 31 := by
    rw [show kLo L s = kLo L (⟨s, hs⟩ : Fin 6) from rfl]; omega
  have hlb' : (kLo L s + kOff j) / 2 ^ 15 % 2 = 0 := by
    rw [show kLo L s = kLo L (⟨s, hs⟩ : Fin 6) from rfl]; omega
  have hda := sdesc_decode hla hla'
  have hdb := sdesc_decode hlb hlb'
  rw [sdesc_q hpre] at hda
  rw [show kLo L s = kLo L (⟨s, hs⟩ : Fin 6) from rfl, sdesc_k hpre] at hdb
  have ht := tc_mma_en (L := L) (mask := masks0) (ms := [0, 0, 0, 0, 0, 0, 0, 0]) hg hd hc
    hA (by unfold descHi; omega) hB (by unfold descHi; omega) hI (by decide) rfl rfl he hda hdb
    qkIdesc_decode (makeOperands_two hpre hg _ _ _ rfl)
  simp only [eventTmpl] at hf
  rw [ht] at hf
  obtain ⟨rfl, -⟩ := hf
  rfl

/-- **A PV MMA's event**: its accumulator column, the A column `a + 8 j` in Tensor Memory, the
V descriptor of slot `s` at K step `j`, the PV instruction descriptor, the enable flag. -/
theorem pv_ev (hpre : Pre P L mem0) (hg : g < L.threads) {t : TState}
    {pc dst ta rb ri c a a' : Nat} {aoff : Int} {s : Nat} (hs : s < 6) (j : Fin 8) {en : Opnd}
    {acc : Bool} {e : Event} {o : Option TState}
    (hd : t.regs dst = some (b32 c)) (hc : c < 2 ^ 32)
    (hA : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32) (ho : tmemOffset a aoff = .ok a')
    (hB : t.regs rb = some (desc (vLo L s + 128 * j.val)))
    (hI : t.regs ri = some (b32 pvIdesc)) (he : mmaEnable t en = .ok acc)
    (hf : Fires pc (eventTmpl asms L g t
      (.tcMma (.dense .two false .f16 dst (.tmem ta aoff) (.reg rb) (.reg ri) masks0 en)))
      e o) :
    e.kind = .tc (.mma c ⟨pvDesc, mnMajorDesc (vStepStart L ⟨s, hs⟩ j),
      mnMajorDesc (vStepStart L ⟨s, hs⟩ j), pairLo L g, pairLo L g + 1, some a', {}⟩ acc
      (List.replicate 8 0)) := by
  have hb := hpre.sharedRange
  have hal := hpre.sharedAlignment
  unfold sharedBytes at hb
  have hj := j.isLt
  obtain ⟨hva, -, hvs⟩ := vWord_eq hpre ⟨s, hs⟩ j
  have hlb : vLo L s + 128 * j.val < 2 ^ 31 := by
    rw [show vLo L s = vLo L (⟨s, hs⟩ : Fin 6) from rfl]; omega
  have hlb' : (vLo L s + 128 * j.val) / 2 ^ 15 % 2 = 0 := by
    rw [show vLo L s = vLo L (⟨s, hs⟩ : Fin 6) from rfl]; omega
  have hdb := sdesc_decode hlb hlb'
  rw [show vLo L s = vLo L (⟨s, hs⟩ : Fin 6) from rfl, sdesc_v hpre] at hdb
  have ht := tc_mmaTs (L := L) (mask := masks0) (ms := [0, 0, 0, 0, 0, 0, 0, 0]) hg hd hc
    hA ha ho hB (by unfold descHi; omega) hI (by decide) rfl rfl he hdb pvIdesc_decode rfl
    (makeOperands_two hpre hg _ _ _ rfl)
  simp only [eventTmpl] at hf
  rw [ht] at hf
  obtain ⟨rfl, -⟩ := hf
  rfl

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
