-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaDesc
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaCount
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStatic
public import Kernels.FlashAttn4Fwd.Proof.Interface.MmaBox
public import Lemmas.Tcgen05.MmaOperandObservations
public import Lemmas.Tcgen05.TcMmaACell

@[expose] public section

/-! # The shared bytes an MMA reads

A shared byte an MMA covers (`AsyncCovers … (.mmaRead isB idx)`) is a byte of its operand
footprint (`MmaFootprint`; the kernel has no `tcgen05.cp`), at a location `byteLoc` of the MMA's
operand specification (`mmaSpec`): A of a QK MMA is in the region of Q stage `mmaStage b`, B of
a QK MMA in the region of the K slot `kSlot`, B of a PV MMA in the region of the V slot
`vSlot`, in one CTA of the thread's pair (`mma_read_region`); a PV MMA reads no A byte in shared
memory. The box arithmetic is that of `Thread/MmaBox` (`qk_a_byteLoc`, `qk_b_byteLoc`,
`pv_b_byteLoc`, `box_inRegion`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The full barrier whose region operand `isB` of MMA block `b` reads: the Q stage of its block
(A), the K slot of a QK block or the V slot of a PV block (B). -/
def Mma.readBar (L : Launch) (d : Mma.D) (b : Fin 8) (isB : Bool) : FBar :=
  if isB then (if Mma.isPv b then .kvFull (Mma.vSlot L d) else .kvFull (Mma.kSlot L d b))
  else .qFull (Mma.mmaStage b)

theorem mmaSpec_qkDesc {L : Launch} {g : Nat} {d : Mma.D} {b j : Fin 8}
    (hp : Mma.isPv b = false) : (Mma.mmaSpec L g d b j).descriptor = SmemElements.qkDesc := by
  rw [Mma.mmaSpec_desc, hp]; rfl

theorem mmaSpec_pvDesc {L : Launch} {g : Nat} {d : Mma.D} {b j : Fin 8}
    (hp : Mma.isPv b = true) : (Mma.mmaSpec L g d b j).descriptor = SmemElements.pvDesc := by
  rw [Mma.mmaSpec_desc, hp]; rfl

/-- **The region of a byte an MMA reads**: the region of the Q stage or KV slot of its block's
descriptor, in one CTA of the thread's pair. -/
theorem mma_read_region (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k : Nat} {isB : Bool} {idx : Nat} {l : Loc}
    (hc : AsyncCovers X (g, k) (.mmaRead isB idx) l) :
    ∃ d b j, MmaSt L X g k d b j ∧ (isB = false → Mma.isPv b = false) ∧
      (l.cta = Mma.pairLo L g ∨ l.cta = Mma.pairLo L g + 1) ∧
      InRegion L l.cta (Mma.readBar L d b isB) l := by
  obtain ⟨a, w, ⟨-, hsz, hfp⟩, hcov⟩ := hc
  have hl := Rings.covers_one hcov hsz
  subst hl
  rcases hfp with ⟨dd, s, acc, mask, hi, hbl⟩ | ⟨a', src, cta, hci, -⟩
  · obtain ⟨d, b, j, h, -, rfl, -, -⟩ := mmaSt_of hpre hX ht hi
    have hlt := OperandSpec.byteLoc_index_lt hbl
    have hidx : idx = 32 * (idx / 32) + 2 * (idx / 2 % 16) + idx % 2 := by omega
    have hz : idx % 2 < 2 := Nat.mod_lt _ (by decide)
    have hk : idx / 2 % 16 < 16 := Nat.mod_lt _ (by decide)
    have hj := j.isLt
    have hlo := Mma.mmaSpec_lowCta L g d b j
    have hhi := Mma.mmaSpec_highCta L g d b j
    refine ⟨d, b, j, h, ?_⟩
    cases hp : Mma.isPv b
    · have hD := mmaSpec_qkDesc (L := L) (g := g) (d := d) (j := j) hp
      have haT : (Mma.mmaSpec L g d b j).aTmem = none := by rw [Mma.mmaSpec_aTmem, hp]; rfl
      have hsa : (Mma.mmaSpec L g d b j).a = kMajorDesc (qStepStart L (Mma.mmaStage b) j) := by
        simp [Mma.mmaSpec, hp]
      have hsb : (Mma.mmaSpec L g d b j).b = kMajorDesc (kStepStart L (Mma.kSlot L d b) j) := by
        simp [Mma.mmaSpec, hp]
      have hs : (Mma.kSlot L d b).val % 2 = 0 := by
        unfold Mma.kSlot
        split
        · rw [Mma.slotOf_mod]
        · rw [Mma.slotOf_mod]; omega
      refine ⟨fun _ => rfl, ?_⟩
      cases isB
      · simp only [Bool.false_eq_true, ↓reduceIte] at hbl hlt
        simp [Operand.rows, hD, SmemElements.qkDesc, Operand.extent, Kind.k, Kind.width] at hlt
        rw [SmemElements.qStepStart_eq] at hsa
        rw [hidx, show idx / 32 = 128 * (idx / 32 / 128) + idx / 32 % 128 by omega,
          SmemElements.qk_a_byteLoc hD haT hsa
            (SmemElements.boxBase_mod hpre (b := .qFull (Mma.mmaStage b)) rfl _) (by omega)
            (by omega) hk hz] at hbl
        rw [← Option.some.inj hbl]
        refine ⟨by split <;> simp [hlo, hhi], ?_⟩
        simp only [Mma.readBar, Bool.false_eq_true, ↓reduceIte]
        exact SmemElements.box_inRegion rfl (by simp only [FBar.copies]; omega) (by omega)
          (by simp only [FBar.copyBytes]; omega) hz
      · simp only [↓reduceIte] at hbl hlt
        simp [Operand.rows, hD, SmemElements.qkDesc, Operand.extent, Kind.k, Kind.width] at hlt
        rw [SmemElements.kStepStart_eq hs] at hsb
        rw [hidx, show idx / 32 = 64 * (idx / 32 / 64) + idx / 32 % 64 by omega,
          SmemElements.qk_b_byteLoc hD hsb
            (SmemElements.boxBase_mod hpre (b := .kvFull (Mma.kSlot L d b)) rfl _) (by omega)
            (by omega) hk hz] at hbl
        rw [← Option.some.inj hbl]
        refine ⟨by split <;> simp [hlo, hhi], ?_⟩
        simp only [Mma.readBar, hp, ↓reduceIte, Bool.false_eq_true]
        exact SmemElements.box_inRegion rfl (by simp only [FBar.copies, hs, ↓reduceIte]; omega)
          (by omega) (by simp only [FBar.copyBytes, hs, ↓reduceIte]; omega) hz
    · have hD := mmaSpec_pvDesc (L := L) (g := g) (d := d) (j := j) hp
      have haT' : (Mma.mmaSpec L g d b j).aTmem.isSome = true := by
        rw [Mma.mmaSpec_aTmem, hp]; rfl
      cases isB
      · simp only [Bool.false_eq_true, ↓reduceIte] at hbl
        rw [byteLoc_a_tmem haT'] at hbl
        cases hbl
      · have hsb : (Mma.mmaSpec L g d b j).b = mnMajorDesc (vStepStart L (Mma.vSlot L d) j) := by
          simp [Mma.mmaSpec, hp]
        have hs' : ¬ (Mma.vSlot L d).val % 2 = 0 := by
          unfold Mma.vSlot; rw [Mma.slotOf_mod]; omega
        refine ⟨(fun h => nomatch h), ?_⟩
        simp only [↓reduceIte] at hbl hlt
        simp [Operand.rows, hD, SmemElements.pvDesc, Operand.extent, Kind.k, Kind.width] at hlt
        rw [SmemElements.vStepStart_eq] at hsb
        rw [hidx, show idx / 32 = 64 * (idx / 32 / 64) + idx / 32 % 64 by omega,
          SmemElements.pv_b_byteLoc hD hsb
            (SmemElements.boxBase_mod hpre (b := .kvFull (Mma.vSlot L d)) rfl _) (by omega)
            (by omega) hk hz] at hbl
        rw [← Option.some.inj hbl]
        refine ⟨by split <;> simp [hlo, hhi], ?_⟩
        simp only [Mma.readBar, hp, ↓reduceIte]
        exact SmemElements.box_inRegion (jb := 0) rfl
          (by simp only [FBar.copies, hs', ↓reduceIte]; omega) (by omega)
          (by simp only [FBar.copyBytes, hs', ↓reduceIte]; omega) hz
  · exact (ScoreFacts_no_cp hX _ _ hci).elim

end
end PTX.Kernels.FlashAttn4Fwd.Proof
