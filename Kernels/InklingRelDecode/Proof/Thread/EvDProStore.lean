-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvDProLoad

@[expose] public section

/-!
# Event shapes of the prologue: the Q stores to shared memory

The prologue packs the 64 loaded query values into 32 words (two bf16 values each, the earlier
load in the low half: `qWord dt i = joinValue (dt.q (2 i)) (dt.q (2 i + 1))`) and writes them with
eight `st.shared.v4.b32`. Site `stqSite (4 m + w)` is element `w` of store `m`: a write of the four
bytes `storeValue 32 (qWord dt (4 m + w))` at `qStoreBase L g dt m + 4 w` of the thread's CTA,
element `w` of the vector store. `qStoreBase` is the 32-bit word the store's address register
holds (the swizzled offset of the thread's rows in the `Q` tile); its closed form is open
(the development notes, "thread-layer gaps").
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-- Packed word `i` of the loaded query values: the two values `2 i` and `2 i + 1`. -/
def qWord (dt : Dat) (i : Nat) : Value := joinValue (dt.q (2 * i)) (dt.q (2 * i + 1))

/-- The shared address (a 32-bit word) of the `m`-th Q store. -/
def qStoreBase (L : Launch) (g : Nat) (dt : Dat) (m : Nat) : Nat :=
  match valueOf L g dt (gloadBase (stqSite (4 * m)).pc) with
  | .bits _ x => x.toNat
  | _ => 0

theorem stq_sstore : ∀ i < 32, isSstore4 (stqSite i).pc = true := by decide +kernel

theorem stq_pc : ∀ i < 32, (stqSite i).pc = (stqSite (4 * (i / 4))).pc := by decide +kernel

theorem stq_sub : ∀ i < 32, (stqSite i).sub = i % 4 := by decide +kernel

theorem stq_live : ∀ i < 32, gloadBase (stqSite i).pc ∈ Flow.live (stqSite i).pc ∧
    ∀ j < 4, memSrc (stqSite i).pc j ∈ Flow.live (stqSite i).pc := by decide +kernel

theorem wAdd32_lt (a b : BitVec 64) : (wAdd32 a b).toNat < 2 ^ 32 := by
  unfold wAdd32 truncBits
  rw [BitVec.toNat_ofNat]
  have h := Nat.mod_lt ((truncBits 32 a + truncBits 32 b).toNat) (show 0 < 2 ^ 32 by decide)
  rw [Nat.mod_eq_of_lt (by omega)]
  exact h

theorem stq_base_bits (L : Launch) (g : Nat) (dt : Dat) :
    ∀ i < 32, ∃ x : BitVec 64, valueOf L g dt (gloadBase (stqSite i).pc) = .bits 32 x ∧
      x.toNat < 2 ^ 32 := by
  intro i hi
  interval_cases i
  all_goals exact ⟨_, rfl, wAdd32_lt _ _⟩

theorem stq_src (L : Launch) (g : Nat) (dt : Dat) :
    ∀ i < 32, valueOf L g dt (memSrc (stqSite i).pc (i % 4)) = qWord dt i := by
  intro i hi
  interval_cases i
  all_goals rfl

/-- **A Q store**: element `w` of the `m`-th `st.shared.v4.b32` writes the four bytes of packed
word `4 m + w` at `qStoreBase + 4 w` of the thread's CTA. -/
theorem shape_stq {m w : Nat} (hm : m < 8) (hw : w < 4) (hF : Fired L g d e (some u))
    (hs : d.site = stqSite (4 * m + w)) :
    ∃ v', storeValue 32 (qWord d.dt (4 * m + w)) = .ok v' ∧
      e = ⟨evPc d.site, .wr (wordAcc ⟨.shared, g / L.block, qStoreBase L g d.dt m + 4 * w⟩ w)
        v'.toBytes⟩ := by
  obtain ⟨t, ins, h, hinv, hc, hf⟩ := fired_unpack hF
  have hi : 4 * m + w < 32 := by omega
  have hpc : d.site.pc = (stqSite (4 * m + w)).pc := by rw [hs]
  have hpc4 : (stqSite (4 * m + w)).pc = (stqSite (4 * m)).pc := by
    have := stq_pc (4 * m + w) hi
    have h4 : (4 * m + w) / 4 = m := by omega
    rw [h4] at this
    exact this
  obtain ⟨gd, hcode⟩ := isSstore4_spec (stq_sstore _ hi)
  rw [hpc] at hc hf
  have hins := Option.some.inj (hc.symm.trans hcode)
  have hop : ins.op = .mem (sstoreV 4 (gloadBase (stqSite (4 * m + w)).pc)
      [.reg (memSrc (stqSite (4 * m + w)).pc 0), .reg (memSrc (stqSite (4 * m + w)).pc 1),
        .reg (memSrc (stqSite (4 * m + w)).pc 2), .reg (memSrc (stqSite (4 * m + w)).pc 3)]) :=
    congrArg Instr.op hins
  obtain ⟨x, hx, hxl⟩ := stq_base_bits L g d.dt (4 * m + w) hi
  have hxb : Value.bits 32 x = b32 x.toNat := by
    unfold b32
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hr : t.regs (gloadBase (stqSite (4 * m + w)).pc) = some (b32 x.toNat) := by
    rw [reg_at h (by rw [hpc]; exact (stq_live _ hi).1), hx, hxb]
  have hsub : t.sub = w := by
    have h2 := h.2.1
    rw [show sub d = d.site.sub from rfl, hs, stq_sub _ hi] at h2
    rw [h2]
    omega
  have hsrc : t.regs (memSrc (stqSite (4 * m + w)).pc w) = some (qWord d.dt (4 * m + w)) := by
    have h3 := reg_at h (r := memSrc (stqSite (4 * m + w)).pc w) (by
      rw [hpc]; exact (stq_live _ hi).2 w hw)
    have h5 : (4 * m + w) % 4 = w := by omega
    rw [h3]
    have := stq_src L g d.dt (4 * m + w) hi
    rw [h5] at this
    rw [this]
  have hbase : qStoreBase L g d.dt m = x.toNat := by
    unfold qStoreBase
    rw [← hpc4]
    simp [hx]
  have hlist : [Opnd.reg (memSrc (stqSite (4 * m + w)).pc 0),
      Opnd.reg (memSrc (stqSite (4 * m + w)).pc 1), Opnd.reg (memSrc (stqSite (4 * m + w)).pc 2),
      Opnd.reg (memSrc (stqSite (4 * m + w)).pc 3)][w]? =
      some (Opnd.reg (memSrc (stqSite (4 * m + w)).pc w)) := by
    interval_cases w <;> rfl
  obtain ⟨v', hsv, he⟩ := fires_st_reg (v := qWord d.dt (4 * m + w)) hop hsub hr hxl hlist
    (by simp [readValue, readReg, hsrc, pure, Except.pure]) rfl (Or.inr (Or.inr rfl)) hf
  refine ⟨v', hsv, ?_⟩
  rw [he, evPc, hpc, hbase]

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
