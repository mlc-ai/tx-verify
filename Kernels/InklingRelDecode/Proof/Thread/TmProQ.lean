-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.TmBase
public import Kernels.InklingRelDecode.Proof.Thread.FootQ

@[expose] public section

/-! # The prologue's query stores are not undefined behaviour

Element `w` of the `m`-th `st.shared.v4.b32` (sites `stq0_0` … `stq7_3`) stores the packed word
`joinValue (q (2 i)) (q (2 i + 1))` (`i = 4 m + w`) of two loaded query values at
`qStoreBase + 4 w`.

* The address: `qStoreBase` is `sharedBase + 196608 + 2048 · group + qSwz tid` (`qStoreBase_form`),
  a multiple of 16, so element `w` is 4-aligned and the vector is 16-aligned.
* The value: the store's width is the instruction's (`.b32`), not the value's. `storeValue 32`
  writes a value of four bytes unchanged and truncates a wider value that has a bit pattern;
  `joinValue` of two 2-byte values is a pair or a whole value of four bytes, or a raw `.bits (2 w)`
  of four or five bytes (`storeValue_join`). So the store is defined for every pair of 2-byte
  values (`ProA.Inv.qb`), and the machine needs no stronger fact about the loaded words. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Tm
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {t : TState}

/-- **A 32-bit store of two packed 2-byte values has a value**: four bytes, or a wider raw
pattern that the store truncates. -/
theorem storeValue_join {a b : Value} (ha : a.bytes = 2) (hb : b.bytes = 2) :
    ∃ v, storeValue 32 (joinValue a b) = .ok v := by
  have hp : (Value.pair a b).bytes = 32 / 8 := by simp [Value.bytes, ha, hb]
  unfold joinValue
  split
  · rename_i whole n whole' off m
    split_ifs with h
    · simp only [Value.bytes] at ha hb
      exact ⟨_, storeValue_of_bytes (by rw [h.2.2]; omega)⟩
    · exact ⟨_, storeValue_of_bytes hp⟩
  · rename_i w x w' y
    split_ifs with h
    · simp only [Value.bytes] at ha hb
      by_cases h4 : 2 * w / 8 = 32 / 8
      · refine ⟨_, storeValue_of_bytes ?_⟩
        simp only [Value.bytes]
        exact h4
      · have hlt : 32 / 8 < 2 * w / 8 := by omega
        refine ⟨.bits 32 (truncBits 32 (BitVec.ofNat 64 (x ||| y <<< w).toNat)), ?_⟩
        have h4' : (Value.bits (2 * w) (x ||| y <<< w)).bytes ≠ 32 / 8 := h4
        have hlt' : 32 / 8 < (Value.bits (2 * w) (x ||| y <<< w)).bytes := hlt
        simp only [storeValue, h4', hlt', ↓reduceIte]
        rfl
    · exact ⟨_, storeValue_of_bytes hp⟩
  · exact ⟨_, storeValue_of_bytes hp⟩

/-- A weak store through a register address that `effAddr` locates, aligned to its element
size, of a register whose value `storeValue` accepts at the store's width, is not undefined
behaviour. -/
theorem storeDirect_sv_ok {A : List Assumption} {a : MemAccess} {sp : Space} {base w : Nat}
    {o : Opnd} (hr : a.rule = some .threadAccess) (hl : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .store) (hs : a.sem = .weak)
    (hpos : 0 < a.elem.width / 8)
    (he : ∃ loc, effAddr L g t sp base a.addr.off = .ok loc ∧
      loc.addr % (a.elem.width / 8 * a.srcs.length) = 0)
    (hsrc : a.srcs[t.sub]? = some o)
    (hv : ∃ v x, readValue L g t a.elem.width o = .ok v ∧ storeValue a.elem.width v = .ok x)
    (f : Fault) : eventTmpl A L g t (.mem a) ≠ .ub f := by
  obtain ⟨loc, he, hal⟩ := he
  obtain ⟨v, x, hv, hsv⟩ := hv
  rw [eventTmpl, memTmpl_direct_weakStore hr hl hb hk hs]
  simp only [storeTmpl, he, bind, Except.bind]
  rw [elemAcc_ok hpos hal]
  simp [hsrc, hv, hsv]

/-- **A query store is not undefined behaviour** for any 2-byte loaded values. -/
theorem stq_ok {i : Nat} (hi : i < 32) {dt : Dat} {ins : Instr} (ht : tidOf L g < 128)
    (hs : SbRoom L) (hsa : L.sharedBase % 1024 = 0) (hqb : ∀ j, (dt.q j).bytes = 2)
    (hsub : t.sub = (stqSite i).sub) (hH : Holds t.regs (facts L g ⟨stqSite i, dt⟩))
    (hc : kernel.code[(stqSite i).pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  obtain ⟨gd, hcode⟩ := isSstore4_spec (stq_sstore _ hi)
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  have hm : i / 4 < 8 := by omega
  have hw : i % 4 < 4 := Nat.mod_lt _ (by decide)
  obtain ⟨x, hx, hxl⟩ := stq_base_bits L g dt i hi
  have hxb : Value.bits 32 x = b32 x.toNat := by
    unfold b32
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hr : t.regs (gloadBase (stqSite i).pc) = some (b32 x.toNat) := by
    rw [← hxb]
    exact holds_reg hH (stq_live _ hi).1 hx
  have hbase : qStoreBase L g dt (i / 4) = x.toNat := by
    unfold qStoreBase
    rw [← stq_pc i hi]
    simp [hx]
  have hform := qStoreBase_form L g dt ht hs hm
  have hg := qGroup_lt _ hm
  have h2 := qSwz_spec _ ht
  have hsub' : t.sub = i % 4 := by rw [hsub, stq_sub _ hi]
  have hsrc : t.regs (memSrc (stqSite i).pc (i % 4)) = some (qWord dt i) := by
    rw [← stq_src L g dt i hi]
    exact holds_reg hH ((stq_live _ hi).2 _ hw) rfl
  have hlist : [Opnd.reg (memSrc (stqSite i).pc 0), Opnd.reg (memSrc (stqSite i).pc 1),
      Opnd.reg (memSrc (stqSite i).pc 2), Opnd.reg (memSrc (stqSite i).pc 3)][t.sub]? =
      some (Opnd.reg (memSrc (stqSite i).pc (i % 4))) := by
    rw [hsub']
    generalize i % 4 = w at hw ⊢
    interval_cases w <;> rfl
  obtain ⟨v, hv⟩ := storeValue_join (hqb (2 * i)) (hqb (2 * i + 1))
  refine storeDirect_sv_ok (a := sstoreV 4 (gloadBase (stqSite i).pc)
      [.reg (memSrc (stqSite i).pc 0), .reg (memSrc (stqSite i).pc 1),
        .reg (memSrc (stqSite i).pc 2), .reg (memSrc (stqSite i).pc 3)])
    rfl rfl rfl rfl rfl (by simp [sstoreV, DType.width]) ?_ hlist
    ⟨_, v, readValue_reg hsrc, (hv : storeValue 32 (qWord dt i) = .ok v)⟩ f
  refine ⟨_, effAddr_b32_off (off := 0) hr (by unfold SbRoom at hs; omega), ?_⟩
  show (x.toNat + 0) % (32 / 8 * 4) = 0
  unfold SbRoom at hs
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
