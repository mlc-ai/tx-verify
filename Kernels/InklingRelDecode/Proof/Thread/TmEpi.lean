-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.TmGlobal
public import Kernels.InklingRelDecode.Proof.Thread.TmDStart
public import Kernels.InklingRelDecode.Proof.Thread.TmSm
public import Kernels.InklingRelDecode.Proof.Thread.EpiAll

@[expose] public section

/-! # The epilogue's sites are not undefined behaviour

Every site. The `tcgen05.ld` reads at `%r1827 = (bw * 2 ^ 21 + c0) % 2 ^ 32`: the recorded lane
bits `bw` are 0 or the warp register `w` (`Inv.lane`), which is the thread's warp (the conjunct of
`DComp.Inv` at an epilogue state), so the lane field is 0 or the warp's lane base, and the column
base leaves room for the load (`Prm.Ok.c0col`). The poll of
`o_final` and the stores use the alignment facts of `Prm.Ok`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Tm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

/-- Both halves of a product pair have four bytes. -/
theorem prod_halves (d : D) (q : Nat) :
    (splitValue 64 (d.prod q)).1.bytes = 4 ∧ (splitValue 64 (d.prod q)).2.bytes = 4 := by
  unfold D.prod
  by_cases hsk : d.sk = true
  · simp [hsk, joinValue, splitValue, b32, Value.bytes]
  · have hsk' : d.sk = false := by simpa using hsk
    simp only [hsk', Bool.false_eq_true, ↓reduceIte]
    obtain ⟨x, y, hxy, hx, hy⟩ := mulOut_pair d.pr.cpair
      (joinValue (d.o.getD (2 * q) (b32 0)) (d.o.getD (2 * q + 1) (b32 0)))
    rw [hxy]
    exact ⟨hx, hy⟩

/-- A word of the product has four bytes: the halves of a pair of four-byte values. -/
theorem word_bytes (d : D) (k : Nat) : (d.word k).bytes = 4 := by
  unfold D.word
  split
  · exact (prod_halves d _).1
  · exact (prod_halves d _).2

/-- **The epilogue's sites have no undefined-behaviour template.** -/
theorem tmpl_ok (hpre : Pre Q L mem0) {d : D} {ins : Instr} (hi : Inv d)
    (hw : d.pr.w = g % L.block / 32) (hsub : t.sub = 0) (hH : Holds t.regs (facts d))
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hsa := hpre.sharedAlignment
  have hsr := hpre.sharedRange
  have hok := hi.ok
  obtain ⟨s, pr, o, sk⟩ := d
  cases s
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_5)
    have hr := holds_reg (r := 624) (v := b32 pr.mb) hH (by table_decide)
      (by simp [valueOf, D.table, D.scalars, lookupLit])
    have hp := holds_reg (r := 1760) (v := zero32) hH (by table_decide)
      (by simp [valueOf, D.table, D.scalars, lookupLit])
    refine mbarWait_bits_ok hr ?_ ⟨_, readBits_bits hp⟩ f
    have h1 := hok.mb
    have h2 := hok.mb8
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, wrapAddr_ofNat (by omega)]
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_15)
    exact shfl_imm_ok (p := none) (x := BitVec.ofNat 64 pr.w) (.inr rfl) hb
      (holds_reg hH (by table_decide) (by simp [valueOf, D.table, D.scalars, lookupLit, b32])) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemLoad_2)
    have hr : t.regs 1827 = some (b32 pr.taddr) :=
      holds_reg hH (by table_decide) (by simp [valueOf, D.table, D.scalars, lookupLit])
    refine tcLd_ok hb (by decide) hr (Nat.mod_lt _ (by decide)) ?_ f
    have h1 : pr.w < 4 := hok.w
    have h2 : pr.c0 + 256 ≤ 2 ^ 16 := hok.c0col
    have hw' : pr.w = g % L.block / 32 := hw
    rcases (hi.lane : pr.bw = 0 ∨ pr.bw = pr.w) with hbw | hbw
    · have he : pr.taddr = pr.c0 := by
        unfold Prm.taddr M32
        rw [hbw]
        omega
      refine tcDataAddressOk_of_row_zero ?_ ?_
      · simp only [TcShape.splitOk, decide_eq_true_eq, he]
        omega
      · rw [he]
        omega
    · have he : pr.taddr = g % L.block / 32 % 4 * 2097152 + pr.c0 := by
        unfold Prm.taddr M32
        rw [hbw]
        omega
      rw [he]
      exact Sm.addr_ok (by norm_num) (by omega) rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_4)
    exact plainOk_tmpl hb rfl f
  · have hc' : kernel.code[2682]? = some ins := hc
    obtain rfl := Option.some.inj (hc'.symm.trans code_stLse)
    have hr : t.regs 2379 = some (b64 pr.lAddr) :=
      holds_reg hH (by table_decide) (by simp [valueOf, D.table, D.scalars, lookupLit, b64])
    have hv : t.regs 1831 = some pr.lseWord :=
      holds_reg hH (by table_decide) (by simp [valueOf, D.table, D.scalars, lookupLit])
    refine gstore32_ok hsub hr (Nat.mod_lt _ (by decide)) hv ?_ ?_ f
    · unfold Prm.lseWord
      split
      · rfl
      · exact hok.lse
    · have h4 : pr.lb % 4 = 0 := hok.lb4
      unfold Prm.lAddr M64
      omega
  · rename_i k
    have hc' : kernel.code[stPc k.val]? = some ins := hc
    obtain rfl := Option.some.inj (hc'.symm.trans (code_stO k.val k.isLt))
    have hr : t.regs (2380 + k.val) = some (b64 ((pr.oAddr + 4 * k.val) % M64)) :=
      holds_reg hH (st_addr_live k.val k.isLt) (valueOf_addr _ k.isLt)
    have hv : t.regs (1832 + k.val) = some (D.word ⟨.stO k, pr, o, sk⟩ k.val) :=
      holds_reg hH (st_word_live k.val k.isLt) (valueOf_word _ k.isLt)
    refine gstore32_ok hsub hr (Nat.mod_lt _ (by decide)) hv (word_bytes _ _) ?_ f
    have h4 : pr.ob % 4 = 0 := hok.ob4
    unfold Prm.oAddr M64
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_34)
    exact barSync_imm_ok (id := 1) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_9)
    exact plainOk_tmpl hb (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_76)
    refine storeAccess_ok rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) ?_
      (o := .imm 50529027) (by simp [hsub]) readValue_imm f
    exact ⟨_, accessLoc_sharedSym (off := 213336) rfl rfl rfl (by omega),
      by simp [DType.width]; omega⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_35)
    exact barSync_imm_ok (id := 1) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_36)
    exact barSync_imm_ok (id := 0) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemDealloc_0)
    exact tcDealloc_imm_ok hb (v := b32 pr.tm) (x := BitVec.ofNat 64 pr.tm)
      (holds_reg hH (by table_decide) (by simp [valueOf, D.table, D.scalars, lookupLit]))
      (by simp [b32, Value.regBits]) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    exact plainOk_tmpl hb rfl f

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
