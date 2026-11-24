-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.CtaGroup
import Kernels.TmlFa4Fwd.Proof.Mma.Export.DescOf
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Recv
public import Lemmas.Execution.ControlProjection
public import Lemmas.Execution.InstructionProjection
public import Lemmas.Flow.RegBits
import Kernels.TmlFa4Fwd.Flow.Code.Part034
import Kernels.TmlFa4Fwd.Flow.Code.Part035
import Kernels.TmlFa4Fwd.Flow.Code.Part036
import Kernels.TmlFa4Fwd.Flow.Code.Part037
import Kernels.TmlFa4Fwd.Flow.Code.Part038
import Kernels.TmlFa4Fwd.Flow.Code.Part039
import Kernels.TmlFa4Fwd.Flow.Code.Part040
import Kernels.TmlFa4Fwd.Flow.Code.Part041

@[expose] public section

/-! # The MMA warp's `tcgen05.mma` issues are no undefined behaviour

An MMA issue faults when a shared descriptor does not decode, when the instruction descriptor does
not decode, when its enable operand is no predicate, when the CTA group does not resolve, and (A in
Tensor Memory) when the A column plus its offset leaves the column range (`mmaSmem_ok`,
`mmaTmem_ok`). The decoded issues of the MMA warp have the instruction descriptors `0x8200490` and
`0x8210490`, which decode, and descriptors `lo ||| dhi << 32` whose high word is fixed and whose
low word is below `2 ^ 31` with its low 16 bits below `2 ^ 15` (`decode_join`): the B words are a
broadcast word of the pattern `BW` plus at most 1030, the Q descriptors are `qx L` plus at most
1030, moved by `-2048` (`qx` is `65536` plus `(sb + 35840) / 16`, at least 2240 by
`Pre.shared`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem dhi_val : dhi.toNat = 1073758272 := by
  simp only [dhi, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]; norm_num

theorem decode_some {x : Nat} (h1 : x / 2 ^ 61 % 8 = 2)
    (h2 : x < 2 ^ 64 ∧ x / 2 ^ 15 % 2 = 0 ∧ x / 2 ^ 31 % 2 = 0 ∧ x / 2 ^ 46 % 8 = 1 ∧
      x / 2 ^ 54 % 128 = 0) : ∃ dsc, TcShared.decode x = some dsc := by
  unfold TcShared.decode
  rw [h1]
  simp only [TcShared.decodeSwizzle]
  rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
  exact ⟨_, rfl⟩

/-- **A descriptor with the fixed high word decodes** when its low word is below `2 ^ 31` and its
bit 15 is clear. -/
theorem decode_join {lo : BitVec 64} (hlo : lo.toNat < 2 ^ 31) (h15 : lo.toNat % 65536 < 32768) :
    ∃ dsc, TcShared.decode (lo ||| dhi <<< 32).toNat = some dsc := by
  rw [toNat_join (by omega), dhi_val]
  generalize hx : lo.toNat + 1073758272 * 2 ^ 32 = x
  have h1 : x / 2 ^ 61 % 8 = 2 := by omega
  have h2 : x < 2 ^ 64 ∧ x / 2 ^ 15 % 2 = 0 ∧ x / 2 ^ 31 % 2 = 0 ∧ x / 2 ^ 46 % 8 = 1 ∧
      x / 2 ^ 54 % 128 = 0 := by omega
  exact decode_some h1 h2

theorem tb64 (x : BitVec 64) : truncBits 64 x = x := by
  apply BitVec.eq_of_toNat_eq; simp [truncBits, x.isLt]

theorem rb_bits {t : TState} {r w w' : Nat} {x : BitVec 64} (h : t.regs r = some (.bits w' x)) :
    readBits L g t w (.reg r) = .ok (truncBits w x) :=
  readBits_regBits h rfl

/-- **An MMA issue with A in shared memory has a rule** when its registers hold words, its
descriptors decode, its enable operand is a predicate and the CTA group is the issuer's. -/
theorem mmaSmem_ok {t : TState} {dst ad bd idr : Nat} {en : Opnd} {xd A B xi : BitVec 64}
    {c : TcMma.Collectors} (hg : g < L.threads)
    (hcg : L.ctaGroup (g / L.block) .one = some [g / L.block])
    (hd : t.regs dst = some (.bits 32 xd)) (ha : t.regs ad = some (.bits 64 A))
    (hb : t.regs bd = some (.bits 64 B)) (hi : t.regs idr = some (.bits 32 xi))
    (hdA : ∃ x, TcShared.decode A.toNat = some x) (hdB : ∃ x, TcShared.decode B.toNat = some x)
    (hI : ∃ dsc, TcMma.decode .one false .f16 (truncBits 32 xi).toNat = some dsc ∧
      dsc.group = .one)
    (hen : ∃ acc, mmaEnable t en = .ok acc) (f : Fault) :
    mmaSmemTmpl L g t .one false .f16 dst (.reg ad) (.reg bd) (.reg idr)
      (List.replicate 4 (.imm 0)) en none c ≠ .ub f := by
  obtain ⟨da, hda⟩ := hdA
  obtain ⟨db, hdb⟩ := hdB
  obtain ⟨dsc, hdsc, hgrp⟩ := hI
  obtain ⟨acc, hacc⟩ := hen
  have hMask : (List.replicate 4 (.imm 0)).mapM (readBits L g t 32) =
      .ok (List.replicate 4 (0 : BitVec 64)) := rfl
  have hops : ∃ s, TcMma.makeOperands L (g / L.block) dsc da db = some s := by
    simp [TcMma.makeOperands, hgrp, hcg]
  obtain ⟨sp, hsp⟩ := hops
  simp only [mmaSmemTmpl, hg, rb_bits hd, rb_bits ha, rb_bits hb, rb_bits hi, tb64, hMask, hacc,
    zeroColumnMaskOk, List.length_replicate, CtaGroup.size, hda, hdb, hdsc, hsp, ↓reduceIte,
    bind, Except.bind, pure, Except.pure, ofExec]
  simp

/-- **An MMA issue with A in Tensor Memory has a rule** when, in addition, the A column plus its
offset stays in the column range. -/
theorem mmaTmem_ok {t : TState} {dst ta bd idr : Nat} {aoff : Int} {en : Opnd}
    {xd xa B xi : BitVec 64} {c : TcMma.Collectors} (hg : g < L.threads)
    (hcg : L.ctaGroup (g / L.block) .one = some [g / L.block])
    (hd : t.regs dst = some (.bits 32 xd)) (ha : t.regs ta = some (.bits 32 xa))
    (hb : t.regs bd = some (.bits 64 B)) (hi : t.regs idr = some (.bits 32 xi))
    (hcol : 0 ≤ ((truncBits 32 xa).toNat % 2 ^ 16 : Int) + aoff ∧
      ((truncBits 32 xa).toNat % 2 ^ 16 : Int) + aoff < 2 ^ 16)
    (hdB : ∃ x, TcShared.decode B.toNat = some x)
    (hI : ∃ dsc, TcMma.decode .one false .f16 (truncBits 32 xi).toNat = some dsc ∧
      dsc.transposeA = false ∧ dsc.group = .one)
    (hen : ∃ acc, mmaEnable t en = .ok acc) (f : Fault) :
    mmaTmemTmpl L g t .one false .f16 dst ta aoff (.reg bd) (.reg idr)
      (List.replicate 4 (.imm 0)) en none c ≠ .ub f := by
  obtain ⟨db, hdb⟩ := hdB
  obtain ⟨dsc, hdsc, htr, hgrp⟩ := hI
  obtain ⟨acc, hacc⟩ := hen
  have hMask : (List.replicate 4 (.imm 0)).mapM (readBits L g t 32) =
      .ok (List.replicate 4 (0 : BitVec 64)) := rfl
  have hops : ∃ s, TcMma.makeOperands L (g / L.block) dsc db db = some s := by
    simp [TcMma.makeOperands, hgrp, hcg]
  obtain ⟨sp, hsp⟩ := hops
  simp only [mmaTmemTmpl, hg, rb_bits hd, rb_bits ha, rb_bits hb, rb_bits hi, tb64, hMask, hacc,
    zeroColumnMaskOk, List.length_replicate, CtaGroup.size, hdb, hdsc, hsp, htr, tmemOffset, hcol,
    ↓reduceIte, bind, Except.bind, pure, Except.pure, ofExec]
  simp

theorem and_16320 (w : Nat) (h1 : w % 64 = 0) (h2 : w < 16384) : w &&& 16320 = w := by
  have e1 : w &&& 16383 = w := by
    rw [show (16383 : Nat) = 2 ^ 14 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  have e2 : w &&& 63 = 0 := by
    rw [show (63 : Nat) = 2 ^ 6 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  have e3 : (16383 : Nat) = 16320 ||| 63 := by decide
  rw [e3, Nat.and_or_distrib_left, e2, Nat.or_zero] at e1
  exact e1

/-- **The Q descriptors' base** is `65536` plus `(sb + 35840) / 16`, so at least 67776. -/
theorem qx_val (hp : Pre p L m) :
    67776 ≤ (qx L).toNat ∧ (qx L).toNat ≤ 69632 := by
  have hs := hp.shared
  have h0 : Iv L.sharedBase L.sharedBase (sbW L) := iv_lit _ (by omega)
  have h1 : Iv ((L.sharedBase + 35840) / 2 ^ 4) ((L.sharedBase + 35840) / 2 ^ 4)
      (shru (addi (sbW L) 35840) 4) :=
    iv_shru (iv_addi h0 35840 (by omega)) 4 (by decide) (by omega)
  have hw : (shru (addi (sbW L) 35840) 4).toNat = (L.sharedBase + 35840) / 16 := by
    unfold Iv at h1; omega
  have ha : (andi (shru (addi (sbW L) 35840) 4) 16320).toNat = (L.sharedBase + 35840) / 16 := by
    show (r32 (shru (addi (sbW L) 35840) 4) &&& i32 16320).toNat = _
    rw [BitVec.toNat_and, toNat_r32, show (i32 16320).toNat = 16320 from rfl, hw,
      Nat.mod_eq_of_lt (by omega)]
    exact and_16320 _ (by omega) (by omega)
  have hi : (i32 65536).toNat = 2 ^ 16 := rfl
  have hr : (r32 (andi (shru (addi (sbW L) 35840) 4) 16320)).toNat =
      (L.sharedBase + 35840) / 16 := by rw [toNat_r32, ha]; omega
  simp only [qx, ori, BitVec.toNat_or, hr, hi]
  rw [Nat.or_two_pow_eq_add_of_lt (by omega)]
  omega

/-- **The Q descriptors decode** at every site past the broadcast. -/
theorem qv_decode (hp : Pre p L m) (b : Bool) (i : Fin 8) :
    ∃ dsc, TcShared.decode (qv L b i).toNat = some dsc := by
  have hx := qx_val hp
  have hlo : 67776 ≤ (qlo (qx L) i).toNat ∧ (qlo (qx L) i).toNat ≤ 70662 := by
    unfold qlo
    split
    · omega
    · have hq : ∃ n : Nat, qoff i = n ∧ n ≤ 1030 := by
        fin_cases i <;> simp only [qoff] <;> exact ⟨_, rfl, by decide⟩
      obtain ⟨n, hn, hn'⟩ := hq
      rw [hn]
      have := iv_addi (show Iv (qx L).toNat (qx L).toNat (qx L) from ⟨le_rfl, le_rfl⟩) n
        (by omega)
      unfold Iv at this
      omega
  cases b
  · simp only [qv, Bool.false_eq_true, ↓reduceIte, qinit]
    exact decode_join (by omega) (by omega)
  · simp only [qv, ↓reduceIte, qinit]
    rw [qstep_join (by omega)]
    have : Iv ((qlo (qx L) i).toNat - 2048) ((qlo (qx L) i).toNat - 2048)
        (addi (qlo (qx L) i) (-2048)) :=
      iv_addi_neg (show Iv (qlo (qx L) i).toNat (qlo (qx L) i).toNat (qlo (qx L) i) from
        ⟨le_rfl, le_rfl⟩) 2048 (by omega) (by omega)
    unfold Iv at this
    exact decode_join (by omega) (by omega)

/-- **A B descriptor decodes**: a broadcast word of the pattern plus at most 1030. -/
theorem bdesc_decode {x : BitVec 64} (hx : BW x) {n : Nat} (hn : n ≤ 1030) :
    ∃ dsc, TcShared.decode (addi x n ||| dhi <<< 32).toNat = some dsc := by
  unfold BW at hx
  have := iv_addi (show Iv x.toNat x.toNat x from ⟨le_rfl, le_rfl⟩) n (by omega)
  unfold Iv at this
  exact decode_join (by omega) (by omega)

/-- A B descriptor whose low word is within 1030 above a broadcast word decodes. -/
theorem bdesc_iv {x lo : BitVec 64} (hx : BW x) (hlo : Iv x.toNat (x.toNat + 1030) lo) :
    ∃ dsc, TcShared.decode (lo ||| dhi <<< 32).toNat = some dsc := by
  unfold BW at hx; unfold Iv at hlo
  exact decode_join (by omega) (by omega)

/-- A Tensor Memory A column of the pattern plus at most 56 stays in the column range. -/
theorem col_ok {x : BitVec 64} (hx : BW x) {n : Nat} (hn : n ≤ 56) :
    0 ≤ ((truncBits 32 x).toNat % 2 ^ 16 : Int) + (n : Int) ∧
      ((truncBits 32 x).toNat % 2 ^ 16 : Int) + (n : Int) < 2 ^ 16 := by
  unfold BW at hx
  rw [toNat_tb32]
  constructor <;> omega

theorem iv_self (x : BitVec 64) (_hx : x.toNat < 2 ^ 27) : Iv x.toNat (x.toNat + 1030) x :=
  ⟨le_rfl, by omega⟩

/-- `iv_addi` for a nonnegative integer immediate as the code states it. -/
theorem iv_addiI {a b : Nat} {x : BitVec 64} (hx : Iv a b x) (n : Int) (h0 : 0 ≤ n)
    (h : b + n.toNat < 2 ^ 32) : Iv (a + n.toNat) (b + n.toNat) (addi x n) := by
  have e : n = ((n.toNat : Nat) : Int) := (Int.toNat_of_nonneg h0).symm
  have := iv_addi hx n.toNat h
  rw [← e] at this
  exact this

/-- **The QK B descriptors' low words** are within 1030 above their broadcast word. -/
theorem qlo_bw {x : BitVec 64} (hx : BW x) (j : Fin 8) :
    Iv x.toNat (x.toNat + 1030) (qlo x j) := by
  unfold BW at hx
  have h0' : Iv x.toNat x.toNat x := ⟨le_rfl, le_rfl⟩
  unfold qlo
  split
  · exact iv_self x hx.1
  · have hq : ∃ n : Nat, qoff j = n ∧ n ≤ 1030 := by
      fin_cases j <;> simp only [qoff] <;> exact ⟨_, rfl, by decide⟩
    obtain ⟨n, hn, hn'⟩ := hq
    rw [hn]
    exact iv_mono (by omega) (by omega) (iv_addi h0' n (by omega))

/-- **The PV B descriptors' low words** are within 896 above their broadcast word. -/
theorem pvlo_bw {x : BitVec 64} (hx : BW x) (j : Nat) (hj : j < 8) :
    Iv x.toNat (x.toNat + 1030) (pvlo x j) := by
  unfold BW at hx
  have h0 : Iv x.toNat x.toNat x := ⟨le_rfl, le_rfl⟩
  have h1 : ∀ n : Int, 0 ≤ n → n ≤ 640 → Iv x.toNat (x.toNat + 1030) (addi x n) :=
    fun n hn hn' => iv_mono (by omega) (by omega) (iv_addiI h0 n hn (by omega))
  interval_cases j
  · exact iv_self x hx.1
  · exact h1 _ (by decide) (by decide)
  · exact h1 _ (by decide) (by decide)
  · exact h1 _ (by decide) (by decide)
  · exact h1 _ (by decide) (by decide)
  · exact h1 _ (by decide) (by decide)
  · exact iv_mono (by omega) (by omega)
      (iv_addiI (iv_addiI h0 640 (by decide) (by omega)) 128 (by decide) (by omega))
  · exact iv_mono (by omega) (by omega) (iv_addiI (iv_addiI (iv_addiI h0 640 (by decide)
      (by omega)) 128 (by decide) (by omega)) 128 (by decide) (by omega))

theorem mmaEnable_reg {t : TState} {r : Nat} {b : Bool} (h : t.regs r = some (.pred b)) :
    mmaEnable t (.reg r) = .ok b := by
  simp [mmaEnable, readReg, h, bind, Except.bind, pure, Except.pure]

set_option hygiene false in
/-- The QK issue of block `b`, step `j` (one theorem per issue, with literal indices). -/
macro "qk_site " n:ident b:num j:num k:num : command => `(
set_option maxHeartbeats 4000000 in
theorem $n (hp : Pre p L m) (hg : g < L.threads) {v : V} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (h : (code p L g (ent p L)).AtD ⟨.qk $b $j, v⟩ t)
    (hc : kernel.code[(code p L g (ent p L)).pc ⟨.qk $b $j, v⟩]? = some ins)
    (hf : Fires ((code p L g (ent p L)).pc ⟨.qk $b $j, v⟩)
      (eventTmpl Assumptions.all L g t ins.op) e o)
    (hD : DOk L ⟨.qk $b $j, v⟩) (f : Fault) : e.kind ≠ .ub f := by
  replace h : At t (Site.qk $b $j).pc (facts p L g (ent p L) ⟨.qk $b $j, v⟩) := h
  replace hc : kernel.code[(Site.qk $b $j).pc]? = some ins := hc
  intro hk
  have hu := fires_ub hf hk
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have hq : v.qd = qv L (neg (.qk $b $j)) := hD.2 rfl
  have hx : BW (sAt v $k) := hD.1 $k
  refine mmaSmem_ok hg (Kernels.TmlFa4Fwd.Mma.singleCtaGroup hp hg)
    (reg_bits h (by lit_mem) rfl) (reg_bits h (by lit_mem) rfl)
    (reg_bits h (by lit_mem) rfl) (reg_bits h (by lit_mem) rfl) ?_ ?_ ⟨_, rfl, rfl⟩ ⟨_, rfl⟩ f hu
  · rw [hq]; exact qv_decode hp _ _
  · exact bdesc_iv hx (qlo_bw hx _))

set_option hygiene false in
/-- The PV issue of block `b`, step `j`. -/
macro "pv_site " n:ident b:num j:num ka:num kb:num : command => `(
set_option maxHeartbeats 4000000 in
theorem $n (hp : Pre p L m) (hg : g < L.threads) {v : V} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (h : (code p L g (ent p L)).AtD ⟨.pv $b $j, v⟩ t)
    (hc : kernel.code[(code p L g (ent p L)).pc ⟨.pv $b $j, v⟩]? = some ins)
    (hf : Fires ((code p L g (ent p L)).pc ⟨.pv $b $j, v⟩)
      (eventTmpl Assumptions.all L g t ins.op) e o)
    (hD : DOk L ⟨.pv $b $j, v⟩) (f : Fault) : e.kind ≠ .ub f := by
  replace h : At t (Site.pv $b $j).pc (facts p L g (ent p L) ⟨.pv $b $j, v⟩) := h
  replace hc : kernel.code[(Site.pv $b $j).pc]? = some ins := hc
  intro hk
  have hu := fires_ub hf hk
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have ha : BW (sAt v $ka) := hD.1 $ka
  have hx : BW (sAt v $kb) := hD.1 $kb
  refine mmaTmem_ok hg (Kernels.TmlFa4Fwd.Mma.singleCtaGroup hp hg)
    (reg_bits h (by lit_mem) rfl) (reg_bits h (by lit_mem) rfl)
    (reg_bits h (by lit_mem) rfl) (reg_bits h (by lit_mem) rfl) (col_ok ha (by decide)) ?_
    ⟨_, rfl, rfl, rfl⟩ ?_ f hu
  · exact bdesc_iv hx (pvlo_bw hx _ (by decide))
  · first
      | exact ⟨_, mmaEnable_reg (reg_pred h (by lit_mem) rfl)⟩
      | exact ⟨_, rfl⟩)

qk_site qk_0_0 0 0 0
qk_site qk_0_1 0 1 0
qk_site qk_0_2 0 2 0
qk_site qk_0_3 0 3 0
qk_site qk_0_4 0 4 0
qk_site qk_0_5 0 5 0
qk_site qk_0_6 0 6 0
qk_site qk_0_7 0 7 0
qk_site qk_1_0 1 0 0
qk_site qk_1_1 1 1 0
qk_site qk_1_2 1 2 0
qk_site qk_1_3 1 3 0
qk_site qk_1_4 1 4 0
qk_site qk_1_5 1 5 0
qk_site qk_1_6 1 6 0
qk_site qk_1_7 1 7 0
qk_site qk_2_0 2 0 6
qk_site qk_2_1 2 1 6
qk_site qk_2_2 2 2 6
qk_site qk_2_3 2 3 6
qk_site qk_2_4 2 4 6
qk_site qk_2_5 2 5 6
qk_site qk_2_6 2 6 6
qk_site qk_2_7 2 7 6
qk_site qk_3_0 3 0 6
qk_site qk_3_1 3 1 6
qk_site qk_3_2 3 2 6
qk_site qk_3_3 3 3 6
qk_site qk_3_4 3 4 6
qk_site qk_3_5 3 5 6
qk_site qk_3_6 3 6 6
qk_site qk_3_7 3 7 6
pv_site pv_0_0 0 0 3 4
pv_site pv_0_1 0 1 3 4
pv_site pv_0_2 0 2 3 4
pv_site pv_0_3 0 3 3 4
pv_site pv_0_4 0 4 3 4
pv_site pv_0_5 0 5 3 4
pv_site pv_0_6 0 6 3 4
pv_site pv_0_7 0 7 3 4
pv_site pv_1_0 1 0 7 4
pv_site pv_1_1 1 1 7 4
pv_site pv_1_2 1 2 7 4
pv_site pv_1_3 1 3 7 4
pv_site pv_1_4 1 4 7 4
pv_site pv_1_5 1 5 7 4
pv_site pv_1_6 1 6 7 4
pv_site pv_1_7 1 7 7 4
pv_site pv_2_0 2 0 9 10
pv_site pv_2_1 2 1 9 10
pv_site pv_2_2 2 2 9 10
pv_site pv_2_3 2 3 9 10
pv_site pv_2_4 2 4 9 10
pv_site pv_2_5 2 5 9 10
pv_site pv_2_6 2 6 9 10
pv_site pv_2_7 2 7 9 10
pv_site pv_3_0 3 0 12 10
pv_site pv_3_1 3 1 12 10
pv_site pv_3_2 3 2 12 10
pv_site pv_3_3 3 3 12 10
pv_site pv_3_4 3 4 12 10
pv_site pv_3_5 3 5 12 10
pv_site pv_3_6 3 6 12 10
pv_site pv_3_7 3 7 12 10

/-- **No `tcgen05.mma` issue of the MMA warp is undefined behaviour** at a state that keeps its
descriptor words. -/
theorem mma_safe (hp : Pre p L m) (hg : g < L.threads) {d : D} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (h : (code p L g (ent p L)).AtD d t)
    (hc : kernel.code[(code p L g (ent p L)).pc d]? = some ins)
    (hf : Fires ((code p L g (ent p L)).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hD : DOk L d) (hs : (∃ b j, d.site = .qk b j) ∨ ∃ b j, d.site = .pv b j) (f : Fault) :
    e.kind ≠ .ub f := by
  obtain ⟨site, v⟩ := d
  rcases hs with ⟨b, j, hs⟩ | ⟨b, j, hs⟩ <;> simp only at hs <;> subst hs <;>
    fin_cases b <;> fin_cases j
  · exact qk_0_0 hp hg h hc hf hD f
  · exact qk_0_1 hp hg h hc hf hD f
  · exact qk_0_2 hp hg h hc hf hD f
  · exact qk_0_3 hp hg h hc hf hD f
  · exact qk_0_4 hp hg h hc hf hD f
  · exact qk_0_5 hp hg h hc hf hD f
  · exact qk_0_6 hp hg h hc hf hD f
  · exact qk_0_7 hp hg h hc hf hD f
  · exact qk_1_0 hp hg h hc hf hD f
  · exact qk_1_1 hp hg h hc hf hD f
  · exact qk_1_2 hp hg h hc hf hD f
  · exact qk_1_3 hp hg h hc hf hD f
  · exact qk_1_4 hp hg h hc hf hD f
  · exact qk_1_5 hp hg h hc hf hD f
  · exact qk_1_6 hp hg h hc hf hD f
  · exact qk_1_7 hp hg h hc hf hD f
  · exact qk_2_0 hp hg h hc hf hD f
  · exact qk_2_1 hp hg h hc hf hD f
  · exact qk_2_2 hp hg h hc hf hD f
  · exact qk_2_3 hp hg h hc hf hD f
  · exact qk_2_4 hp hg h hc hf hD f
  · exact qk_2_5 hp hg h hc hf hD f
  · exact qk_2_6 hp hg h hc hf hD f
  · exact qk_2_7 hp hg h hc hf hD f
  · exact qk_3_0 hp hg h hc hf hD f
  · exact qk_3_1 hp hg h hc hf hD f
  · exact qk_3_2 hp hg h hc hf hD f
  · exact qk_3_3 hp hg h hc hf hD f
  · exact qk_3_4 hp hg h hc hf hD f
  · exact qk_3_5 hp hg h hc hf hD f
  · exact qk_3_6 hp hg h hc hf hD f
  · exact qk_3_7 hp hg h hc hf hD f
  · exact pv_0_0 hp hg h hc hf hD f
  · exact pv_0_1 hp hg h hc hf hD f
  · exact pv_0_2 hp hg h hc hf hD f
  · exact pv_0_3 hp hg h hc hf hD f
  · exact pv_0_4 hp hg h hc hf hD f
  · exact pv_0_5 hp hg h hc hf hD f
  · exact pv_0_6 hp hg h hc hf hD f
  · exact pv_0_7 hp hg h hc hf hD f
  · exact pv_1_0 hp hg h hc hf hD f
  · exact pv_1_1 hp hg h hc hf hD f
  · exact pv_1_2 hp hg h hc hf hD f
  · exact pv_1_3 hp hg h hc hf hD f
  · exact pv_1_4 hp hg h hc hf hD f
  · exact pv_1_5 hp hg h hc hf hD f
  · exact pv_1_6 hp hg h hc hf hD f
  · exact pv_1_7 hp hg h hc hf hD f
  · exact pv_2_0 hp hg h hc hf hD f
  · exact pv_2_1 hp hg h hc hf hD f
  · exact pv_2_2 hp hg h hc hf hD f
  · exact pv_2_3 hp hg h hc hf hD f
  · exact pv_2_4 hp hg h hc hf hD f
  · exact pv_2_5 hp hg h hc hf hD f
  · exact pv_2_6 hp hg h hc hf hD f
  · exact pv_2_7 hp hg h hc hf hD f
  · exact pv_3_0 hp hg h hc hf hD f
  · exact pv_3_1 hp hg h hc hf hD f
  · exact pv_3_2 hp hg h hc hf hD f
  · exact pv_3_3 hp hg h hc hf hD f
  · exact pv_3_4 hp hg h hc hf hD f
  · exact pv_3_5 hp hg h hc hf hD f
  · exact pv_3_6 hp hg h hc hf hD f
  · exact pv_3_7 hp hg h hc hf hD f

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
