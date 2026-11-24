-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.DescOf
public import Kernels.TmlFa4Fwd.Proof.Lib.TmemRegion
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Desc
import Kernels.TmlFa4Fwd.Proof.Mma.Open
import Lemmas.Flow.RegBits
import Kernels.TmlFa4Fwd.Flow.Code.Part034
import Kernels.TmlFa4Fwd.Flow.Code.Part035
import Kernels.TmlFa4Fwd.Flow.Code.Part036
import Kernels.TmlFa4Fwd.Flow.Code.Part037
import Kernels.TmlFa4Fwd.Flow.Code.Part038
import Kernels.TmlFa4Fwd.Flow.Code.Part039
import Kernels.TmlFa4Fwd.Flow.Code.Part040
import Kernels.TmlFa4Fwd.Flow.Code.Part041

@[expose] public section

/-! # The operands of the MMA warp's `tcgen05.mma` issues

An MMA issue event of a QK site has the destination of its block's accumulator word, the shared A
descriptor of the Q stage and the B descriptor of the block's slot (`IssueQk`); a PV one reads A
from Tensor Memory at its block's A word plus `8 j` (`IssuePv`). Both have the dense `bf16 × bf16
→ f32` shape 128 × 128. Over the words a state records (`Mma.V`); the words' values are
`Mma/Export/Words.lean`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open Tm (qkDsc pvDsc)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The event of QK MMA `j` of block `b` at words `v`. -/
def IssueQk (L : Launch) (g : Nat) (v : V) (b : Fin 4) (j : Fin 8) (k : Kind) : Prop :=
  ∃ da db, TcShared.decode (qv L (neg (.qk b j)) j).toNat = some da ∧
    TcShared.decode (qlo (qkStart v b) j ||| dhi <<< 32).toNat = some db ∧
    k = .tc (.mma (truncBits 32 (qkAcc v b)).toNat
      ⟨qkDsc, da, db, g / L.block, g / L.block, none, {}⟩ (j.val != 0) [0, 0, 0, 0])

/-- The event of PV MMA `j` of block `b` at words `v`. -/
def IssuePv (L : Launch) (g : Nat) (v : V) (b : Fin 4) (j : Fin 8) (k : Kind) : Prop :=
  ∃ db, TcShared.decode (pvlo (pvB v b) j.val ||| dhi <<< 32).toNat = some db ∧
    k = .tc (.mma (truncBits 32 (pvAcc v b)).toNat
      ⟨pvDsc, db, db, g / L.block, g / L.block,
        some ((truncBits 32 (pvA v b)).toNat / 2 ^ 16 * 2 ^ 16 +
          (((truncBits 32 (pvA v b)).toNat % 2 ^ 16 : Int) + (8 * j.val : Nat)).toNat), {}⟩
      (if j.val = 0 then scmpi .ne .b v.accum 0 else true) [0, 0, 0, 0])

theorem fires_tc_kind {pc : Nat} {k : TcKind} {t' : TState} {tm : Tmpl} {e : Event}
    {o : Option TState} (hf : Fires pc tm e o) (ht : tm = .tc k t') : e.kind = .tc k := by
  subst ht
  simp only [Fires] at hf
  rw [hf.1]

/-- The issue of an MMA with A in shared memory. -/
theorem mmaSmem_issue {t : TState} {dst ad bd idr pc : Nat} {en : Opnd} {xd A B xi : BitVec 64}
    {dsc : TcMma.Descriptor} {acc : Bool} {e : Event} {o : Option TState} (hg : g < L.threads)
    (hcg : L.ctaGroup (g / L.block) .one = some [g / L.block])
    (hf : Fires pc (mmaSmemTmpl L g t .one false .f16 dst (.reg ad) (.reg bd) (.reg idr)
      (List.replicate 4 (.imm 0)) en none {}) e o)
    (hd : t.regs dst = some (.bits 32 xd)) (ha : t.regs ad = some (.bits 64 A))
    (hb : t.regs bd = some (.bits 64 B)) (hi : t.regs idr = some (.bits 32 xi))
    (hdA : ∃ x, TcShared.decode A.toNat = some x) (hdB : ∃ x, TcShared.decode B.toNat = some x)
    (hI : TcMma.decode .one false .f16 (truncBits 32 xi).toNat = some dsc)
    (hgrp : dsc.group = .one) (hen : mmaEnable t en = .ok acc) :
    ∃ da db, TcShared.decode A.toNat = some da ∧ TcShared.decode B.toNat = some db ∧
      e.kind = .tc (.mma (truncBits 32 xd).toNat
        ⟨dsc, da, db, g / L.block, g / L.block, none, {}⟩ acc [0, 0, 0, 0]) := by
  obtain ⟨da, hda⟩ := hdA
  obtain ⟨db, hdb⟩ := hdB
  have hMask : (List.replicate 4 (.imm 0)).mapM (readBits L g t 32) =
      .ok (List.replicate 4 (0 : BitVec 64)) := rfl
  have hsp : TcMma.makeOperands L (g / L.block) dsc da db =
      some ⟨dsc, da, db, g / L.block, g / L.block, none, {}⟩ := by
    simp [TcMma.makeOperands, hgrp, hcg]
  refine ⟨da, db, hda, hdb, fires_tc_kind hf (t' := next t) ?_⟩
  simp only [mmaSmemTmpl, hg, rb_bits hd, rb_bits ha, rb_bits hb, rb_bits hi, tb64, hMask, hen,
    zeroColumnMaskOk, List.length_replicate, CtaGroup.size, hda, hdb, hI, hsp, ↓reduceIte,
    bind, Except.bind, pure, Except.pure, ofExec]
  rfl

/-- The issue of an MMA with A in Tensor Memory. -/
theorem mmaTmem_issue {t : TState} {dst ta bd idr pc : Nat} {aoff : Int} {en : Opnd}
    {xd xa B xi : BitVec 64} {dsc : TcMma.Descriptor} {acc : Bool} {e : Event}
    {o : Option TState} (hg : g < L.threads)
    (hcg : L.ctaGroup (g / L.block) .one = some [g / L.block])
    (hf : Fires pc (mmaTmemTmpl L g t .one false .f16 dst ta aoff (.reg bd) (.reg idr)
      (List.replicate 4 (.imm 0)) en none {}) e o)
    (hd : t.regs dst = some (.bits 32 xd)) (ha : t.regs ta = some (.bits 32 xa))
    (hb : t.regs bd = some (.bits 64 B)) (hi : t.regs idr = some (.bits 32 xi))
    (hcol : 0 ≤ ((truncBits 32 xa).toNat % 2 ^ 16 : Int) + aoff ∧
      ((truncBits 32 xa).toNat % 2 ^ 16 : Int) + aoff < 2 ^ 16)
    (hdB : ∃ x, TcShared.decode B.toNat = some x)
    (hI : TcMma.decode .one false .f16 (truncBits 32 xi).toNat = some dsc)
    (htr : dsc.transposeA = false) (hgrp : dsc.group = .one) (hen : mmaEnable t en = .ok acc) :
    ∃ db, TcShared.decode B.toNat = some db ∧
      e.kind = .tc (.mma (truncBits 32 xd).toNat
        ⟨dsc, db, db, g / L.block, g / L.block,
          some ((truncBits 32 xa).toNat / 2 ^ 16 * 2 ^ 16 +
            (((truncBits 32 xa).toNat % 2 ^ 16 : Int) + aoff).toNat), {}⟩ acc [0, 0, 0, 0]) := by
  obtain ⟨db, hdb⟩ := hdB
  have hMask : (List.replicate 4 (.imm 0)).mapM (readBits L g t 32) =
      .ok (List.replicate 4 (0 : BitVec 64)) := rfl
  have hsp : TcMma.makeOperands L (g / L.block) dsc db db =
      some ⟨dsc, db, db, g / L.block, g / L.block, none, {}⟩ := by
    simp [TcMma.makeOperands, hgrp, hcg]
  refine ⟨db, hdb, fires_tc_kind hf (t' := next t) ?_⟩
  simp only [mmaTmemTmpl, hg, rb_bits hd, rb_bits ha, rb_bits hb, rb_bits hi, tb64, hMask, hen,
    zeroColumnMaskOk, List.length_replicate, CtaGroup.size, hdb, hI, hsp, htr, tmemOffset, hcol,
    ↓reduceIte, bind, Except.bind, pure, Except.pure, ofExec]
  rfl

set_option hygiene false in
/-- The QK issue of block `b`, step `j` (one theorem per issue, with literal indices). -/
macro "qk_issue " n:ident b:num j:num k:num : command => `(
set_option maxHeartbeats 4000000 in
theorem $n (hp : Pre p L m) (hg : g < L.threads) {v : V} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (h : (code p L g (ent p L)).AtD ⟨.qk $b $j, v⟩ t)
    (hc : kernel.code[(code p L g (ent p L)).pc ⟨.qk $b $j, v⟩]? = some ins)
    (hf : Fires ((code p L g (ent p L)).pc ⟨.qk $b $j, v⟩)
      (eventTmpl Assumptions.all L g t ins.op) e o)
    (hD : DOk L ⟨.qk $b $j, v⟩) : IssueQk L g v $b $j e.kind := by
  replace h : At t (Site.qk $b $j).pc (facts p L g (ent p L) ⟨.qk $b $j, v⟩) := h
  replace hc : kernel.code[(Site.qk $b $j).pc]? = some ins := hc
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have hq : v.qd = qv L (neg (.qk $b $j)) := hD.2 rfl
  have hx : BW (sAt v $k) := hD.1 $k
  have hr := mmaSmem_issue hg (Kernels.TmlFa4Fwd.Mma.singleCtaGroup hp hg) hf
    (reg_bits h (by lit_mem) rfl) (reg_bits h (by lit_mem) rfl)
    (reg_bits h (by lit_mem) rfl) (reg_bits h (by lit_mem) rfl) (by rw [hq]; exact qv_decode hp _ _)
    (bdesc_iv hx (qlo_bw hx $j)) (dsc := qkDsc) rfl rfl rfl
  rw [hq] at hr
  exact hr)

set_option hygiene false in
/-- The PV issue of block `b`, step `j`. -/
macro "pv_issue " n:ident b:num j:num ka:num kb:num : command => `(
set_option maxHeartbeats 4000000 in
theorem $n (hp : Pre p L m) (hg : g < L.threads) {v : V} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (h : (code p L g (ent p L)).AtD ⟨.pv $b $j, v⟩ t)
    (hc : kernel.code[(code p L g (ent p L)).pc ⟨.pv $b $j, v⟩]? = some ins)
    (hf : Fires ((code p L g (ent p L)).pc ⟨.pv $b $j, v⟩)
      (eventTmpl Assumptions.all L g t ins.op) e o)
    (hD : DOk L ⟨.pv $b $j, v⟩) : IssuePv L g v $b $j e.kind := by
  replace h : At t (Site.pv $b $j).pc (facts p L g (ent p L) ⟨.pv $b $j, v⟩) := h
  replace hc : kernel.code[(Site.pv $b $j).pc]? = some ins := hc
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have ha : BW (sAt v $ka) := hD.1 $ka
  have hx : BW (sAt v $kb) := hD.1 $kb
  exact mmaTmem_issue hg (Kernels.TmlFa4Fwd.Mma.singleCtaGroup hp hg) hf
    (reg_bits h (by lit_mem) rfl) (reg_bits h (by lit_mem) rfl)
    (reg_bits h (by lit_mem) rfl) (reg_bits h (by lit_mem) rfl) (col_ok ha (by decide))
    (bdesc_iv hx (pvlo_bw hx $j (by decide))) (dsc := pvDsc) rfl rfl rfl
    (by first | exact mmaEnable_reg (reg_pred h (by lit_mem) rfl) | rfl))

qk_issue qkI_0_0 0 0 0
qk_issue qkI_0_1 0 1 0
qk_issue qkI_0_2 0 2 0
qk_issue qkI_0_3 0 3 0
qk_issue qkI_0_4 0 4 0
qk_issue qkI_0_5 0 5 0
qk_issue qkI_0_6 0 6 0
qk_issue qkI_0_7 0 7 0
qk_issue qkI_1_0 1 0 0
qk_issue qkI_1_1 1 1 0
qk_issue qkI_1_2 1 2 0
qk_issue qkI_1_3 1 3 0
qk_issue qkI_1_4 1 4 0
qk_issue qkI_1_5 1 5 0
qk_issue qkI_1_6 1 6 0
qk_issue qkI_1_7 1 7 0
qk_issue qkI_2_0 2 0 6
qk_issue qkI_2_1 2 1 6
qk_issue qkI_2_2 2 2 6
qk_issue qkI_2_3 2 3 6
qk_issue qkI_2_4 2 4 6
qk_issue qkI_2_5 2 5 6
qk_issue qkI_2_6 2 6 6
qk_issue qkI_2_7 2 7 6
qk_issue qkI_3_0 3 0 6
qk_issue qkI_3_1 3 1 6
qk_issue qkI_3_2 3 2 6
qk_issue qkI_3_3 3 3 6
qk_issue qkI_3_4 3 4 6
qk_issue qkI_3_5 3 5 6
qk_issue qkI_3_6 3 6 6
qk_issue qkI_3_7 3 7 6
pv_issue pvI_0_0 0 0 3 4
pv_issue pvI_0_1 0 1 3 4
pv_issue pvI_0_2 0 2 3 4
pv_issue pvI_0_3 0 3 3 4
pv_issue pvI_0_4 0 4 3 4
pv_issue pvI_0_5 0 5 3 4
pv_issue pvI_0_6 0 6 3 4
pv_issue pvI_0_7 0 7 3 4
pv_issue pvI_1_0 1 0 7 4
pv_issue pvI_1_1 1 1 7 4
pv_issue pvI_1_2 1 2 7 4
pv_issue pvI_1_3 1 3 7 4
pv_issue pvI_1_4 1 4 7 4
pv_issue pvI_1_5 1 5 7 4
pv_issue pvI_1_6 1 6 7 4
pv_issue pvI_1_7 1 7 7 4
pv_issue pvI_2_0 2 0 9 10
pv_issue pvI_2_1 2 1 9 10
pv_issue pvI_2_2 2 2 9 10
pv_issue pvI_2_3 2 3 9 10
pv_issue pvI_2_4 2 4 9 10
pv_issue pvI_2_5 2 5 9 10
pv_issue pvI_2_6 2 6 9 10
pv_issue pvI_2_7 2 7 9 10
pv_issue pvI_3_0 3 0 12 10
pv_issue pvI_3_1 3 1 12 10
pv_issue pvI_3_2 3 2 12 10
pv_issue pvI_3_3 3 3 12 10
pv_issue pvI_3_4 3 4 12 10
pv_issue pvI_3_5 3 5 12 10
pv_issue pvI_3_6 3 6 12 10
pv_issue pvI_3_7 3 7 12 10

/-- **The event of an MMA site** of the MMA warp, at a state that keeps its descriptor words. -/
theorem issue_at (hp : Pre p L m) (hg : g < L.threads) {d : D} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (h : (code p L g (ent p L)).AtD d t)
    (hc : kernel.code[(code p L g (ent p L)).pc d]? = some ins)
    (hf : Fires ((code p L g (ent p L)).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hD : DOk L d) :
    (∀ b j, d.site = .qk b j → IssueQk L g d.v b j e.kind) ∧
      ∀ b j, d.site = .pv b j → IssuePv L g d.v b j e.kind := by
  obtain ⟨site, v⟩ := d
  refine ⟨fun b j hs => ?_, fun b j hs => ?_⟩ <;> simp only at hs <;> subst hs <;>
    fin_cases b <;> fin_cases j
  · exact qkI_0_0 hp hg h hc hf hD
  · exact qkI_0_1 hp hg h hc hf hD
  · exact qkI_0_2 hp hg h hc hf hD
  · exact qkI_0_3 hp hg h hc hf hD
  · exact qkI_0_4 hp hg h hc hf hD
  · exact qkI_0_5 hp hg h hc hf hD
  · exact qkI_0_6 hp hg h hc hf hD
  · exact qkI_0_7 hp hg h hc hf hD
  · exact qkI_1_0 hp hg h hc hf hD
  · exact qkI_1_1 hp hg h hc hf hD
  · exact qkI_1_2 hp hg h hc hf hD
  · exact qkI_1_3 hp hg h hc hf hD
  · exact qkI_1_4 hp hg h hc hf hD
  · exact qkI_1_5 hp hg h hc hf hD
  · exact qkI_1_6 hp hg h hc hf hD
  · exact qkI_1_7 hp hg h hc hf hD
  · exact qkI_2_0 hp hg h hc hf hD
  · exact qkI_2_1 hp hg h hc hf hD
  · exact qkI_2_2 hp hg h hc hf hD
  · exact qkI_2_3 hp hg h hc hf hD
  · exact qkI_2_4 hp hg h hc hf hD
  · exact qkI_2_5 hp hg h hc hf hD
  · exact qkI_2_6 hp hg h hc hf hD
  · exact qkI_2_7 hp hg h hc hf hD
  · exact qkI_3_0 hp hg h hc hf hD
  · exact qkI_3_1 hp hg h hc hf hD
  · exact qkI_3_2 hp hg h hc hf hD
  · exact qkI_3_3 hp hg h hc hf hD
  · exact qkI_3_4 hp hg h hc hf hD
  · exact qkI_3_5 hp hg h hc hf hD
  · exact qkI_3_6 hp hg h hc hf hD
  · exact qkI_3_7 hp hg h hc hf hD
  · exact pvI_0_0 hp hg h hc hf hD
  · exact pvI_0_1 hp hg h hc hf hD
  · exact pvI_0_2 hp hg h hc hf hD
  · exact pvI_0_3 hp hg h hc hf hD
  · exact pvI_0_4 hp hg h hc hf hD
  · exact pvI_0_5 hp hg h hc hf hD
  · exact pvI_0_6 hp hg h hc hf hD
  · exact pvI_0_7 hp hg h hc hf hD
  · exact pvI_1_0 hp hg h hc hf hD
  · exact pvI_1_1 hp hg h hc hf hD
  · exact pvI_1_2 hp hg h hc hf hD
  · exact pvI_1_3 hp hg h hc hf hD
  · exact pvI_1_4 hp hg h hc hf hD
  · exact pvI_1_5 hp hg h hc hf hD
  · exact pvI_1_6 hp hg h hc hf hD
  · exact pvI_1_7 hp hg h hc hf hD
  · exact pvI_2_0 hp hg h hc hf hD
  · exact pvI_2_1 hp hg h hc hf hD
  · exact pvI_2_2 hp hg h hc hf hD
  · exact pvI_2_3 hp hg h hc hf hD
  · exact pvI_2_4 hp hg h hc hf hD
  · exact pvI_2_5 hp hg h hc hf hD
  · exact pvI_2_6 hp hg h hc hf hD
  · exact pvI_2_7 hp hg h hc hf hD
  · exact pvI_3_0 hp hg h hc hf hD
  · exact pvI_3_1 hp hg h hc hf hD
  · exact pvI_3_2 hp hg h hc hf hD
  · exact pvI_3_3 hp hg h hc hf hD
  · exact pvI_3_4 hp hg h hc hf hD
  · exact pvI_3_5 hp hg h hc hf hD
  · exact pvI_3_6 hp hg h hc hf hD
  · exact pvI_3_7 hp hg h hc hf hD

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
