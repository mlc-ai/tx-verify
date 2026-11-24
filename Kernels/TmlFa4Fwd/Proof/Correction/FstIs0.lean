-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.MemWrite
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part133
import Kernels.TmlFa4Fwd.Flow.Code.Part134
import Kernels.TmlFa4Fwd.Flow.Code.Part135
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Kernels.TmlFa4Fwd.Flow.Code.Part138
import Kernels.TmlFa4Fwd.Flow.Code.Part139
import Kernels.TmlFa4Fwd.Flow.Code.Part140
import Kernels.TmlFa4Fwd.Flow.Code.Part141

@[expose] public section

/-! # The address of every final store of a correction lane, stage 0

`fst_exact`: element `s` of the store `hh` of chunk `j` of stage `st` is the word `s` of the lane's
column `2 (j mod 4) + hh` in the quarter `j / 4` of the stage's staging buffer. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A final store's exact word. -/
def FstIs (L : Launch) (g : Nat) (st : Fin 2) (k : Fin 8) (q s : Nat) (acc : Acc) : Prop :=
  acc.size = 4 ∧ acc.loc = ⟨.shared, g / L.block, (colW L g st k).toNat + 16384 * q + 4 * s⟩

theorem fstIs_of (hp : Pre p L m) {st : Fin 2} {k : Fin 8} {s q : Nat} {off : Int} (hq : q < 4)
    (ho : off = ((16384 * q : Nat) : Int)) {acc : Acc}
    (hl : acc.loc = ⟨.shared, g / L.block,
      (truncBits 32 (truncBits 32 (colW L g st k) + BitVec.ofInt 64 off)).toNat + 4 * s⟩)
    (hz : acc.size = 4) : FstIs L g st k q s acc := by
  have hsb := hp.shared
  subst ho
  have hb := (colW_col (g := g) hp st k).bounds k.isLt
  have hr : rowN L g < 128 := Nat.mod_lt _ (by decide)
  have := st.isLt
  unfold lineAt at hb
  rw [eff_shared (by omega)] at hl
  exact ⟨hz, hl⟩

set_option hygiene false in
/-- The final store at stage `st`, chunk `j`, half `hh`. -/
macro "fst_is " n:ident st:num j:num hh:num k:num q:num : command => `(
set_option maxHeartbeats 4000000 in
theorem $n (hp : Pre p L m) {d : Control.D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (Control.code p L g).AtD d t)
    (hc : kernel.code[(Control.code p L g).pc d]? = some ins)
    (hf : Fires ((Control.code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : d.site = .fst $st $j $hh) {acc : Acc} {bs : List Byte}
    (hk : e.kind = .wr acc bs) : FstIs L g $st $k $q d.k.val acc := by
  have hreg : ∀ r ∈ Control.live d, t.regs r = some (Control.valueOf p L g d r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub : t.sub = d.k.val := h.2.1
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨site, v, k⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  obtain ⟨h1, h2⟩ := stShared_wr rfl rfl rfl rfl rfl (hreg _ (by lit_mem)) hf hk
  rw [hsub] at h1
  exact fstIs_of hp (by decide) rfl h1 h2)

fst_is fstIs_0_0_0 0 0 0 0 0
fst_is fstIs_0_0_1 0 0 1 1 0
fst_is fstIs_0_1_0 0 1 0 2 0
fst_is fstIs_0_1_1 0 1 1 3 0
fst_is fstIs_0_2_0 0 2 0 4 0
fst_is fstIs_0_2_1 0 2 1 5 0
fst_is fstIs_0_3_0 0 3 0 6 0
fst_is fstIs_0_3_1 0 3 1 7 0
fst_is fstIs_0_4_0 0 4 0 0 1
fst_is fstIs_0_4_1 0 4 1 1 1
fst_is fstIs_0_5_0 0 5 0 2 1
fst_is fstIs_0_5_1 0 5 1 3 1
fst_is fstIs_0_6_0 0 6 0 4 1
fst_is fstIs_0_6_1 0 6 1 5 1
fst_is fstIs_0_7_0 0 7 0 6 1
fst_is fstIs_0_7_1 0 7 1 7 1
fst_is fstIs_0_8_0 0 8 0 0 2
fst_is fstIs_0_8_1 0 8 1 1 2
fst_is fstIs_0_9_0 0 9 0 2 2
fst_is fstIs_0_9_1 0 9 1 3 2
fst_is fstIs_0_10_0 0 10 0 4 2
fst_is fstIs_0_10_1 0 10 1 5 2
fst_is fstIs_0_11_0 0 11 0 6 2
fst_is fstIs_0_11_1 0 11 1 7 2
fst_is fstIs_0_12_0 0 12 0 0 3
fst_is fstIs_0_12_1 0 12 1 1 3
fst_is fstIs_0_13_0 0 13 0 2 3
fst_is fstIs_0_13_1 0 13 1 3 3
fst_is fstIs_0_14_0 0 14 0 4 3
fst_is fstIs_0_14_1 0 14 1 5 3
fst_is fstIs_0_15_0 0 15 0 6 3
fst_is fstIs_0_15_1 0 15 1 7 3

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
