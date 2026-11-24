-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.WordAlign
public import Kernels.TmlFa4Fwd.Proof.Startup.Machine
public import Kernels.TmlFa4Fwd.Proof.Loader.Mem.Addr
public import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpOk
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.Local

@[expose] public section

/-! # One theorem per loader row copy

`cp_site name per v i c` states and proves that row copy `c` of row `i` of the packet of period
`per` and half `v` is no undefined behaviour at a state that keeps the row-address pattern
(`cp_ok` with the table's words: the swizzled destination by the `Al` closure, the source by
`AOk` and the column offset, the size a `selp` of 16 and 0). The theorems are generated per site
with literal indices (as the MMA warp's issues, `Mma/Export/Desc.lean`): `fin_cases` on a site's
indices leaves terms that make the code and value lookups slower. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

theorem sb_al (hp : Pre p L m) : Al 4 (Mma.sbW L) := by
  have := hp.shared.1
  unfold Al Mma.sbW; simp only [BitVec.toNat_ofNat]; omega

theorem sz_le (c : Bool) : (truncBits 32 (Epilogue.sel c (i32 16) (i32 0))).toNat ≤ 16 := by
  cases c <;> decide

set_option hygiene false in
/-- The theorem of one row copy. -/
macro "cp_site " n:ident per:term:max b:term:max i:num c:num : command => `(
set_option maxHeartbeats 4000000 in
theorem $n (hp : Pre p L m) {v : V} {kk : Fin 2} (hA : AOk v) {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (h : (code p L g w ent).AtD ⟨.cp $per $b $i $c, v, kk⟩ t)
    (hc : kernel.code[(Site.cp $per $b $i $c).pc]? = some ins)
    (hf : Fires (Site.cp $per $b $i $c).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (f : Fault) : e.kind ≠ .ub f := by
  intro hk
  have hu := fires_ub hf hk
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have hsb := sb_al hp
  have hra := al_rowsAt hp g
  exact cp_ok hu (lreg h (by lit_mem) rfl) (lreg h (by lit_mem) rfl) (lreg h (by lit_mem) rfl)
    (by al_tac) (by decide) (LdWarp.add64_m16 (pair_m16 hA.2)
      (by first | exact wideU2_m16 (al_tidc L g) | exact and112_m16 _)) (by decide) (sz_le _))

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
