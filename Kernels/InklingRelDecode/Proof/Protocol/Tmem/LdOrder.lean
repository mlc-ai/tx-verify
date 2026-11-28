-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdOrderS
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdOrderO
import Kernels.InklingRelDecode.Proof.Lib.NoEvents

@[expose] public section

/-! # A load is ordered with every writer of its cells

The three loads of the kernel by their site: the score load (pc 1265), the accumulator load of a
round (pc 2260) and the epilogue's accumulator load (pc 2607). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.TcMma

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Every writer of a cell of a load is ordered with it.** -/
public theorem ld_order (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) {t k0 pc a vals sh j w}
    (he : X.get (t,k0) = some ⟨pc,.tc (.ld a vals sh)⟩)
    (hpc : pc = 1265 ∨ pc = 2260 ∨ pc = 2607) (hj : j < vals.length)
    (hw : TmemWrite L X w (tcDataCell L t sh a j)) :
    WriteBefore L X w (t,k0) ∨ ReadBefore L X .ld (t,k0) w := by
  rcases hpc with rfl|rfl|rfl
  · exact ld_s_order hp hX hf safe base rows init he hj hw
  all_goals
    rcases tmemWrite_of_no_copy (Lib.no_cp hX) (no_shift hX) hw with hm | hs
    swap
    · exact ld_o_store hp hX hf base he (by omega) hj hs
  · exact ld_o_pv hp hX hf safe base rows init he hj hm
  · exact .inl (ld_e_mma hp hX hf rows init base he hm)

end PTX.Kernels.InklingRelDecode.Proof.Tmem
