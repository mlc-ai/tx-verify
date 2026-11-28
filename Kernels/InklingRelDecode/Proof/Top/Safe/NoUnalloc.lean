-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Protocol.Alloc.Mbar
public import Kernels.InklingRelDecode.Proof.Protocol.Alloc.Access
import Kernels.InklingRelDecode.Proof.Lib.NoEvents

@[expose] public section

/-! # ERR-UNALLOCATED: every access is to allocated memory

A read or write intent is allocated by `Alloc.read_alloc` and `Alloc.write_alloc` (the shared
window of its CTA, the input bytes, the two output arrays); the kernel has no non-coherent
load; an mbarrier operand is one of the twelve objects of a launched CTA (`Alloc.mbar_operand`),
inside the window. Nothing is open. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem Safe.noUnalloc (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) (gr : Iface.GlobalReads Q X)
    (placed : Protocol.Shared.OutputPlaced Q X) : ¬ Unalloc m X := by
  rintro (⟨ref,a,l,⟨w,hi⟩|⟨i,bs,-,pc,nc⟩,cov,none⟩|⟨e,mb,l,hu,cov,none⟩)
  · cases w
    · exact Protocol.Alloc.read_alloc hp hX hf gr hi cov none
    · exact Protocol.Alloc.write_alloc hp hX hf placed hi cov none
  · exact Lib.no_nc hX nc
  · obtain ⟨c,hc,j,rfl⟩ := Protocol.Alloc.mbar_operand hX rows init hu
    have off : ∀ j : Fin 12, 213216 ≤ MbarRow.initOffset j ∧ MbarRow.initOffset j + 8 ≤ 213336 :=
      by decide
    obtain ⟨hs,hcc,lo,hi⟩ := cov
    have := off j
    dsimp only at hs hcc lo hi
    exact Protocol.Alloc.shared_alloc hp hs (hcc ▸ hc) (by omega)
      (by simp only [sharedBytes]; omega) none

end PTX.Kernels.InklingRelDecode.Proof.Top
