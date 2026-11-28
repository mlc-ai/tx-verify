-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Roles
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Mma.Export.Broadcast

@[expose] public section

/-! # No broadcast of the MMA loop is skipped

The thread machine counts the broadcasts that received no 7 (`Cls.skip`). Every broadcast of the
loop received one, so a lane's count is zero. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

/-- **No broadcast of the loop is skipped**: every one received a 7. -/
theorem skip_zero {Q L m X g} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (warp : g%L.block/32=7) (k : Nat) : ((X.tr g).take k).countP (cls .skip) = 0 := by
  refine List.countP_eq_zero.mpr fun e he => ?_
  obtain ⟨j, get⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take he)
  obtain ⟨pc, kd⟩ := e
  by_contra hs
  cases kd <;> try (simp [cls, Mma.skipEv] at hs; done)
  rename_i md a b c recv ok
  simp only [cls, Mma.skipEv, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hs
  have := Mma.Export.broadcast_seven hp hX hf words warp get hs.1
  subst this
  have := hs.2
  simp [Mma.low, b32, Value.regBits, truncBits] at this

end PTX.Kernels.InklingRelDecode.Proof
