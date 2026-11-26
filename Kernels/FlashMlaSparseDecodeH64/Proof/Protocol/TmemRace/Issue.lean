-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Writers
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaFoot
public import Lemmas.Tcgen05.TcReadFinishMma

@[expose] public section

/-! # Every MMA is the MMA lane's, with a valid descriptor

From the Tensor Memory rows only (`TmemRows`): an MMA event of a launched thread is a QK or PV MMA
of the MMA warp after its election (`MmaOn`), with the descriptor its idesc word decodes to, which
is valid (`MmaFoot.qkD_valid`, `pvD_valid`). So two MMA issuers of one warp are one thread
(`MmaOne`): the premise `TcMma.WarpIssuerUnique` of the MMA completions. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

namespace TmRace

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **An MMA event is the MMA lane's after the election, with a valid descriptor.** -/
theorem mma_on (hX : Consistent L kernel Assumptions.all m X) (hR : TmemRows P L X)
    {g k pc d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (he : X.get (g, k) = some ⟨pc, .tc (.mma d s acc mask)⟩) :
    g < L.threads ∧ MmaOn L g pc ∧ TcMma.Valid s.descriptor := by
  have hg := Frame.lt_of_get hX he
  refine ⟨hg, ?_⟩
  rcases tc_role hR hg he rfl with ⟨-, hW⟩ | ⟨hat, hM⟩ | ⟨_, _, _, hc'⟩
  · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
  · rcases hM with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, k', hk, hpc, h, hops⟩ |
      ⟨_, _, k', hk, hpc, h, -, hops⟩ <;> cases h
    · obtain ⟨-, hd, -⟩ := hops
      refine ⟨⟨hat, ?_⟩, by rw [MmaFoot.qkD_eq hd]; exact MmaFoot.qkD_valid⟩
      simp only [TmemRow.qkPc] at hpc
      split at hpc <;> omega
    · obtain ⟨-, hd, -⟩ := hops
      refine ⟨⟨hat, ?_⟩, by rw [MmaFoot.pvD_eq hd]; exact MmaFoot.pvD_valid⟩
      simp only [TmemRow.pvPc] at hpc
      split at hpc <;> omega
  · cases hc'

/-- **One issuer per warp**: two MMA issuers of one warp are one thread. -/
theorem mma_warpUnique (hX : Consistent L kernel Assumptions.all m X) (hR : TmemRows P L X)
    (hO : MmaOne L X) : TcMma.WarpIssuerUnique L X := by
  rintro ⟨g, i⟩ ⟨h, j⟩ ⟨d, s, acc, mask, pc, hi⟩ ⟨d', s', acc', mask', pc', hj⟩ hw
  obtain ⟨-, hon, -⟩ := mma_on hX hR hi
  obtain ⟨-, hon', -⟩ := mma_on hX hR hj
  exact hO hi hj (fun _ h => by cases h) (fun _ h => by cases h) hon hon'
    hw.1.2.2

end TmRace

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
