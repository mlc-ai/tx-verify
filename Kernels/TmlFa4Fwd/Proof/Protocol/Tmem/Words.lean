-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Assumptions
public import Core.Tc.TcMmaValue
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
import Lemmas.Assumption.Facts
import Lemmas.Flow.NotBulk
import Lemmas.Flow.TcStBytes
import Lemmas.Tcgen05.TmemWriters

@[expose] public section

/-! # Every Tensor Memory write leaves a 4-byte word in its cell

An MMA result is a single-precision float (the ideal `bf16 × bf16 → f32` MMA, `TcMma.eval_f16`); a
`tcgen05.st` stores 4-byte values (the template's check; every store has the shape `.32x32b`); the
kernel issues no copy or shift. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **An MMA result is a single-precision float.** -/
theorem result_f32 (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {i : EvId} {cell : Cell} {v : Value}
    (h : Result L Assumptions.all X i cell v) : ∃ r, v = .float .f32 r := by
  have hk : ∀ {d s acc mask}, X.MmaIssue i d s acc mask →
      s.descriptor.kind = .f16 .bf16 .f32 := by
    intro d s acc mask hi
    obtain ⟨-, -, st, -, ⟨_, _, -, -, h, -⟩ | ⟨_, _, -, -, h, -⟩⟩ := mma_acc_at hp hX hFw hi <;>
      rw [h] <;> rfl
  have hm : Kind.f16 .bf16 .f32 ∈ Assumptions.arithScope.mma := List.mem_singleton.mpr rfl
  cases h with
  | overwrite hi _ _ ha => exact eval_f16 (hk hi) (by rw [hk hi]; exact hm) ha
  | accumulate hi _ _ _ _ ha => exact eval_f16 (hk hi) (by rw [hk hi]; exact hm) ha
  | accumulateStored hi _ _ _ _ ha => exact eval_f16 (hk hi) (by rw [hk hi]; exact hm) ha

/-- **Every Tensor Memory write leaves a 4-byte word in its cell.** -/
theorem words (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {s : EvId} {cell : Cell} {v : Value}
    (h : Wrote L Assumptions.all X s cell v) : v.bytes = 4 := by
  have ht := scoreFacts hp hX hFw
  rcases h with h | ⟨a, vals, sh, j, hs, hj, -⟩ | ⟨c, -, -, -, -, -, -, hcp, -⟩ |
    ⟨-, -, ⟨hsc, -⟩, -⟩
  · obtain ⟨r, rfl⟩ := result_f32 hp hX hFw h
    rfl
  · obtain rfl := ht.tc_shape (.inr hs)
    obtain ⟨pc, he⟩ := hs
    rcases get_source hX he with ⟨_, hb⟩ | ⟨t, ins, o, -, -, hf⟩
    · cases hb
    · exact fires_tcSt_bytes hf rfl (by intro s h; cases h) v (List.mem_of_getElem? hj)
  · exact (ht.no_cp _ _ hcp).elim
  · obtain ⟨sp, hsp, -⟩ := hsc
    exact (ht.no_shift _ _ hsp).elim

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
