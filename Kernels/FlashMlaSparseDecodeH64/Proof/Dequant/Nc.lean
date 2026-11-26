-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LenRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.NcRead

@[expose] public section

/-! # Warpgroup 2's two length loads read the row's lengths

-- domain: consistent

At a length load whose pointer is set, the state's event is the `.nc` read of the row's four
bytes (`len_read`, `Lib/LenRead.lean`); in a consistent execution it returns the row's length
word (`rebuild_topk`, `rebuild_extra`), so the machine continues with that word (`deq_topk`,
`deq_extra`), as the TMA warp's (`Tma/Nc.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

section
variable {X : Execution} {i : EvId} {d : D} {t : TState} {ins : Instr} {e : Event}
  {o : Option TState}
  (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hget : X.get i = some e)
  (hat : (code P L g w).AtD d t) (hi : (code P L g w).inv d)
  (hc : kernel.code[(code P L g w).pc d]? = some ins)
  (hf : Fires ((code P L g w).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
include hp hX hget hat hi hc hf

/-- **The top-k length load continues with the row's length.** -/
theorem deq_topk (hptr : eqz64 (pw8 (P.topkLenBase.getD 0)) = false) (hs : d.site = .lenA) :
    succ P L g d e = some (some (afterA P { d with l0 := W (P.topkLen (ctaidY L g)) })) := by
  obtain ⟨x, hx⟩ := len_ptr hptr
  obtain ⟨bs, hk, hpcE⟩ := topk_read hp hx hs hat hi hc hf
  have hr := rebuild_topk hp hX (ctaid_lt hp g).2 hx hget ⟨hk, hpcE⟩
  simp [succ, hs, Code.ncNext, hk, hr, b32, W]

/-- **The extra length load continues with the row's length.** -/
theorem deq_extra (hptr : eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = false)
    (hs : d.site = .lenB) :
    succ P L g d e = some (some { d with site := .wq, l1 := W (P.extraTopkLen (ctaidY L g)) }) := by
  obtain ⟨x, hx⟩ := len_ptr hptr
  obtain ⟨bs, hk, hpcE⟩ := extra_read hp hx hs hat hi hc hf
  have hr := rebuild_extra hp hX (ctaid_lt hp g).2 hx hget ⟨hk, hpcE⟩
  simp [succ, hs, Code.ncNext, hk, hr, b32, W]

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
