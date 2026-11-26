-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LenRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.NcRead

@[expose] public section

/-! # The TMA warp's two length loads read the row's lengths

-- domain: consistent

At a length load whose pointer is set (`SiteOk`), the state's event is the `.nc` read of the row's
four bytes (`len_read`, `Lib/LenRead.lean`); in a consistent execution it returns the row's length
word (`rebuild_topk`, `rebuild_extra`), so the machine continues with that word (`tma_topk`,
`tma_extra`): it never stops at a length load. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

section
variable {X : Execution} {i : EvId} {d : D} {t : TState} {ins : Instr} {e : Event}
  {o : Option TState}
  (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hget : X.get i = some e)
  (hok : SiteOk P L g d) (hat : (code P L g).AtD d t)
  (hc : kernel.code[(code P L g).pc d]? = some ins)
  (hf : Fires ((code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
include hp hX hget hok hat hc hf

/-- **The top-k length load continues with the row's length.** -/
theorem tma_topk (hs : d.site = .loadTopk) :
    succ P L g d e = some (some (afterTopk P d (W (P.topkLen (ctaidY L g))))) := by
  obtain ⟨x, hx⟩ := len_ptr (hok.1 hs)
  obtain ⟨bs, hk, hpcE⟩ := topk_read hp hx hs hat hc hf
  have hr := rebuild_topk hp hX (ctaid_lt hp g).2 hx hget ⟨hk, hpcE⟩
  simp [succ, hs, ncWord, hk, hr, word32, b32, W]

/-- **The extra length load continues with the row's length.** -/
theorem tma_extra (hs : d.site = .loadExtra) :
    succ P L g d e = some (some (lensD d d.l0 (W (P.extraTopkLen (ctaidY L g))))) := by
  obtain ⟨x, hx⟩ := len_ptr (hok.2.1 hs)
  obtain ⟨bs, hk, hpcE⟩ := extra_read hp hx hs hat hc hf
  have hr := rebuild_extra hp hX (ctaid_lt hp g).2 hx hget ⟨hk, hpcE⟩
  simp [succ, hs, ncWord, hk, hr, word32, b32, W]

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
