-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.TmEnv
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MmaElem

@[expose] public section

/-! # The operand elements of the QK MMAs need no validity of warpgroup 0's words

The A elements of a QK MMA are the query tile's, the B elements the dequantized tiles': neither
reads a word warpgroup 0 stores. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **The operand elements of the QK MMAs decode.** -/
theorem Safe.qkElements (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    QkElements X := by
  have hb := Safe.tmBase hp hIn hX hFw
  intro g i pc s acc mask he
  refine TmRace.mma_elem_at hp hX hFw (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw)
    (hIn.bar0 hp X hX hFw) (hIn.dequant hp X hX hFw) hb.hv
    (fun _ _ _ _ _ hi => Safe.issueShape hp hX hFw hi) (tmem_rows hp hX hFw)
    (mmaOne hp hX hFw) (Safe.tmemOne hp hIn hX hFw) hb.hmd (g, i) ?_
  intro d s' acc' mask' ops row col cell hi _ _ _ hd256
  obtain ⟨pc', he'⟩ := hi
  rw [he] at he'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
