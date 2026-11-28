-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NoUbAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.AllocRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Alloc
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.NoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.NoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.NoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Export.NoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.NoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.NoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.DqValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.CoordBits
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.NoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.Payloads

@[expose] public section

/-! # ERR-UNDEFINED-INSTRUCTION: no undefined-behaviour event

The safety class of Core's `Unsafe` this file owns (`HasUb`), proved by the leaves of the roles
(`Safe.noUb`): warpgroup 0's from the typing of its words (`w0_payloads`), warpgroup 2's from the
valid data (`dq_valid`). No event after a lane's read-back of the allocation word is undefined
behaviour (`Safe.noTrap`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **Warpgroup 0's leaf**: its events are no undefined behaviour (`wg0_noUb`), from the typing of
its words. -/
theorem Safe.wg0Leaf : NoUbLeaf P L mem0 .wg0 :=
  fun hp _ hX hFw _ k e he ha => wg0_noUb hp hX hFw (w0_payloads hp hX hFw) k e he ha

/-- **The startup's leaf**: the startup's events are no undefined behaviour, the read-back
at pc 92 reading `b32 0` (`allocRead`, `startup_noUb`). -/
theorem Safe.startupLeaf : NoUbLeaf P L mem0 .startup :=
  fun hp _ hX hFw g k e he ha =>
    startup_noUb hp hX (fun _ _ _ _ h => allocRead hp hX hFw (Frame.lt_of_get hX h) h) g k e he ha

/-- **Warpgroup 1's leaf**: the head's and the idle code's events are no undefined behaviour
(`wg1_noUb`). -/
theorem Safe.wg1Leaf : NoUbLeaf P L mem0 .wg1 :=
  fun hp _ hX _ g k e he ha => wg1_noUb hp hX g k e he ha

/-- **The MMA warp's leaf**: its events are no undefined behaviour (`mma_noUb`). -/
theorem Safe.mmaLeaf : NoUbLeaf P L mem0 .mma :=
  fun hp _ hX hFw g k e he ha => mma_noUb hp hX hFw g k e he ha

/-- **The index warp's leaf**: its events are no undefined behaviour (`index_noUb`). -/
theorem Safe.indexLeaf : NoUbLeaf P L mem0 .index :=
  fun hp _ hX hFw g k e he ha => index_noUb hp hX hFw g k e he ha

/-- **The TMA warp's leaf**: its events are no undefined behaviour (`tma_noUb`), the reads of its
coordinates rebuilding 32-bit words (`coord_words_bits`: the bytes are the index warp's stores). -/
theorem Safe.tmaLeaf : NoUbLeaf P L mem0 .tma :=
  fun hp _ hX hFw g k e he ha =>
    tma_noUb hp hX hFw (coord_words_bits hp hX hFw
      ((Inputs.of_pre hp).mbar hp _ hX hFw) ((Inputs.of_pre hp).initRows hp _ hX hFw)
      ((Inputs.of_pre hp).bar0 hp _ hX hFw) ((Inputs.of_pre hp).coord hp _ hX hFw)) g k e he ha

/-- **Warpgroup 2's leaf**: its events are no undefined behaviour (`dequant_noUb`), the data its
lanes read being valid (`dq_valid`; `noUbInner`). -/
theorem Safe.dequantLeaf : NoUbLeaf P L mem0 .dequant :=
  fun hp _ hX hFw g k e he ha =>
    dequant_noUb hp hX hFw (fun g' k' hk => dq_valid hp hX hFw
      ((Inputs.of_pre hp).mbar hp _ hX hFw) ((Inputs.of_pre hp).initRows hp _ hX hFw)
      ((Inputs.of_pre hp).bar0 hp _ hX hFw) ((Inputs.of_pre hp).raw hp _ hX hFw)
      (noUbInner hX) ((Inputs.of_pre hp).coord hp _ hX hFw)
      g' k' hk) g k e he ha

/-- **ERR-UNDEFINED-INSTRUCTION**: no undefined-behaviour event. -/
theorem Safe.noUb (hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    ¬ HasUb X :=
  noUb_of_leaves hp (fun r => by
    cases r
    exacts [Safe.startupLeaf, Safe.wg1Leaf, Safe.mmaLeaf, Safe.tmaLeaf, Safe.indexLeaf,
      Safe.dequantLeaf, Safe.wg0Leaf]) hX hFw

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
