-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Steps.Base
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part052
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part053
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part054
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part055
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part056

@[expose] public section

/-! # Warpgroup 2's obligations in row 3 of a block (pcs 3370–3594)

The scale load (`scale 3`, four elements), the eight raw-word loads (`raw 3 s`, any payload
continues) and the eight chunk stores (`store 3 s`); the float runs between them write data
registers only and are havocked, the chunk addresses are stepped exactly. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The scale load of row 3, element by element. -/
theorem stepAt_scale3 (d : D) (hs : d.site = .scale 3) : (code P L g w).StepAtU d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  dsimp only at hs; subst hs
  refine scaleAt rfl (by rfl) Flow.code_3370 rfl rfl rfl rfl rfl (by decide +kernel) ?_
  dq_seg

/-- The raw-word loads of row 3. -/
theorem stepAt_raw3 (d : D) (s : Fin 8) (hs : d.site = .raw 3 s) :
    (code P L g w).StepAtU d := by
  dq_site
  fin_cases s
  · raw_at Flow.code_3404
  · raw_at Flow.code_3412
  · raw_at Flow.code_3435
  · raw_at Flow.code_3459
  · raw_at Flow.code_3483
  · raw_at Flow.code_3507
  · raw_at Flow.code_3531
  · raw_at Flow.code_3555

/-- The chunk stores of row 3. -/
theorem stepAt_store3 (d : D) (s : Fin 8) (hs : d.site = .store 3 s) :
    (code P L g w).StepAtU d := by
  dq_site
  fin_cases s
  · st_at Flow.code_3427
  · st_at Flow.code_3451
  · st_at Flow.code_3475
  · st_at Flow.code_3499
  · st_at Flow.code_3523
  · st_at Flow.code_3547
  · st_at Flow.code_3571
  · st_at Flow.code_3594

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
