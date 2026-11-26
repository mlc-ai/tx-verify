-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictBase
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part020
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part021
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part022
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part023
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part024
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part025
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part026
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part027
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part028
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part029
import Lemmas.Flow.IssueNext
import Lemmas.Flow.CtlStepsU
import Lemmas.Flow.Step.TcSteps

@[expose] public section

/-! # Warpgroup 0's strict steps at the output chunks' sites -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The output chunk's proxy fence 0. -/
w0s_free stepAt_ofpx0S : .ofpx 0

/-- The output chunk's barrier 0. -/
w0s_free stepAt_obar0S : .obar 0

/-- The output chunk's election 0. -/
w0s_free stepAt_oel0S : .oel 0

/-- The output chunk's TMA store 0. -/
w0s_free stepAt_otma0S : .otma 0

/-- The output chunk's proxy fence 1. -/
w0s_free stepAt_ofpx1S : .ofpx 1

/-- The output chunk's barrier 1. -/
w0s_free stepAt_obar1S : .obar 1

/-- The output chunk's election 1. -/
w0s_free stepAt_oel1S : .oel 1

/-- The output chunk's TMA store 1. -/
w0s_free stepAt_otma1S : .otma 1

/-- The output chunk's proxy fence 2. -/
w0s_free stepAt_ofpx2S : .ofpx 2

/-- The output chunk's barrier 2. -/
w0s_free stepAt_obar2S : .obar 2

/-- The output chunk's election 2. -/
w0s_free stepAt_oel2S : .oel 2

/-- The output chunk's TMA store 2. -/
w0s_free stepAt_otma2S : .otma 2

/-- The output chunk's proxy fence 3. -/
w0s_free stepAt_ofpx3S : .ofpx 3

/-- The output chunk's barrier 3. -/
w0s_free stepAt_obar3S : .obar 3

/-- The output chunk's election 3. -/
w0s_free stepAt_oel3S : .oel 3

/-- The output chunk's TMA store 3. -/
w0s_free stepAt_otma3S : .otma 3

theorem stepAt_ofpxS (c : Fin 4) (d : D) (hs : d.site = .ofpx c) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  fin_cases c
  · exact stepAt_ofpx0S d hs he
  · exact stepAt_ofpx1S d hs he
  · exact stepAt_ofpx2S d hs he
  · exact stepAt_ofpx3S d hs he

theorem stepAt_obarS (c : Fin 4) (d : D) (hs : d.site = .obar c) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  fin_cases c
  · exact stepAt_obar0S d hs he
  · exact stepAt_obar1S d hs he
  · exact stepAt_obar2S d hs he
  · exact stepAt_obar3S d hs he

theorem stepAt_oelS (c : Fin 4) (d : D) (hs : d.site = .oel c) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  fin_cases c
  · exact stepAt_oel0S d hs he
  · exact stepAt_oel1S d hs he
  · exact stepAt_oel2S d hs he
  · exact stepAt_oel3S d hs he

theorem stepAt_otmaS (c : Fin 4) (d : D) (hs : d.site = .otma c) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  fin_cases c
  · exact stepAt_otma0S d hs he
  · exact stepAt_otma1S d hs he
  · exact stepAt_otma2S d hs he
  · exact stepAt_otma3S d hs he

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
