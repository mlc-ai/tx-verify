-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.TcCpWs
public import Lemmas.Flow.Step.TcSteps

@[expose] public section

/-! # `advances` for `tcgen05.cp` and every `tcgen05.mma` form

`advances` (`Lemmas/Flow/Step/SiteCases.lean`, extended in `TcSteps.lean`) closes the
continuation of the `.dense` MMA forms only. With this file imported it also closes `tcgen05.cp`
(`fires_tcCp_next`) and every `tcgen05.mma` form, `.ws` with a zero-column mask included
(`fires_tcMma_next`), so the site tactics (`site_cases`, `step_issue`'s `advances` premise) need
no override at these instructions. -/

namespace PTX.Flow

macro_rules
  | `(tactic| advances) => `(tactic| advances_of PTX.Op.tcCp PTX.Flow.fires_tcCp_next)
macro_rules
  | `(tactic| advances) => `(tactic| advances_of PTX.Op.tcMma PTX.Flow.fires_tcMma_next)

end PTX.Flow
