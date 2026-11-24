-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.TailRun

/-! Every store of every clearing thread, for every live length of the first tile. -/
namespace FlashKda.Tail

set_option maxHeartbeats 1600000000
set_option maxRecDepth 150000

theorem fixed_writes : ∀ (r : Fin 16) (c : Fin 128), traceMatches false (r.val+1) c = true := by
  decide +kernel

theorem packed_writes : ∀ (r : Fin 16) (c : Fin 128), traceMatches true (r.val+1) c = true := by
  decide +kernel

end FlashKda.Tail
