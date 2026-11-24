-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.TailCoverage
import Kernels.FlashKdaFwd.Audit.TailEntry

/-! Actual thread paths and exact zero stores in both first-tile clearing intervals. -/
namespace FlashKda.Tail
open PTX
noncomputable section

/-- Start at the first tile's clearing interval with the documented input registers.
Each of its 128 key writers emits exactly its list of zero stores and reconverges. -/
theorem all_writers (mode : Bool) (k : Kernel) (decodedEntry : whole mode = .ok k)
    (r : Fin 16) (c : Fin 128) :
    ∃ last, last.pc = finish mode ∧ Relation.ReflTransGen (advancing k (128+c))
      (entryState mode (r.val+1) c, expected (r.val+1) c) (last,[]) := by
  apply entry_trace mode k decodedEntry
  cases mode
  · exact fixed_writes r c
  · exact packed_writes r c

end
end FlashKda.Tail
