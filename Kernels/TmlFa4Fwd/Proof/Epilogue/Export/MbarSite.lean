-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Shape
public import Lemmas.Kernel.Safety.Classes
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The output warp's sites that name an mbarrier -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

set_option maxHeartbeats 4000000 in
/-- The output warp names its ready barriers at its ready polls and its free barriers at its
free arrivals. -/
theorem epi_site {d : Epilogue.D} {e : Event} {l : Loc} (hev : Epilogue.Ev p L g d e)
    (hm : MbarOf e l) : (∃ st, d.site = .ready st ∧ l = Epilogue.readyLoc L g st) ∨
      ∃ st, d.site = .free st ∧ l = Epilogue.freeLoc L g st := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨site, rest⟩ := d
  cases site <;> simp only [Epilogue.Ev] at hev
  all_goals (try split at hev)
  all_goals cases kind <;> simp only [MbarOf] at hm
  all_goals simp_all [Epilogue.isStore]

end
end PTX.Kernels.TmlFa4Fwd.Proof
