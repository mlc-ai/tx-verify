-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.AsyncChain
public import Lemmas.Order.CommitOperandFrame
public import Core.Memory.Read

@[expose] public section

namespace PTX
open AsyncCopy
variable {L : Launch} {X Y : Execution}

/-- A resource extension preserves causality when it preserves reads, their
sources and visibility into old effects. -/
theorem NoFuture.of_frame (h : NoFuture L X)
    (hr : ∀ e a bs, Y.MemReads e a bs → X.MemReads e a bs)
    (hrf : Y.rf = X.rf)
    (hv : ∀ l e f, ByteCausality L Y l e f → ByteCausality L X l e f) : NoFuture L Y := by
  intro e a bs k w he hk hs hh
  rw [hrf] at hs
  exact h e a bs k w (hr e a bs he) hk hs (hv _ _ _ hh)

/-- The same reflection preserves exclusion of hidden read sources. -/
theorem Hidden.of_frame (h : Hidden L X)
    (hr : ∀ e a bs, Y.MemReads e a bs → X.MemReads e a bs)
    (hw : ∀ e a bs, Y.MemWrites e a bs → X.MemWrites e a bs)
    (hrf : Y.rf = X.rf)
    (hv : ∀ l e f, ByteCausality L Y l e f → ByteCausality L X l e f) : Hidden L Y := by
  intro e a bs k w dst bytes he hk hwr hc hh
  have hs := h e a bs k w dst bytes (hr e a bs he) hk (hw w dst bytes hwr) hc
    (hv _ _ _ hh)
  rw [hrf]
  cases hsrc : X.rf e k with
  | none => rw [hsrc] at hs; exact hs
  | some source =>
    rw [hsrc] at hs
    exact fun hbefore => hs (hv _ _ _ hbefore)

end PTX
