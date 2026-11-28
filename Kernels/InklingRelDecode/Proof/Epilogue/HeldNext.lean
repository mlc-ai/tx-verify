-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Control.Machine

@[expose] public section

/-! # The broadcast word of the epilogue

The epilogue shuffles the warp index once, unless the launch has no block (`Entry.skip`), and
holds the word it receives at the load. A step into the load is the shuffle's, the sites before
the shuffle are the wait and the shuffle itself, and every other site follows the shuffle or the
skip. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue
open _root_.PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control

/-- The sites after the epilogue's shuffle, or that skip it. -/
def pastShfl : Site → Bool
  | .wait | .shfl => false
  | _ => true

theorem held_next {e L g d ev dn} (step : Control.next e L g d ev = some (some dn)) :
    (dn.site = .load → d.site = .shfl ∧ ∃ m a b c ok, ev.kind = .shfl m a b c dn.received ok) ∧
    ((dn.site = .wait ∨ dn.site = .shfl) → d.site = .wait) ∧
    (pastShfl dn.site = true → pastShfl d.site = true ∨ d.site = .shfl ∨
      (d.site = .wait ∧ e.skip = true)) := by
  obtain ⟨s,v⟩ := d
  cases s <;> simp only [Control.next,firstStore,storeAt] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals simp_all [pastShfl]

end PTX.Kernels.InklingRelDecode.Proof.Epilogue
