-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WinEpi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.StrictChain

@[expose] public section

/-! # The side conditions of warpgroup 0's strict step from a valid trace

`stepConds_of`: the strict step before an event of a lane of warpgroup 0 (`StepConds`) from the
context of a window (`WCtx`: the data state's invariants, the valid trace through the event, the
typed words of the event and the words its block has loaded), when the event is an `nc` read only at
the pcs of the sink and the length loads. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

noncomputable section

variable {L : Launch} {g : Nat} {sc : ℝ} {l : List Event} {d : D} {e : Event}

/-- **All the windows' conditions** from the context of a window. -/
theorem winCond_of (c : WCtx L g sc l d e) : WinCond L g d e where
  w156 := wc_156 c
  w289 := wc_289 c
  w403 := wc_403 c
  w413 := wc_413 c
  w423 := wc_423 c
  w433 := wc_433 c
  w443 := wc_443 c
  w453 := wc_453 c
  w463 := wc_463 c
  w475 := wc_475 c
  w477 := wc_477 c
  w482 := wc_482 c
  w487 := wc_487 c
  w492 := wc_492 c
  w497 := wc_497 c
  w502 := wc_502 c
  w507 := wc_507 c
  w512 := wc_512 c
  w572 := wc_572 c
  w578 := wc_578 c
  w711 := wc_711 c
  w717 := wc_717 c
  w818 := wc_818 c
  w919 := wc_919 c
  w1020 := wc_1020 c
  w1122 := wc_1122 c
  w1157 := wc_1157 c
  w1187 := wc_1187 c
  w1202 := wc_1202 c
  w1362 := wc_1362 c
  w1520 := wc_1520 c
  w1677 := wc_1677 c

/-- **The side conditions of the strict step** from the context of a window. -/
theorem stepConds_of (c : WCtx L g sc l d e)
    (hnc : ∀ x bs, e.kind = .nc x bs → e.pc = 156 ∨ e.pc = 168 ∨ e.pc = 181) :
    StepConds L g d e := by
  refine ⟨fun h1 h2 => c.hOk (by simp [innerSite, h1, h2]), fun x bs hk => ?_, winCond_of c⟩
  rcases hnc x bs hk with hp | hp | hp
  · obtain ⟨bits, q, -, -, hr⟩ := c.hpay.sink x bs hk hp
    exact ⟨_, hr⟩
  · exact c.hpay.length x bs hk (.inl hp)
  · exact c.hpay.length x bs hk (.inr hp)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
