-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Projection
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsFirstCtl
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasPCtl
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainCtl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control

/-- The stores, waits, election and elected arrival common to the three probability rounds. -/
theorem stepAt_probabilityU {p L m g} (hp : Pre p L m) (hg : g < L.threads) (s : Site) (r : Rd)
    (v : V) (hs : s = .pst r 2 ∨ s = .pwst r 0 ∨ s = .pst r 3 ∨ s = .pwst r 1 ∨
      s = .pws r ∨ s = .pel r ∨ s = .parr2 r) : (code p L g).StepAtU ⟨s,v,0,[]⟩ := by
  have hr : readsData s = false := by rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  apply project hr
  cases r with
  | first => exact stepAt_first_pctl hp hg _ rfl rfl hs
  | bias => exact stepAt_bias_pctl hp hg _ rfl rfl hs
  | plain => exact stepAt_plain_pctl hp hg _ rfl rfl hs

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
