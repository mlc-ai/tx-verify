-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Startup.Transparency
public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Flow.Code.Part000
public import Lemmas.Flow.Regs
public import Lemmas.Isa.Rule

@[expose] public section

/-! # The warp of a thread -/

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Proof

/-- Linear warp number in the CTA. -/
def warpIndex (l : Launch) (g : Nat) : Nat := g % l.block / 32

theorem warpIndex_lt {p : Params} {l : Launch} {m : Mem0} (hpre : Pre p l m) (g : Nat) :
    warpIndex l g < 16 := by
  unfold warpIndex
  rw [hpre.block]
  have := Nat.mod_lt g (show 0 < 512 by decide)
  omega

end PTX.Kernels.TmlFa4Fwd.Prologue
