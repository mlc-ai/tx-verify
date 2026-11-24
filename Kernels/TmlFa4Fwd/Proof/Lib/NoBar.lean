-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Place
import Kernels.TmlFa4Fwd.Proof.Epilogue.Open
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init

@[expose] public section

/-! # The output and loader warps' barrier events are the startup's -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A barrier event of an output or loader warp** is the startup's. -/
theorem late_bar_pc (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 13 ≤ Prologue.warpIndex L g) {k pc id : Nat} {cnt : Option Nat}
    {mode : BarMode} (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) :
    pc = mmaPc (((X.tr g).take k).countP Execution.isBar) := by
  have hg := Frame.lt_of_get hX he
  have h16 := Prologue.warpIndex_lt hp g
  rcases Nat.lt_or_ge (Prologue.warpIndex L g) 14 with h1 | h1
  · rcases Epilogue.open_ev hp hX hFw (by omega) he (fun f h => by cases h) with
      ⟨s, n, hσ, -, hJ, -, hev⟩ | ⟨d, n, -, -, -, -, hev⟩
    · rw [start_bar_pc hp hX he hσ hJ hev, start_bar_ord hp hX hFw hg he hσ]
      rfl
    · exact (epi_nobar hev _ _ _ rfl).elim
  · rcases LdWarp.open_ev hp hX hFw (by omega) he (fun f h => by cases h) with
      ⟨s, n, hσ, -, hJ, -, hev⟩ | ⟨b, d, n, -, -, -, -, hev⟩
    · rw [start_bar_pc hp hX he hσ hJ hev, start_bar_ord hp hX hFw hg he hσ]
      rfl
    · exact (ld_nobar hev).elim

end PTX.Kernels.TmlFa4Fwd.Proof
