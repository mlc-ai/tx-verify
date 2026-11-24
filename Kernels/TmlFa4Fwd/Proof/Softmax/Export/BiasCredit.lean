-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.RoundCredit
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BiasReadAt
public import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Named
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Numerics
import Kernels.TmlFa4Fwd.Proof.SmWarp.Counts
import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.Common.Frame

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

private theorem bias_counts (lz z : Bool) (c : Fin 16) :
    (ptsOf lz (.acquire 80)).countP (Softmax.before (.bld z c)) =
      (ptsOf lz (.acquire 320)).countP (Softmax.before (.bld z c)) ∧
    (ptsOf lz (.acquire 80)).countP inBias = (ptsOf lz (.acquire 320)).countP inBias ∧
    (if z then inBias (Site.bld z c).pos else preR (.bld z c)) = true := by
  cases z <;> revert c lz <;> decide +kernel

/-- The ordinal used to select the loader's bias block is the score credit of this round. -/
theorem soft_bias_credit {p L m X g i z c a bs v k acc} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
    (hw : Prologue.warpIndex L g < 8)
    (he : X.get (g,i) = some ⟨(Site.bld z c).pc,.rd a bs⟩)
    (hs : softState p L X g i = some ⟨.bld z c,v,k,acc⟩) :
    Tm.sPolls L X g (Prologue.warpIndex L g/4) i =
      barOrd X g i (stageId (Prologue.warpIndex L g/4))+1 := by
  have hb := (soft_bias_read_at hp hX hf hw z c he).1
  unfold softState at hs
  split at hs
  · rename_i d n hd
    cases Option.some.inj hs
    let d := Control.erase (⟨.bld z c,v,k,acc⟩ : D)
    have hc : Frame.stateAt (thread p L) X g i = some (some (SmWarp.sinj p L g d n)) :=
      control_of_data hp hd
    obtain ⟨⟨cnt,⟨⟨rb,rp,hQ⟩⟩,link⟩,_⟩ :=
      ((SmWarp.good hp hX hw (Frame.lt_of_get hX he) rfl i).2 _ hc).2 (ub_zero hX he hc)
    change RefQ p L g d.scheduler cnt rb rp at hQ
    rw [← hb]
    rw [(tm_counts hw hc).1,← link _ rfl,sobj,soft_okPolls hw,count hc,← link _ rfl,
      hQ.cnt (.acquire 80) rfl,hQ.cnt (.acquire 320) rfl]
    obtain ⟨now,bias,place⟩ := bias_counts (lz L g) z c
    have zero : rp = 0 := by
      cases z
      · exact (hQ.pre place).2
      · exact (hQ.bias place).1
    change passed _ (.bld z c) rb rp = passed _ (.bld z c) rb rp
    simp only [passed,zero,Nat.zero_mul,Nat.add_zero,now,bias]
  · cases hs

end PTX.Kernels.TmlFa4Fwd.Proof.Values
