-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.NoUb
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Def
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.SmWarp.DataEvent
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.SmWarp.NoUb
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Numerics

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX.Flow PTX.Proof Softmax

theorem alive_of_prefix_reads {p L m X g K e} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hw : Prologue.warpIndex L g < 8)
    (hB : BiasReadHandoff p L X) (he : X.get (g,K) = some e)
    (hld : ∀ i < K, ∀ a vals sh, X.TLd (g,i) a vals sh → Values.F32s vals) :
    ∃ σ, Frame.stateAt (threadD p L) X g K = some (some σ) := by
  have hg := Frame.lt_of_get hX he
  apply alive hp hX (numSteps hp) (storeSafe hp) hw hg rfl _ K (Nat.le_refl _) (len_of_get he)
  intro i hi d n c ev hget hst href
  have hctl := control_of_data hp hst
  have fitted := (((good hp hX hw hg rfl i).2 _ hctl).2 (ub_zero hX hget hctl)).2
  have hn := (data_event hp hX (storeSafe hp g) hget hst).1.2
  apply expectD_of (d := d) hp hg fitted (sexpect hp hX (cuQReadsFromLaunch hp hX) hg rfl hget hctl
    fitted hn (fun _ _ j hin _ => good hp hX hw hin.1 hin.2 j))
  cases hs : d.site with
  | bld b j => simpa only [ExpectRest, hs] using expect_bias hp hX hB hget hst href hs
  | sld r j =>
    simp only [ExpectRest, ExpectD, hs]
    intro a vals sh hk
    obtain ⟨pc, kd⟩ := ev
    cases hk
    exact hld i hi a vals sh ⟨pc,hget⟩
  | _ => simp only [ExpectRest, hs]

end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
