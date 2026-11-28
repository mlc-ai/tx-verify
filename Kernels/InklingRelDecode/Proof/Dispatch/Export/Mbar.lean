-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Dispatch
public import Kernels.InklingRelDecode.Proof.Common.Follow
import Lemmas.Protocol.MbarRowSource

namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch.Export
open PTX MbarRow PTX.MbarRow

public theorem mbarRow {Q L m X} (_hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (_hf : Follow Q L X) : MbarRow.Dispatch Q L X := by
  intro g k e l _ he hat hm
  obtain ⟨_,h | h | h⟩ := hat
  · obtain ⟨_,hs,_⟩ := region_source dispatch_sites hX he hm h.1 h.2
    contradiction
  · obtain ⟨_,hs,_⟩ := region_source dispatch_sites_1 hX he hm h.1 h.2
    contradiction
  · obtain ⟨_,hs,_⟩ := region_source dispatch_sites_2 hX he hm h.1 h.2
    contradiction

end PTX.Kernels.InklingRelDecode.Proof.Dispatch.Export
