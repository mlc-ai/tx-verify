-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Startup
import Lemmas.Protocol.MbarRowSource

namespace PTX.Kernels.InklingRelDecode.Proof.Startup.Export
open PTX MbarRow PTX.MbarRow

/-- Neither startup pc range contains an instruction referencing an mbarrier. -/
public theorem mbarRow {Q L m X} (hX : Consistent L kernel Assumptions.all m X) :
    MbarRow.Startup Q L X := by
  intro g k e l _ he atPc hm
  rcases atPc with h | h
  · obtain ⟨_,hs,_⟩ := region_source startup_sites hX he hm (Nat.zero_le _) h
    contradiction
  · obtain ⟨_,hs,_⟩ := region_source startup_sites_1 hX he hm h.1 h.2
    contradiction

end PTX.Kernels.InklingRelDecode.Proof.Startup.Export
