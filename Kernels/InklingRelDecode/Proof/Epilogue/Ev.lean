-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Control.Machine
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Epilogue

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue
open PTX PTX.Flow PTX.Proof Control

/-- The only mbarrier operation after the data-role handoff is the final O wait. -/
def ObjectEv (L : Launch) (g : Nat) (site : Site) (ev : Event) : Prop :=
  site = .wait → PTX.MbarRow.Wait ev (MbarRow.loc L g Iface.oFinal) 0

end PTX.Kernels.InklingRelDecode.Proof.Epilogue
