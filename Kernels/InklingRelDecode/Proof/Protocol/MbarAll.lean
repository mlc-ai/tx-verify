-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOHyp
public import Kernels.InklingRelDecode.Proof2.Lib.MbarInit
public import Kernels.InklingRelDecode.Proof.Protocol.MbarReach
public import Kernels.InklingRelDecode.Proof.Protocol.MbarRoute
public import Kernels.InklingRelDecode.Proof.Protocol.MbarWords

@[expose] public section

/-!
# The mbarrier protocols of the Inkling decode kernel: umbrella

* `MbarRoute`, `MbarReach`: the reuse paths of the S/P/O handshake (`Notify.Reach` of `s_ready`
  and `o_done`, `Unit.Reach` of `p_ready`), their gates, and the fault freedom of `s_ready`,
  `p_ready`, `o_done` and `o_final`.
* `MbarInit`: an mbarrier initialized once and published to its users is initialized first, and
  every record lies in a published lifetime.
* `MbarWords`: `Interface.ProWordsMatch`, the premise of `Interface.early_stores_same`.
-/
