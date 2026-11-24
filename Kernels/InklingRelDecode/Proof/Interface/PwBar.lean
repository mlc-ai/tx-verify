-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.BarLaneLoop
public import Kernels.InklingRelDecode.Proof.Protocol.BarOrd
public import Kernels.InklingRelDecode.Proof.Protocol.BarLaneCta

@[expose] public section

/-! # The phased ledger and the sources of named barrier 0, for the progress layer

`NamedBar.Phased`, `PhSources`, `gen_of_record`, `D_arrival_key`, `Bar.bar0_sources`,
`Bar.loopGroup` (`Protocol/BarLanePhase.lean`, `BarLaneKeys.lean`, `BarLaneLoop.lean`), and the
early sources (`Bar.earlySources_bar0`, `Protocol/BarOrd.lean`). -/
