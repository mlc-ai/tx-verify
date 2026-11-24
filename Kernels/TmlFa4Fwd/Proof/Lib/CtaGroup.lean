-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.TcTmpl

@[expose] public section

/-! # The single-CTA group of a lane -/

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow

/-- A CTA's group of qualifier `one` is the CTA. -/
theorem singleCtaGroup {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) : l.ctaGroup (g / l.block) .one = some [g / l.block] := by
  have hBlock : 0 < l.block := by rw [hp.block]; decide
  have hCta := (Nat.div_lt_iff_lt_mul hBlock).2 (show g < l.grid * l.block from hg)
  have hOne := hp.cluster.2.2
  have hSize := hp.cluster.1
  rw [Launch.ctaGroup_one]
  simp [Launch.peerCta, Launch.oneDim_rankOfCta hOne, Launch.oneDim_clusterOfCta hOne,
    Launch.oneDim_clusterSizeOf hOne, Launch.oneDim_clusterStart hOne, hSize, Nat.mod_one, hCta]

end PTX.Kernels.TmlFa4Fwd.Mma
