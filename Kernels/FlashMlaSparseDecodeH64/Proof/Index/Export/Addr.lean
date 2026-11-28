-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Index
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexPair
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.RefLoop
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.PairCore
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Blocks
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexAddr

@[expose] public section

/-! # The index warp's pair loads read the row's index words

Each `.nc` pair load of the index warp reads two 4-byte words (element `el < 2`), the words `j`
and `j + 1` of the lane's index row, `j = 64 b + 2 lane` (`lane = tidOf L g % 32`):

* `index_mainPairAddr`: the main array, `P.indicesBase + 4 ((e s_q + q) topk + j)` with
  `e = ctaidY`, `q = ctaidX` and `j + el < topk`: the first pair (pc `2403`) is block `b = 0`,
  the next pair (pc `2429`, made inside block `n`) block `n + 1`, `n = ixBlocksDone` the arrivals
  so far. So `Pre.idxInput` backs the words (`j + el < topk`, four bytes each);
* `index_extraPairAddr`: the extra array, `P.extraIndicesBase + 4 ((e s_q + q) extra_topk + j)`
  with `j + el < extra_topk` (`Pre.extraIdxInput`): the first extra pair (pc `2501`) is block
  `b = 0`, the next (pc `2517`, inside block `n`) block `n + 1 - M`, `M = numOrigBlocks`
  the length's main blocks (`Data/Indices.lean`).

The block is the machine's (the arrivals' count `blockOf`, the loop counters `Index.Ctr`); the
words' addresses are the code's registers (`Lib/IndexAddr.lean`, the table's `aptr` and `xa`);
the blocks fit the arrays by the lengths' bounds (`Index/Blocks.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The blocks a lane of the index warp has finished**: its arrivals on the four slots of
`valid_coord_ready`, over a trace prefix. -/
def ixBlocksDone (L : Launch) (g : Nat) (tr : List Event) : Nat :=
  arrivals (mbarLoc L (g / L.block) (.coordReady 0)) tr +
    arrivals (mbarLoc L (g / L.block) (.coordReady 1)) tr +
    arrivals (mbarLoc L (g / L.block) (.coordReady 2)) tr +
    arrivals (mbarLoc L (g / L.block) (.coordReady 3)) tr

/-- The state of a pair load: its site, element, block, counters and the lane's length words. -/
private theorem pair_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .nc a bs⟩)
    (hpc : pc = 2403 ∨ pc = 2429 ∨ pc = 2501 ∨ pc = 2517) :
    ∃ (d : Index.D) (i : Nat), d.site.pc = pc ∧ Index.EvK P L g d ⟨pc, .nc a bs⟩ ∧
      d.el < 2 ∧ Index.Ctr P L g d.site d.c i ∧ ixBlocksDone L g ((X.tr g).take k) = i ∧
      d.c.l0 = lenWA P L (g / L.block) ∧ d.c.l1 = lenWB P L (g / L.block) := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he (fun f h => by cases h)
  obtain ⟨d, n, i, -, hw, h1, h2, h3, h4, hb, h5, h6⟩ := pair_state hp hX he hpc hσ hJ hi hev hpcσ
  refine ⟨d, i, h1, h2, h3, h4, ?_, h5, h6⟩
  simp only [Index.blockOf] at hb
  simp only [ixBlocksDone, ix_arrivals hp hX hFw hw]
  exact hb

/-- **The main index array's pair loads** (pcs `2403`, `2429`) read word `64 b + 2 lane + el` of
the lane's row, below `topk`. -/
theorem index_mainPairAddr (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .nc a bs⟩) (hpc : pc = 2403 ∨ pc = 2429) :
    ∃ b el : Nat, el < 2 ∧ (pc = 2403 → b = 0) ∧
      (pc = 2429 → b = ixBlocksDone L g ((X.tr g).take k) + 1) ∧
      64 * b + 2 * (tidOf L g % 32) + el < P.topk ∧ a.size = 4 ∧
      a.loc = ⟨.global, 0, P.indicesBase + 4 * ((ctaidY L g * P.s_q + ctaidX L g) * P.topk +
        (64 * b + 2 * (tidOf L g % 32) + el))⟩ := by
  obtain ⟨d, i, hpcd, hEv, hel, hct, hdone, h0, -⟩ := pair_at hp hX hFw he (by omega)
  obtain ⟨b, h1, h2, h3, h4, h5, h6⟩ := main_pair_core hp hpcd hEv hel hct h0 hpc
  exact ⟨b, d.el, h1, h2, fun h => by rw [h3 h, hdone], h4, h5, h6⟩

/-- **The extra index array's pair loads** (pcs `2501`, `2517`) read word `64 b + 2 lane + el` of
the lane's row, below `extra_topk`. -/
theorem index_extraPairAddr (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .nc a bs⟩) (hpc : pc = 2501 ∨ pc = 2517) :
    ∃ b el : Nat, el < 2 ∧ (pc = 2501 → b = 0) ∧
      (pc = 2517 → b + numOrigBlocks (P.topkLen (ctaidY L g)) =
        ixBlocksDone L g ((X.tr g).take k) + 1) ∧
      64 * b + 2 * (tidOf L g % 32) + el < P.extra_topk ∧ a.size = 4 ∧
      a.loc = ⟨.global, 0, P.extraIndicesBase + 4 * ((ctaidY L g * P.s_q + ctaidX L g) *
        P.extra_topk + (64 * b + 2 * (tidOf L g % 32) + el))⟩ := by
  obtain ⟨d, i, hpcd, hEv, hel, hct, hdone, h0, h1⟩ := pair_at hp hX hFw he (by omega)
  obtain ⟨b, g1, g2, g3, g4, g5, g6⟩ := extra_pair_core hp hpcd hEv hel hct h0 h1 hpc
  exact ⟨b, d.el, g1, g2, fun h => by rw [g3 h, hdone], g4, g5, g6⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
