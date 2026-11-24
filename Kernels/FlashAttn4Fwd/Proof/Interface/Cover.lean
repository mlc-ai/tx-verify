-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.TmemRoute
public import Kernels.FlashAttn4Fwd.Proof.Interface.MmaSteps

@[expose] public section

/-! # What the thread layer exports for the coverage of the Tensor Memory loads

A softmax load of score tile `u` and a correction load of credit `q` read cells that some MMA of
the tile wrote. Which cells an MMA writes is arithmetic on its descriptor and accumulator address
(`Protocol/Cover.lean`: an MMA of the kernel writes all 128 lanes of both CTAs of its pair, over
the 128 columns of the region it writes). What the thread layer adds is that the MMAs were
issued, up to the last K step of their block (step 7: `qkStep`, `pvStep`): with `n = kvTiles`
tiles per item, the MMA thread of a pair issues, per stage `st`,

* the QK block of score tile `u` (`u` commits to the stage's S-full object before it) before the
  commit of tile `u` to that object (`qk_sfull`);
* the PV block of tile `u - 1` (`u` successful polls of the stage's P-ready object before it)
  before the S-full commit of tile `u ≥ 1` (`pv_sfull`): the PV block of a tile comes before the
  QK block of the next tile of the stage, which precedes its commit;
* the PV block of every tile `v - 1` with `v ≤ n (I + 1)` before the commit of item `I` to the
  stage's O-full object (`pv_ofull`): that commit follows the item's last PV block.

The fields are event-level facts of the MMA thread from its run invariant (`Mma.Counts`: the
asm blocks of the S and PV MMAs and the commits between them, per item and trip) and the
accumulator addresses of the MMA sites. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow TcMma

noncomputable section

/-- The thread layer's facts for the coverage of the Tensor Memory loads. -/
structure CoverFacts (L : Launch) (X : Execution) : Prop where
  /-- A commit to stage `st`'s S-full object of its CTA follows step 7 of an MMA block of its
  thread writing the stage's scores, after as many commits to the object. -/
  qk_sfull : ∀ {y : EvId} {s : TcCommit.Spec} {st : Nat}, X.Commit y s → st < 2 →
    s.mbar = sFullBar L (ctaOf L y.1) st →
    ∃ k < y.2, QkAt X y.1 st k ∧ sCommits L X y.1 st k = sCommits L X y.1 st y.2 ∧
      qkStep L X y.1 st k = 7
  /-- A commit to stage `st`'s S-full object of its CTA with `u ≥ 1` commits to it before follows
  step 7 of an MMA block of its thread writing the stage's accumulator, after `u` successful polls
  of the stage's P-ready object. -/
  pv_sfull : ∀ {y : EvId} {s : TcCommit.Spec} {st : Nat}, X.Commit y s → st < 2 →
    s.mbar = sFullBar L (ctaOf L y.1) st → 1 ≤ sCommits L X y.1 st y.2 →
    ∃ k < y.2, PvAt X y.1 st k ∧ pPolls L X y.1 st k = sCommits L X y.1 st y.2 ∧
      pvStep L X y.1 st k = 7
  /-- A commit to stage `st`'s O-full object of its CTA with `I` commits to it before follows, for
  every `1 ≤ v ≤ n (I + 1)`, step 7 of an MMA block of its thread writing the stage's
  accumulator, after `v` successful polls of the stage's P-ready object. -/
  pv_ofull : ∀ {y : EvId} {s : TcCommit.Spec} {st v : Nat}, X.Commit y s → st < 2 →
    s.mbar = oFullBar L (ctaOf L y.1) st → 1 ≤ v →
    v ≤ kvTiles L * (oFullCommits L X y.1 st y.2 + 1) →
    ∃ k < y.2, PvAt X y.1 st k ∧ pPolls L X y.1 st k = v ∧ pvStep L X y.1 st k = 7

end
end PTX.Kernels.FlashAttn4Fwd.Proof
