-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.Start
public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.Entry
public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.End
public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.Qk
public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.Pv
public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.Sites

@[expose] public section

/-! # The MMA warp's steps

Every site is an event instruction whose guard holds by the site's facts: the sites outside the
eight asm blocks and the elections and inner polls inside them are unguarded, and an MMA is
guarded by the lane's election, which its facts record as true (only the elected lane reaches
it). Each event reaches the successor's concrete state by local steps. `site_cases`
(`mma_cases`) proves this site by site from the instruction at the site, `next` and the value
table; the hand proofs it is given are the pair allocation (`Start.lean`), the broadcast of the
Q descriptor (`Entry.lean`), the peer pointer and the hand-off poll (`End.lean`), the three ring
advances (`Ring*.lean`) and the slot wrap after PV block 0 (`Cut.lean`). One theorem per site
family (per block for the MMAs, per election for the long election segments), in three files,
keeps them checked in parallel. -/
