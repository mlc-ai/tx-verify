-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Machine
public import Lemmas.Flow.Step.Alloc
public import Lemmas.Flow.Step.SiteCases
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Epilogue.Base

@[expose] public section

/-! # Shared tactics of the MMA warp's step files

The transition lemmas of the machine (`mma_trans`) and the role's tactic for the obligations of
one site family (`mma_sites`): `site_cases` over the site, segments by `seg_fp` closed by `rfl`
or `sym_close` (`ep_seg`, with the output warp's launch facts: the explicit parameters, the
CTA index bound, no rule of an assumption on the integer code). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

/-- `mma_sites s except […]`: the obligations of the sites of `s` that the theorem's hypothesis
`hs` admits. -/
syntax "mma_sites " ident (" except " "[" siteOverride,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| mma_sites $s $[except [$ovs,*]]?) => `(tactic|
      site_cases $s:ident $[except [$ovs,*]]? skip_by (simp at hs)
        trans [succ, word32, scAt, afterTotal, loopHead, scanExit,
          PTX.Kernels.TmlFa4Fwd.Proof.Epilogue.loopOf,
          PTX.Kernels.TmlFa4Fwd.Proof.Epilogue.Scan.late,
          PTX.Kernels.TmlFa4Fwd.Proof.Epilogue.tlOf, afterTiles, coords, passStart, enterLoop,
          loopEnd, setS, shNext, wtNext, qkDone, pvDone, qkOff, ceNext]
        seg_by (ep_seg) inv_by (exact fun _ => trivial) guard_by (trivial))

/-- `mma_issue lemma`: the obligation of an event that continues at the next instruction by
`lemma` (an override of `mma_sites`). -/
syntax "mma_issue " term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| mma_issue $adv) => `(tactic|
      issue_step $adv
        trans [succ, word32, scAt, afterTotal, loopHead, scanExit,
          PTX.Kernels.TmlFa4Fwd.Proof.Epilogue.loopOf,
          PTX.Kernels.TmlFa4Fwd.Proof.Epilogue.Scan.late,
          PTX.Kernels.TmlFa4Fwd.Proof.Epilogue.tlOf, afterTiles, coords, passStart, enterLoop,
          loopEnd, setS, shNext, wtNext, qkDone, pvDone, qkOff, ceNext]
        seg_by (ep_seg) inv_by (exact fun _ => trivial))

end PTX.Kernels.TmlFa4Fwd.Proof.Mma
