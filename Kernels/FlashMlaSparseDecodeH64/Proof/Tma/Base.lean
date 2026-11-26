-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamSteps
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Seg
public import Lemmas.Flow.Step.SiteCases

@[expose] public section

/-! # The TMA warp's step tactics

`tma_sites s` discharges the step obligations of the sites of `s` that the theorem's hypothesis
`hs` admits: `site_cases` with the machine's transitions, segments by `seg_fp` closed by `rfl` or
`sym_close` (`tma_seg`), the trivial invariant and guards. No assumption gives an integer
instruction of the role a rule of its own (`asms_localRule_int`), and a branch on a parameter
word is decided by the case split's hypothesis (`sym_decide`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow

scoped macro_rules
  | `(tactic| sym_local_none) => `(tactic| (
      intro t ht a ha
      exact asms_localRule_int (t := t) (by rw [ht]; decide) (by rw [ht]; decide)
        (by rw [ht]; decide) (by simp [Assumptions.peerPackRule, Assumptions.peerPack, ht]) a ha))

scoped macro_rules
  | `(tactic| sym_decide) => `(tactic| first
      | assumption
      | exact Bool.eq_false_iff.mpr (by assumption))

/-- The TMA warp's segments, closed by the table's terms. -/
macro "tma_seg" : tactic => `(tactic| (intro t h; seg_fp h using first | rfl | sym_close))

/-- `tma_sites s except […]`: the obligations of the sites of `s` that `hs` admits. -/
syntax "tma_sites " ident (" except " "[" siteOverride,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| tma_sites $s $[except [$ovs,*]]?) => `(tactic|
      site_cases $s:ident $[except [$ovs,*]]? skip_by (simp at hs)
        trans [succ, electNext, poll, loopEntry, loopEnd, leadNext, afterTopk, lensD, ncWord,
          word32]
        seg_by (tma_seg) inv_by (exact fun _ => trivial) guard_by (trivial))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
