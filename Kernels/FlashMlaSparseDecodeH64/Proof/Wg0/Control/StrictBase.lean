-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamSteps
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Seg
public import Lemmas.Flow.Step.SiteCases

@[expose] public section

/-! # Warpgroup 0's strict step tactics

`w0s_sites s` discharges the exact (strict) step obligations (`Code.StepAt`) of the control
machine at the sites `hs` admits: `site_cases` with the machine's transitions, segments by
`seg_fp` closed by `rfl` or `sym_close`, the invariant (checked from the site's elements) and
guards. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
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

/-- Warpgroup 0's segments, closed by the table's terms. -/
macro "w0_segS" : tactic => `(tactic| (
  intro t h
  seg_fp h using first | rfl | sym_close))

syntax "w0s_sites " ident (" except " "[" siteOverride,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| w0s_sites $s $[except [$ovs,*]]?) => `(tactic|
      site_cases $s:ident $[except [$ovs,*]]? skip_by (simp at hs)
        trans [succ, afterSmr, afterSink, afterA, finish, loopEntry, advance, elemNext, poll,
          tcLoad, dataRd, ncWord, afterOst, afterEld, afterObar, nextChunk]
        seg_by (w0_segS)
        inv_by (intro _; (try dsimp only [elems])
                first | decide | (split_ifs <;> (try dsimp only [elems]) <;> decide))
        guard_by (trivial))

set_option hygiene false in
macro "w0s_state " d:ident : tactic => `(tactic|
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := $d)

set_option hygiene false in
/-- The strict step of a site without data: `w0s_sites` at the site. -/
macro (name := w0sFree) doc:(docComment)? "w0s_free " n:ident " : " site:term : command =>
  `($[$doc]? theorem $n (d : D) (hs : d.site = $site) (he : d.el = 0) :
      (code P L g w).StepAt d := by
    w0s_state d
    simp only at hs he
    subst he
    w0s_sites s)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
