-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamSteps
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Seg
public import Lemmas.Flow.Step.SiteCases

@[expose] public section

/-! # Warpgroup 2's strict step tactics

`dq_sites s` discharges the exact (strict) step obligations of the sites of `s` that `hs` admits:
`site_cases` with the machine's transitions, segments by `seg_fp` closed by `rfl` or `sym_close`,
the trivial invariant (checked from the site's elements) and guards. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
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

/-- Follow a 32-bit word. -/
def word32 (v : Value) (f : BitVec 64 → D) : Option (Option D) :=
  match v with
  | .bits 32 x => some (some (f x))
  | _ => some none

/-- A length load's successor, by the value its bytes rebuild to. -/
theorem ncNext_eq {f : BitVec 64 → D} {bs : List (Option Byte)} :
    Code.ncNext f bs = match rebuild 3 bs with | .ok v => word32 v f | .error _ => none := by
  unfold Code.ncNext word32
  rcases h : rebuild 3 bs with _ | v
  · rfl
  · dsimp only
    rcases v with ⟨n, x⟩ | _ <;> try rfl
    all_goals
      by_cases hn : n = 32
      · subst hn; rfl
      · simp [hn]

/-- Warpgroup 2's segments, closed by the table's terms. -/
macro "dq_segS" : tactic => `(tactic| (
  intro t h
  seg_fp h using first | rfl |
    (simp only [slW, parB, Bool.not_true, Bool.not_false]; decide +kernel) | sym_close))

syntax "dq_sites " ident (" except " "[" siteOverride,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| dq_sites $s $[except [$ovs,*]]?) => `(tactic|
      site_cases $s:ident $[except [$ovs,*]]? skip_by (simp at hs)
        trans [succ, afterSmr, afterA, loopEntry, advance, poll, rowNext, rawNext, storeNext,
          scaleNext, ncNext_eq, word32]
        seg_by (dq_segS)
        inv_by (intro _; (try dsimp only [elems])
                first | decide | (split_ifs <;> (try dsimp only [elems]) <;> decide))
        guard_by (trivial))

set_option hygiene false in
macro "dq_state " d:ident : tactic => `(tactic|
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := $d)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
