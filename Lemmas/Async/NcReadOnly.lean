-- SPDX-License-Identifier: Apache-2.0
module

public import Assumption.NcReadOnly
public import Lemmas.Snoc.PlainExtend
public import Lemmas.Snoc.SnocAsync

@[expose] public section

/-! # Assumption `ncReadOnly`: extending an execution keeps its condition -/

namespace PTX.Proof
open PTX

theorem ncReadOnly_wf_snoc {name why : String} {sites : List Nat} {L : Launch} {mem0 : Mem0}
    {X : Execution} {g : Nat} {e : Event} {r : Nat → Option AsyncCopy.Ref}
    (hwf : (Assumption.ncReadOnly name sites why).wf L mem0 X)
    (he : ∀ a bs, e.kind = .nc a bs → sites.contains e.pc → bs.length = a.size ∧
      ∀ k < a.size, ∀ c, mem0 (a.loc.at k) = some c →
        bs[k]? = some (X.initialByte c (a.loc.at k))) :
    (Assumption.ncReadOnly name sites why).wf L mem0 (X.snoc g e r) := by
  intro v pc a bs hv hs
  rw [snoc_get] at hv
  split_ifs at hv
  · cases hv; exact he a bs rfl hs
  · exact hwf v pc a bs hv hs

end PTX.Proof
