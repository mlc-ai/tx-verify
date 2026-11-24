-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.AsyncOrder
public import Lemmas.Clc.ClcReadSources

@[expose] public section

/-! # The source of a cancellation response's completion

A proof tool. A completion record of a cluster launch control response on an mbarrier names an
actual request whose targets include the notified CTA, which the request notified on its
response barrier there (`Consistent.clc_notified`). -/

namespace PTX

open AsyncCopy

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

theorem Consistent.clc_notified (hX : Consistent L K A mem0 X) {m : Loc}
    {r : MBarrier.Record Ref} (hr : r ∈ X.objects m) {i : EvId} {c : Nat}
    (hid : r.id = .async i (.notify (.cta c))) :
    ∃ s targets, X.ClcIssue i s targets ∧ c ∈ targets ∧ c ∈ (X.clc i).notified ∧
      m = { s.mbar with cta := c } := by
  have ha := ((hX.tma.2.2.1 m).2.1 r hr).1
  rw [hid] at ha
  cases he : X.get i with
  | none => simp [objectAction, he] at ha
  | some ev =>
    rcases ev with ⟨pc, kind⟩
    cases kind <;> simp only [objectAction, he, reduceCtorEq] at ha
    case clcIssue s targets =>
      split_ifs at ha with hn
      exact ⟨s, targets, ⟨pc, he⟩, hn⟩

end PTX
