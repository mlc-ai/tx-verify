-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyCursorContinue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader
  (reuseEntry reuseArrival recurringEmptyWait readySlot emptySlot kvUseStage kvEmptyPhase
    loaderSliceEvents actualEmptySeedPrefix)

noncomputable section

/-- The poll issued at the chosen cursor use. -/
def cursorPoll (l : Launch) (g use : Nat) (site : Fin 4) (ok : Bool) : Event :=
  ⟨(recurringEmptyWait site).pc,
    .wait (Prologue.initObject l (g / l.block) (emptySlot (kvUseStage use)))
      (if kvEmptyPhase use then 1 else 0) ok true .cta⟩

/-- The publication corresponding to the chosen cursor use. -/
def cursorArrival (l : Launch) (g use : Nat) (site : Fin 4) : Event :=
  ⟨reuseArrival site,
    .asyncArrive (Prologue.initObject l (g / l.block) (readySlot (kvUseStage use))) true⟩

/-- The recurring wait and publication events in an actual loader prefix follow its
local cursor. Between uses, the scheduler may emit events that touch neither marker. -/
inductive RecurringCursorTrace (l : Launch) (g : Nat) : Nat → List Event → Prop
  | nil (use) : RecurringCursorTrace l g use []
  | gap {use : Nat} {pre tail : List Event}
      (quiet : ∀ e ∈ pre, ¬ recurringPublicationEvent e ∧ ¬ recurringEmptyEvent e)
      (next : RecurringCursorTrace l g use tail) : RecurringCursorTrace l g use (pre ++ tail)
  | packet {use n : Nat} {site : Fin 4} {mid tail : List Event}
      (plane : site.val % 2 = use % 2)
      (quiet : ∀ e ∈ mid, ¬ recurringPublicationEvent e ∧ ¬ recurringEmptyEvent e)
      (next : RecurringCursorTrace l g (use + 1) tail) :
      RecurringCursorTrace l g use (List.replicate n (cursorPoll l g use site false) ++
        cursorPoll l g use site true :: mid ++ cursorArrival l g use site :: tail)

/-- Truncate an actual walk at an exact event count while retaining its visit prefix. -/
theorem takeLoaderEvents {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs) (n : Nat) :
    ∃ leading, leading <+: vs ∧ Walk kernel Assumptions.all l g s (es.take n) leading := by
  induction hw generalizing n with
  | stop => exact ⟨[], List.nil_prefix, by simpa using (Walk.stop _)⟩
  | tau ht _ ih =>
    obtain ⟨p, hp, hw⟩ := ih n
    exact ⟨_, List.cons_prefix_cons.mpr ⟨rfl, hp⟩, .tau ht hw⟩
  | ev he _ ih =>
    cases n with
    | zero => exact ⟨[], List.nil_prefix, .stop _⟩
    | succ n =>
      obtain ⟨p, hp, hw⟩ := ih n
      exact ⟨_, List.cons_prefix_cons.mpr ⟨rfl, hp⟩, .ev he hw⟩
  | last he =>
    cases n with
    | zero => exact ⟨[], List.nil_prefix, .stop _⟩
    | succ _ => exact ⟨_, List.prefix_rfl, by simpa using (Walk.last he)⟩

private theorem getLastAppendOfNonempty {α : Type} {xs ys : List α} (hy : ys ≠ []) :
    (xs ++ ys).getLast? = ys.getLast? := by
  rw [List.getLast?_append]
  cases h : ys.getLast? with
  | none => exact (hy (List.getLast?_eq_none_iff.mp h)).elim
  | some => rfl

/-- Induct along the actual packet continuations, keeping stage and parity of every
recurring use that reaches publication in the selected prefix. -/
theorem recurringCursorPrefix {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g use : Nat} (site : Fin 4) {s : TState} {es : List Event} {vs : List Visit}
    {last : Event} (hPlane : site.val % 2 = use % 2)
    (hs : At s (reuseEntry site) (emptyCursorFrame l site use))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hScope : ∀ v ∈ vs, v.pc < 1744)
    (hLast : es.getLast? = some last) (hPub : recurringPublicationEvent last) :
    RecurringCursorTrace l g use es := by
  generalize hk : vs.length = k
  induction k using Nat.strong_induction_on generalizing use site s es vs with
  | h k ih =>
    have hSeen := List.mem_of_getLast? hLast
    obtain ⟨n, mid, after, u, post, hEs, hLength, hSuffix, hQuiet, hu, hWalk⟩ :=
      completeEmptyPacket hp site hs hw ⟨last, hSeen, hPub⟩
    rw [hEs]
    apply RecurringCursorTrace.packet hPlane hQuiet
    by_cases hEmpty : after = []
    · rw [hEmpty]
      exact .nil _
    have hLast' : after.getLast? = some last := by
      cases h : after.getLast? with
      | none => exact (hEmpty (List.getLast?_eq_none_iff.mp h)).elim
      | some seen =>
        rw [hEs] at hLast
        simpa [List.getLast?_cons, h] using hLast
    obtain ⟨j, t, pre, tail, next, hCut, hNext, ht, hNextPlane, hNo, hw'⟩ :=
      nextEmptyPacket site hu hWalk (fun v hv => hScope v (hSuffix.sublist.subset hv))
        ⟨last, List.mem_of_getLast? hLast', hPub⟩
    have hTail : last ∈ tail := by
      have h := List.mem_of_getLast? hLast'
      rw [hCut] at h
      exact (List.mem_append.mp h).resolve_left (fun hm => (hNo last hm).1 hPub)
    have hZ : tail ≠ [] := by rintro rfl; cases hTail
    have hLast'' : tail.getLast? = some last := by
      rwa [hCut, getLastAppendOfNonempty hZ] at hLast'
    rw [hCut]
    apply RecurringCursorTrace.gap hNo
    apply ih next.length (by have := hNext.length_le; omega) j (by omega) ht hw'
      (fun v hv => hScope v ((hNext.trans hSuffix).sublist.subset hv)) hLast'' rfl

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
