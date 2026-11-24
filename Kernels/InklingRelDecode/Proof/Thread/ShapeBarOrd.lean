-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DCompAll
public import Kernels.InklingRelDecode.Proof.Thread.WCompAll

@[expose] public section

/-!
# The ordinal of a thread's events on named barrier 0, as a measure of its abstract state

Named barrier 0 has three groups in turn (`bar.sync 0` of all 256 threads at the common start,
`bar.sync 0, 128` of the default partition, `bar.sync 0` of all threads at the end), so the
library's generation lemmas, which ask one group for the whole barrier, do not apply to it as it
stands. What the early generations need is a statement about the first events of a thread on the
barrier: the first two (source ordinals 0 and 1) are the `bar.sync 0` of the common start, and every
later barrier event of the thread comes after them.

`dLb` and `wLb` give, for a state of the default-partition machine and of the worker machine, a
lower bound for the number of barrier-0 events of the thread before the event of the state. It is
2 at every state but the sites of the common start, where it is exact: 0 before the first
`bar.sync 0` (the allocation sites included), 1 between the two. The increment `dInc`, `wInc` is
1 exactly at the two `bar.sync 0` sites. `dLb_next`, `wLb_next`: a successor's bound is the
state's plus its increment; a successor is a common-start state only from a common-start state.

The sites of the common start are the default partition's `DStart` sites `alloc`, `allocWr`, `bar0`,
`ld0`, `bar1` (and `relinq`, `shfl` after the second barrier), and the worker's `Worker.Site.bar0`,
`ld0`, `bar1`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.BarOrd
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-! ### The default partition -/

/-- The bound of a default-partition state. -/
def dLb : DComp.St → Nat
  | .dstart d =>
    match d.site with
    | .alloc | .allocWr | .bar0 => 0
    | .ld0 | .bar1 => 1
    | _ => 2
  | _ => 2

/-- The increment of a default-partition state: 1 at the two `bar.sync 0` of the common start. -/
def dInc : DComp.St → Nat
  | .dstart d =>
    match d.site with
    | .bar0 | .bar1 => 1
    | _ => 0
  | _ => 0

theorem dLb_of_ne {s : DComp.St} (h : ∀ d, s ≠ .dstart d) : dLb s = 2 := by
  cases s with
  | dstart d => exact absurd rfl (h d)
  | _ => rfl

theorem map_ne {α : Type} {f : α → DComp.St} (hf : ∀ a d, f a ≠ .dstart d)
    {x : Option (Option α)} {s' : DComp.St} (h : x.map (Option.map f) = some (some s')) :
    ∀ d, s' ≠ .dstart d := by
  cases x with
  | none => simp at h
  | some o =>
    cases o with
    | none => simp at h
    | some a =>
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact hf a

theorem pro_ne {L : Launch} {g : Nat} {Q : Params} {d : ProA.D} {e : Event} {s' : DComp.St}
    (h : DComp.next L g Q (.pro d) e = some (some s')) : ∀ d', s' ≠ .dstart d' := by
  simp only [DComp.next, DComp.proNext] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp
    · simp at h
  · exact map_ne (f := DComp.St.pro) (fun _ _ => by simp) h

theorem sm_ne {L : Launch} {g : Nat} {Q : Params} {d : Sm.D} {e : Event} {s' : DComp.St}
    (h : DComp.next L g Q (.sm d) e = some (some s')) : ∀ d', s' ≠ .dstart d' := by
  simp only [DComp.next, DComp.smNext] at h
  split at h
  · simp only [DComp.exitNext] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp
    · simp at h
  · exact map_ne (f := DComp.St.sm) (fun _ _ => by simp) h

theorem dLb_next {L : Launch} {g : Nat} {Q : Params} {s s' : DComp.St} {e : Event}
    (h : DComp.next L g Q s e = some (some s')) :
    dLb s' ≤ dLb s + dInc s ∧ (dLb s' < 2 → dLb s' = dLb s + dInc s ∧ dLb s < 2) := by
  cases s with
  | dstart d =>
    obtain ⟨site, tm⟩ := d
    cases site
    · by_cases hl : laneOf L g = 0 <;>
        simp [DComp.next, DComp.dstartNext, DStart.next, hl] at h <;> subst h <;>
        simp [dLb, dInc]
    · simp [DComp.next, DComp.dstartNext, DStart.next] at h
      subst h
      simp [dLb, dInc]
    · simp [DComp.next, DComp.dstartNext, DStart.next] at h
      subst h
      simp [dLb, dInc]
    · simp [DComp.next, DComp.dstartNext, DStart.next] at h
      obtain ⟨a, ha, rfl⟩ := h
      have hb : a.site = DStart.Site.bar1 := by
        repeat' split at ha
        all_goals first
          | (simp at ha; done)
          | (simp only [Option.some.injEq] at ha; subst ha; rfl)
      simp [hb, dLb, dInc]
    · by_cases hl : g % L.block < 32 <;>
        simp [DComp.next, DComp.dstartNext, DStart.next, hl] at h <;> subst h <;>
        simp [dLb, dInc]
    · simp [DComp.next, DComp.dstartNext, DStart.next] at h
      subst h
      simp [dLb, dInc]
    · simp [DComp.next, DComp.dstartNext, DStart.next] at h
      obtain ⟨a, ha, rfl⟩ := h
      have hb : a.site = DStart.Site.toProA := by
        repeat' split at ha
        all_goals first
          | (simp at ha; done)
          | (simp only [Option.some.injEq] at ha; subst ha; rfl)
      simp [hb, dLb, dInc]
    · simp [DComp.next, DComp.dstartNext, DStart.next] at h
  | pro d =>
    have hne := pro_ne h
    rw [dLb_of_ne hne]
    simp [dLb, dInc]
  | sm d =>
    have hne := sm_ne h
    rw [dLb_of_ne hne]
    simp [dLb, dInc]
  | epi d =>
    have hne := map_ne (f := DComp.St.epi) (fun _ _ => by simp) h
    rw [dLb_of_ne hne]
    simp [dLb, dInc]

/-! ### The worker threads -/

/-- The bound of a worker state. -/
def wLb : WComp.WSt → Nat
  | .worker w =>
    match w.site with
    | .bar0 => 0
    | .ld0 | .bar1 => 1
    | _ => 2
  | _ => 2

/-- The increment of a worker state: 1 at the two `bar.sync 0` of the common start. -/
def wInc : WComp.WSt → Nat
  | .worker w =>
    match w.site with
    | .bar0 | .bar1 => 1
    | _ => 0
  | _ => 0

/-- A worker state that is not a site of the common start. -/
def WNotStart (s : WComp.WSt) : Prop :=
  ∀ w, s = .worker w → w.site ≠ .bar0 ∧ w.site ≠ .ld0 ∧ w.site ≠ .bar1

theorem wLb_of_notStart {s : WComp.WSt} (h : WNotStart s) : wLb s = 2 := by
  cases s with
  | worker w =>
    obtain ⟨h0, h1, h2⟩ := h w rfl
    obtain ⟨site, P⟩ := w
    cases site <;> simp_all [wLb]
  | _ => rfl

theorem notStart_loop (P : Loader.Pro) : WNotStart (.worker ⟨.loop, P⟩) := by
  intro w hw
  cases hw
  simp

theorem wmap_notStart {α : Type} {f : α → WComp.WSt}
    (hf : ∀ a, WNotStart (f a)) {x : Option (Option α)} {s' : WComp.WSt}
    (h : x.map (Option.map f) = some (some s')) : WNotStart s' := by
  cases x with
  | none => simp at h
  | some o =>
    cases o with
    | none => simp at h
    | some a =>
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact hf a

theorem roleStart_notStart {L : Launch} {g : Nat} {P : Loader.Pro} {x : Worker.Site}
    {s' : WComp.WSt} (h : WComp.roleStart L g P x = some (some s')) : WNotStart s' := by
  intro w hw
  subst hw
  cases x <;> simp only [WComp.roleStart] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp at h; subst h; simp)

theorem wLb_next {L : Launch} {g : Nat} {s s' : WComp.WSt} {e : Event}
    (h : WComp.next L g s e = some (some s')) :
    wLb s' ≤ wLb s + wInc s ∧ (wLb s' < 2 → wLb s' = wLb s + wInc s ∧ wLb s < 2) := by
  cases s with
  | worker w =>
    obtain ⟨site, P⟩ := w
    cases site
    · simp [WComp.next, Worker.next] at h
      subst h
      simp [wLb, wInc]
    · simp [WComp.next, Worker.next] at h
      obtain ⟨a, ha, rfl⟩ := h
      have hb : a.site = Worker.Site.bar1 := by
        repeat' split at ha
        all_goals first
          | (simp at ha; done)
          | (simp only [Option.some.injEq] at ha; subst ha; rfl)
      simp [hb, wLb, wInc]
    · simp [WComp.next, Worker.next] at h
      subst h
      simp [wLb, wInc]
    · simp [WComp.next, Worker.next] at h
      obtain ⟨a, ha, rfl⟩ := h
      have hb : a.site = Worker.Site.loop := by
        repeat' split at ha
        all_goals first
          | (simp at ha; done)
          | (simp only [Option.some.injEq] at ha; subst ha; rfl)
      simp [hb, wLb, wInc]
    · simp [WComp.next, Worker.next] at h
      subst h
      simp [wLb, wInc]
    · simp [WComp.next, Worker.next] at h
      subst h
      simp [wLb, wInc]
    · simp only [WComp.next, WComp.dispatch] at h
      split at h
      · rename_i d' hd
        have := wLb_of_notStart (roleStart_notStart h)
        rw [this]
        simp [wLb, wInc]
      · simp at h
      · simp at h
    all_goals first
      | (simp [WComp.next, Worker.next] at h; done)
      | (simp [WComp.next, Worker.next] at h; subst h; simp [wLb, wInc])
  | idle d =>
    have hn : WNotStart s' := by
      simp only [WComp.next] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact notStart_loop _
      · exact wmap_notStart (f := WComp.WSt.idle) (fun _ _ hw => by cases hw) h
    rw [wLb_of_notStart hn]
    simp [wLb, wInc]
  | loader d P =>
    have hn : WNotStart s' := by
      simp only [WComp.next] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact notStart_loop _
      · exact wmap_notStart (f := fun d' => WComp.WSt.loader d' P) (fun _ _ hw => by cases hw) h
    rw [wLb_of_notStart hn]
    simp [wLb, wInc]
  | mma d P =>
    have hn : WNotStart s' := by
      simp only [WComp.next] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact notStart_loop _
      · exact wmap_notStart (f := fun d' => WComp.WSt.mma d' P) (fun _ _ hw => by cases hw) h
    rw [wLb_of_notStart hn]
    simp [wLb, wInc]
  | exit x =>
    have hn : WNotStart s' := by
      simp only [WComp.next] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        intro w hw
        cases hw
      · simp at h
    rw [wLb_of_notStart hn]
    simp [wLb, wInc]

/-! ### The first states -/

theorem dLb_init (L : Launch) (g : Nat) (Q : Params) : dLb (DComp.code L g Q).init = 0 := by
  show dLb (.dstart (DStart.D.start L g)) = 0
  unfold DStart.D.start
  split_ifs <;> rfl

theorem wLb_init (L : Launch) (g : Nat) (Q : Params) : wLb (WComp.code L g Q).init = 0 := rfl

end
end PTX.Kernels.InklingRelDecode.Proof.BarOrd
