-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Trace
public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Final
public import Kernels.FlashKdaFwd.Proof.Protocol.Layout
public import Lemmas.Async.BulkCommitted
public import Lemmas.Step.ExitLast
public import Lemmas.Kernel.Progress.Warp

@[expose] public section

/-! # Epilogue phase: facts about the events of a thread in the epilogue

Everything here is about one launched thread `g` of a consistent execution that **entered the
epilogue before its event `k0`** (`Entered P L X g k0`: a followed state with the entry
condition `In` there) and about its events at the positions `k ≥ k0`. The contracts of the
other layers quantify over all events of an execution; the assembly finds the phase of an event
and uses the facts of this file for the events of the epilogue.

* `event_in`: the machine is at a state before the event, the state has the invariant, and the
  event is the exact event of its position (`EvX`).
* By kind of event (each with the number of earlier `bar.sync 0`, `Protocol.bar0Before`):
  - `wr_in`: a write event is store `j` of a compute thread: four bytes at `stAddr` of the
    block's window, the bytes of the carry register `stSrc j` as a 32-bit store writes them,
    seven barriers before it, at event `k0 + 1 + j`;
  - `ts_in`: a tensor store is the `i`-th final-state store of the store leader (`finalSpec`),
    eight barriers before it, at event `k0 + 3 + i`;
  - `bar_in`: a barrier event is `bar.sync 0` at the instruction of its ordinal (3113, 3775,
    3834 with 6, 7, 8 earlier ones), and the second one directly follows the proxy fence;
  - `exit_in`: the exit is at instruction 3835 after nine barriers;
  - `ub_in`: an undefined-behaviour event is the event of a store whose carry register holds a
    value that a 32-bit store cannot write (the only data condition of the phase);
  - `kind_in`: an event is of one of these kinds, a proxy fence, a group commit or a group
    wait.
* History, from the invariant's trail: `stores_done` (at the second barrier a compute thread
  has made its 128 writes, each with seven barriers before it), `stores_issued` (at its exit
  the store leader has issued the sixteen final-state stores), `waits_for` (between a
  final-state store and a later barrier or exit of the leader there is the group wait that
  covers it).
* Counts: `count_in` (a class of events that the epilogue does not make has the same count at
  `k` as at `k0`), `count_exit` (and over the whole trace when the thread exits), `bars_le`
  (at most nine `bar.sync 0`), with the instances `quiet_*` of the classes the contracts count.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (bar0Before bar0Pcs)

noncomputable section
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat} {e : Event}

/-- **Thread `g` entered the epilogue before its event `k0`**: its machine is at a followed
state there that satisfies the entry condition. -/
def Entered (P : Params) (L : Launch) (X : Execution) (g k0 : Nat) : Prop :=
  ∃ s0, Frame.stateAt (code L) X g k0 = some (some s0) ∧ In P X g k0 s0

/-! ### The program counters of the positions -/

theorem st_pc : ∀ j : Fin 128, (Pos.st j).site.pc = 3132 + 5 * j.val := by decide +kernel
theorem ts_pc : ∀ i : Fin 16, (Pos.ts i).site.pc = 3786 + 3 * i.val := by decide +kernel

/-! ### Classes of events the epilogue does not make -/

theorem quiet_isBarId {id : Nat} (h : id ≠ 0) : Quiet P L g (Execution.isBarId id) := by
  intro pos e he
  cases pos with
  | st j => obtain ⟨bs, rfl⟩ := he; rfl
  | _ =>
    simp only [Ev] at he
    subst he
    first | rfl | (simp [Execution.isBarId]; omega)

theorem quiet_isMatrix : Quiet P L g isMatrix := by
  intro pos e he
  cases pos with
  | st j => obtain ⟨bs, rfl⟩ := he; rfl
  | _ => simp only [Ev] at he; subst he; rfl

theorem quiet_okPoll (m : Loc) : Quiet P L g (okPoll m) := by
  intro pos e he
  cases pos with
  | st j => obtain ⟨bs, rfl⟩ := he; rfl
  | _ => simp only [Ev] at he; subst he; rfl

theorem quiet_arrivesOn (m : Loc) : Quiet P L g (arrivesOn m) := by
  intro pos e he
  cases pos with
  | st j => obtain ⟨bs, rfl⟩ := he; rfl
  | _ => simp only [Ev] at he; subst he; rfl

theorem quiet_issuesTo (m : Loc) : Quiet P L g (issuesTo m) := by
  intro pos e he
  cases pos with
  | st j => obtain ⟨bs, rfl⟩ := he; rfl
  | _ => simp only [Ev] at he; subst he; rfl

theorem quiet_isWarpColl : Quiet P L g Sched.isWarpColl := by
  intro pos e he
  cases pos with
  | st j => obtain ⟨bs, rfl⟩ := he; rfl
  | _ => simp only [Ev] at he; subst he; rfl

theorem quiet_isShfl : Quiet P L g Execution.isShfl := by
  intro pos e he
  cases pos with
  | st j => obtain ⟨bs, rfl⟩ := he; rfl
  | _ => simp only [Ev] at he; subst he; rfl

/-- The barrier events of other barriers than barrier 0. -/
def isOtherBar (e : Event) : Bool := Execution.isBar e && !Execution.isBarId 0 e

theorem quiet_isOtherBar : Quiet P L g isOtherBar := by
  intro pos e he
  cases pos with
  | st j => obtain ⟨bs, rfl⟩ := he; rfl
  | _ => simp only [Ev] at he; subst he; rfl

/-- The barrier events of a list are its `bar.sync 0` and those of the other barriers. -/
theorem countP_isBar (es : List Event) :
    es.countP Execution.isBar = es.countP (Execution.isBarId 0) + es.countP isOtherBar := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons, ih]
    have key : (if Execution.isBar e = true then 1 else 0) =
        (if Execution.isBarId 0 e = true then 1 else 0) +
          (if isOtherBar e = true then 1 else 0) := by
      obtain ⟨pc, k⟩ := e
      cases k with
      | bar id cnt mode =>
        by_cases h : id = 0 <;> simp [Execution.isBarId, Execution.isBar, isOtherBar, h]
      | _ => rfl
    omega

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads) {k0 : Nat} (hE : Entered P L X g k0)
include hpre hX hg hE

/-! ### The event at a position -/

/-- **An event of a thread in the epilogue**: the state before it, the invariant, the position
and the exact event. -/
theorem event_in {k : Nat} (hk : k0 ≤ k) (he : X.get (g, k) = some e) :
    ∃ s pos, Frame.stateAt (code L) X g k = some (some s) ∧ Inv P L X g k0 k s ∧
      RefAt P g pos s ∧ OnPath g pos ∧ k = k0 + ord g pos ∧
      bar0Before X (g, k) = bars pos ∧ Trail P L X g k0 pos ∧ EvX P L g pos s.x e := by
  obtain ⟨s0, h0, hin⟩ := hE
  obtain ⟨s, hσ, hI⟩ := epilogue_all hpre hX hg h0 hin hk (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨pos, h1, h2, h3, h4, h5, h6⟩ := event_at hpre hX hg he hσ hI
  exact ⟨s, pos, hσ, hI, h1, h2, h3, h4, h5, h6⟩

/-- **A write event in the epilogue** is store `j` of a compute thread. -/
theorem wr_in {k pc : Nat} {a : Acc} {bs : List Byte} (hk : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) :
    ∃ s, ∃ j : Fin 128, Frame.stateAt (code L) X g k = some (some s) ∧
      s.site = (Pos.st j).site ∧ tid g < 128 ∧ k = k0 + 1 + j.val ∧ pc = 3132 + 5 * j.val ∧
      a = stAcc P L g j.val ∧ (∃ v, storeValue 32 (s.x (stSrc j.val)) = .ok v ∧ bs = v.toBytes) ∧
      bar0Before X (g, k) = 7 := by
  obtain ⟨s, pos, hσ, -, hr, hon, hkp, hb, -, hex⟩ := event_in hpre hX hg hE hk he
  cases pos with
  | st j =>
    rcases hex with ⟨v, hv, h⟩ | ⟨f, -, h⟩
    · cases h
      exact ⟨s, j, hσ, hr.site, hon, by rw [hkp]; simp only [ord]; omega, st_pc j, rfl,
        ⟨v, hv, rfl⟩, hb⟩
    · cases h
  | _ => simp only [EvX, Ev] at hex; cases hex

/-- **A tensor store in the epilogue** is the `i`-th final-state store of the store leader. -/
theorem ts_in {k pc al : Nat} {sp : TensorStore.Spec} (hk : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩) :
    ∃ i : Fin 16, tid g = 160 ∧ k = k0 + 3 + i.val ∧ pc = 3786 + 3 * i.val ∧
      al = P.objectBase 9 ∧ sp = finalSpec P L g i.val ∧ bar0Before X (g, k) = 8 := by
  obtain ⟨s, pos, hσ, -, hr, hon, hkp, hb, -, hex⟩ := event_in hpre hX hg hE hk he
  cases pos with
  | st j => rcases hex with ⟨v, -, h⟩ | ⟨f, -, h⟩ <;> cases h
  | ts i =>
    simp only [EvX, Ev] at hex
    cases hex
    exact ⟨i, hon, by rw [hkp]; simp only [ord]; omega, ts_pc i, rfl, rfl, hb⟩
  | _ => simp only [EvX, Ev] at hex; cases hex

/-- **A barrier event in the epilogue** is a `bar.sync 0` at the instruction of its ordinal,
and the second one (seven earlier barriers) directly follows the proxy fence. -/
theorem bar_in {k pc id : Nat} {cnt : Option Nat} {mode : BarMode} (hk : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) :
    id = 0 ∧ cnt = none ∧ mode = .sync ∧ bar0Pcs[bar0Before X (g, k)]? = some pc ∧
      6 ≤ bar0Before X (g, k) ∧ bar0Before X (g, k) ≤ 8 ∧
      (bar0Before X (g, k) = 7 → 0 < k ∧
        X.get (g, k - 1) = some ⟨3774, .fenceProxy (.async (some (.shared .cta))) none⟩) := by
  obtain ⟨s, pos, hσ, -, hr, hon, hkp, hb, htr, hex⟩ := event_in hpre hX hg hE hk he
  cases pos with
  | st j => rcases hex with ⟨v, -, h⟩ | ⟨f, -, h⟩ <;> cases h
  | bar7 =>
    simp only [EvX, Ev] at hex
    cases hex
    rw [hb]
    exact ⟨rfl, rfl, rfl, rfl, by decide, by decide, fun h => by cases h⟩
  | bar8 =>
    simp only [EvX, Ev] at hex
    cases hex
    rw [hb]
    refine ⟨rfl, rfl, rfl, rfl, by decide, by decide, fun _ => ?_⟩
    obtain ⟨e', he', hev, -⟩ := htr .fence trivial (by simp only [ord]; split <;> omega)
    simp only [Ev] at hev
    subst hev
    have hord : k0 + ord g .fence = k - 1 := by
      rw [hkp]
      simp only [ord]
      split <;> omega
    rw [hord] at he'
    exact ⟨by rw [hkp]; simp only [ord]; split <;> omega, he'⟩
  | bar9 =>
    simp only [EvX, Ev] at hex
    cases hex
    rw [hb]
    exact ⟨rfl, rfl, rfl, rfl, by decide, by decide, fun h => by cases h⟩
  | _ => simp only [EvX, Ev] at hex; cases hex

/-- **The exit of a thread in the epilogue** is at instruction 3835, after nine barriers. -/
theorem exit_in {k pc : Nat} (hk : k0 ≤ k) (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    ∃ s, Frame.stateAt (code L) X g k = some (some s) ∧ Inv P L X g k0 k s ∧
      s.site = .exit 0 ∧ pc = 3835 ∧ k = k0 + ord g .exit ∧ bar0Before X (g, k) = 9 ∧
      Trail P L X g k0 .exit := by
  obtain ⟨s, pos, hσ, hI, hr, hon, hkp, hb, htr, hex⟩ := event_in hpre hX hg hE hk he
  cases pos with
  | st j => rcases hex with ⟨v, -, h⟩ | ⟨f, -, h⟩ <;> cases h
  | exit =>
    simp only [EvX, Ev] at hex
    cases hex
    exact ⟨s, hσ, hI, hr.site, rfl, hkp, hb, htr⟩
  | _ => simp only [EvX, Ev] at hex; cases hex

/-- **An undefined-behaviour event in the epilogue** is the event of a store of a compute
thread whose carry register holds a value that a 32-bit store cannot write, with the fault of
that conversion. There is no other undefined behaviour in the phase. -/
theorem ub_in {k pc : Nat} {f : Fault} (hk : k0 ≤ k) (he : X.get (g, k) = some ⟨pc, .ub f⟩) :
    ∃ s, ∃ j : Fin 128, Frame.stateAt (code L) X g k = some (some s) ∧
      s.site = (Pos.st j).site ∧ tid g < 128 ∧
      storeValue 32 (s.x (stSrc j.val)) = .error f := by
  obtain ⟨s, pos, hσ, -, hr, hon, -, -, -, hex⟩ := event_in hpre hX hg hE hk he
  cases pos with
  | st j =>
    rcases hex with ⟨v, -, h⟩ | ⟨f', hf, h⟩
    · cases h
    · cases h
      exact ⟨s, j, hσ, hr.site, hon, hf⟩
  | _ => simp only [EvX, Ev] at hex; cases hex

/-- **The kinds of event of the epilogue.** -/
theorem kind_in {k : Nat} (hk : k0 ≤ k) (he : X.get (g, k) = some e) :
    (∃ f, e.kind = .ub f) ∨ (∃ a bs, e.kind = .wr a bs) ∨ e.kind = .bar 0 none .sync ∨
      e.kind = .fenceProxy (.async (some (.shared .cta))) none ∨
      (∃ al sp, e.kind = .tensorStore al sp) ∨ e.kind = .bulkCommit ∨
      e.kind = .bulkWait .read 0 ∨ e.kind = .exit := by
  obtain ⟨s, pos, -, -, -, -, -, -, -, hex⟩ := event_in hpre hX hg hE hk he
  cases pos with
  | st j =>
    rcases hex with ⟨v, -, rfl⟩ | ⟨f, -, rfl⟩
    · exact .inr (.inl ⟨_, _, rfl⟩)
    · exact .inl ⟨f, rfl⟩
  | ts i =>
    simp only [EvX, Ev] at hex
    subst hex
    exact .inr (.inr (.inr (.inr (.inl ⟨_, _, rfl⟩))))
  | bar7 => simp only [EvX, Ev] at hex; subst hex; exact .inr (.inr (.inl rfl))
  | bar8 => simp only [EvX, Ev] at hex; subst hex; exact .inr (.inr (.inl rfl))
  | bar9 => simp only [EvX, Ev] at hex; subst hex; exact .inr (.inr (.inl rfl))
  | fence => simp only [EvX, Ev] at hex; subst hex; exact .inr (.inr (.inr (.inl rfl)))
  | commit =>
    simp only [EvX, Ev] at hex
    subst hex
    exact .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
  | bwait =>
    simp only [EvX, Ev] at hex
    subst hex
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  | exit =>
    simp only [EvX, Ev] at hex
    subst hex
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))

/-! ### History -/

/-- **At the second barrier a compute thread has made its 128 stores**: when the event `k` is a
`bar.sync 0` with seven earlier ones, store `j` was event `k0 + 1 + j`, before `k`, with seven
barriers before it. -/
theorem stores_done {k pc : Nat} {cnt : Option Nat} {mode : BarMode} (hk : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .bar 0 cnt mode⟩) (hb : bar0Before X (g, k) = 7)
    (ht : tid g < 128) (j : Fin 128) :
    k0 + 1 + j.val < k ∧ bar0Before X (g, k0 + 1 + j.val) = 7 ∧
      ∃ bs, X.get (g, k0 + 1 + j.val) = some ⟨3132 + 5 * j.val, .wr (stAcc P L g j.val) bs⟩ := by
  obtain ⟨s, pos, hσ, -, hr, hon, hkp, hb', htr, hex⟩ := event_in hpre hX hg hE hk he
  have hpos : pos = .bar8 := by
    cases pos with
    | st j => rcases hex with ⟨v, -, h⟩ | ⟨f, -, h⟩ <;> cases h
    | bar8 => rfl
    | bar7 => rw [hb'] at hb; cases hb
    | bar9 => rw [hb'] at hb; cases hb
    | _ => simp only [EvX, Ev] at hex; cases hex
  subst hpos
  have hj := j.isLt
  obtain ⟨e', he', hev, hbj⟩ := htr (.st j) ht (by simp only [ord, ite_eq_left ht]; omega)
  obtain ⟨bs, rfl⟩ := hev
  simp only [ord] at he' hbj
  rw [Nat.add_assoc] at *
  refine ⟨by rw [hkp]; simp only [ord, ite_eq_left ht]; omega, hbj, bs, ?_⟩
  rw [he', st_pc j]

/-- **At its exit the store leader has issued the sixteen final-state stores**: store `i` was
event `k0 + 3 + i`. -/
theorem stores_issued {k pc : Nat} (hk : k0 ≤ k) (he : X.get (g, k) = some ⟨pc, .exit⟩)
    (ht : tid g = 160) (i : Fin 16) :
    k0 + 3 + i.val < k ∧ X.get (g, k0 + 3 + i.val) =
      some ⟨3786 + 3 * i.val, .tensorStore (P.objectBase 9) (finalSpec P L g i.val)⟩ := by
  obtain ⟨s, hσ, hI, hsite, rfl, hkp, hb, htr⟩ := exit_in hpre hX hg hE hk he
  have hi := i.isLt
  have h1 : ¬ tid g < 128 := by omega
  obtain ⟨e', he', hev, -⟩ := htr (.ts i) ht
    (by simp only [ord, ite_eq_right h1, ite_eq_left ht]; omega)
  simp only [Ev] at hev
  subst hev
  simp only [ord] at he'
  rw [Nat.add_assoc] at *
  refine ⟨by rw [hkp]; simp only [ord, ite_eq_right h1, ite_eq_left ht]; omega, ?_⟩
  rw [he', ts_pc i]

/-- **The group wait covers the final-state stores**: between a tensor store of the epilogue
and a later barrier or exit of the thread there is a `.read` group wait that covers the
store. -/
theorem waits_for {k k' pc al : Nat} {sp : TensorStore.Spec} {e' : Event} (hk : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩) (hkk : k < k')
    (he' : X.get (g, k') = some e')
    (hkind : (∃ id cnt mode, e'.kind = .bar id cnt mode) ∨ e'.kind = .exit) :
    ∃ w, k < w ∧ w < k' ∧ BulkWaitsFor X .read (g, k) (g, w) := by
  obtain ⟨i, ht, hki, -, -, -, -⟩ := ts_in hpre hX hg hE hk he
  have hi := i.isLt
  have h1 : ¬ tid g < 128 := by omega
  obtain ⟨s', pos', hσ', -, hr', hon', hkp', hb', htr', hex'⟩ :=
    event_in hpre hX hg hE (by omega) he'
  -- the later event is at the third barrier or at the exit, so the commit and the wait are
  -- in its history
  have hord : 21 ≤ ord g pos' := by
    cases pos' with
    | st j => exact absurd (show tid g < 128 from hon') h1
    | ts i' =>
      simp only [EvX, Ev] at hex'
      subst hex'
      rcases hkind with ⟨_, _, _, h⟩ | h <;> cases h
    | fence =>
      simp only [EvX, Ev] at hex'
      subst hex'
      rcases hkind with ⟨_, _, _, h⟩ | h <;> cases h
    | commit =>
      simp only [EvX, Ev] at hex'
      subst hex'
      rcases hkind with ⟨_, _, _, h⟩ | h <;> cases h
    | bwait =>
      simp only [EvX, Ev] at hex'
      subst hex'
      rcases hkind with ⟨_, _, _, h⟩ | h <;> cases h
    | bar7 => simp only [ord] at hkp'; omega
    | bar8 => simp only [ord, ite_eq_right h1] at hkp'; omega
    | bar9 => simp only [ord, ite_eq_right h1, ite_eq_left ht]; omega
    | exit => simp only [ord, ite_eq_right h1, ite_eq_left ht]; omega
  obtain ⟨ec, hec, hevc, -⟩ := htr' .commit ht (show 19 < ord g pos' by omega)
  obtain ⟨ew, hew, hevw, -⟩ := htr' .bwait ht (show 20 < ord g pos' by omega)
  simp only [Ev] at hevc hevw
  subst hevc hevw
  simp only [ord] at hec hew
  exact ⟨k0 + 20, by omega, by omega,
    bulkWaitsFor_of_commit he hec hew (by omega) (by omega)⟩

/-! ### Counts -/

/-- **A class of events that the epilogue does not make** has the same count before an event
of the epilogue as at the entry. -/
theorem count_in {k : Nat} (hk : k0 ≤ k) (hlt : k < (X.tr g).length) {c : Event → Bool}
    (hc : Quiet P L g c) : ((X.tr g).take k).countP c = ((X.tr g).take k0).countP c := by
  obtain ⟨s0, h0, hin⟩ := hE
  obtain ⟨s, hσ, pos, -, -, -, -, -, hq⟩ := epilogue_all hpre hX hg h0 hin hk hlt
  exact hq c hc

/-- **And over the whole trace of a thread that exits.** -/
theorem count_exit {k pc : Nat} (hk : k0 ≤ k) (he : X.get (g, k) = some ⟨pc, .exit⟩)
    {c : Event → Bool} (hc : Quiet P L g c) :
    (X.tr g).countP c = ((X.tr g).take k0).countP c := by
  have hlast := Execution.exit_last hX hg he
  obtain ⟨s, hσ, hI, hsite, rfl, hkp, hb, htr⟩ := exit_in hpre hX hg hE hk he
  have h1 := count_in hpre hX hg hE hk (by omega) hc
  have h2 := count_snoc c he
  rw [hlast, List.take_length, h1, hc .exit ⟨3835, .exit⟩ rfl] at h2
  simpa using h2

/-- **A thread that exits has made nine `bar.sync 0`.** -/
theorem bars_exit {k pc : Nat} (hk : k0 ≤ k) (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    (X.tr g).countP (Execution.isBarId 0) = 9 := by
  have hlast := Execution.exit_last hX hg he
  obtain ⟨s, hσ, hI, hsite, rfl, hkp, hb, htr⟩ := exit_in hpre hX hg hE hk he
  have h2 := count_snoc (Execution.isBarId 0) he
  rw [hlast, List.take_length] at h2
  rw [h2]
  exact hb

/-- **A thread in the epilogue makes at most nine `bar.sync 0`.** -/
theorem bars_le : (X.tr g).countP (Execution.isBarId 0) ≤ 9 := by
  obtain ⟨s0, h0, hin⟩ := id hE
  rcases Nat.lt_or_ge k0 (X.tr g).length with hlt | hge
  · -- the last event of the thread is an event of the epilogue
    obtain ⟨n, hn⟩ : ∃ n, (X.tr g).length = n + 1 := ⟨(X.tr g).length - 1, by omega⟩
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[n]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨s, pos, hσ, -, hr, hon, hkp, hb, htr, hex⟩ :=
      event_in hpre hX hg hE (k := n) (by omega) he
    have h2 := count_snoc (Execution.isBarId 0) he
    rw [← hn, List.take_length] at h2
    rw [h2, evx_isBar hex]
    have hb' : ((X.tr g).take n).countP (Execution.isBarId 0) = bars pos := hb
    rw [hb']
    cases pos <;> simp [bars, Pos.isBar]
  · rw [← List.take_of_length_le hge, hin.2]
    decide

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
