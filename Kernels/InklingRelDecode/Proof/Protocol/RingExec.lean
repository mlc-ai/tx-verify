-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.RingLoader
public import Kernels.InklingRelDecode.Proof.Protocol.RingMma
public import Lemmas.Kernel.Frame

@[expose] public section

/-!
# The ring's polls on an execution

The run theorems of `RingLoader` and `RingMma` speak about a run of the machine from a state. Here
they are read on an execution `X` of the kernel: the worker thread `g` is followed by
`WComp.code L g Q`, `wAt Q L X g k` is its abstract state before its `k`-th event (it is
`Frame.stateAt (fun g => WComp.code L g Q) X g k`, `wAt_eq`), and the thread's events are a run of
the machine from its first state (`trace_of`).

* `loader_poll_exec`: a successful poll of `kv_empty s` by the loader, at event `k`, with the
  loader's loop running from an anchor event `k₀` to `k` (the loader's states between are in the
  loop), and no earlier event of the thread polling `kv_empty s` successfully before `k₀`:
  the thread's state at `k` is the `wait` site of an iteration `i` of slot `s`, the parity of the
  poll is `1 - (i / 3) % 2`, block `i` is the loader's `n`-th block of the slot, where `n` is the
  number of the thread's earlier successful polls of `kv_empty s`, and the parity is
  `(n + δ) % 2`, `δ = 0` if `s < np` and `1` otherwise (`np = Ld.polled d₀ ≤ 3` the preloaded
  blocks). This is the parity field of the ring's thread-layer facts (`FBar.poll` of FA4).
* `mma_poll_exec`: the same for the MMA warp's successful polls of `kv_ready s`, from an anchor
  at the start of the loop: block `i` is the warp's `n`-th block of the slot and the parity is
  `n % 2`.

Two facts are premises here and are the role-table protocol (obligation 6): that the thread's
loop (resp. MMA role) is one run from the anchor to the event (`hin`: the role is entered once and
not left), and that no earlier event polled the barrier (`hfresh`); they are derived from the shapes
of the worker's own events (none is a poll of a ring barrier) and from the role table having
one byte per warp.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvEmpty kvReady MapReg)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {X : Execution}

/-- The abstract state of worker thread `g` before its `k`-th event. -/
abbrev wAt (Q : Params) (L : Launch) (X : Execution) (g k : Nat) :
    Option (Option WComp.WSt) :=
  (WComp.code L g Q).toMachine.after (some (WComp.code L g Q).init) ((X.tr g).take k)

/-- **The events of a worker thread are a run of its machine.** -/
theorem trace_of (hpre : Pre Q L mem0) (hw : 4 ≤ WComp.warpOf L g) (hg : g < L.threads)
    (hX : Consistent L kernel WComp.asms mem0 X) :
    (WComp.code L g Q).toMachine.Trace (some (WComp.code L g Q).init) (X.tr g) :=
  (WComp.machine_sound hpre hw).produces (hX.thr g hg)

/-- The state after the first `n` events is the state after the first `k₀`, then the events up to
`n`. -/
theorem after_split (σ0 : Option WComp.WSt) (l : List Event) {k0 n : Nat} (h : k0 ≤ n) :
    (WComp.code L g Q).toMachine.after σ0 (l.take n) =
      ((WComp.code L g Q).toMachine.after σ0 (l.take k0)).bind fun σ =>
        (WComp.code L g Q).toMachine.after σ ((l.drop k0).take (n - k0)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, Machine.after_append (WComp.code L g Q).toMachine σ0, Nat.add_sub_cancel_left]

/-- A prefix of the run from an anchor. -/
theorem run_from (hpre : Pre Q L mem0) (hw : 4 ≤ WComp.warpOf L g) (hg : g < L.threads)
    (hX : Consistent L kernel WComp.asms mem0 X) {k0 : Nat} (k : Nat) {σ0 : Option WComp.WSt}
    (h0 : wAt Q L X g k0 = some σ0) :
    (WComp.code L g Q).toMachine.Trace σ0 (((X.tr g).drop k0).take (k - k0)) :=
  trace_take (trace_drop (trace_of hpre hw hg hX) h0) _

/-- **The states of an anchored run.** If the thread is at `σ0` before its event `k₀` and at `σ`
before its event `k ≥ k₀`, then the events from `k₀` to `k` lead from `σ0` to `σ`; and the states
`σ_j` before them are those the run passes through. -/
theorem run_states {k0 k : Nat} (hk : k0 ≤ k) {σ0 σ : Option WComp.WSt}
    (h0 : wAt Q L X g k0 = some σ0) (hσ : wAt Q L X g k = some σ) :
    (WComp.code L g Q).toMachine.after σ0 (((X.tr g).drop k0).take (k - k0)) = some σ ∧
      ∀ j, j < k - k0 → (WComp.code L g Q).toMachine.after σ0
        ((((X.tr g).drop k0).take (k - k0)).take j) = wAt Q L X g (k0 + j) := by
  simp only [wAt] at h0 hσ ⊢
  constructor
  · have := after_split (Q := Q) (L := L) (g := g) (some (WComp.code L g Q).init) (X.tr g) hk
    rw [hσ, h0] at this
    exact this.symm
  · intro j hj
    have := after_split (Q := Q) (L := L) (g := g) (some (WComp.code L g Q).init) (X.tr g)
      (Nat.le_add_right k0 j)
    rw [h0, Nat.add_sub_cancel_left] at this
    rw [List.take_take, Nat.min_eq_left (by omega)]
    exact this.symm.trans (by rfl)

/-- The event at an anchored state fires with a continuation unless it ends the thread. -/
theorem fired_some {k : Nat} {σ : Option WComp.WSt} {e : Event}
    (hT : (WComp.code L g Q).toMachine.Trace (some (WComp.code L g Q).init) (X.tr g))
    (he : (X.tr g)[k]? = some e) (hσ : wAt Q L X g k = some σ) (hne : ¬ Ends e) :
    ∃ u, (WComp.code L g Q).toMachine.Fired σ e (some u) := by
  obtain ⟨o, hF⟩ := hT.fired_at he hσ
  cases o with
  | none =>
    obtain ⟨t, -, hfire⟩ := hF
    exact absurd (fires_none_ends hfire) hne
  | some u => exact ⟨u, hF⟩

variable (hpre : Pre Q L mem0) (hw : 4 ≤ WComp.warpOf L g) (hg : g < L.threads)
include hpre hw hg

/-- **The loader's successful poll of `kv_empty s`, on an execution.** -/
theorem loader_poll_exec (hX : Consistent L kernel WComp.asms mem0 X) {k0 k : Nat} (hk : k0 ≤ k)
    {d0 d : Loader.D} {P : Loader.Pro} (h0 : wAt Q L X g k0 = some (some (.loader d0 P)))
    (hd : wAt Q L X g k = some (some (.loader d P))) (hrg : Loader.Rng d)
    (hin : ∀ j, k0 ≤ j → j < k → ∃ d', wAt Q L X g j = some (some (.loader d' P)) ∧
      Ld.InLoop d' ∧ d'.site ≠ .setMaxInc) (hnp : Ld.polled d0 ≤ 3) {s : Nat}
    (hfresh : okPolls (kvEmpty L (g / L.block) s) ((X.tr g).take k0) = 0) {pc p : Nat} {acq : Bool}
    {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait (kvEmpty L (g / L.block) s) p true acq sc⟩) :
    d.site = .wait ∧ d.i % 3 = s ∧ p = emptyParity d.i ∧
      d.i = loaderBlock (Ld.polled d0) s
        (okPolls (kvEmpty L (g / L.block) s) ((X.tr g).take k)) ∧
      p % 2 = (okPolls (kvEmpty L (g / L.block) s) ((X.tr g).take k) +
        if s < Ld.polled d0 then 0 else 1) % 2 := by
  have hT := trace_of hpre hw hg hX
  have hne : ¬ Ends (⟨pc, .wait (kvEmpty L (g / L.block) s) p true acq sc⟩ : Event) := by
    rintro (⟨f, h⟩ | h) <;> simp only at h <;> cases h
  obtain ⟨u, hF⟩ := fired_some hT he hd hne
  have hmap : MapReg P := EvW.after_mapReg hd
  have hok := ld_okPoll hpre hmap hrg hF s
  rw [okPoll_wait rfl] at hok
  simp only [Bool.true_and, decide_true] at hok
  have hsite : d.site = .wait ∧ d.i % 3 = s := by
    have := hok.symm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  obtain ⟨hsw, hs3⟩ := hsite
  have hrun := run_from hpre hw hg hX k h0
  obtain ⟨hend, hmid⟩ := run_states hk h0 hd
  have hin' : ∀ j < (((X.tr g).drop k0).take (k - k0)).length, ∃ d',
      (WComp.code L g Q).toMachine.after (some (.loader d0 P))
        ((((X.tr g).drop k0).take (k - k0)).take j) = some (some (.loader d' P)) ∧
      Ld.InLoop d' ∧ d'.site ≠ .setMaxInc := by
    intro j hj
    have hj' : j < k - k0 := lt_of_lt_of_le hj (List.length_take_le _ _)
    obtain ⟨d', h1, h2, h3⟩ := hin (k0 + j) (by omega) (by omega)
    exact ⟨d', (hmid j hj').trans h1, h2, h3⟩
  obtain ⟨ok, heq, hblk, hpar⟩ := loader_wait hpre hmap hrun hin' hend hrg hnp hsw hF
  have hp : p = emptyParity d.i := by
    simp only [Event.mk.injEq, Kind.wait.injEq] at heq
    exact heq.2.2.1
  have hcount : okPolls (kvEmpty L (g / L.block) s) ((X.tr g).take k) =
      okPolls (kvEmpty L (g / L.block) s) ((X.tr g).take k0) +
        okPolls (kvEmpty L (g / L.block) s) ((((X.tr g).drop k0).take (k - k0))) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [List.take_add, okPolls, List.countP_append, Nat.add_sub_cancel_left]
    rfl
  rw [hs3] at hblk hpar
  refine ⟨hsw, hs3, hp, ?_, ?_⟩
  · rw [hcount, hfresh, Nat.zero_add]
    exact hblk
  · rw [hcount, hfresh, Nat.zero_add, hp]
    exact hpar

/-- **The MMA warp's successful poll of `kv_ready s`, on an execution.** -/
theorem mma_poll_exec (hX : Consistent L kernel WComp.asms mem0 X) {k0 k : Nat} (hk : k0 ≤ k)
    {d0 d : Mma.D} {P : Loader.Pro} (h0 : wAt Q L X g k0 = some (some (.mma d0 P)))
    (hd : wAt Q L X g k = some (some (.mma d P)))
    (hin : ∀ j, k0 ≤ j → j < k → ∃ d', wAt Q L X g j = some (some (.mma d' P)) ∧
      Mma.Inv d' ∧ d'.site ≠ .setMaxRegInc) (h0p : Mm.polled d0 = 0) {s : Nat} (hs : s < 3)
    (hfresh : okPolls (kvReady L (g / L.block) s) ((X.tr g).take k0) = 0) {pc p : Nat} {acq : Bool}
    {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait (kvReady L (g / L.block) s) p true acq sc⟩) :
    d.site = .kvWait ∧ d.i % 3 = s ∧ p = readyParity d.i ∧
      d.i = blockOf s (okPolls (kvReady L (g / L.block) s) ((X.tr g).take k)) ∧
      p % 2 = okPolls (kvReady L (g / L.block) s) ((X.tr g).take k) % 2 := by
  have hT := trace_of hpre hw hg hX
  have hne : ¬ Ends (⟨pc, .wait (kvReady L (g / L.block) s) p true acq sc⟩ : Event) := by
    rintro (⟨f, h⟩ | h) <;> simp only at h <;> cases h
  obtain ⟨u, hF⟩ := fired_some hT he hd hne
  have hok := mm_okPoll hpre hg hF hs
  rw [okPoll_wait rfl] at hok
  simp only [Bool.true_and, decide_true] at hok
  have hsite : d.site = .kvWait ∧ d.i % 3 = s := by
    have := hok.symm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  obtain ⟨hsw, hs3⟩ := hsite
  have hrun := run_from hpre hw hg hX k h0
  obtain ⟨hend, hmid⟩ := run_states hk h0 hd
  have hin' : ∀ j < (((X.tr g).drop k0).take (k - k0)).length, ∃ d',
      (WComp.code L g Q).toMachine.after (some (.mma d0 P))
        ((((X.tr g).drop k0).take (k - k0)).take j) = some (some (.mma d' P)) ∧
      Mma.Inv d' ∧ d'.site ≠ .setMaxRegInc := by
    intro j hj
    have hj' : j < k - k0 := lt_of_lt_of_le hj (List.length_take_le _ _)
    obtain ⟨d', h1, h2, h3⟩ := hin (k0 + j) (by omega) (by omega)
    exact ⟨d', (hmid j hj').trans h1, h2, h3⟩
  obtain ⟨ok, heq, hblk, hpar⟩ := mma_wait hpre hg hrun hin' hend h0p hsw hF
  have hp : p = readyParity d.i := by
    simp only [Event.mk.injEq, Kind.wait.injEq] at heq
    exact heq.2.2.1
  have hcount : okPolls (kvReady L (g / L.block) s) ((X.tr g).take k) =
      okPolls (kvReady L (g / L.block) s) ((X.tr g).take k0) +
        okPolls (kvReady L (g / L.block) s) ((((X.tr g).drop k0).take (k - k0))) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [List.take_add, okPolls, List.countP_append, Nat.add_sub_cancel_left]
    rfl
  rw [hs3] at hblk hpar
  refine ⟨hsw, hs3, hp, ?_, ?_⟩
  · rw [hcount, hfresh, Nat.zero_add]
    exact hblk
  · rw [hcount, hfresh, Nat.zero_add, hp]
    unfold readyParity at hpar ⊢
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Ring
