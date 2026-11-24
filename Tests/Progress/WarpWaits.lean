-- SPDX-License-Identifier: Apache-2.0
module

public import Tests.Progress.WarpCollectives

@[expose] public section

/-!
# Deadlock tests: warp waits recorded at the arrival (checklist rows A16, C11)

`setmaxnreg` and the `.sync` `tcgen05` waits record their event at the arrival and return when
the thread's next event exists (`Kind.resume` is `.blocking false`). A stuck program therefore
has a maximal execution that contains the arrivals; proving that this execution is possible needs
a construction of possible executions with these events, which `Tests/Progress/Plain.lean` does
not provide. Each test proves the strongest statement that builds now: no possible execution
has an event of a stuck thread after its arrival.

* `setMaxReg_stuck` (A16): lane 0 runs `setmaxnreg.inc.sync.aligned.u32 240`, lanes 1–31 run
  `setmaxnreg.dec.sync.aligned.u32 120` at another source position; no lane returns.
* `tcWaitLd_stuck` (C11): lane 0 runs `tcgen05.wait::ld.sync.aligned`, lanes 1–31 exit; lane 0
  does not return, since the wait has no exit clause.
-/

namespace PTX.Tests.Progress
open PTX

noncomputable section

/-! ## `setmaxnreg` -/

def setMaxRegK : Kernel := splitK (.setMaxReg true 240) (.setMaxReg false 120)

theorem setMaxReg_trace0 {tr : List Event} {o : Option TState}
    (h : Run setMaxRegK [] L32 0 {} tr o) :
    OneThenExit tr (fun e => ∃ i, e = ⟨4, .setMaxReg true 240 i⟩) 5 :=
  oneThenExit_of_run (fun _ _ _ h => run_of_tau rfl (run_of_tau rfl h)) rfl
    (fun e o hf => by obtain ⟨i, rfl, rfl⟩ := hf; exact ⟨⟨i, rfl⟩, _, rfl, rfl, rfl⟩) h

theorem setMaxReg_trace {g : Nat} (hg : 0 < g) (hg' : g < 32) {tr : List Event}
    {o : Option TState} (h : Run setMaxRegK [] L32 g {} tr o) :
    OneThenExit tr (fun e => ∃ i, e = ⟨2, .setMaxReg false 120 i⟩) 3 := by
  interval_cases g <;>
  exact oneThenExit_of_run (fun _ _ _ h => run_of_tau rfl (run_of_tau rfl h)) rfl
    (fun e o hf => by obtain ⟨i, rfl, rfl⟩ := hf; exact ⟨⟨i, rfl⟩, _, rfl, rfl, rfl⟩) h

/-- A request at `pc` of a lane whose only request is at another position has not returned. -/
theorem setMaxReg_blocked {Y : Execution} {K : Kernel} (hd : DependencyOk L32 K Y) {g pc pcx : Nat}
    {inc : Bool} {n i : Nat} {pcx' : Nat} (he : Y.get (g, 0) = some ⟨pc, .setMaxReg inc n i⟩)
    (hret : 1 < (Y.tr g).length) {l : Nat} (hl : l < 32)
    (hother : OneThenExit (Y.tr (warpLane L32 g l))
      (fun e => ∃ inc' n' i', e = ⟨pcx, .setMaxReg inc' n' i'⟩) pcx') (hne : pcx ≠ pc) :
    False := by
  have hn : Need.node (fun x => ∃ j, x = .thread (warpLane L32 g l, j) ∧
      SetMaxNReg.SameRequest L32 Y (g, 0) (warpLane L32 g l, j)) ∈ Needs L32 Y (g, 0) := by
    simp only [Needs, he, KindNeeds]
    exact List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩
  obtain ⟨x, -, j, rfl, -, -, pc', inc', n', ei, fi, hei, hfi⟩ :=
    hd.ready _ (by simp [Returned, he, Kind.resume, hret]) _ hn
  simp only [SetMaxNReg.Request, he, Option.some.injEq, Event.mk.injEq] at hei
  obtain ⟨rfl, -⟩ := hei
  simp only [SetMaxNReg.Request, Execution.get] at hfi
  rcases hother with h | ⟨e, ⟨inc'', n'', i'', rfl⟩, h | h⟩ <;> rw [h] at hfi
  · simp at hfi
  · rcases j with _ | j <;> simp at hfi
    exact hne hfi.1
  · rcases j with _ | _ | j <;> simp at hfi
    exact hne hfi.1

/-- A16: no lane gets past its `setmaxnreg`: every possible execution has at most the request in
each thread. -/
theorem setMaxReg_stuck {mem0 : Mem0} (Y : Execution) (hY : Consistent L32 setMaxRegK [] mem0 Y) :
    ∀ g < L32.threads, (Y.tr g).length ≤ 1 := by
  have t0 := setMaxReg_trace0 (hY.thr 0 (by decide)).choose_spec
  intro g hg
  have hg32 := lt_L32 hg
  by_contra hlen
  rw [Nat.not_le] at hlen
  rcases Nat.eq_zero_or_pos g with rfl | hpos
  · rcases t0 with h | ⟨e, ⟨i, rfl⟩, htr⟩
    · simp [h] at hlen
    · have t1 := setMaxReg_trace (g := 1) (by decide) (by decide) (hY.thr 1 (by decide)).choose_spec
      exact setMaxReg_blocked hY.dependency (get_first htr) hlen (l := 1) (by decide)
        (t1.mono fun e ⟨i, he⟩ => ⟨_, _, _, he⟩) (by decide)
  · rcases setMaxReg_trace hpos hg32 (hY.thr g hg).choose_spec with h | ⟨e, ⟨i, rfl⟩, htr⟩
    · simp [h] at hlen
    · refine setMaxReg_blocked hY.dependency (get_first htr) hlen (l := 0) (pcx' := 5)
        (by decide) ?_
        (show 4 ≠ 2 by decide)
      rw [warpLane_L32 hg32]
      exact t0.mono fun e ⟨i, he⟩ => ⟨_, _, _, he⟩

/-! ## `tcgen05.wait::ld` -/

def tcWaitK : Kernel := splitK .tcWaitLd .exit

theorem tcWait_trace0 {tr : List Event} {o : Option TState} (h : Run tcWaitK [] L32 0 {} tr o) :
    OneThenExit tr (fun e => e = ⟨4, .tc .waitLd⟩) 5 :=
  oneThenExit_of_run (fun _ _ _ h => run_of_tau rfl (run_of_tau rfl h)) rfl
    (fun e o hf => by obtain ⟨rfl, rfl⟩ := hf; exact ⟨rfl, _, rfl, rfl, rfl⟩) h

theorem tcWait_trace1 {tr : List Event} {o : Option TState} (h : Run tcWaitK [] L32 1 {} tr o) :
    tr = [] ∨ tr = [⟨2, .exit⟩] := by
  rcases tr with _ | ⟨e, l⟩
  · exact .inl rfl
  · obtain ⟨rfl, rfl⟩ := run_exit rfl (run_of_tau rfl (run_of_tau rfl h))
    exact .inr rfl

/-- C11: lane 0 does not get past `tcgen05.wait::ld` while lane 1 exits without it. -/
theorem tcWaitLd_stuck {mem0 : Mem0} (Y : Execution) (hY : Consistent L32 tcWaitK [] mem0 Y) :
    (Y.tr 0).length ≤ 1 := by
  by_contra hlen
  rw [Nat.not_le] at hlen
  rcases tcWait_trace0 (hY.thr 0 (by decide)).choose_spec with h | ⟨e, rfl, htr⟩
  · simp [h] at hlen
  have he := get_first htr
  have hn : Need.node (fun x => ∃ j, x = .thread (warpLane L32 0 1, j) ∧
      Y.TcK (warpLane L32 0 1, j) (((Y.tr 0).take 0).countP isTcColl)) ∈ Needs L32 Y (0, 0) := by
    simp only [Needs, he, KindNeeds, tcNeeds, warpLanes]
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨1, List.mem_range.mpr (by decide), rfl⟩, rfl⟩
  obtain ⟨x, -, j, rfl, ⟨ev, hev, hc⟩, -⟩ :=
    hY.dependency.ready _ (by simp [Returned, he, Kind.resume, TcKind.resume, hlen]) _ hn
  rcases tcWait_trace1 (hY.thr 1 (by decide)).choose_spec with h | h <;>
    simp only [Execution.get, show warpLane L32 0 1 = 1 from rfl, h] at hev
  · simp at hev
  · rcases j with _ | j <;> simp at hev
    subst hev
    simp [isTcColl] at hc

end

end PTX.Tests.Progress
