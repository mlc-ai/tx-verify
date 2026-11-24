-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.SchedulerCount
public import Kernels.Fp16Gemm8192.Proof.Thread.SchedulerSites
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaUnelected

@[expose] public section

/-! # The scheduler's time against its response arrivals

A scheduler's time (`Scheduler.vtime`, at its successful response polls `R`) is at most the block of
its arrivals on its CTA's response barrier plus four, outside the exit stage. The arrivals are its
successful response polls plus one at its response wait (`Run.arr`). A scheduler past its
response poll (the sites `clcLoad` to `ack`) has polled its response barrier successfully at least
once: it holds the latest poll's read (`Run.exit`).

The same file proves the scheduler's unelected path: a warp-10 thread without an election event
is before its scheduler election (its prologue, or the scheduler's first state, time 58). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

namespace Scheduler

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The sites after a successful response poll of the scheduler, before its exit. -/
def PostSite : Site → Prop
  | .clcLoad | .clcStatus | .clcFirst | .clcFence | .ack => True
  | _ => False

/-- **The scheduler's time is at most the block of its arrivals, plus four.** A scheduler outside
its exit stage at its state `s` ranks at most `blockAt A + 4`, where `A` is its arrivals on its
CTA's
response barrier: the table of `Scheduler.vtime` is one block per successful poll, and its arrivals
are its polls plus one at its response wait. -/
theorem sched_time (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads)
    {s : Scheduler.D} (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.sched s)))) (hx : Scheduler.exitOff s = none) :
    Scheduler.vtime (okPolls (clcResp L g) (X.tr g)) s ≤
      blockAt (arrivals (clcResp L g) (X.tr g)) + 4 := by
  have hR := run_end hpre hX hg hσ
  have hA' : arrivals (clcResp L g) (X.tr g) =
      okPolls (clcResp L g) (X.tr g) + (if s.site = .clcWait then 1 else 0) := hR.arr
  have hP' : PostSite s.site → 0 < okPolls (clcResp L g) (X.tr g) := by
    obtain ⟨-, hLd, hSt, hFe, -⟩ := hR.exit
    have hH : ∀ rr, HeldRead L g (X.tr g) rr → 0 < okPolls (clcResp L g) (X.tr g) := by
      rintro rr ⟨j, -, -, -, -, -, -, -, hc, -⟩
      omega
    intro hp
    cases hs : s.site <;> rw [hs] at hp <;> simp only [PostSite] at hp
    · obtain ⟨pc, p, acq, sc, hl⟩ := hLd hs
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hl
      rw [hys, okPolls_snoc]
      simp [okPoll, sourceWaitSuccess]
    · obtain ⟨rr, -, h⟩ := hSt (.inl hs)
      exact hH rr h
    · obtain ⟨rr, -, h⟩ := hSt (.inr hs)
      exact hH rr h
    · obtain ⟨rr, -, h, -⟩ := hFe (.inl hs)
      exact hH rr h
    · obtain ⟨rr, -, h, -⟩ := hFe (.inr hs)
      exact hH rr h
  rw [hA']
  rcases s with ⟨site, ap, cp, resp, x⟩
  cases site <;> simp_all [Scheduler.vtime, Scheduler.exitOff, PostSite, blockAt, blockSpan] <;>
    omega

/-- **The scheduler's arrivals are its successful response polls, plus one at its response wait**,
at
every state of its run: the exact response arrivals (`Run.arr`) at the state `s`. -/
theorem sched_arrivals (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {s : Scheduler.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.sched s)))) :
    arrivals (clcResp L g) (X.tr g) =
      okPolls (clcResp L g) (X.tr g) + (if s.site = .clcWait then 1 else 0) := by
  exact (run_end hpre hX hg hσ).arr

/-- **A scheduler outside its exit stage whose arrivals are at most `n` ranks at most
`blockAt n + 4`.**
Its time is at most the block of its arrivals (`sched_time`), and blocks grow with their index. -/
theorem sched_time_le (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {s : Scheduler.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.sched s))))
    (hx : Scheduler.exitOff s = none) {n : Nat}
    (hn : arrivals (clcResp L g) (X.tr g) ≤ n) :
    Scheduler.vtime (okPolls (clcResp L g) (X.tr g)) s ≤ blockAt n + 4 := by
  have h := sched_time hpre hX hg hσ hx
  have hmono : blockAt (arrivals (clcResp L g) (X.tr g)) ≤ blockAt n := by
    unfold blockAt blockSpan
    omega
  omega

end Scheduler

/-! ## The unelected warp-10 thread -/

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxHeartbeats 4000000 in
/-- The scheduler warp's register count is followed by its scheduler's first state (warp 10 has no
role election: its register count leads straight to the scheduler). -/
theorem schedPath6 (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat}
    (hg : g < L.threads) (hw : Prologue.warpOf L g = 10) (h5 : 5 < (X.tr g).length) :
    Frame.stateAt (code L) X g 6 = some (some (.inr (.sched Prologue.schedStart))) := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[5]? = some e := ⟨_, List.getElem?_eq_getElem h5⟩
  show Frame.stateAt (code L) X g (5 + 1) = _
  rw [stateAt_succ_inl he (mmaPath5 hpre hX hg (by omega) (by omega) (by omega))]
  simp [Prologue.next, hw]

set_option maxHeartbeats 8000000 in
/-- **A warp-10 thread without an election is before its scheduler election.** Its trace has at most
six events: a seventh would fire the scheduler's election, which the full mask makes an election
event. Its final state is a prologue state (time at most 54) or the scheduler's first state
(its election, time 58); neither exits. -/
theorem sched_unelected_thm (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ∀ {g : Nat}, g < L.threads → g % L.block / 32 = 10 →
    (∀ j pc mask inst leader, ¬ X.Elect (g, j) pc mask inst leader) →
    ∃ d, Frame.stateAt (code L) X g (X.tr g).length = some (some d) ∧
      ((∃ p, d = .inl p) ∨ d = .inr (.sched Prologue.schedStart)) ∧ d.exitOff = none ∧
      d.vtime L g (X.tr g) ≤ 58 := by
  intro g hg hw hnoel
  have hw10 : Prologue.warpOf L g = 10 := hw
  -- A seventh event would fire the scheduler's election, which the full mask makes an election.
  have hn6 : (X.tr g).length ≤ 6 := by
    by_contra hlt
    obtain ⟨e6, he6⟩ : ∃ e, (X.tr g)[6]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hs6 := schedPath6 hpre hX hg hw10 (by omega)
    obtain ⟨t, ins, _, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he6 hs6
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_2)
    have hmask : readBits L g t 32 (.reg 630) = .ok (BitVec.ofNat 64 4294967295) :=
      readBits_b32 (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom
        (show 630 ∈ Flow.live Scheduler.Site.elect.pc by table_decide))) (by decide)
    obtain ⟨inst, leader, rfl⟩ := fires_elect_full hmask (by decide) hfire
    exact hnoel 6 _ 4294967295 inst leader he6
  rcases (show (X.tr g).length = 0 ∨ (X.tr g).length = 1 ∨ (X.tr g).length = 2 ∨
      (X.tr g).length = 3 ∨ (X.tr g).length = 4 ∨ (X.tr g).length = 5 ∨
      (X.tr g).length = 6 by omega) with h | h | h | h | h | h | h
  · refine ⟨.inl ⟨.shfl, 0⟩, ?_, Or.inl ⟨_, rfl⟩, rfl, ?_⟩
    · rw [h]
      exact stateAt_zero L X g
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inl ⟨.fence, Prologue.warpOf L g⟩, ?_, Or.inl ⟨_, rfl⟩, rfl, ?_⟩
    · rw [h]
      exact mmaPath1 hpre hX hg (by omega) (by omega)
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inl ⟨.fenceInit, Prologue.warpOf L g⟩, ?_, Or.inl ⟨_, rfl⟩, rfl, ?_⟩
    · rw [h]
      exact mmaPath2 hpre hX hg (by omega) (by omega)
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inl ⟨.arrive, Prologue.warpOf L g⟩, ?_, Or.inl ⟨_, rfl⟩, rfl, ?_⟩
    · rw [h]
      exact mmaPath3 hpre hX hg (by omega) (by omega)
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inl ⟨.wait, Prologue.warpOf L g⟩, ?_, Or.inl ⟨_, rfl⟩, rfl, ?_⟩
    · rw [h]
      exact mmaPath4 hpre hX hg (by omega) (by omega)
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inl ⟨.setMaxReg, Prologue.warpOf L g⟩, ?_, Or.inl ⟨_, rfl⟩, rfl, ?_⟩
    · rw [h]
      exact mmaPath5 hpre hX hg (by omega) (by omega) (by omega)
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inr (.sched Prologue.schedStart), ?_, Or.inr rfl, rfl, ?_⟩
    · rw [h]
      exact schedPath6 hpre hX hg hw10 (by omega)
    · simp [ThreadD.vtime, Scheduler.vtime, Prologue.schedStart]

end
end PTX.Kernels.Fp16Gemm8192.Proof
