-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.MmaLeader
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderTasks
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleWarp
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderUnelected
public import Kernels.Fp16Gemm8192.Proof.Thread.Tracked
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleRun
public import Kernels.Fp16Gemm8192.Proof.Thread.SchedulerTime
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.RunInv

@[expose] public section

/-! # A thread elects at most once

The kernel's four `elect.sync` instructions are the prologue's (warp 0, event 1), the loader's role
election (warp 11), the MMA warps' and the scheduler's (events 6). Every election event of a thread
is
at event 1 (warp 0) or event 6 (any other warp) (`elect_pos`): a prologue election is at its path
index (`stateAt_prologue`), a role's election is its first state's, the state at event 6, and from
event 7 on a role state is no election (`mma_run`, `sched_run`); the loader and the consumer have no
election site. So a thread has at most one election event (`elect_once_thm`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

/-- Whether an instruction is an election. -/
def electOp : Op → Bool
  | .warp w => w.kind == .elect
  | _ => false

/-- The kernel's elections are at its four election sites (decided on the code). -/
theorem kernel_elect_pcs : OpPcs kernel.code electOp
    [Flow.elect_0, Flow.elect_1, Flow.elect_2, Flow.elect_3] = true :=
  OpPcsFast.opPcs (by decide +kernel)

/-- A scheduler site at an election position is the election. -/
theorem Scheduler.site_elect {s : Scheduler.Site}
    (h : s.pc ∈ [Flow.elect_0, Flow.elect_1, Flow.elect_2, Flow.elect_3]) : s = .elect := by
  cases s <;> simp_all [Scheduler.Site.pc]

/-- No consumer site is at an election position. -/
theorem Consumer.site_pc_ne (s : Consumer.Site) :
    s.pc ∉ [Flow.elect_0, Flow.elect_1, Flow.elect_2, Flow.elect_3] := by
  cases s <;> simp only [Consumer.Site.pc]
  case load j => revert j; decide +kernel
  case loadWait j => revert j; decide +kernel
  case drain k => revert k; decide +kernel
  case barA k => revert k; decide +kernel
  case store k i el => revert k i el; decide +kernel
  case barB k => revert k; decide +kernel
  case fence k => revert k; decide +kernel
  case tma k => revert k; decide +kernel
  case commit k => revert k; decide +kernel
  all_goals decide +kernel


/-- The successor of a scheduler state is no election state. -/
theorem Scheduler.next_site_ne_elect {L : Launch} {g : Nat} {s s' : Scheduler.D} {e : Event}
    (hn : Scheduler.next L g s e = some (some s')) : s'.site ≠ .elect := by
  obtain ⟨site, ap, cp, r, x⟩ := s
  obtain ⟨s', ap', cp', r', x'⟩ := s'
  cases site <;> simp only [Scheduler.next, Scheduler.loopHead] at hn <;> (repeat' split at hn) <;>
    (intro h; subst h; simp_all)

namespace Loader

/-- No loader site's instruction is an election. -/
theorem notElect_site (s : Site) {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :
    ∀ w : WarpInstr, ins.op = .warp w → w.kind ≠ .elect := by
  intro w h
  cases s with
  | wait b =>
    rw [code_wait_ops b] at hc
    obtain rfl := Option.some.inj hc
    cases h
  | load b j =>
    obtain ⟨dst, map, cs, hc'⟩ := code_load_op b j
    rw [hc'] at hc
    obtain rfl := Option.some.inj hc
    cases h
  | arrive b =>
    rw [code_arrive_ops b] at hc
    obtain rfl := Option.some.inj hc
    cases h
  | clcWait =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_8)
    cases h
  | clcLoad =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_loadAcquire_0)
    cases h
  | clcStatus =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_0)
    cases h
  | clcFirst =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_1)
    cases h
  | clcFence =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_1)
    cases h
  | ack =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_8)
    cases h
  | drain i =>
    rw [code_drain_ops i] at hc
    obtain rfl := Option.some.inj hc
    cases h
  | exitArrive =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_1)
    cases h
  | exitWait =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_1)
    cases h
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    cases h

end Loader

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- A scheduler state's successor along the thread's run. -/
theorem stateAt_sched {k : Nat} {e : Event} {s : Scheduler.D} (he : (X.tr g)[k]? = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.sched s)))) :
    Frame.stateAt (code L) X g (k + 1) = (Scheduler.next L g s e).map
      (Option.map fun s' => (Sum.inr (Prologue.Role.sched s') : ThreadD)) := by
  rw [Frame.stateAt_succ he, hσ]
  rfl

/-- Along the run from the seventh state on, every scheduler state is no election. -/
theorem sched_run (ht : Frame.Tracked (code L) X) (hg : g < L.threads)
    (base : Frame.stateAt (code L) X g 7 = none ∨
      ∃ s7, Frame.stateAt (code L) X g 7 = some (some (.inr (.sched s7))) ∧ s7.site ≠ .elect) :
    ∀ n, 7 + n ≤ (X.tr g).length → Frame.stateAt (code L) X g (7 + n) = none ∨
      ∃ s, Frame.stateAt (code L) X g (7 + n) = some (some (.inr (.sched s))) ∧ s.site ≠ .elect :=
        by
  intro n
  induction n with
  | zero => intro _; exact base
  | succ n ih =>
    intro hn
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[7 + n]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [show 7 + (n + 1) = 7 + n + 1 by omega]
    rcases ih (by omega) with hnone | ⟨s, hσ, hsite⟩
    · exact Or.inl (by rw [Frame.stateAt_succ he, hnone]; rfl)
    · have hsucc := stateAt_sched he hσ
      cases hn' : Scheduler.next L g s e with
      | none => exact Or.inl (by rw [hsucc, hn']; rfl)
      | some o =>
        cases o with
        | none => exact absurd (by rw [hsucc, hn']; rfl) (ht g _ hg)
        | some s' =>
          exact Or.inr ⟨s', by rw [hsucc, hn']; rfl, Scheduler.next_site_ne_elect hn'⟩

/-- An election instruction. -/
theorem op_elect_form {op : Op} (h : electOp op = true) :
    ∃ w : WarpInstr, op = .warp w ∧ w.kind = .elect := by
  cases op <;> simp [electOp] at h
  exact ⟨_, rfl, h⟩

/-- An election event fires from an election instruction. -/
theorem electOp_of_fires {A : List Assumption} {t : TState} {op : Op} {pc : Nat} {e : Event}
    {o : Option TState} {mask inst leader : Nat} (hf : Fires pc (eventTmpl A L g t op) e o)
    (he : e.kind = .elect mask inst leader) : electOp op = true := by
  by_contra h
  exact fires_notElect_op (fun w h' hk => h (by simp [electOp, h', hk])) hf mask inst leader he

set_option maxHeartbeats 8000000 in
/-- **Every election event of a thread is at event 1 (warp 0) or event 6 (the other warps).** -/
theorem elect_pos (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {j pc mask inst leader : Nat} (hg : g < L.threads)
    (hj : X.get (g, j) = some ⟨pc, .elect mask inst leader⟩) :
    (j = 1 ∧ Prologue.warpOf L g = 0) ∨ (j = 6 ∧ Prologue.warpOf L g ≠ 0) := by
  have hjlt : j < (X.tr g).length := len_of_get hj
  obtain ⟨d, hτ⟩ := Frame.event_state (fun _ => sound hpre) hX (tracked hpre hX) hj nofun
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site (fun _ => sound hpre) hX hj hτ
  have hop := electOp_of_fires hf rfl
  have hpcm := OpPcs.mem kernel_elect_pcs hc hop
  have hjle : j ≤ (X.tr g).length := by omega
  have hon := onPath_all hpre hX hg j hjle
  have hw12 := Prologue.warpOf_lt hpre g
  cases d with
  | inl p =>
    obtain ⟨hidx, hwp, hcan⟩ := hon.1 p hτ
    have hs : p.site = .elect ∨ p.site = .roleElect := by
      by_contra hne
      push Not at hne
      exact prologue_not_elect hpre hX hg hj hτ hne.1 hne.2 mask inst leader rfl
    rcases hs with hs | hs
    · have hw0 : p.w = 0 := hcan.1 (Or.inl hs)
      have hj1 : j = 1 := by rw [hidx]; simp [Prologue.index, hs]
      subst hj1
      exact Or.inl ⟨rfl, by rw [← hwp (by omega)]; exact hw0⟩
    · have hw11 : p.w = 11 := hcan.2.2.2.2 hs
      have hwo : Prologue.warpOf L g = 11 := by
        rw [← hwp (by rw [hidx]; simp [Prologue.index, hs])]; exact hw11
      refine Or.inr ⟨?_, by omega⟩
      rw [hidx]
      simp [Prologue.index, hs, Prologue.fenceIdx, hw11]
  | inr r =>
    have hrw := role_warp hpre hX hg j hjle r hτ
    have hwait := hon.2 r hτ
    cases r with
    | loader l =>
      obtain ⟨w, h, hk⟩ := op_elect_form hop
      exact (Loader.notElect_site l.site hc w h hk).elim
    | cons c => exact (Consumer.site_pc_ne c.site hpcm).elim
    | mma m =>
      have hs : m.site = .elect := by
        by_contra hne
        obtain ⟨w, h, hk⟩ := op_elect_form hop
        exact Mma.notElect_site hne hc w h hk
      simp only [roleWarp] at hrw
      obtain ⟨-, hw89⟩ := hrw
      have hw0 : Prologue.warpOf L g ≠ 0 := by omega
      refine Or.inr ⟨?_, hw0⟩
      have h4 : 4 < j := by
        have := hwait
        simp only [Prologue.index, Prologue.fenceIdx, hw0, ↓reduceIte] at this
        omega
      rcases Nat.lt_or_ge j 7 with hj7 | hj7
      · rcases Nat.lt_or_ge j 6 with hj6 | hj6
        · exfalso
          have hj5 : j = 5 := by omega
          subst hj5
          rw [mmaPath5 hpre hX hg hw0 (by omega) (by omega)] at hτ
          cases hτ
        · omega
      · exfalso
        have hs6 := mmaPath6 hpre hX hg hw89 (by omega)
        obtain ⟨e6, he6⟩ : ∃ e, (X.tr g)[6]? = some e :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hrun := mma_run (stateAt_seven hs6 he6) (j - 7) (by omega)
        rw [show 7 + (j - 7) = j by omega] at hrun
        rcases hrun with hdead | ⟨m', hσ, hsite⟩
        · rw [hdead] at hτ
          cases hτ
        · rw [hσ] at hτ
          cases hτ
          exact hsite hs
    | sched sc =>
      have hs : sc.site = .elect := Scheduler.site_elect hpcm
      simp only [roleWarp] at hrw
      have hw0 : Prologue.warpOf L g ≠ 0 := by omega
      refine Or.inr ⟨?_, hw0⟩
      have h4 : 4 < j := by
        have := hwait
        simp only [Prologue.index, Prologue.fenceIdx, hw0, ↓reduceIte] at this
        omega
      rcases Nat.lt_or_ge j 7 with hj7 | hj7
      · rcases Nat.lt_or_ge j 6 with hj6 | hj6
        · exfalso
          have hj5 : j = 5 := by omega
          subst hj5
          rw [mmaPath5 hpre hX hg hw0 (by omega) (by omega)] at hτ
          cases hτ
        · omega
      · exfalso
        have hs6 := schedPath6 hpre hX hg (by omega) (by omega)
        obtain ⟨e6, he6⟩ : ∃ e, (X.tr g)[6]? = some e :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hbase : Frame.stateAt (code L) X g 7 = none ∨
            ∃ s7, Frame.stateAt (code L) X g 7 = some (some (.inr (.sched s7))) ∧ s7.site ≠
              .elect := by
          have h7 := stateAt_sched he6 hs6
          cases hn : Scheduler.next L g Prologue.schedStart e6 with
          | none => exact Or.inl (by rw [h7, hn]; rfl)
          | some o =>
            cases o with
            | none => exact absurd (by rw [h7, hn]; rfl) (tracked hpre hX g 7 hg)
            | some s7 =>
              exact Or.inr ⟨s7, by rw [h7, hn]; rfl, Scheduler.next_site_ne_elect hn⟩
        have hrun := sched_run (tracked hpre hX) hg hbase (j - 7) (by omega)
        rw [show 7 + (j - 7) = j by omega] at hrun
        rcases hrun with hdead | ⟨s', hσ, hsite⟩
        · rw [hdead] at hτ
          cases hτ
        · rw [hσ] at hτ
          cases hτ
          exact hsite hs

/-- **A thread has at most one election event.** -/
theorem elect_once_thm (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {j j' pc pc' mask mask' inst inst' leader leader' : Nat} (hg : g < L.threads)
    (h : X.Elect (g, j) pc mask inst leader) (h' : X.Elect (g, j') pc' mask' inst' leader') :
    j = j' := by
  rcases elect_pos hpre hX hg h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases elect_pos hpre hX hg h' with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega


/-- **An elected loader in its exit stage has polled.** Without empty polls it would have been left
idle by an election of another lane (`LoaderTasks.Idle`), a second election. With them, its response
polls are positive (`CountOK`). -/
theorem loader_elected_polled (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {k : Nat} {l : Loader.D} (hg : g < L.threads)
    (hel : ∃ j pc mask inst, X.Elect (g, j) pc mask inst (laneOf L g))
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.loader l)))) (hd : l.site.done = true) :
    0 < lcount L g ((X.tr g).take k) ∧ 0 < okPolls (clcResp L g) ((X.tr g).take k) := by
  obtain ⟨hc, -, -, hidle⟩ : LoaderTasks.AlongT L g (.inr (.loader l)) ((X.tr g).take k) :=
    LoaderTasks.runT hpre hg (Frame.trace (fun _ => sound hpre) hX hg) k _ hσ
  have hN : 0 < lcount L g ((X.tr g).take k) := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    obtain ⟨i, ⟨pce, ke⟩, hi, x, y, leader, hk, hne⟩ := hidle hd h0
    simp only at hk
    subst hk
    have hlt := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_take] at hlt
    rw [List.getElem?_take_of_lt (by omega)] at hi
    obtain ⟨j, pc, mask, inst, hj⟩ := hel
    have hij := elect_once_thm hpre hX hg (show X.Elect (g, i) pce x y leader from hi) hj
    subst hij
    have := Option.some.inj ((show X.get (g, i) = _ from hi).symm.trans hj)
    simp only [Event.mk.injEq, Kind.elect.injEq] at this
    exact hne this.2.2.2
  refine ⟨hN, ?_⟩
  have hr := hc.resp
  obtain ⟨site, m, n, q, cp, resp, x⟩ := l
  cases site <;> simp_all [LoaderTasks.CountOK, Loader.Site.done] <;> omega

/-- **An elected loader in its exit stage has polled**, at the end of its trace. -/
theorem loader_elected_exit_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {l : Loader.D} (hg : g < L.threads) (_hw : g % L.block / 32 = 11)
    (hel : ∃ j pc mask inst, X.Elect (g, j) pc mask inst (laneOf L g))
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))))
    (hd : l.site.done = true) :
    0 < loaderCount L g (X.tr g) ∧ 0 < okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) :=
      by
  have h := loader_elected_polled hpre hX hg hel hσ hd
  rw [List.take_length] at h
  rw [loaderCount_eq]
  exact h

end
end PTX.Kernels.Fp16Gemm8192.Proof
