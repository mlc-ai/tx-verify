-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaLeader
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaAcc
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerAcc
public import Kernels.Fp16Gemm8192.Proof.Thread.SchedulerSites
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderEvents
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderDiscipline
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerClc
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Observes
public import Lemmas.Flow.PollFacts
public import Kernels.Fp16Gemm8192.Proof.NoBarArrive

@[expose] public section

/-! # The kernel's polls: one object per position, and selected where two lanes poll

`not_warpDivergent_polls` needs three facts of the kernel. Its guarded uniform instructions are
the branches of its wait loops (`poll_guards`, decided on the code). Each poll position polls one
mbarrier in all lanes of a warp (`poll_obj_uniform`, by `PollObjUniform.of_at`): every role polls
at a fixed set of sites, and the object of each site depends on the thread only through its CTA and
warp (`PollAt`). Two distinct lanes of a warp polling one object at a position whose branch
`Assumptions.pollAgree` does not select are ordered (`poll_ordered`, by `PollOrdered.of_cases`):

* the loader, MMA and scheduler roles run on the lane their warp elected; one warp elects one
  lane (DEP-WARP-ELECT: equal masks return one leader), so two distinct lanes of a warp never both
  poll in these roles;
* the consumers poll on all lanes, only at their accumulator and response waits, whose branches
  `Assumptions.pollAgree` selects (ASM-POLL-AGREE; `cons_poll_selected`), so their polls of one
  object need no order.

This file sits at the top of the proof tree, outside the layer order: the safety root uses it. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

/-- Every guarded `bra.uni` or aligned instruction of the kernel is the branch of a wait loop on
the poll right before it, and every poll is followed by its branch. -/
theorem poll_guards : kernel.pollGuardsOk = true := by decide +kernel

/-- The local rules of the kernel's assumptions advance or branch, writing only their
destinations. -/
theorem local_frames {L : Launch} :
    ∀ g t op t', execLocalA Prod L g t op = .ok t' → LocalFrame op t t' :=
  fun _ _ _ _ => execLocalA_frame (RulesFrame.idealReal fun a ha => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> intro _ _ _ _ _ h <;> cases h)

/-- The CLC response barrier of thread `x`'s CTA. -/
abbrev clcLoc (L : Launch) (x : Nat) : Loc := ⟨.shared, x / L.block, L.sharedBase + 104⟩

/-- Where a thread of role `r` polls, by position: the object depends on the thread only through
its CTA and warp. -/
def PollAt (L : Launch) (x pc : Nat) (m : Loc) : Prologue.Role → Prop
  | .loader _ =>
    (∃ b : Fin 8, pc = (Loader.Site.wait b).pc ∧
      m = InputRing.emptyLoc L (x / L.block) (InputRing.slotOf b)) ∨
    (∃ i : Fin 4, pc = (Loader.Site.drain i).pc ∧ m = InputRing.emptyLoc L (x / L.block) i) ∨
    (pc = Loader.Site.clcWait.pc ∧ m = clcLoc L x)
  | .mma mm =>
    (∃ s : Fin 4, pc = (Mma.Site.full s).pc ∧ m = Bar.loc L (x / L.block) ⟨.input, s.val, true⟩) ∨
    (pc = Mma.Site.accWait.pc ∧ m = Mma.accBar L x (mm.w % 2) false) ∨
    (pc = Mma.Site.clcWait.pc ∧ m = clcLoc L x)
  | .sched _ =>
    (pc = Scheduler.Site.ackWait.pc ∧ m = Scheduler.ackBar L x) ∨
    (pc = Scheduler.Site.clcWait.pc ∧ m = Scheduler.respBar L x)
  | .cons _ =>
    (pc = Consumer.Site.accWait.pc ∧ m = Consumer.accFull L x (Consumer.accIdx L x)) ∨
    (pc = Consumer.Site.clcWait.pc ∧ m = clcLoc L x)

theorem clc_loc_of {L : Launch} {x : Nat} {m : Loc} (ha : m.addr = L.sharedBase + 104)
    (hl : m.space = .shared ∧ m.cta = x / L.block) : m = clcLoc L x := by
  obtain ⟨sp, c, a⟩ := m
  simp only at ha hl
  obtain ⟨rfl, rfl⟩ := hl
  subst ha
  rfl

set_option maxHeartbeats 4000000 in
/-- **A poll of a thread is where its role polls.** -/
theorem poll_at {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {x k pc : Nat} {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope} (hx : x < L.threads)
    (he : X.get (x, k) = some ⟨pc, .wait m p ok acq sc⟩) :
    ∃ r, Frame.stateAt (code L) X x k = some (some (.inr r)) ∧ roleWarp (x % L.block / 32) r ∧
      PollAt L x pc m r ∧ ∀ c, r = .cons c →
        (c.site = .accWait ∧ pc = Consumer.Site.accWait.pc ∧
          m = Consumer.accFull L x (Consumer.accIdx L x)) ∨
        (c.site = .clcWait ∧ pc = Consumer.Site.clcWait.pc ∧ m = clcLoc L x) := by
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  have hloc := ht.wait_local hx he hσ rfl
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hpc : pc = (code L x).pc d := EventFrame.fires_source_pc hfire
  rcases d with q | r
  · exact absurd rfl (ht.prologue_no_wait hx he hσ m p ok acq sc)
  refine ⟨r, hσ, ht.role_warp hx (List.getElem?_eq_some_iff.mp he).1.le hσ, ?_⟩
  rcases r with l | mm | sd | c
  · -- the loader
    refine ⟨?_, fun c h => by cases h⟩
    obtain ⟨site, m0, n, q, cp, r, x0⟩ := l
    simp only [code] at hpc hat hc hfire
    cases hp : site.polls with
    | false =>
      exact (fires_notWait (eventTmpl_notWait (Loader.code_notPoll _ hp hc)) hfire _ _ _ _ _
        rfl).elim
    | true =>
      cases site with
      | wait b =>
        obtain ⟨ok', acq', sc', he'⟩ := Loader.wait_event hpre b rfl hat hc hfire
        simp only [Event.mk.injEq, Kind.wait.injEq] at he'
        exact .inl ⟨b, hpc, he'.2.1⟩
      | drain i =>
        obtain ⟨ok', acq', sc', he'⟩ := Loader.drain_event hpre i rfl hat hc hfire
        simp only [Event.mk.injEq, Kind.wait.injEq] at he'
        exact .inr (.inl ⟨i, hpc, he'.2.1⟩)
      | clcWait =>
        obtain ⟨p', ok', acq', sc', -, he'⟩ :=
          Loader.clcWait_event (d := ⟨.clcWait, m0, n, q, cp, r, x0⟩) hpre rfl hat hc hfire
        simp only [Event.mk.injEq, Kind.wait.injEq] at he'
        exact .inr (.inr ⟨hpc, he'.2.1⟩)
      | _ => simp [Loader.Site.polls] at hp
  · -- an MMA thread
    refine ⟨?_, fun c h => by cases h⟩
    simp only [code] at hpc hat hc hfire hinv
    rcases Mma.wait_site hpre hinv.1 hat hc hfire rfl with ⟨s, hs, hm, -⟩ | ⟨hs, hm, -⟩ |
        ⟨hs, ha⟩
    · exact .inl ⟨s, by rw [hpc, hs], hm⟩
    · exact .inr (.inl ⟨by rw [hpc, hs], hm⟩)
    · exact .inr (.inr ⟨by rw [hpc, hs], clc_loc_of ha hloc⟩)
  · -- the scheduler
    refine ⟨?_, fun c h => by cases h⟩
    simp only [code] at hpc hat hc hfire hinv
    rcases Scheduler.wait_site hpre hinv.1 hat hc hfire rfl with ⟨hs, hm, -⟩ | ⟨hs, hm, -⟩
    · exact .inl ⟨by rw [hpc, hs], hm⟩
    · exact .inr ⟨by rw [hpc, hs], hm⟩
  · -- a consumer thread
    simp only [code] at hpc hat hc hfire hinv
    rcases Consumer.wait_site hpre hinv.1 hat.2.2.2.2 hc hfire rfl with ⟨hs, hm, -⟩ |
        ⟨hs, ha, -⟩
    · exact ⟨.inl ⟨by rw [hpc, hs], hm⟩, fun c' h => by
      cases h; exact .inl ⟨hs, by rw [hpc, hs], hm⟩⟩
    · exact ⟨.inr ⟨by rw [hpc, hs], clc_loc_of ha hloc⟩,
        fun c' h => by cases h; exact .inr ⟨hs, by rw [hpc, hs], clc_loc_of ha hloc⟩⟩

/-! The poll positions of each role are distinct. -/

theorem loader_wait_inj : ∀ b b' : Fin 8, (Loader.Site.wait b).pc = (Loader.Site.wait b').pc →
    b = b' := by decide
theorem loader_drain_inj : ∀ i i' : Fin 4, (Loader.Site.drain i).pc = (Loader.Site.drain i').pc →
    i = i' := by decide
theorem loader_wait_drain : ∀ (b : Fin 8) (i : Fin 4),
    (Loader.Site.wait b).pc ≠ (Loader.Site.drain i).pc := by decide
theorem loader_wait_clc : ∀ b : Fin 8, (Loader.Site.wait b).pc ≠ Loader.Site.clcWait.pc := by
  decide
theorem loader_drain_clc : ∀ i : Fin 4, (Loader.Site.drain i).pc ≠ Loader.Site.clcWait.pc := by
  decide
theorem mma_full_inj : ∀ s s' : Fin 4, (Mma.Site.full s).pc = (Mma.Site.full s').pc → s = s' := by
  decide
theorem mma_full_acc : ∀ s : Fin 4, (Mma.Site.full s).pc ≠ Mma.Site.accWait.pc := by decide
theorem mma_full_clc : ∀ s : Fin 4, (Mma.Site.full s).pc ≠ Mma.Site.clcWait.pc := by decide
theorem mma_acc_clc : Mma.Site.accWait.pc ≠ Mma.Site.clcWait.pc := by decide
theorem sched_ack_clc : Scheduler.Site.ackWait.pc ≠ Scheduler.Site.clcWait.pc := by decide
theorem cons_acc_clc : Consumer.Site.accWait.pc ≠ Consumer.Site.clcWait.pc := by decide

/-- Two threads of one warp polling at one position poll one object. -/
theorem pollAt_unique {L : Launch} {g h pc : Nat} {m m' : Loc} {r r' : Prologue.Role}
    (hc : g / L.block = h / L.block) (hw : g % L.block / 32 = h % L.block / 32)
    (hr : roleWarp (g % L.block / 32) r) (hr' : roleWarp (h % L.block / 32) r')
    (hp : PollAt L g pc m r) (hp' : PollAt L h pc m' r') : m = m' := by
  rw [← hw] at hr'
  rcases r with l | mm | sd | c <;> rcases r' with l' | mm' | sd' | c' <;>
    simp only [roleWarp] at hr hr' <;> try omega
  · rcases hp with ⟨b, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hp' with ⟨b', hb, rfl⟩ | ⟨i', hi, rfl⟩ | ⟨hcl, rfl⟩
    · obtain rfl := loader_wait_inj b b' hb; simp only [hc]
    · exact absurd hi (loader_wait_drain b i')
    · exact absurd hcl (loader_wait_clc b)
    · exact absurd hb.symm (loader_wait_drain b' i)
    · obtain rfl := loader_drain_inj i i' hi; simp only [hc]
    · exact absurd hcl (loader_drain_clc i)
    · exact absurd hb.symm (loader_wait_clc b')
    · exact absurd hi.symm (loader_drain_clc i')
    · simp only [clcLoc, hc]
  · obtain ⟨hw1, -⟩ := hr
    obtain ⟨hw2, -⟩ := hr'
    rcases hp with ⟨s, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hp' with ⟨s', hs, rfl⟩ | ⟨ha, rfl⟩ | ⟨hcl, rfl⟩
    · obtain rfl := mma_full_inj s s' hs; simp only [hc]
    · exact absurd ha (mma_full_acc s)
    · exact absurd hcl (mma_full_clc s)
    · exact absurd hs.symm (mma_full_acc s')
    · simp only [Mma.accBar, hc, hw1, hw2]
    · exact absurd hcl mma_acc_clc
    · exact absurd hs.symm (mma_full_clc s')
    · exact absurd ha.symm mma_acc_clc
    · simp only [clcLoc, hc]
  · rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hp' with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · simp only [Scheduler.ackBar, hc]
    · exact absurd h1 sched_ack_clc
    · exact absurd h1.symm sched_ack_clc
    · simp only [Scheduler.respBar, hc]
  · rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hp' with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · simp only [Consumer.accFull, Consumer.accIdx, Consumer.tidOf, hc, hw]
    · exact absurd h1 cons_acc_clc
    · exact absurd h1.symm cons_acc_clc
    · simp only [clcLoc, hc]

/-- **Each poll position polls one object in all lanes of a warp.** -/
theorem poll_obj_uniform {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    PollObjUniform L X :=
  PollObjUniform.of_at (fun g pc m => ∃ r, roleWarp (g % L.block / 32) r ∧ PollAt L g pc m r)
    (fun hg he => by
      obtain ⟨r, -, hr, hp, -⟩ := poll_at hpre hX ht hg he
      exact ⟨r, hr, hp⟩)
    (fun hw ⟨_, hr, hp⟩ ⟨_, hr', hp'⟩ => pollAt_unique hw.1.2.2 hw.2 hr hr' hp hp')

/-- The assumptions select exactly the sites of `pollAgreeSites` with `uniPoll`. -/
theorem prod_uniPoll (pc : Nat) :
    List.any Prod (·.uniPoll pc) = Assumptions.pollAgreeSites.contains pc := by
  simp [Assumptions.idealArith, Assumption.idealReal, Assumptions.clusterMbar,
    Assumption.clusterScopeMbarAt, Assumptions.pollAgree, Assumption.pollAgreeAt]

/-- The branches after the consumers' waits are selected by `Assumptions.pollAgree`. -/
theorem cons_poll_selected :
    Assumptions.pollAgreeSites.contains (Consumer.Site.accWait.pc + 1) = true ∧
      Assumptions.pollAgreeSites.contains (Consumer.Site.clcWait.pc + 1) = true := by
  decide

/-- **Two distinct lanes of a warp polling one object at a position whose branch no assumption
selects are ordered**: the polling roles there run on their warp's elected lane. -/
theorem poll_ordered {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    PollOrdered L kernel Prod X := by
  refine PollOrdered.of_cases hX.elect
    fun g h k k' pc m p p' ok ok' acq acq' sc sc' hg hh hgh hw he he' hs => ?_
  obtain ⟨r, hσ, hr, -, hsite⟩ := poll_at hpre hX ht hg he
  obtain ⟨r', hσ', hr', -, -⟩ := poll_at hpre hX ht hh he'
  have hww : g % L.block / 32 = h % L.block / 32 := hw.2
  rw [← hww] at hr'
  -- elected roles: the polling lane leads its warp's full-mask election
  have leads : ∀ {x kx : Nat} {ex : Event} {rx : Prologue.Role} {pc0 : Nat}, x < L.threads →
      X.get (x, kx) = some ex → Frame.stateAt (code L) X x kx = some (some (.inr rx)) →
      rx.electPc = some pc0 → ObjectKind ex.kind → Leads L X 4294967295 x := by
    intro x kx ex rx pc0 hx hex hσx h0 hk
    obtain ⟨j, inst, leader, -, hj, hl⟩ := ht.elected hx hex hσx h0 hk
    exact ⟨j, pc0, inst, hl ▸ hj⟩
  rcases r with l | mm | sd | c <;> rcases r' with l' | mm' | sd' | c' <;>
    simp only [roleWarp] at hr hr' <;> try omega
  all_goals try exact .inl ⟨_, leads hg he hσ rfl trivial, leads hh he' hσ' rfl trivial⟩
  -- two consumers: their branches are selected
  rw [prod_uniPoll] at hs
  rcases hsite c rfl with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
  · rw [cons_poll_selected.1] at hs
    cases hs
  · rw [cons_poll_selected.2] at hs
    cases hs

end

end PTX.Kernels.Fp16Gemm8192.Proof
