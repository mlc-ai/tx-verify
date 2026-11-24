-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Poll
public import Kernels.TmlFa4Fwd.Proof.Mma.Fits
public import Kernels.TmlFa4Fwd.Proof.Progress.Time
public import Lemmas.Flow.Step.ShapeRegs
public import Lemmas.Kernel.Progress.Poll
import Kernels.TmlFa4Fwd.Flow.Code.Part033
import Kernels.TmlFa4Fwd.Flow.Code.Part034
import Kernels.TmlFa4Fwd.Flow.Code.Part035
import Kernels.TmlFa4Fwd.Flow.Code.Part036
import Kernels.TmlFa4Fwd.Flow.Code.Part037
import Kernels.TmlFa4Fwd.Flow.Code.Part038
import Kernels.TmlFa4Fwd.Flow.Code.Part039
import Kernels.TmlFa4Fwd.Flow.Code.Part040
import Kernels.TmlFa4Fwd.Flow.Code.Part041
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.SharedSites
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Lemmas.Kernel.Progress.PollsOn
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Progress at the MMA warp's polls

The MMA warp polls fourteen sites (`Mma.Site.wt k`, `Mma.Site.mw b ld`): Q stage 0 and 1 (barrier
offsets 0 and 8), the K/V ring's full barriers (32, 40, 48), and the P halves of the softmax warps
(96, 104, 112, 120). At each, the barrier is a function of the round `r` (`pollO`) and the poll's
parity is the parity of the lane's successful polls of it so far (`par_eq`, from the count
conjuncts `RefQ` of the warp's reference invariant: the ring's slot and parity, the P parity).
So a lane of warp 12 at a poll site at the end of its trace polls `bl L g (pollO r s)` next with
`δ = 0` (`mma_pollsOn`), from `Mma.good`, the ghost ledger and the shape table.

The producers' side is the premise `MmaFullLag`, one statement for both producer roles: when the
barrier's phase has the poll's parity, the lane has a blocker. It is proved by the loader (Q and
K/V: a lagging loader lane or the open TMA copy, the K/V ring and the Q stages as `RingDecl`
instances) and the softmax (P: a lagging softmax lane) when those fragments are glued; the split
by offset is `fromLoader`. With it the lane is at an `MbarAt` below its time, which
`Sched.mbar_at_steps` turns into a descent step (`mma_mbarAt`).

**Commits.** The MMA warp is the producer of the barriers its commits signal (offsets 16, 24,
56–72, 80, 88, 144, 152). A commit's arrival is asynchronous: before the commit is issued the
committing lane is pending at a state whose time is at most the commit site's
(`Mm.pipeT` of its place and round, which orders the pipeline by slot and then offset, the
program order); after it, the open commit obligation is the blocker (rank 2, `Sched.Blk`). The
waiters' lag lemmas against these times are written with the waiting roles' tables (loader
ring-empty, softmax S-full, correction O-full and Q-free). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Progress
open PTX PTX.Proof PTX.Flow MBarrier
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (minj bl RefQ RefCounts LoopRegs acqAt ringAcq ringCount pq
  iw)

noncomputable section
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

open Mma in
set_option maxHeartbeats 4000000 in
/-- **The event a poll site fires**: a wait on its barrier with its parity bit, or a fault on a
misaligned barrier. -/
theorem poll_fires {d : Mma.D} (hs : isPoll d.site = true) {t : TState}
    {ins : Instr} {e : Event} {o : Option TState}
    (h : At t d.site.pc (facts p L g (ent p L) d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    (∃ ok, e.kind = .wait (pollLoc L g d) (pollPar L d) ok true .cta) ∨
      ∃ f, e.kind = .ub f ∧ (pollLoc L g d).addr % 8 ≠ 0 := by
  obtain ⟨site, v⟩ := d
  cases site <;> simp only [isPoll, reduceCtorEq, Bool.false_eq_true] at hs
  case wt k =>
    simp only [pollLoc, pollPar]
    fin_cases k <;> site_code <;>
      refine fires_wait_reg_al (wx := 32) (wq := 32) ?_ (reg_bits h ?_ ?_) (reg_bits h ?_ ?_) hf <;>
      first | (rw [h.1]; decide) | lit_mem | rfl
  case mw b ld =>
    simp only [pollLoc, pollPar]
    fin_cases b <;> cases ld <;> site_code <;>
      refine fires_wait_reg_al (wx := 32) (wq := 32) ?_ (reg_bits h ?_ ?_) (reg_bits h ?_ ?_) hf <;>
      first | (rw [h.1]; decide) | lit_mem | rfl

/-! ### The poll premise -/

/-- The MMA warp's successful polls of a barrier are its ledger's count. -/
theorem okPolls_eq {k : Nat} {d : Mma.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n))) (l : Loc) :
    okPolls l ((X.tr g).take k) = n (.mma (.acquire l)) :=
  count hσ (.mma (.acquire l))

/-- No undefined-behaviour event in the execution: the ledger's count of them is zero. -/
theorem ub_count_zero (hub : ¬ HasUb X) {k : Nat} {σ : (glued p L g).D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (σ, n))) : n .ub = 0 := by
  rw [← count hσ .ub, List.countP_eq_zero]
  intro e he hc
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp [cls] at hc
  rename_i f
  obtain ⟨j, hj, hje⟩ := List.getElem_of_mem he
  have hjk : j < k := by rw [List.length_take] at hj; omega
  refine hub ⟨(g, j), pc, f, ?_⟩
  show (X.tr g)[j]? = _
  rw [← List.getElem?_take_of_lt hjk, List.getElem?_eq_getElem hj, hje]

/-- The reference invariant of a lane of warp 12 at the end of its trace, in an execution
without undefined behaviour. -/
theorem mma_ref (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hub : ¬ HasUb X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 12) {d : Mma.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (minj p L g d n))) :
    RefCounts p L g (d, Mma.rc n) ∧ Mma.MFits p L g d (n .shfl) (n .vote) :=
  (Mma.good hp hX (cuQReadsFromLaunch hp hX) hg hw _).2 _ hσ (ub_count_zero hub hσ)

/-- **A lane of warp 12 at a poll site polls its barrier next**, with the parity of its
successful polls of it (`δ = 0`); `r` is the round of its count conjuncts. -/
theorem mma_pollsOn (hp : Pre p L m) (hg : g < L.threads) {d : Mma.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (minj p L g d n)))
    (hs : isPoll d.site = true) {r : Nat} {w : Bool}
    (hQ : RefQ p L g d.site.ord d.v (Mma.rc n) r w) :
    Sched.PollsOn kernel Assumptions.all L X g (bl L g (pollO r d.site)) 0 := by
  have hok : okPolls (bl L g (pollO r d.site)) (X.tr g) =
      n (.mma (.acquire (bl L g (pollO r d.site)))) := by
    have h := okPolls_eq hσ (bl L g (pollO r d.site))
    rwa [List.take_length] at h
  obtain ⟨hl, hq⟩ := par_eq hp hQ hs
  obtain ⟨gd, pp, b, off, par, sc, hc⟩ : ∃ gd pp b off par sc,
      kernel.code[(thread p L g).pc (minj p L g d n)]? =
        some ⟨gd, .mbarWait pp b off par true sc⟩ := by
    obtain ⟨site, v⟩ := d
    show ∃ gd pp b off par sc, kernel.code[site.pc]? = _
    cases site <;> simp only [isPoll, reduceCtorEq, Bool.false_eq_true] at hs
    case wt k => fin_cases k <;> exact ⟨_, _, _, _, _, _, by code_lookup⟩
    case mw b ld => fin_cases b <;> cases ld <;> exact ⟨_, _, _, _, _, _, by code_lookup⟩
  have hal : (pollLoc L g d).addr % 8 = 0 := by
    rw [hl]
    have := hp.shared.1
    have := pollO_al r d.site
    simp only [bl]
    omega
  refine strict_pollsOn hp hg hσ rfl
    (P := fun e => (∃ ok, e.kind = .wait (pollLoc L g d) (pollPar L d) ok true .cta) ∨
      ∃ f, e.kind = .ub f ∧ (pollLoc L g d).addr % 8 ≠ 0)
    (fun hat _ hc' hf => poll_fires hs
      ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩ hc' hf) hc ?_ ?_
  · rintro f (⟨_, h⟩ | ⟨_, h, hm⟩)
    · cases h
    · exact hm hal
  · rintro l q ok sc' (⟨_, h⟩ | ⟨_, h, -⟩)
    · simp only [Kind.wait.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      refine ⟨hl, ?_⟩
      rw [Nat.add_zero, hok, ← hq]
    · cases h

/-! ### The producers' premise and the descent step -/

/-- **The producers' side of the MMA warp's polls**: in every consistent execution without
undefined behaviour, a lane of warp 12 at a poll site at the end of its trace, polling the barrier
at offset `o` of its CTA, finds a state of the barrier, and when the barrier's phase has the
parity of its successful polls it has a blocker (`Sched.Blk`). The loader proves the case
`fromLoader o`, the softmax warps the other. -/
def MmaFullLag (p : Params) (L : Launch) (m : Mem0) : Prop :=
  ∀ X, Consistent L kernel Assumptions.all m X → ¬ HasUb X → ∀ g (d : Mma.D) (n : Cls → Nat) r,
    g < L.threads → Prologue.warpIndex L g = 12 →
    Frame.stateAt (thread p L) X g (X.tr g).length = some (some (minj p L g d n)) →
    isPoll d.site = true → RefCounts p L g (d, Mma.rc n) →
    (∃ w, RefQ p L g d.site.ord d.v (Mma.rc n) r w) →
    ∃ before, stateBefore (X.objects (bl L g (pollO r d.site)))
        (X.objects (bl L g (pollO r d.site))).length = some before ∧
      (before.phase % 2 = n (.mma (.acquire (bl L g (pollO r d.site)))) % 2 →
        Sched.Blk (timed p L) X g)

/-- **One producer side of the MMA warp's polls**: `MmaFullLag` at the polls whose producer is the
loader (`b = true`: the Q stages and the K/V ring) or a softmax warp (`b = false`). -/
def MmaLagFrom (b : Bool) (p : Params) (L : Launch) (m : Mem0) : Prop :=
  ∀ X, Consistent L kernel Assumptions.all m X → ¬ HasUb X → ∀ g (d : Mma.D) (n : Cls → Nat) r,
    g < L.threads → Prologue.warpIndex L g = 12 →
    Frame.stateAt (thread p L) X g (X.tr g).length = some (some (minj p L g d n)) →
    isPoll d.site = true → RefCounts p L g (d, Mma.rc n) →
    (∃ w, RefQ p L g d.site.ord d.v (Mma.rc n) r w) → fromLoader (pollO r d.site) = b →
    ∃ before, stateBefore (X.objects (bl L g (pollO r d.site)))
        (X.objects (bl L g (pollO r d.site))).length = some before ∧
      (before.phase % 2 = n (.mma (.acquire (bl L g (pollO r d.site)))) % 2 →
        Sched.Blk (timed p L) X g)

/-- `MmaFullLag` from its loader and softmax sides. -/
theorem mmaFullLag_of (hL : MmaLagFrom true p L m) (hS : MmaLagFrom false p L m) :
    MmaFullLag p L m := by
  intro X hX hub g d n r hg hw hσ hs hR hQ
  cases hb : fromLoader (pollO r d.site)
  · exact hS X hX hub g d n r hg hw hσ hs hR hQ hb
  · exact hL X hX hub g d n r hg hw hσ hs hR hQ hb

/-- **The MMA warp's poll as an `MbarAt`** with a blocker time below the lane's, and the lane's
time at least 2 (`Sched.mbar_at_steps`' premises). -/
theorem mma_mbarAt (hp : Pre p L m) (hR : MmaFullLag p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hub : ¬ HasUb X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 12) {d : Mma.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (minj p L g d n)))
    (hs : isPoll d.site = true) :
    ∃ b, Sched.MbarAt (timed p L) m X g b ∧ b < Sched.threadTime (timed p L) X g ∧
      2 ≤ Sched.threadTime (timed p L) X g := by
  obtain ⟨⟨r, w, hQ, hcm⟩, hF⟩ := mma_ref hp hX hub hg hw hσ
  obtain ⟨before, hstate, hblk⟩ := hR X hX hub g d n r hg hw hσ hs ⟨r, w, hQ, hcm⟩ ⟨w, hQ⟩
  have hok : okPolls (bl L g (pollO r d.site)) (X.tr g) =
      n (.mma (.acquire (bl L g (pollO r d.site)))) := by
    have h := okPolls_eq hσ (bl L g (pollO r d.site))
    rwa [List.take_length] at h
  have hP := mma_pollsOn hp hg hσ hs hQ
  have hB : Sched.PollBlocked (timed p L) X g :=
    Sched.pollBlocked_of hP hstate fun hpar => hblk (by rw [hpar, hok, Nat.add_zero])
  have ht := Mm.time_ge (p := p) (d := d) (n := n)
  have hT : Sched.threadTime (timed p L) X g = Mm.time p d n :=
    Sched.threadTime_of (M := timed p L) hσ
  refine ⟨_, Sched.mbarAt_of hB, ?_, ?_⟩ <;> rw [hT] <;> omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Progress
