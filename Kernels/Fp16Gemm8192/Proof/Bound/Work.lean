-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Bound.Loader
public import Kernels.Fp16Gemm8192.Proof.Bound.Mma
public import Kernels.Fp16Gemm8192.Proof.Bound.Scheduler
public import Kernels.Fp16Gemm8192.Proof.Bound.Consumer
public import Lemmas.Kernel.Bound

@[expose] public section

/-! # The work of a thread

A thread's counted events lower the rank of its abstract state (`Ranks.lean`), except a successful
poll at a role's response wait, which polls the thread's CTA's response barrier
(`ThreadFacts.clc_wait_event`) and raises the rank by less than `resetBudget`. So a thread has at
most `2002 + resetBudget` counted events per successful poll of its CTA's response barrier: one
task's work per response it reads (`counted_work`, from `Frame.count_le` with these polls as the
resets). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Bound

open PTX PTX.Flow

set_option linter.unusedSimpArgs false in
/-- A prologue event lowers the rank: the next prologue site comes later, and a role starts below
the prologue. -/
theorem prologue_step {L : Launch} {g : Nat} {p : Prologue.D} {σ' : ThreadD} {e : Event}
    (hn : Prologue.next L g p e = some (some σ')) :
    rank (some σ') + (if e.counts then 1 else 0) ≤ rank (some (.inl p)) := by
  have hc : (if e.counts then 1 else 0) ≤ 1 := by split <;> omega
  suffices h : rank (some σ') + 1 ≤ rank (some (.inl p)) by omega
  obtain ⟨site, w⟩ := p
  cases site
  all_goals simp only [Prologue.next] at hn
  all_goals (repeat' (first | split_ifs at hn | split at hn))
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals simp only [rank, prologueOrd, loaderRank, mmaRank, schedRank, consRank,
    Prologue.afterElect, Prologue.afterInits, Prologue.loaderStart, Prologue.loaderIdle,
    Prologue.mmaStart, Prologue.consStart, Prologue.schedStart]
  all_goals (try split_ifs)
  all_goals (try simp only [prologueOrd])
  all_goals omega

/-- A counted event of a thread lowers the rank of its abstract state, except a successful poll at
a role's response wait (`r`). -/
theorem rank_step {L : Launch} {g : Nat} {d d' : ThreadD} {e : Event} {r : Bool}
    (hinv : (code L g).inv d) (hn : (code L g).next d e = some (some d'))
    (hr : d.AtClcWait → e.counts = true → r = true) :
    rank (some d') + (if e.counts then 1 else 0) ≤
      rank (some d) + (if r then resetBudget else 0) := by
  rcases d with p | (l | m | s | c)
  · have h := prologue_step (L := L) (g := g) (p := p) (e := e) hn
    omega
  · change (Loader.next L g l e).map (Option.map (.inr ∘ .loader)) = some (some d') at hn
    cases hl : Loader.next L g l e with
    | none => rw [hl] at hn; cases hn
    | some o =>
      rw [hl] at hn
      cases o with
      | none => cases hn
      | some l' =>
        simp only [Option.map_some, Option.some.injEq, Function.comp_apply] at hn
        subst hn
        exact loader_step hinv.1 hl hr
  · change (Mma.next L g m e).map (Option.map (.inr ∘ .mma)) = some (some d') at hn
    cases hm : Mma.next L g m e with
    | none => rw [hm] at hn; cases hn
    | some o =>
      rw [hm] at hn
      cases o with
      | none => cases hn
      | some m' =>
        simp only [Option.map_some, Option.some.injEq, Function.comp_apply] at hn
        subst hn
        exact mma_step hinv.1 hm hr
  · change (Scheduler.next L g s e).map (Option.map (.inr ∘ .sched)) = some (some d') at hn
    cases hs : Scheduler.next L g s e with
    | none => rw [hs] at hn; cases hn
    | some o =>
      rw [hs] at hn
      cases o with
      | none => cases hn
      | some s' =>
        simp only [Option.map_some, Option.some.injEq, Function.comp_apply] at hn
        subst hn
        exact sched_step hs hr
  · change (Consumer.next L g c e).map (Option.map (.inr ∘ .cons)) = some (some d') at hn
    cases hc' : Consumer.next L g c e with
    | none => rw [hc'] at hn; cases hn
    | some o =>
      rw [hc'] at hn
      cases o with
      | none => cases hn
      | some c' =>
        simp only [Option.map_some, Option.some.injEq, Function.comp_apply] at hn
        subst hn
        exact cons_step hc' hr

/-- **The work of a thread.** A thread has at most `2002 + resetBudget` counted events per
successful poll of its CTA's response barrier. -/
theorem counted_work {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {g : Nat} (hg : g < L.threads) :
    (X.tr g).countP Event.counts ≤
      2002 + resetBudget * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
  refine (Frame.count_le ht.sound hX hg ht.tracked (fun d => rank (some d))
    (okPoll (clcResp L g)) resetBudget fun k d d' e hk hσ hinv hn =>
      rank_step hinv hn fun hd hc => ?_).trans (by simp [rank, prologueOrd, okPolls])
  obtain ⟨p, ok, acq, sc, hke⟩ := ht.clc_wait_event hg hk hσ hd
  have hok : ok = true := (counts_of_wait hke).symm.trans hc
  subst hok
  obtain ⟨pc, kind⟩ := e
  simp only at hke
  subst hke
  simp [okPoll_wait (m := clcResp L g) rfl]

end PTX.Kernels.Fp16Gemm8192.Proof.Bound
