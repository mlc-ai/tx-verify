-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStore
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsFire
public import Lemmas.Flow.PollRounds

@[expose] public section

/-! # The store warp's parts of the cross-warp premises

* `Cross.NoRegReentry_store`: the store warp's successor is never its `setmaxnreg` site.
* `Cross.pollAgree_store`: two lanes of the store warp polling at one position in one round poll
  one object with one parity. A store lane's polls at `wait st` are exactly its polls of stage
  `st`'s staged barrier (`store_round_eq`), one per earlier item (`Store.Counts.staged`), so the
  round is the item, whose parity the poll carries (`Store.Ev`).
* `Cross.PollRest_store`: the store warp needs no order between its lanes' polls. Its polls are
  at the two staged waits, each of one staged barrier per CTA (`store_poll_state`), and the
  branches after them are exempt for polls of one mbarrier (`Assumptions.pollAgree`,
  ASM-POLL-AGREE; `store_wait_pollAgree`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The store warp's successor is never its `setmaxnreg` site. -/
theorem Store.next_not_setMaxReg {g : Nat} {d d' : Store.D} {e : Event}
    (hn : Store.next L g d e = some (some d')) : d'.site ≠ .setMaxReg := by
  obtain ⟨site, i⟩ := d
  cases site <;> simp only [Store.next] at hn
  all_goals (repeat' split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals (try unfold Store.itemEnd)
  all_goals (try split_ifs)
  all_goals simp

/-- **`Cross.NoRegReentry`, store part.** -/
theorem Cross.NoRegReentry_store {g : Nat} {d : Store.D} {r' : Role} {e : Event}
    (h : (code L g).next (.inr (.store d)) e = some (some (.inr r'))) :
    nextKind (.inr r') ≠ .reg := by
  obtain ⟨r'', hr, hk⟩ := code_next_inr h
  cases hr
  cases r' with
  | store d' =>
    have hn := next_role (fun _ _ h => Role.store.inj h) h
    have hs := Store.next_not_setMaxReg hn
    obtain ⟨site', i'⟩ := d'
    simp only at hs
    cases site' <;> simp_all [nextKind, storeKind]
  | _ => simp [Role.kind] at hk

/-- A store lane's polls at `wait st` are its polls of stage `st`'s staged barrier. -/
theorem store_round_eq (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k : Nat} (hg : g < L.threads) (hw : warpOf L g = 13)
    (st : Fin 2) :
    pollRound (Store.Site.wait st).pc ((X.tr g).take k) =
      okPolls (Store.stagedAt L g st) ((X.tr g).take k) := by
  unfold pollRound okPolls
  apply List.countP_congr
  intro x hx
  obtain ⟨j, -, hj⟩ := get_of_mem_take hx
  obtain ⟨xpc, xk⟩ := x
  cases xk
  case wait m' p' ok' acq' sc' =>
    cases ok'
    · simp [okPollAt, okPoll, sourceWaitSuccess]
    · obtain ⟨d, -, -, -, hev, hpc⟩ := Facts.store_ev' hpre hX ht hg hw hj id nofun
      obtain ⟨st0, hs, rfl, -⟩ := Store.ev_wait hev
      rw [hs] at hpc
      subst hpc
      simp only [okPollAt, okPoll, sourceWaitSuccess, beq_iff_eq, decide_eq_true_eq]
      rcases Store.fin2_cases st with rfl | rfl <;> rcases Store.fin2_cases st0 with rfl | rfl <;>
        simp [Store.stagedAt, Store.Site.pc]
  all_goals simp [okPollAt, okPoll, sourceWaitSuccess]

/-- A store lane's poll is at the wait of a stage `st`, of stage `st`'s staged barrier, with the
parity of the item `i`, which is the number of its earlier successful polls of that barrier. -/
theorem store_poll_state (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {y j pcy py : Nat} {my : Loc} {oky acqy : Bool}
    {scy : MbarScope} (hy : y < L.threads) (hwy : warpOf L y = 13)
    (hey : X.get (y, j) = some ⟨pcy, .wait my py oky acqy scy⟩) :
    ∃ st : Fin 2, ∃ i, pcy = (Store.Site.wait st).pc ∧ my = Store.stagedAt L y st ∧
      py = i % 2 ∧ okPolls (Store.stagedAt L y st) ((X.tr y).take j) = i := by
  obtain ⟨⟨site, i⟩, -, hJ, -, hev, hpc⟩ := Facts.store_ev' hpre hX ht hy hwy hey id nofun
  obtain ⟨st0, rfl, rfl, rfl, -⟩ := Store.ev_wait hev
  refine ⟨st0, i, hpc, rfl, rfl, ?_⟩
  rw [hJ.staged st0]
  simp [Store.done, Store.before]

/-- The branches after the store warp's waits are selected by `Assumptions.pollAgree`. -/
theorem store_wait_pollAgree (st : Fin 2) :
    Assumptions.all.any (·.uniPoll ((Store.Site.wait st).pc + 1)) = true := by
  revert st
  decide

/-- **`PollRest`, store part**: two lanes of the store warp polling at one position poll one
object, at a branch exempt for polls of one mbarrier, so the premise of `PollRest` that asks for
an order fails. -/
theorem Cross.PollRest_store (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g h k k' pc p p' : Nat} {m m' : Loc}
    {ok ok' acq acq' : Bool} {sc sc' : MbarScope} (hw : warpOf L g = 13)
    (hsw : SameWarp L g h) (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩)
    (he' : X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩) :
    ¬ (m ≠ m' ∨ Assumptions.all.any (·.uniPoll (pc + 1)) = false) := by
  obtain ⟨⟨hg, hh, hcta⟩, hwarp⟩ := hsw
  have hwh : warpOf L h = 13 := by simp only [warpOf] at hw ⊢; omega
  obtain ⟨st, -, hpc, rfl, -⟩ := store_poll_state hpre hX ht hg hw he
  obtain ⟨st', -, hpc', rfl, -⟩ := store_poll_state hpre hX ht hh hwh he'
  have hst : st = st' := by
    rw [hpc] at hpc'
    rcases Store.fin2_cases st with rfl | rfl <;> rcases Store.fin2_cases st' with rfl | rfl <;>
      first | rfl | (exfalso; revert hpc'; decide)
  subst hst
  rintro (hm | hs)
  · exact hm (by simp only [Store.stagedAt, hcta])
  · rw [hpc, store_wait_pollAgree] at hs
    cases hs

/-- **`PollAgree`, store part**: two lanes of the store warp polling at one position in one
round poll one object with one parity. -/
theorem Cross.pollAgree_store (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g h k k' pc p p' : Nat} {m m' : Loc}
    {ok ok' acq acq' : Bool} {sc sc' : MbarScope} (hw : warpOf L g = 13)
    (hsw : SameWarp L g h) (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩)
    (he' : X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩)
    (hr : pollRound pc ((X.tr g).take k) = pollRound pc ((X.tr h).take k')) :
    m = m' ∧ p % 2 = p' % 2 := by
  obtain ⟨⟨hg, hh, hcta⟩, hwarp⟩ := hsw
  have hwh : warpOf L h = 13 := by simp only [warpOf] at hw ⊢; omega
  have hctah : h / L.block = g / L.block := hcta.symm
  obtain ⟨st, i, hpc, rfl, rfl, hc1⟩ := store_poll_state hpre hX ht hg hw he
  obtain ⟨st', i', hpc', rfl, rfl, hc2⟩ := store_poll_state hpre hX ht hh hwh he'
  have hst : st = st' := by
    rw [hpc] at hpc'
    rcases Store.fin2_cases st with rfl | rfl <;> rcases Store.fin2_cases st' with rfl | rfl <;>
      first | rfl | (exfalso; revert hpc'; decide)
  subst hst
  rw [hpc, store_round_eq hpre hX ht hg hw, hc1] at hr
  rw [store_round_eq hpre hX ht hh hwh, hc2] at hr
  subst hr
  refine ⟨?_, rfl⟩
  simp only [Store.stagedAt, hctah]

end
end PTX.Kernels.FlashAttn4Fwd.Proof
