-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Softmax.Soft.Induct
import Kernels.InklingRelDecode.Proof.Softmax.PollStep
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.ValueFollow
import Kernels.InklingRelDecode.Proof.Common.ValueThread
import Kernels.InklingRelDecode.Proof.Softmax.Export.AlphaOperand

/-! # The accumulator load and the rescale store of a round

In a thread, the accumulator load of pc 2260 of a round (the rounds are counted by the successful
polls of pc 1257) is the only one of its round, and it comes before the rescale store of pc 2328 of
the round, which exists only after a load of the round. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Control Data Soft

variable {Q : Params} {L : Launch} {g : Nat}

/-- The sites of a round strictly before the accumulator load. -/
private def beforeLd : Site → Bool
  | .shfl4 | .ldS | .waitLd | .shfl5 | .shfl6 | .waitO | .bar22 | .shfl7 | .shfl8 | .shfl9
  | .shfl10 | .store10 | .bar23 | .ldL | .shfl11 | .shfl12 => true
  | _ => false

private def upToLd (s : Site) : Bool := beforeLd s || decide (s = .ldO)

private theorem next_dom {e : Entry} {d dn : Control.D} {ev : Event}
    (step : Control.next e L g d ev = some (some dn)) (h : upToLd dn.site = true) :
    beforeLd d.site = true ∨ (d.site = .waitS ∧ ∃ a b c s, ev.kind = .wait a b true c s) := by
  obtain ⟨s, i, v⟩ := d
  have loop : ∀ t i, upToLd (loopSite e t i) = false := by
    intro t i
    unfold loopSite
    split <;> first | decide | (split <;> decide)
  cases s <;> simp only [Control.next, advance] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals dsimp only at h ⊢
  all_goals first
    | (rw [loop] at h; exact absurd h (by decide))
    | exact absurd h (by decide)
    | (left; decide)
    | (right; rename_i hk hok; subst hok; exact ⟨rfl, _, _, _, _, hk⟩)
    | exact absurd h (by simp [upToLd, beforeLd])

private theorem before_pc (s : Site) (h : beforeLd s = true) : s.pc ≠ 1257 ∧ s.pc ≠ 2260 := by
  cases s <;> simp_all [beforeLd, Site.pc]

private theorem site_2260 (s : Site) (h : s.pc = 2260) : s = .ldO := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- No accumulator load of the round before the sites up to its own. -/
private def NoLd (X : Execution) (g k : Nat) (y : Data.D) : Prop :=
  upToLd y.c.site = true → ∀ kl < k, ∀ kd, X.get (g, kl) = some ⟨2260, kd⟩ →
    pollRound 1257 ((X.tr g).take kl) < pollRound 1257 ((X.tr g).take k)

private theorem no_ld {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) :
    ∀ k, k ≤ (X.tr g).length → ∀ s, Frame.stateAt (threadD Q L) X g k = some (some s) →
      Frame.NoUbBefore X g k → ∀ w ent y n, s = softDState w ent y n → NoLd X g k y := by
  refine soft_induct hp hX (fun k y => NoLd X g k y) (fun _ h => ?_) ?_
  · exact absurd h (by decide)
  intro k ent old y e he hu pc hn IH
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  intro hy kl hkl kd hget
  rcases next_dom hnc hy with hb | ⟨hw, a, b, c, s, hk⟩
  · obtain ⟨n1, n2⟩ := before_pc _ hb
    have hold : upToLd old.c.site = true := by simp [upToLd, hb]
    rw [poll_same he (by rw [pc]; exact n1)]
    by_cases hlk : kl = k
    · subst hlk
      rw [he] at hget
      obtain rfl := Option.some.inj hget
      exact absurd pc (by simpa using n2.symm)
    · exact IH hold kl (by omega) kd hget
  · have p1257 : e.pc = 1257 := by rw [pc, hw]; rfl
    have step := poll_step he
    have ok : okPollAt 1257 e = true := by
      obtain ⟨p, kk⟩ := e
      change p = 1257 at p1257
      change kk = _ at hk
      subst hk p1257
      simp [okPollAt]
    simp only [ok, ite_true] at step
    rw [step]
    by_cases hlk : kl = k
    · subst hlk
      rw [he] at hget
      obtain rfl := Option.some.inj hget
      exact absurd p1257 (by simp)
    · have := poll_mono (X := X) (g := g) (show kl ≤ k by omega)
      omega

public theorem ld_rounds {m : Mem0} {X : Execution} {k a : Nat} {ov : List Value}
    {sh : TcShape} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (g, k) = some ⟨2260, .tc (.ld a ov sh)⟩) :
    ∀ kl < k, ∀ kd, X.get (g, kl) = some ⟨2260, kd⟩ →
      pollRound 1257 ((X.tr g).take kl) < pollRound 1257 ((X.tr g).take k) := by
  have clean : ∀ f, (Event.mk 2260 (.tc (.ld a ov sh))).kind ≠ .ub f := fun _ => nofun
  obtain ⟨w, ent, d, n, hsc, atpc⟩ := at_site hp hX get clean (by show 574 < 2260; omega)
    (by show 2260 < 2331; omega)
  obtain ⟨s, hs, hse⟩ := value_state hsc
  obtain ⟨y, hy, rfl⟩ := softD_shape hse
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nub := Frame.noUbBefore_of_get hX get
  have site : y.c.site = .ldO := site_2260 _ (by
    have := atpc
    rw [← hy] at this
    exact this.symm)
  exact no_ld hp hX k len _ hs nub w ent y n rfl (by rw [site]; decide)

/-- **Every rescale store has the accumulator load of its round before it.** -/
public theorem rescale_ld {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) :
    ∀ t k a vals sh, X.get (t, k) = some ⟨2328, .tc (.st a vals sh)⟩ →
      ∃ kl < k, ∃ a' ov sh', X.get (t, kl) = some ⟨2260, .tc (.ld a' ov sh')⟩ ∧
        pollRound 1257 ((X.tr t).take kl) = pollRound 1257 ((X.tr t).take k) :=
  fun _ _ _ _ _ get => rescale_round hp hX get

/-- **Every accumulator load of a round precedes every rescale store of the round.** -/
public theorem ld_before_st {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) :
    ∀ t kl k a' ov sh' a vals sh, X.get (t, kl) = some ⟨2260, .tc (.ld a' ov sh')⟩ →
      X.get (t, k) = some ⟨2328, .tc (.st a vals sh)⟩ →
      pollRound 1257 ((X.tr t).take kl) = pollRound 1257 ((X.tr t).take k) → kl < k := by
  intro t kl k a' ov sh' a vals sh hl hs eq
  obtain ⟨j, hj, a2, ov2, sh2, hjg, rj⟩ := rescale_round hp hX hs
  rcases Nat.lt_trichotomy kl j with h | h | h
  · have := ld_rounds hp hX hjg kl h _ hl
    omega
  · omega
  · have := ld_rounds hp hX hl j h _ hjg
    omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
