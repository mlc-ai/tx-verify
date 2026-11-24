-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsOrigin
public import Kernels.FlashAttn4Fwd.Proof.Thread.ElectFull
public import Kernels.FlashAttn4Fwd.Proof.Interface.WarpSync
public import Kernels.FlashAttn4Fwd.Proof.Interface.Stats
public import Lemmas.Flow.PollRendezvous
public import Lemmas.Flow.WarpAgree
public import Lemmas.Flow.CountFirst
public import Lemmas.Protocol.NamedBarWarp

@[expose] public section

/-! # The lanes of a warp (`WarpSyncFacts`, `StatsFacts.bar_warp`)

The fields of `WarpSyncFacts` and `StatsFacts.bar_warp` speak of the lanes of a warp through
functions of the warp (`warpKey`) or through a prefix order of their barrier events. Each is
reduced here to a pairwise fact of two lanes of one warp, which the role packages prove from
their run invariants (the lanes of a warp run one role on one schedule, so their states at
equal counts agree):

* `poll_round` from `PollAgree`: two lanes polling at one position in one round poll one object
  with one parity (`exists_fun_of_agree`);
* `tc_seq` from `TcAgree`: the `n`-th warp-collective `tcgen05` events of two lanes are at one
  position with one static part;
* `tc_count` from `TcExitAgree` and `TcExitAbove`: lanes exit with one count of collective
  events, above every ordinal of a collective event of the warp (`exists_bound_of_exit`);
* `bar_warp` from `BarAgree`: the `n`-th named-barrier events of two lanes are equal
  (`prefix_of_agree`);
* `poll_order` from `PollColl` and `PollRest` by `PollRoundsMet.of_collectives`, with the
  elections' facts of every consistent execution (`ElectOk`, and `ElectOrdinal` from the full
  masks, `elect_full`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Two launched threads with one warp key are in one warp. -/
theorem sameWarp_of_key {g h : Nat} (hg : g < L.threads) (hh : h < L.threads)
    (hk : warpKey L g = warpKey L h) : SameWarp L g h := by
  simp only [warpKey, ctaOf, warpOf, Prod.mk.injEq] at hk
  exact ⟨⟨hg, hh, hk.1⟩, hk.2⟩

/-! ### Polls -/

/-- Two lanes of a warp polling at one position in one round poll one object with one parity
(per role: the state at a poll is fixed by the position and the round). -/
def PollAgree (L : Launch) (X : Execution) : Prop :=
  ∀ {g h k k' pc p p' : Nat} {m m' : Loc} {ok ok' acq acq' : Bool} {sc sc' : MbarScope}
    {d d' : ThreadD}, SameWarp L g h → St L X g k = some (some d) →
    St L X h k' = some (some d') → X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
    X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩ →
    pollRound pc ((X.tr g).take k) = pollRound pc ((X.tr h).take k') → m = m' ∧ p % 2 = p' % 2

/-- **The object and the parity of a poll are a function of the warp, the position and the
poll's round.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.WarpSyncFacts_poll_round
    (_hpre : Pre P L mem0) (_hX : Consistent L kernel asms mem0 X)
    (_ht : Frame.Tracked (code L) X) (hagree : PollAgree L X) :
    ∃ R : Nat × Nat → Nat → Nat → Loc × Nat,
      ∀ {g k pc : Nat} {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope} {d : ThreadD},
        g < L.threads → St L X g k = some (some d) →
        X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
        R (warpKey L g) pc (pollRound pc ((X.tr g).take k)) = (m, p % 2) := by
  have : Inhabited (Loc × Nat) := ⟨(⟨.shared, 0, 0⟩, 0)⟩
  obtain ⟨F, hF⟩ := exists_fun_of_agree (warpKey L)
    (fun g (a : Nat × Nat) (b : Loc × Nat) => ∃ k m p ok acq sc d, g < L.threads ∧
      St L X g k = some (some d) ∧ X.get (g, k) = some ⟨a.1, .wait m p ok acq sc⟩ ∧
      pollRound a.1 ((X.tr g).take k) = a.2 ∧ b = (m, p % 2))
    (by
      rintro g h ⟨pc, r⟩ b b' hk ⟨k, m, p, ok, acq, sc, d, hg, hσ, he, hr, rfl⟩
        ⟨k', m', p', ok', acq', sc', d', hh, hσ', he', hr', rfl⟩
      obtain ⟨h1, h2⟩ := hagree (sameWarp_of_key hg hh hk) hσ hσ' he he' (hr.trans hr'.symm)
      rw [h1, h2])
  exact ⟨fun key pc r => F key (pc, r), fun {g k pc m p ok acq sc d} hg hσ he =>
    hF ⟨k, m, p, ok, acq, sc, d, hg, hσ, he, rfl, rfl⟩⟩

/-- The rendezvous positions' collectives (`rdvSites`, EXT-DEPENDENCY-ORDER): an ordinal fixed by
the warp, the position and the round, performed by each lane after its poll of the round when
another lane of its warp polls the position in a later round, and before each poll of a later
round (per role: the MMA and loader warps' elections and shuffles). -/
def PollColl (L : Launch) (X : Execution) : Prop :=
  ∃ C : Nat × Nat → Nat → Nat → Bool × Nat,
    (∀ {g h k k' pc m m' p p' ok ok' acq acq' sc sc'}, g < L.threads → h < L.threads →
      g ≠ h → SameWarp L g h → X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
      X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩ →
      rdvPos (pc + 1) = true →
      pollRound pc ((X.tr g).take k) < pollRound pc ((X.tr h).take k') →
      ∃ a, k < a ∧ CollAt X g a (C (warpKey L g) pc (pollRound pc ((X.tr g).take k)))) ∧
    (∀ {g k pc m p ok acq sc r}, g < L.threads →
      X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
      rdvPos (pc + 1) = true →
      r < pollRound pc ((X.tr g).take k) → ∃ b, b < k ∧ CollAt X g b (C (warpKey L g) pc r))

/-- At the other positions followed by a poll branch (a guarded `bra.uni` on the poll's predicate;
the MMA warp's inner P-ready polls are followed by a plain `@p bra`), two lanes' polls of
different rounds are ordered in the execution-dependency order (`PollBefore`), except polls of
one object at the poll branches `Assumptions.pollAgree` selects (per role: the softmax warps'
`bar.warp.sync`, and the phases the correction warps wait on; the store warp's polls are all
exempt, `Cross.PollRest_store`). -/
def PollRest (L : Launch) (X : Execution) : Prop :=
  ∀ g h k k' pc m m' p p' ok ok' acq acq' sc sc', g < L.threads → h < L.threads →
    g ≠ h → SameWarp L g h → X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
    X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩ → kernel.pollBranch (pc + 1) = true →
    rdvPos (pc + 1) = false →
    (m ≠ m' ∨ Assumptions.all.any (·.uniPoll (pc + 1)) = false) →
    pollRound pc ((X.tr g).take k) < pollRound pc ((X.tr h).take k') →
    PollBefore L kernel X (g, k) (h, k')

/-- **Two distinct lanes of a warp polling at one position in different rounds are met**, when
they poll different objects or at a branch no assumption selects. -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.WarpSyncFacts_poll_order
    (_hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (_ht : Frame.Tracked (code L) X) (hc : PollColl L X) (hr : PollRest L X) :
    PollRoundsMet L kernel Assumptions.all X := by
  obtain ⟨C, hafter, hbefore⟩ := hc
  exact PollRoundsMet.of_collectives hX
    (electOrdinal hX (ElectMutual.of_full fun he => elect_full hX he)) rdvPos (warpKey L)
    warpKey_eq C hafter hbefore hr

/-! ### Warp-collective `tcgen05` events -/

/-- The `n`-th warp-collective `tcgen05` events of two lanes of a warp are at one position with
one static part (per role: the lanes run the same sites with warp-uniform operands). -/
def TcAgree (L : Launch) (X : Execution) : Prop :=
  ∀ {g h k k' pc pc' n : Nat} {kd kd' : TcKind} {d d' : ThreadD}, SameWarp L g h →
    St L X g k = some (some d) → St L X h k' = some (some d') →
    X.get (g, k) = some ⟨pc, .tc kd⟩ → X.get (h, k') = some ⟨pc', .tc kd'⟩ →
    X.TcK (g, k) n → X.TcK (h, k') n → pc = pc' ∧ tcStatic kd = tcStatic kd'

/-- **The position and the operands of the `n`-th warp-collective `tcgen05` event of a lane are a
function of the warp and `n`.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.WarpSyncFacts_tc_seq
    (_hpre : Pre P L mem0) (_hX : Consistent L kernel asms mem0 X)
    (_ht : Frame.Tracked (code L) X) (hagree : TcAgree L X) :
    ∃ F : Nat × Nat → Nat → Nat × TcKind,
      ∀ {g k pc n : Nat} {kd : TcKind} {d : ThreadD}, g < L.threads →
        St L X g k = some (some d) → X.get (g, k) = some ⟨pc, .tc kd⟩ → X.TcK (g, k) n →
        F (warpKey L g) n = (pc, tcStatic kd) := by
  have : Inhabited (Nat × TcKind) := ⟨(0, .waitLd)⟩
  obtain ⟨F, hF⟩ := exists_fun_of_agree (warpKey L)
    (fun g (n : Nat) (b : Nat × TcKind) => ∃ k pc kd d, g < L.threads ∧
      St L X g k = some (some d) ∧ X.get (g, k) = some ⟨pc, .tc kd⟩ ∧ X.TcK (g, k) n ∧
      b = (pc, tcStatic kd))
    (by
      rintro g h n b b' hk ⟨k, pc, kd, d, hg, hσ, he, hK, rfl⟩
        ⟨k', pc', kd', d', hh, hσ', he', hK', rfl⟩
      obtain ⟨h1, h2⟩ := hagree (sameWarp_of_key hg hh hk) hσ hσ' he he' hK hK'
      rw [h1, h2])
  exact ⟨F, fun {g k pc n kd d} hg hσ he hK => hF ⟨k, pc, kd, d, hg, hσ, he, hK, rfl⟩⟩

/-- Two lanes of a warp exit with one count of warp-collective `tcgen05` events. -/
def TcExitAgree (L : Launch) (X : Execution) : Prop :=
  ∀ {g h k k' pc pc' : Nat} {d d' : ThreadD}, SameWarp L g h →
    St L X g k = some (some d) → St L X h k' = some (some d') →
    X.get (g, k) = some ⟨pc, .exit⟩ → X.get (h, k') = some ⟨pc', .exit⟩ →
    ((X.tr g).take k).countP isTcColl = ((X.tr h).take k').countP isTcColl

/-- A lane at its exit has made more warp-collective `tcgen05` events than the ordinal of any
such event of a lane of its warp. -/
def TcExitAbove (L : Launch) (X : Execution) : Prop :=
  ∀ {g h k k' pc n : Nat} {d d' : ThreadD}, SameWarp L g h →
    St L X g k = some (some d) → St L X h k' = some (some d') →
    X.get (h, k') = some ⟨pc, .exit⟩ → X.TcK (g, k) n →
    n < ((X.tr h).take k').countP isTcColl

/-- **A lane performs fewer warp-collective `tcgen05` events than a number fixed by its warp, and
has performed at least that many when it exits.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.WarpSyncFacts_tc_count
    (_hpre : Pre P L mem0) (_hX : Consistent L kernel asms mem0 X)
    (_ht : Frame.Tracked (code L) X) (hagree : TcExitAgree L X) (habove : TcExitAbove L X) :
    ∃ T : Nat × Nat → Nat,
      (∀ {g k n : Nat} {d : ThreadD}, g < L.threads → St L X g k = some (some d) →
        X.TcK (g, k) n → n < T (warpKey L g)) ∧
      (∀ {g k pc : Nat} {d : ThreadD}, g < L.threads → St L X g k = some (some d) →
        X.get (g, k) = some ⟨pc, .exit⟩ →
        T (warpKey L g) ≤ ((X.tr g).take k).countP isTcColl) := by
  obtain ⟨T, h1, h2⟩ := exists_bound_of_exit (warpKey L) L.threads
    (fun g o => ∃ k d, St L X g k = some (some d) ∧ X.TcK (g, k) o)
    (fun g => (X.tr g).length + 1)
    (by
      rintro g o - ⟨k, d, -, ⟨ev, he, -⟩, hc⟩
      have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
      have : ((X.tr g).take k).countP isTcColl ≤ k :=
        (List.countP_le_length).trans (by simp)
      simp only at hc
      omega)
    (fun g c => ∃ k pc d, St L X g k = some (some d) ∧ X.get (g, k) = some ⟨pc, .exit⟩ ∧
      c = ((X.tr g).take k).countP isTcColl)
    (by
      rintro g h c c' hg hh hk ⟨k, pc, d, hσ, he, rfl⟩ ⟨k', pc', d', hσ', he', rfl⟩
      exact hagree (sameWarp_of_key hg hh hk) hσ hσ' he he')
    (by
      rintro g h c o hg hh hk ⟨k', pc, d', hσ', he', rfl⟩ ⟨k, d, hσ, hK⟩
      exact habove (sameWarp_of_key hg hh hk) hσ hσ' he' hK)
  exact ⟨T, fun {g k n d} hg hσ hK => h1 hg ⟨k, d, hσ, hK⟩,
    fun {g k pc d} hg hσ he => h2 hg ⟨k, pc, d, hσ, he, rfl⟩⟩

/-! ### Named-barrier events -/

/-- Two lanes of a warp make the same named-barrier event as their `n`-th (per role: the
softmax, correction and MMA lanes of a warp pass the same barrier sites with warp-uniform
ids). -/
def BarAgree (L : Launch) (X : Execution) : Prop :=
  ∀ {g h i j : Nat} {x y : Event}, SameWarp L g h → X.get (g, i) = some x →
    X.get (h, j) = some y → Execution.isBar x = true → Execution.isBar y = true →
    ((X.tr g).take i).countP Execution.isBar = ((X.tr h).take j).countP Execution.isBar → x = y

/-- The `n`-th entry of a filtered list is an entry with `n` selected entries before it. -/
theorem filter_entry {α : Type} {p : α → Bool} {l : List α} {n : Nat} {x : α}
    (h : (l.filter p)[n]? = some x) :
    ∃ i, l[i]? = some x ∧ p x = true ∧ (l.take i).countP p = n := by
  have hn : n < (l.take l.length).countP p := by
    rw [List.take_length, List.countP_eq_length_filter]
    exact (List.getElem?_eq_some_iff.mp h).1
  obtain ⟨b, -, y, hy, hp, hc⟩ := nth_countP hn
  have hf := NamedBar.getElem_filter_countP hy hp
  rw [hc, h] at hf
  cases hf
  exact ⟨b, hy, hp, hc⟩

/-- **The lanes of a warp make the same named-barrier events in the same order.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.StatsFacts_bar_warp
    (_hpre : Pre P L mem0) (_hX : Consistent L kernel asms mem0 X)
    (_ht : Frame.Tracked (code L) X) (hagree : BarAgree L X) : NamedBar.WarpBars L X := by
  intro g h hw
  refine prefix_of_agree fun n x y hx hy => ?_
  obtain ⟨i, hi, hpi, hci⟩ := filter_entry hx
  obtain ⟨j, hj, hpj, hcj⟩ := filter_entry hy
  exact hagree hw hi hj hpi hpj (hci.trans hcj.symm)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
