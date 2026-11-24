-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface
public import Lemmas.Flow.PollRounds

@[expose] public section

/-! # What the thread layer exports for the lanes of a warp

All lanes of a warp run one role on one work schedule, so what a lane does at a poll or at a
warp-collective `tcgen05` instruction is a function of its warp and of how far it has come. The
fields state this per thread, at the states of its machine (`St`), with functions of the warp
(`warpKey`: the CTA and the warp in it):

* **Polls.** The object and the parity of a poll are a function of the warp, the position and the
  poll's round (`pollRound`: the successful polls at that position before it) (`poll_round`).
  The MMA warp's KV polls compute their ring slot from the item and the trip, so one position
  polls different slots in different rounds; the round fixes the item and the trip.
* **Rounds.** Two distinct lanes of a warp polling at one position followed by a poll branch (a
  guarded `bra.uni` on the poll's predicate, `Kernel.pollBranch`) in different rounds, when they
  poll different objects, are ordered in the execution-dependency order (`poll_order`, a pairwise
  fact: `PollRoundsMet`; EXT-DEPENDENCY-ORDER): in `hb`, or, at the loader's and the MMA warp's
  loop poll branches (`rdvSites`), through a full-mask `elect.sync` or `shfl.sync` instance
  between them. Every poll branch is selected by `Assumptions.pollAgree` (ASM-POLL-AGREE), so polls
  of one object need no order. The MMA warp's inner P-ready polls are followed by a plain `@p bra`,
  which ERR-NONUNIFORM-GUARD does not constrain.
* **Collectives.** The `n`-th warp-collective `tcgen05` event of a lane is at a source position
  and has operands (`tcStatic`: without the loaded or stored values) that are a function of the
  warp and `n` (`tc_seq`); a lane performs fewer than a number of them fixed by its warp, and has
  performed at least that many when it exits (`tc_count`).

`poll_round`, `tc_seq` and `tc_count` are facts of each thread's own events, for the role run
invariants (the per-site event counts of `Mma.Counts`, `Loader`, `Store`, `Softmax`,
`Correction`). `poll_order` relates two lanes and is not a fact of one thread's run:

* the softmax warps (0-7) execute `bar.warp.sync` between the rounds of their loop, which orders
  the lanes (`WarpBarSync`, MEM-BASE-CAUSALITY) when an event of the earlier lane lies between its
  poll and the barrier, and one of the later lane between the barrier and its poll;
* the MMA warp (12) and the loader warp (14) run on all 32 lanes, and between two rounds of a poll
  a lane that the elections do not return executes only `elect.sync`, `shfl.sync` and local
  instructions. Their collectives order the lanes not in `hb` but in the execution-dependency
  order (`DepStep`, DEP-ORDER), so at their loop poll branches (`rdvSites`) the rounds are met
  through a full-mask collective. `PollRoundsMet.of_collectives`
  (`Lemmas.Flow.PollRendezvous`) reduces this to facts of each lane's own events: after its poll of
  a round, and before each poll of a later round, a lane performs the collective (`CollAt`: its
  `n`-th shuffle, or a full-mask election with `n` elections before it) of an ordinal fixed by the
  warp, the position and the round;
* the correction warps (8-11) arrive on mbarriers on every lane; an order between their rounds
  runs through the phases of other roles, some completed by `tcgen05.commit`, whose arrivals are
  not thread releases (`MbarRelease`);
* the store warp (13) spins on all 32 lanes at its two staged waits, each on one barrier per CTA.
  A lane whose poll of one item's phase fails and a lane whose poll of the next item's phase
  succeeds are ordered by no chain (the next phase's arrivals do not reach the lane still
  spinning); its polls are of one object at each position, so they need no order. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof

noncomputable section

/-- The warp of a thread in the grid: its CTA and its warp in the CTA. -/
def warpKey (L : Launch) (g : Nat) : Nat × Nat := (ctaOf L g, warpOf L g)

/-- Two threads of a warp have one key. -/
theorem warpKey_eq {L : Launch} {g h : Nat} (hw : SameWarp L g h) : warpKey L g = warpKey L h := by
  obtain ⟨⟨-, -, hc⟩, hwp⟩ := hw
  simp only [warpKey, ctaOf, warpOf, hc, hwp]

/-- The poll branches of the loops of the loader warp (14: pcs 262-423) and of the MMA warp
(12: pcs 596-1058), at which the proof meets the rounds of a poll through the warp collectives
between them. Between two rounds of such a poll a lane that the elections do not return executes
only `elect.sync`, `shfl.sync`, polls and local instructions; the branches after the polls executed
once per thread (the loader's tail and the MMA warp's handshake) are not listed. -/
def rdvSites : List Nat :=
  [262, 292, 322, 352, 383, 423, 596, 602, 671, 752, 755, 809, 877, 1004, 1007, 1058]

/-- The position is one of `rdvSites`. -/
def rdvPos (pc : Nat) : Bool := rdvSites.contains pc

/-- The thread layer's facts about the lanes of a warp. -/
structure WarpSyncFacts (L : Launch) (X : Execution) : Prop where
  /-- The object and the parity of a poll are a function of the warp, the position and the
  poll's round. -/
  poll_round : ∃ R : Nat × Nat → Nat → Nat → Loc × Nat,
    ∀ {g k pc : Nat} {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope} {d : ThreadD},
      g < L.threads → St L X g k = some (some d) →
      X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
      R (warpKey L g) pc (pollRound pc ((X.tr g).take k)) = (m, p % 2)
  /-- Two distinct lanes of a warp polling at one position followed by a poll branch in different
  rounds, when they poll different objects, are ordered: in `hb`, or through a full-mask collective
  at `rdvSites`. -/
  poll_order : PollRoundsMet L kernel Assumptions.all X
  /-- The source position and the operands of the `n`-th warp-collective `tcgen05` event of a
  lane are a function of the warp and `n`. -/
  tc_seq : ∃ F : Nat × Nat → Nat → Nat × TcKind,
    ∀ {g k pc n : Nat} {kd : TcKind} {d : ThreadD}, g < L.threads →
      St L X g k = some (some d) → X.get (g, k) = some ⟨pc, .tc kd⟩ → X.TcK (g, k) n →
      F (warpKey L g) n = (pc, tcStatic kd)
  /-- A lane performs fewer warp-collective `tcgen05` events than a number fixed by its warp,
  and has performed at least that many when it exits. -/
  tc_count : ∃ T : Nat × Nat → Nat,
    (∀ {g k n : Nat} {d : ThreadD}, g < L.threads → St L X g k = some (some d) →
      X.TcK (g, k) n → n < T (warpKey L g)) ∧
    (∀ {g k pc : Nat} {d : ThreadD}, g < L.threads → St L X g k = some (some d) →
      X.get (g, k) = some ⟨pc, .exit⟩ → T (warpKey L g) ≤ ((X.tr g).take k).countP isTcColl)

end
end PTX.Kernels.FlashAttn4Fwd.Proof
