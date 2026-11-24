-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Base
public import Kernels.FlashAttn4Fwd.Proof.Interface.Rings
public import Kernels.FlashAttn4Fwd.Proof.Interface.Cluster
public import Lemmas.Order.ElectOrdinal

@[expose] public section

/-! # What the thread layer exports for the loader's empty waits and drain

Every lane of the loader (warp 14 of each CTA) polls, before each use of a ring slot, the slot's
empty barrier of its own CTA (`wait u`), and after its items polls the six KV empty barriers and
the Q stage 1 empty barrier once more (`drain k`, `drainQ`). The polled barrier is the partner
of the full barrier `loaderPollBar d`: Q stage 0 or 1 for `q0`, `q1` and the drain's last poll;
for a KV use the slot of the ring's use, `d.s` for the item's last K tile and a trip's K tile,
`d.s + 1` (mod 6) for the V tiles, `d.s + k` (mod 6) for the drain's poll `k` (`d.s` is the slot
of the state's next K use, `Loader.Ledger.ring`). The leader CTA's MMA lane (warp 12 of the
pair's even CTA, the lane its elections returned) commits once per use to its CTA's empty
barrier, multicast to both CTAs; the elected loader lane of each CTA issues the use's copies on
the pair's full barrier after its poll.

The facts, of single threads' runs (the loader's run invariant `Loader.Counts`, the MMA warp's
`Mma.Counts`, and the site tables of `Thread/Roles.lean`):

* `poll`: a loader thread at a poll site is a lane of warp 14 whose next event polls that empty
  barrier, with the parity of its successful polls of it plus one (`FBar.pollOffset`);
* `started`: it has made an event of a kind the prologue does not make (its `setmaxnreg`);
* `lane`: a lane of its warp that has issued the copies of one use more on the slot than the
  thread's successful polls of the empty barrier (so it has passed the thread's poll and the
  elections of that use's copies) has made more elections than the thread;
* `lag`: the pair's MMA lane that every election of its returned its own lane, with fewer
  commits to its CTA's empty barrier of the slot than the thread's successful polls of the
  empty barrier, has not exited, and its state is earlier than the thread's. Its last missing
  commit is that of the use the thread waits for (one use, or six KV uses, earlier): in the band
  M of the use's consuming slot of an earlier item, or of an item before the tail for the drain
  (`Time.qEmpty_lt`, `Time.kvEmpty_lt`, `Time.lt_tail`); the MMA lane exits after the
  commits of all the cluster's uses. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

/-- The full barrier whose partner empty barrier the loader's poll at state `d` polls: the Q
stage of a Q use or of the drain's last poll, the KV slot of a K or V use or of the drain's poll
`k`. -/
def loaderPollBar (d : Loader.D) : FBar :=
  match d.site with
  | .wait .q0 => .qFull 0
  | .wait .q1 | .drainQ => .qFull 1
  | .wait .k0 | .wait .k => .kvFull ⟨d.s % 6, Nat.mod_lt _ (by decide)⟩
  | .wait .v0 | .wait .v => .kvFull ⟨(d.s + 1) % 6, Nat.mod_lt _ (by decide)⟩
  | .drain k => .kvFull ⟨(d.s + k.val) % 6, Nat.mod_lt _ (by decide)⟩
  | _ => .qFull 0

/-- The thread layer's facts for the loader's empty waits and drain. -/
structure LoaderPollFacts (L : Launch) (X : Execution) : Prop where
  /-- A loader thread at a poll site is a lane of warp 14 whose next event polls its CTA's empty
  barrier partnered with `loaderPollBar d`, with the parity of its successful polls of that
  barrier plus one. -/
  poll : ∀ {g : Nat} {d : Loader.D}, g < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.loader d))) → loaderKind d.site = .wait →
      warpOf L g = 14 ∧ PollsOn L X g ((loaderPollBar d).partner.loc L (ctaOf L g)) 1
  /-- A loader thread at a poll site has made an event of a kind the prologue does not make,
  and which is not undefined behaviour (its `setmaxnreg`). -/
  started : ∀ {g : Nat} {d : Loader.D}, g < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.loader d))) → loaderKind d.site = .wait →
      ∃ j ev, X.get (g, j) = some ev ∧ ¬ PreKind ev.kind ∧ ∀ f, ev.kind ≠ .ub f
  /-- A lane `y` of the warp of a loader thread `g` at a poll site, whose copies on the pair's
  full barrier `loaderPollBar d` are at least that barrier's copies per use times one more than
  `g`'s successful polls of the empty barrier, has made more elections than `g`. -/
  lane : ∀ {g y : Nat} {d : Loader.D}, g < L.threads → y < L.threads → SameWarp L g y →
    St L X g (X.tr g).length = some (some (.inr (.loader d))) → loaderKind d.site = .wait →
    (loaderPollBar d).copies *
        (okPolls ((loaderPollBar d).partner.loc L (ctaOf L g)) (X.tr g) + 1) ≤
      (X.tr y).countP (issuesTo ((loaderPollBar d).loc L (pairBase L g))) →
      (X.tr g).countP isElectEv < (X.tr y).countP isElectEv
  /-- A thread `y` of warp 12 of the pair's even CTA, every election of which returned its own
  lane, with fewer commits to its CTA's empty barrier partnered with `loaderPollBar d` than a
  loader thread `g` at a poll site has successful polls of its own CTA's one, lags `g`. -/
  lag : ∀ {g y : Nat} {d : Loader.D}, g < L.threads → y < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.loader d))) → loaderKind d.site = .wait →
    warpOf L y = 12 → ctaOf L y = pairBase L g → SelfElected L X y →
    (X.tr y).countP (commitsTo ((loaderPollBar d).partner.loc L (ctaOf L y))) + 1 ≤
      okPolls ((loaderPollBar d).partner.loc L (ctaOf L g)) (X.tr g) →
      Lags L X y g (.inr (.loader d))

end
end PTX.Kernels.FlashAttn4Fwd.Proof
