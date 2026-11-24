-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.QRingSlot
public import Kernels.FlashAttn4Fwd.Proof.Protocol.InitFirst
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tc
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Base
public import Lemmas.Protocol.PairTmaRing.Waiter
public import Lemmas.Protocol.MbarPending
public import Lemmas.Kernel.Obligation
public import Lemmas.Order.ElectOrdinal

@[expose] public section

/-! # Who blocks a loader lane at a ring empty barrier

A loader lane `g` (any lane of warp 14, not only the elected one) polls its CTA's empty barrier
of a Q stage or KV slot, the partner of full barrier `b`, of the slot `Rings.slot L X c b` of its
pair `c`, as producer `a` (its CTA's rank in the pair). With `K` its successful polls of that
barrier, when the barrier's final phase has the parity of `K + 1` (`loaderBlocked`, from
`PairTmaRing.waiter_short`):

* the pair's MMA lane (`leadOf` of warp 12 of the even CTA) has made fewer than `K` commits to
  its CTA's empty barrier of the slot;
* or a commit has an undelivered target (`Descent.Obl L X .commit`);
* or the elected loader lane of `g`'s CTA has issued the copies of `K + 1` uses on the slot.

Every commit is the MMA lane's multicast over the pair with mask 3 (`TcFacts.commit_spec`), so
it notifies the empty barrier of both CTAs. The barrier has a state once a thread of its pair
has made an event after the start (`ring_state`: warp 0 initialized it, `InitFirst`). The MMA
lane is self-elected (`leadOf_selfElected`: the lane an election returned is the warp's lead
thread; every election names the full mask, a premise `elect_full` discharges). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof AsyncCopy MBarrier

noncomputable section

namespace Rings

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A thread of a launched CTA is a launched thread. -/
theorem lt_threads (hpre : Pre P L mem0) {y : Nat} (h : ctaOf L y < L.grid) : y < L.threads := by
  have hb : 0 < L.block := by rw [hpre.block]; decide
  unfold ctaOf at h
  unfold Launch.threads
  exact (Nat.div_lt_iff_lt_mul hb).mp h

/-- The lead thread of a warp of a launched CTA is launched. -/
theorem leadOf_lt (hpre : Pre P L mem0) {cta w : Nat} (hw : w < 16) (hc : cta < L.grid) :
    leadOf L X cta w < L.threads :=
  lt_threads hpre (by rw [(leadOf_place hpre hw).1]; exact hc)

/-- **The lead thread of a warp is self-elected**: an election it made returned a lane whose
thread made an election of the same instance (`ElectOrd.partner`, a filled need of the
election), which returned the same lane (full masks), so that thread is the warp's lead
thread. -/
theorem leadOf_selfElected (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hfull : ∀ {e : EvId} {pc mask inst l : Nat}, X.Elect e pc mask inst l → mask = 4294967295)
    {cta w : Nat} (hw : w < 16) : SelfElected L X (leadOf L X cta w) := by
  intro j pc mask inst leader he
  have hmask := hfull he
  subst hmask
  have hb := hpre.block
  obtain ⟨hy, -, hlm⟩ := hX.elect.1 _ _ _ _ _ he
  have hl32 : leader < 32 := hlm.1
  generalize hyd : leadOf L X cta w = y at he hy ⊢
  have hht : y - laneOf L y + leader < L.threads := by
    unfold laneOf Launch.threads at *
    rw [hb] at *
    omega
  have hsw : SameWarp L y (y - laneOf L y + leader) := by
    refine ⟨⟨hy, hht, ?_⟩, ?_⟩ <;> unfold laneOf <;> rw [hb] <;> omega
  have hlh : laneOf L (y - laneOf L y + leader) = leader := by
    unfold laneOf
    rw [hb]
    omega
  obtain ⟨x, pc0, pc', m0, m', inst', l0, l', -, hx⟩ :=
    ElectOrd.partner hX hsw he (by rw [hlh]; exact hlm)
  have hm' := hfull hx
  subst hm'
  have hll : leader = l' := hX.elect.2.2 _ _ _ _ _ _ _ _ _ he hx hsw
  have hl' : l' = laneOf L (y - laneOf L y + leader) := by rw [hlh]; exact hll.symm
  have hlead : LeadAt L X (y - laneOf L y + leader) (x + 1) :=
    ⟨x, Nat.lt_succ_self _, pc', inst', hl' ▸ hx⟩
  have heq := leadOf_eq hX hht hlead
  obtain ⟨hc0, hw0⟩ := leadOf_place (X := X) hpre (cta := cta) hw
  rw [hyd] at hc0 hw0
  obtain ⟨⟨-, -, hc⟩, hwp⟩ := hsw
  have hch : ctaOf L (y - laneOf L y + leader) = cta := by rw [← hc0]; exact hc.symm
  have hwh : warpOf L (y - laneOf L y + leader) = w := by rw [← hw0]; exact hwp.symm
  rw [hch, hwh, hyd] at heq
  rw [heq, hlh]

/-- **A ring barrier has a state** once a thread of its pair has made an event after the
start. -/
theorem ring_state (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (hi : InitFacts L X) {b : FBar} {cta : Nat}
    (hni : NoInval (X.objects (b.loc L cta))) {g j : Nat} {ev : Event}
    (he : X.get (g, j) = some ev) (hk : ¬ PreKind ev.kind) (hub : ∀ f, ev.kind ≠ .ub f)
    (hcl : ctaOf L g / 2 = cta / 2) :
    ∃ before, stateBefore (X.objects (b.loc L cta)) (X.objects (b.loc L cta)).length =
      some before := by
  obtain ⟨⟨h, k⟩, pc, n, hget⟩ := InitFirst.init_exists hpre hX hc hi b he hk hub hcl
  have hact : objectAction X X.async (b.loc L cta) (.thread (h, k)) = some (.init n) := by
    simp [objectAction, hget]
  obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 _).2.2 _ _ hact
  have hra := ((hX.tma.2.2.1 _).2.1 r hr).1
  rw [hid, hact, Option.some.injEq] at hra
  obtain ⟨-, -, rfl⟩ := InitFirst.init_of_site hc (Frame.lt_of_get hX hget) hget
  exact stateBefore_length_some (X.objects_checked hX _) hni hr hra.symm
    (InitFirst.count_valid b)

/-- The slot of `g`'s pair: its producer of rank `ctaOf g % 2` is the lead loader thread of
`g`'s CTA, and that rank's empty barrier is `g`'s CTA's. -/
theorem slot_rank {b : FBar} (g : Nat) :
    (slot L X (ctaOf L g / 2) b).prod ⟨ctaOf L g % 2, Nat.mod_lt _ (by decide)⟩ =
        leadOf L X (ctaOf L g) 14 ∧
      (slot L X (ctaOf L g / 2) b).empty ⟨ctaOf L g % 2, Nat.mod_lt _ (by decide)⟩ =
        b.partner.loc L (ctaOf L g) := by
  have h : 2 * (ctaOf L g / 2) + ctaOf L g % 2 = ctaOf L g := by omega
  refine ⟨?_, ?_⟩ <;> simp [slot, h]

/-- **The commits notify both CTAs' empty barriers**: a commit of the slot's consumer to its
CTA's empty barrier targets the empty barrier of rank `a`. -/
theorem commit_target (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (htc : TcFacts L X) {b : FBar} {c : Nat} (a : Fin 2) {j pc : Nat} {sp : TcCommit.Spec}
    (he : X.get ((slot L X c b).cons 0, j) = some ⟨pc, .tc (.commit sp)⟩)
    (hm : sp.mbar = (slot L X c b).empty 0) :
    TcCommit.target sp (PairTmaRing.rankOf a) = some ((slot L X c b).empty a) := by
  have hcons : ctaOf L (leadOf L X (2 * c) 12) = 2 * c := (leadOf_place hpre (by decide)).1
  obtain ⟨-, -, b', -, rfl⟩ := htc.commit_spec (Frame.lt_of_get hX he) he
  simp only [slot, FBar.loc, Loc.mk.injEq] at hm ⊢
  rw [hcons] at hm ⊢
  obtain ⟨-, -, hoff⟩ := hm
  obtain ⟨a, ha⟩ := a
  simp only [TcCommit.target, PairTmaRing.rankOf]
  rw [hoff]
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> simp

/-- **Who blocks a loader lane at a ring empty barrier.** A thread `g` whose CTA's empty barrier
partnered with full barrier `b` ends in a phase of the parity of `K + 1`, `K` its successful polls
of that barrier: the pair's MMA lane made fewer than `K` commits to its CTA's empty barrier of
the slot, or a commit has an undelivered target, or the lead loader thread of `g`'s CTA issued
the copies of `K + 1` uses on the slot. -/
def LoaderBlocked (L : Launch) (X : Execution) : Prop :=
  ∀ {b : FBar} {g : Nat} {before : State}, b.isFull → g < L.threads →
    stateBefore (X.objects (b.partner.loc L (ctaOf L g)))
      (X.objects (b.partner.loc L (ctaOf L g))).length = some before →
    before.phase % 2 = (okPolls (b.partner.loc L (ctaOf L g)) (X.tr g) + 1) % 2 →
    (X.tr (leadOf L X (pairBase L g) 12)).countP
        (commitsTo (b.partner.loc L (pairBase L g))) + 1 ≤
        okPolls (b.partner.loc L (ctaOf L g)) (X.tr g) ∨
      Descent.Obl L X .commit ∨
      b.copies * (okPolls (b.partner.loc L (ctaOf L g)) (X.tr g) + 1) ≤
        (X.tr (leadOf L X (ctaOf L g) 14)).countP (issuesTo (b.loc L (pairBase L g)))

theorem loaderBlocked (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : RingFacts L X) (htm : TmemFacts L X) (hinit : RingInit L X) (htc : TcFacts L X) :
    LoaderBlocked L X := by
  intro b g before hb hg hstate hpar
  have H := hyp hpre hX ht htm hinit hb (ctaOf L g / 2)
  obtain ⟨hprod, hempty⟩ := slot_rank (X := X) (b := b) g
  rw [← hempty] at hstate hpar
  rcases PairTmaRing.waiter_short hX H hstate hpar
      (fun he hm => commit_target hpre hX htc _ he hm) with h | h | h
  · left
    rw [← hempty]
    exact h
  · exact .inr (.inl h)
  · right; right
    rw [← hempty, ← hprod]
    exact h

end Rings

end
end PTX.Kernels.FlashAttn4Fwd.Proof
