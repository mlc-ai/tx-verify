-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.PReadyBlocked
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Base
public import Lemmas.Order.ElectOrdinal

@[expose] public section

/-! # Who blocks the MMA warp at a second P-ready poll

Stage `st`'s second P-ready object of the pair led by CTA `c` (`pReady2Bar`) is a unit object of
its 8 producers (`p2Obj`: producer `a` is the thread of warp `a` that arrives on it, or the warp's
first thread when none does), whose arrivals the MMA warp's polls enable (`p2Reach`). So when its
final phase has the parity of an MMA thread's next poll, the phase is the thread's successful
polls of it, and some producer has made no more arrivals on it than that phase
(`MbarRing.Unit.Obj.reach_short`, when no record faults).

That producer's warp has a thread every election of which returned its own lane (`SelfElected`)
with no more arrivals (`p2_blocked`). All elections use the full mask, so the elections of one warp
return one lane (DEP-WARP-ELECT, `ElectOk.deterministic`), and a thread that went on as the leader
of one of them is the leader of all of them (`selfElected_of_elect`):

* when a thread of the warp arrives, it is the producer, and it arrived after an election that
  returned its lane (`P2Facts.p2_arrive`);
* otherwise no thread of the warp has an arrival on the object; the warp's leader lane, when the
  warp made an election (`ElectOk` names a participant at the leader's lane), and the producer
  else (it made no election), is such a thread. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof
open AsyncCopy MBarrier

noncomputable section

namespace Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- **A thread that went on as the leader of an election is the leader of all its elections.** -/
theorem selfElected_of_elect (H : RouteCtx P L mem0 K A X) {y j pc mask inst : Nat}
    (he : X.Elect (y, j) pc mask inst (laneOf L y)) : SelfElected L X y := by
  intro j' pc' mask' inst' leader he'
  have hm := H.efull he
  have hm' := H.efull he'
  subst hm hm'
  have hy := (H.cons.elect.1 _ _ _ _ _ he).1
  exact H.cons.elect.deterministic he' he ⟨⟨hy, hy, rfl⟩, rfl⟩

/-- **The second P-ready blocker.** When the final phase of stage `st`'s second P-ready object of
the pair led by `c` has the parity of an MMA thread's next poll, the phase is the thread's
successful polls of it, and a softmax thread of the stage in the pair, every election of which
returned its own lane, has made no more arrivals on it than the phase. -/
theorem p2_blocked (H : RouteCtx P L mem0 K A X) {c st h : Nat} (hc : leadCta c = c)
    (hcg : c < L.grid) (hst : st < 2) (hh : mmaIn L c h)
    (hff : ∀ r ∈ X.objects (pReady2Bar L c st), r.fault = none) {before : State}
    (hb : stateBefore (X.objects (pReady2Bar L c st)) (X.objects (pReady2Bar L c st)).length =
      some before)
    (hpar : before.phase % 2 = okPolls (pReady2Bar L c st) (X.tr h) % 2) :
    before.phase = okPolls (pReady2Bar L c st) (X.tr h) ∧
      ∃ y, y < L.threads ∧ leadCta (ctaOf L y) = c ∧ warpOf L y < 8 ∧ warpOf L y / 4 = st ∧
        SelfElected L X y ∧ arrivals (pReady2Bar L c st) (X.tr y) ≤ before.phase := by
  have O := p2Obj H.pre H.cons H.p2 H.tm H.p2init hc hst
  obtain ⟨h1, a, ha⟩ := O.reach_short H.cons (p2Reach H c st hc hst h hh) hff hb
    (Nat.zero_le _) (by simpa using hpar)
  refine ⟨by simpa using h1, ?_⟩
  have hbl := H.pre.block
  have hwarp : ∀ y, InP2Warp L c st a y →
      leadCta (ctaOf L y) = c ∧ warpOf L y < 8 ∧ warpOf L y / 4 = st := by
    rintro y ⟨-, hcy, hwy⟩
    have := a.isLt
    unfold leadCta at hc ⊢
    rw [hcy, hwy]
    omega
  by_cases hA : ∃ g, InP2Warp L c st a g ∧ P2Arrives L X c st g
  · obtain ⟨g, hin, harr⟩ := hA
    have hgp := p2Prod_eq H.cons H.p2 hst hin harr
    obtain ⟨k, pc, tx, cnt, rel, sc, hk⟩ := harr
    obtain ⟨-, -, -, -, -, -, -, -, -, e, pce, inst, -, he⟩ := H.p2.p2_arrive hin.1 hst hk
    obtain ⟨h1, h2, h3⟩ := hwarp g hin
    refine ⟨g, hin.1, h1, h2, h3, selfElected_of_elect H he, ?_⟩
    rw [hgp]
    exact ha
  · -- no thread of the warp arrives on the object
    have hz : ∀ y, InP2Warp L c st a y → arrivals (pReady2Bar L c st) (X.tr y) = 0 := by
      intro y hy
      unfold arrivals
      refine List.countP_eq_zero.mpr fun e he hp => ?_
      obtain ⟨k, hk, hke⟩ := List.getElem_of_mem he
      obtain ⟨pc, kind⟩ := e
      cases kind with
      | arrive m' tx cnt rel sc =>
        have hm : m' = pReady2Bar L c st := by simpa [arrivesOn, sourceArrive] using hp
        subst hm
        exact hA ⟨y, hy, k, pc, tx, cnt, rel, sc, by
          show (X.tr y)[k]? = _
          rw [List.getElem?_eq_getElem hk, hke]⟩
      | _ => simp [arrivesOn, sourceArrive] at hp
    by_cases hE : ∃ y0 j pc mask inst l, InP2Warp L c st a y0 ∧ X.Elect (y0, j) pc mask inst l
    · obtain ⟨y0, j, pc, mask, inst, l, hin, he⟩ := hE
      -- the leader lane made an election of the same instance (`ElectOrd.partner`), which
      -- returned the same lane
      obtain ⟨hy0, -, hmem⟩ := H.cons.elect.1 _ _ _ _ _ he
      have hl32 : l < 32 := hmem.1
      have hy : y0 - laneOf L y0 + l < L.threads := by
        unfold laneOf Launch.threads at *
        rw [hbl] at *
        omega
      have hsw : SameWarp L y0 (y0 - laneOf L y0 + l) := by
        refine ⟨⟨hy0, hy, ?_⟩, ?_⟩ <;> unfold laneOf <;> rw [hbl] <;> omega
      have hly : laneOf L (y0 - laneOf L y0 + l) = l := by
        unfold laneOf
        rw [hbl]
        omega
      obtain ⟨j', pc0, pc', m0, m', inst', l0, l', h0, he'⟩ :=
        ElectOrd.partner H.cons hsw he (by rw [hly]; exact hmem)
      have h1 : X.get (y0, j) = some ⟨pc0, .elect m0 inst' l0⟩ := h0
      have h2 : X.get (y0, j) = some ⟨pc, .elect mask inst l⟩ := he
      rw [h2] at h1
      simp only [Option.some.injEq, Event.mk.injEq, Kind.elect.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      obtain ⟨-, -, rfl, -⟩ := H.cons.elect.2.1 _ _ _ _ _ _ _ _ _ h0 he' hsw
      generalize y0 - laneOf L y0 + l = y at hy hsw hly he'
      have hin' : InP2Warp L c st a y := by
        obtain ⟨⟨-, -, hct⟩, hwp⟩ := hsw
        have e1 : ctaOf L y0 = ctaOf L y := hct
        have e2 : warpOf L y0 = warpOf L y := hwp
        exact ⟨hy, e1 ▸ hin.2.1, e2 ▸ hin.2.2⟩
      rw [← hly] at he'
      obtain ⟨h1, h2, h3⟩ := hwarp y hin'
      exact ⟨y, hy, h1, h2, h3, selfElected_of_elect H he', by rw [hz y hin']; omega⟩
    · have hin : InP2Warp L c st a (p2Prod L X c st a) := by
        obtain ⟨hcy, hwy⟩ := p2Prod_spec (X := X) H.pre (c := c) hst a
        refine ⟨?_, hcy, hwy⟩
        have := a.isLt
        have hgr := H.pre.grid
        unfold leadCta at hc
        unfold p2Prod
        rw [dite_eq_right_of_eq_false (eq_false hA)]
        simp only [Launch.threads]
        rw [hbl]
        omega
      obtain ⟨h1, h2, h3⟩ := hwarp _ hin
      exact ⟨_, hin.1, h1, h2, h3,
        fun j pc mask inst leader he => absurd ⟨_, j, pc, mask, inst, leader, hin, he⟩ hE,
        by rw [hz _ hin]; omega⟩

end Score

end
end PTX.Kernels.FlashAttn4Fwd.Proof
