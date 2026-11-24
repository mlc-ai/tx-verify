-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.OAcc
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ScoreHandoff

@[expose] public section

/-! # The accumulator is ready for the correction's loads

**OReady** (`OAcc.OReady`): every PV MMA of stage `st` of a tile before `q` is done before a
correction load of credit `q` of the stage. A load of credit `q` is a rescale's or a final
pass's, and each reaches the PV MMAs by its own route (`ORoute`):

* **rescale**: a softmax thread of the stage and CTA, at an event with more than `q` successful
  polls of the S-full object, happens before the load (its statistics `bar.arrive` and the
  correction's `bar.sync`, `Stats.stats_baseCausality`'s chain). The softmax poll of tile `q`
  observes the commit of tile `q` (`SFullHandoff`), which tracks every MMA issued before it, the PV
  MMAs of the tiles before `q` among them (`ScoreFacts.pv_polls`: a PV MMA of tile `u` comes before
  the commit of tile `u + 1`) (`rescale_done`).
* **final**: the correction's earlier poll of its stage's O-full object observes the commit to
  it that follows the PV MMAs of the item (`OFullHandoff`, the O-full analog of SFull: the poll
  with `u` earlier successful polls observes the notification of the commit with `u` earlier
  commits) (`final_done`).

`oready` assembles them. The routes' thread facts (the statistics barrier ordinals against the
tile and credit counts; the O-full commit after the item's PV MMAs) and the O-full attribution
are the premises `ORoute` and `OFullHandoff`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma

noncomputable section

namespace OAcc
open Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Commits of thread `g` to stage `st`'s O-full object of its CTA before its event `i`. -/
def oCommits (L : Launch) (X : Execution) (g st i : Nat) : Nat :=
  ((X.tr g).take i).countP (commitsTo (oFullBar L (ctaOf L g) st))

/-- **The O-full handoff**: a correction poll of its stage's O-full object with `u` earlier
successful polls observes the notification of the MMA thread's commit to the object with `u`
earlier commits. -/
def OFullHandoff (L : Launch) (X : Execution) : Prop :=
  ∀ {h j pc p st : Nat} {acq : Bool} {sc : MbarScope}, h < L.threads → 8 ≤ warpOf L h →
    warpOf L h < 12 → st < 2 →
    X.get (h, j) = some ⟨pc, .wait (oFullBar L (ctaOf L h) st) p true acq sc⟩ →
    ∃ x s rank ws, X.Commit x s ∧ leadCta (ctaOf L x.1) = leadCta (ctaOf L h) ∧
      s.mbar = oFullBar L (ctaOf L x.1) st ∧
      oCommits L X x.1 st x.2 = okPolls (oFullBar L (ctaOf L h) st) ((X.tr h).take j) ∧
      TcCommit.target s rank = some (oFullBar L (ctaOf L h) st) ∧
      rank ∈ X.tcNotified x ∧
      AsyncCopy.WaitObserves X (.async x (.tcNotify rank)) (h, j) (oFullBar L (ctaOf L h) st)
        true ws ∧ ScopesMeet L .cluster x.1 ws h

/-- **The routes of a correction load**: a load of credit `q ≥ 1` of stage `st` follows a softmax
event of the stage and CTA with more than `q` S-full polls (rescale), or an earlier successful
poll of the stage's O-full object whose commit follows every PV MMA of the stage of a tile
before `q` (final). -/
def ORoute (L : Launch) (X : Execution) : Prop :=
  ∀ {h i a st : Nat} {vals : List Value}, h < L.threads → 8 ≤ warpOf L h → warpOf L h < 12 →
    X.TLd (h, i) a vals .s32x32b → (∀ j < vals.length, InO st (tcDataCell32 L h a j)) →
    (∃ g e, g < L.threads ∧ ctaOf L g = ctaOf L h ∧ warpOf L g < 8 ∧ warpOf L g / 4 = st ∧
      e < (X.tr g).length ∧ pArr L X h st i + 1 ≤ sPolls L X g st e ∧ baseCausality L X (g, e) (h,
          i) ) ∨
    (∃ j pc p acq sc, j < i ∧
      X.get (h, j) = some ⟨pc, .wait (oFullBar L (ctaOf L h) st) p true acq sc⟩ ∧
      ∀ x, IsMma X x → (∃ cell, X.MmaCell x cell ∧ InO st cell) →
        ctaOf L x.1 = leadCta (ctaOf L h) → pPolls L X x.1 st x.2 ≤ pArr L X h st i →
          oCommits L X x.1 st x.2 ≤ okPolls (oFullBar L (ctaOf L h) st) ((X.tr h).take j))

/-- The stage of an MMA writing a cell of a stage's accumulator. -/
theorem mma_pv (ht : ScoreFacts L X) {x : EvId} (hx : IsMma X x) {st : Nat}
    (hxc : ∃ cell, X.MmaCell x cell ∧ InO st cell) :
    sCommits L X x.1 st x.2 ≤ pPolls L X x.1 st x.2 := by
  obtain ⟨d, s, acc, mask, hm⟩ := hx
  obtain ⟨cell, hc, hO⟩ := hxc
  exact (ht.pv_polls hm hc hO).2.1

/-- **The rescale route.** A PV MMA of a tile before `q` is done before an event that a softmax
event with more than `q` S-full polls happens before. -/
theorem rescale_done (ht : ScoreFacts L X) (hS : SFullHandoff L X) {g e st q : Nat}
    {f : EvId} (hg : g < L.threads) (hw : warpOf L g < 8) (hst : warpOf L g / 4 = st)
    (he : e < (X.tr g).length) (hq : q + 1 ≤ sPolls L X g st e) (hf : baseCausality L X (g, e) f)
    {x : EvId} (hx : IsMma X x) (hxc : ∃ cell, X.MmaCell x cell ∧ InO st cell)
    (hc : leadCta (ctaOf L x.1) = leadCta (ctaOf L g)) (hu : pPolls L X x.1 st x.2 ≤ q) :
    DoneBefore L X x f := by
  subst hst
  have hsc := mma_pv ht hx hxc
  obtain ⟨j, pc, p, acq, sc, hje, hget, hcnt⟩ :=
    MbarRing.UnitHandoff.exists_poll (X := X) (h := g) (f := e)
      (m := sFullBar L (ctaOf L g) (warpOf L g / 4))
      (c := sCommits L X x.1 (warpOf L g / 4) x.2) (by unfold sPolls at hq; omega)
  obtain ⟨ws, ho, hs⟩ := sfull_observes ht hS hg hw hget hx hc (by unfold sPolls; omega)
  exact .inl ⟨(g, j), ws, ho, hs, (baseCausality_src (f := (g, e)) hget rfl rfl hje he).trans hf⟩

/-- **The final route.** A PV MMA before the commit observed by a correction poll of the O-full
object is done before every later event of the correction thread. -/
theorem final_done (ht : ScoreFacts L X) (hO : OFullHandoff L X) {h j f pc p st : Nat}
    {acq : Bool} {sc : MbarScope} (hh : h < L.threads) (h8 : 8 ≤ warpOf L h)
    (h12 : warpOf L h < 12) (hst : st < 2)
    (hget : X.get (h, j) = some ⟨pc, .wait (oFullBar L (ctaOf L h) st) p true acq sc⟩)
    (hjf : j < f) (hf : f < (X.tr h).length) {x : EvId} (hx : IsMma X x)
    (hc : leadCta (ctaOf L x.1) = leadCta (ctaOf L h))
    (hu : oCommits L X x.1 st x.2 ≤ okPolls (oFullBar L (ctaOf L h) st) ((X.tr h).take j)) :
    DoneBefore L X x (h, f) := by
  obtain ⟨y, s, rank, ws, hcom, hcy, hmbar, hcnt, htgt, hrank, hobs, hsc⟩ :=
    hO hh h8 h12 hst hget
  have hthr : x.1 = y.1 := ht.tc_one hx (.inr ⟨s, hcom⟩) (hc.trans hcy.symm)
  obtain ⟨pcy, hy⟩ := hcom
  have hlt : x.2 < y.2 := by
    obtain ⟨_, _, _, _, _, hxp⟩ := hx.get
    by_contra hle
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with hlt | heq
    · have h1 := countP_take_succ (p := commitsTo (oFullBar L (ctaOf L y.1) st)) hy
        (by simp [commitsTo, hmbar])
      have h2 := countP_take_mono (commitsTo (oFullBar L (ctaOf L y.1) st)) (X.tr y.1)
        (show y.2 + 1 ≤ x.2 by omega)
      unfold oCommits at hcnt hu
      rw [hthr] at hu
      omega
    · have hxy : y = x := Prod.ext hthr.symm heq
      rw [hxy, hxp] at hy
      cases hy
  refine .inl ⟨(h, j), ws, ⟨.async y (.tcNotify rank), oFullBar L (ctaOf L h) st,
    ⟨y, s, rank, rfl, ⟨hthr, hlt, .inl hx, s, pcy, hy⟩, ⟨pcy, hy⟩, htgt, hrank⟩, hobs⟩, ?_,
    baseCausality_src hget rfl rfl hjf hf⟩
  rw [hthr]
  exact hsc

/-- **OReady** from the S-full and O-full handoffs and the routes of the correction loads. -/
theorem oready (ht : ScoreFacts L X) (hS : SFullHandoff L X) (hO : OFullHandoff L X)
    (hR : ORoute L X) : OReady L X := by
  intro h i a st vals x hh h8 h12 hld hcells hx hxc hc hu
  have hst : st < 2 := by
    obtain ⟨d, s, acc, mask, hm⟩ := hx
    obtain ⟨cell, hcl, hO'⟩ := hxc
    obtain ⟨-, -, -, st', hst', h1 | h1⟩ := ht.mma_cells hm
    · have := (h1 cell hcl).1
      unfold InS at this
      unfold InO at hO'
      omega
    · have := (h1 cell hcl).1
      unfold InO at this hO'
      omega
  have hcx : leadCta (ctaOf L x.1) = leadCta (ctaOf L h) := by
    rw [hc, leadCta_idem]
  rcases hR hh h8 h12 hld hcells with ⟨g, e, hg, hcg, hw, hgs, he, hq, hhb⟩ |
      ⟨j, pc, p, acq, sc, hji, hget, hall⟩
  · exact rescale_done ht hS hg hw hgs he hq hhb hx hxc (by rw [hcx, hcg]) hu
  · exact final_done ht hO hh h8 h12 hst hget hji (TLd.lt hld) hx hcx (hall x hx hxc hc hu)

end OAcc

end
end PTX.Kernels.FlashAttn4Fwd.Proof
