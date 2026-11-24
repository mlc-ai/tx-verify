-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.LifetimeReach
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OAccReady
public import Kernels.FlashAttn4Fwd.Proof.Interface.Async
public import Lemmas.Protocol.UnitHandoff

@[expose] public section

/-! # An MMA finishes before the CTAs of its operands exit

The premise `MmaFinished` of `Safety.no_sharedLifetimeUnsafe` (`mmaFinished`): an MMA's
completion precedes an exit of each CTA holding its operands, once that CTA exited.

An MMA of stage `st` comes before the stage's O-full commit of its item, an item that passed the
loop test (`ExitFacts.mma_ofull`). The operands are in a CTA `c` of the MMA thread's pair
(`AsyncFacts.mma_pair`); once `c` exited, so did its correction thread of warp 8, lane 0, which
polled the stage's O-full object of `c` for every such item (`ExitFacts.corr_exit`). Its poll for
the MMA's item observes the commit of that item (`OAcc.OFullHandoff`), which tracks the MMA (one
thread issues the pair's MMAs and commits, `ScoreFacts.tc_one`): the poll observes the MMA's
completion (`ofull_observes`). The poll is a canonical spin, so the thread's exit resumes from it
(`Resumes.of_spin`), and the completion precedes the exit in the dependency order (`DepStep`,
`CompletedBefore.of_observesMma`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Lifetime
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier TcMma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **OFull.observes**: a correction poll of a stage's O-full object with `u` earlier successful
polls observes the completion of every MMA of its pair issued before `u + 1` commits to the
object. -/
theorem ofull_observes (ht : ScoreFacts L X) (hO : OAcc.OFullHandoff L X) {h j pc p st : Nat}
    {acq : Bool} {sc : MbarScope} (hh : h < L.threads) (h8 : 8 ≤ warpOf L h)
    (h12 : warpOf L h < 12) (hst : st < 2)
    (hget : X.get (h, j) = some ⟨pc, .wait (oFullBar L (ctaOf L h) st) p true acq sc⟩)
    {i : EvId} (hi : IsMma X i) (hc : leadCta (ctaOf L i.1) = leadCta (ctaOf L h))
    (hu : OAcc.oCommits L X i.1 st i.2 ≤ okPolls (oFullBar L (ctaOf L h) st) ((X.tr h).take j)) :
    ∃ ws, AsyncCopy.AsyncObserved X i .mmaDone (h, j) true ws := by
  obtain ⟨x, s, rank, ws, hcom, hcx, hmbar, hcnt, htgt, hrank, hobs, -⟩ :=
    hO hh h8 h12 hst hget
  have hthr : i.1 = x.1 := ht.tc_one hi (.inr ⟨s, hcom⟩) (hc.trans hcx.symm)
  obtain ⟨pcx, hx⟩ := hcom
  have hlt : i.2 < x.2 := by
    obtain ⟨_, _, _, _, _, hip⟩ := hi.get
    by_contra hle
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with hlt | heq
    · have h1 := countP_take_succ (p := commitsTo (oFullBar L (ctaOf L x.1) st)) hx
        (by simp [commitsTo, hmbar])
      have h2 := countP_take_mono (commitsTo (oFullBar L (ctaOf L x.1) st))
        (X.tr x.1) (show x.2 + 1 ≤ i.2 by omega)
      unfold OAcc.oCommits at hcnt hu
      rw [hthr] at hu
      omega
    · have hxi : x = i := Prod.ext hthr.symm heq
      rw [hxi, hip] at hx
      cases hx
  exact ⟨ws, .async x (.tcNotify rank), oFullBar L (ctaOf L h) st,
    ⟨x, s, rank, rfl, ⟨hthr, hlt, .inl hi, s, pcx, hx⟩, ⟨pcx, hx⟩, htgt, hrank⟩, hobs⟩

/-- Thread `c · block + 32 w` is lane 0 of warp `w < 16` of CTA `c`. -/
theorem lane_place (hpre : Pre P L mem0) {c w : Nat} (hc : c < L.grid) (hw : w < 16) :
    c * L.block + 32 * w < L.threads ∧ ctaOf L (c * L.block + 32 * w) = c ∧
      warpOf L (c * L.block + 32 * w) = w := by
  unfold ctaOf warpOf Launch.threads
  rw [hpre.block] at *
  refine ⟨by nlinarith, by omega, by omega⟩

/-- Two threads of one pair handle the same work items. -/
theorem workOf_pair (hpre : Pre P L mem0) {g h : Nat} (hc : ctaOf L h / 2 = ctaOf L g / 2) :
    workOf L h = workOf L g := by
  funext i
  unfold workOf
  rw [clusterOf_eq hpre, clusterOf_eq hpre, hc]

/-- **MmaFinished**: an MMA's completion precedes an exit of each CTA holding its operands, once
that CTA exited. -/
theorem mmaFinished (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : ScoreFacts L X) (ha : AsyncFacts P L X) (hx : ExitFacts P L X)
    (hO : OAcc.OFullHandoff L X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, kernel.CanonicalSpin pc exit) :
    ∀ i d (s : TcMma.OperandSpec) acc mask (c : Nat), X.MmaIssue i d s acc mask →
      (c = s.lowCta ∨ c = s.highCta) → CtaExited L X c →
        SharedFinished L kernel asms X (.async i .mmaDone) c := by
  rintro ⟨g, k⟩ d s acc mask c hmi hlh hex
  obtain ⟨hg, -, -, -⟩ := ht.mma_cells hmi
  obtain ⟨h1, h2⟩ := ha.mma_pair hmi
  have hcg : c / 2 = ctaOf L g / 2 := by rcases hlh with rfl | rfl <;> assumption
  have hc : c < L.grid := pair_lt hpre (cta_lt hg) hcg
  obtain ⟨hh, hch, hwh⟩ := lane_place hpre hc (w := 8) (by decide)
  set h := c * L.block + 32 * 8
  obtain ⟨kh, pch, hkh⟩ := exit_of_exited hex hh hch
  obtain ⟨st, hst, hwork⟩ := hx.mma_ofull hmi
  have hu := hx.corr_exit hh (by omega) (by omega) hkh hst
    (u := OAcc.oCommits L X g st k) (by
      rw [workOf_pair (g := g) hpre (by rw [hch]; exact hcg)]
      exact hwork)
  obtain ⟨j, pcj, pj, acq, sc, hjk, hget, hcnt⟩ :=
    MbarRing.UnitHandoff.exists_poll (m := oFullBar L (ctaOf L h) st) hu
  obtain ⟨ws, hobs⟩ := ofull_observes ht hO hh (by omega) (by omega) hst hget
    (i := (g, k)) ⟨d, s, acc, mask, hmi⟩ (by unfold leadCta; rw [hch]; omega) (by rw [hcnt])
  obtain ⟨ex, hsp⟩ := hspin _ _ _ _ _ _ hget
  have hres : Resumes kernel X (h, j) (h, kh) :=
    Resumes.of_spin hget hsp rfl hjk (len_of_get hkh)
  obtain ⟨hd, hcb⟩ := CompletedBefore.of_observesMma hX.tcCommit hobs
    (.single (DepStep.of_resumes L hres))
  exact SharedFinished.of_completedBefore (finish := (h, kh)) hd ⟨hh, hch, pch, hkh⟩ hcb

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Lifetime
