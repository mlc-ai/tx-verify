-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.LifetimeReach
public import Kernels.FlashAttn4Fwd.Proof.Protocol.QRingSlot
public import Kernels.FlashAttn4Fwd.Proof.Interface.Async
public import Lemmas.Protocol.PairTmaRing.Order
public import Lemmas.Protocol.UnitHandoff

@[expose] public section

/-! # A tensor load finishes before the CTAs it uses exit

The premise `CopyFinished` of `Safety.no_sharedLifetimeUnsafe` (`copyFinished`): a tensor load's
writes complete before an exit of its destination CTA (its loader's), and its completion before
an exit of its mbarrier's CTA (the pair's even CTA), once that CTA exited.

A copy on full barrier `b` of pair `p` (`RingFacts.issue`) is of a use whose item passed the
loop test (`AsyncFacts.copy_started`). Every lane of the even CTA's MMA warp, the ring's consumer
(`Rings.slot`) among them, made its handshake arrival before an exit of either CTA of the pair
once that CTA exited (`lane_reach`), and by then it had polled `b` for that use
(`ExitFacts.mma_full`). That poll observes the copy's release complete-tx
(`PairTmaRing.copy_observed`), an acquire at cluster scope (`RingFacts.poll`), so the completion
precedes the handshake arrival in base causality (`StageCausedBefore.of_copyRelease`), which reaches
the exit. The writes precede the completion (`AsyncWaits`), and a notified copy wrote every slot
of its box (`EffectValidity`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Lifetime
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier TmemAlloc

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem thread_lt_of_cta (hpre : Pre P L mem0) {h : Nat} (hc : ctaOf L h < L.grid) :
    h < L.threads := by
  unfold ctaOf at hc
  unfold Launch.threads
  rw [hpre.block] at *
  omega

/-- **A copy's completion is caused before what reaches an exit of a CTA of its pair**: the
consumer's handshake arrival. -/
theorem notify_caused (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hr : RingFacts L X) (htm : TmemFacts L X) (ha : AsyncFacts P L X) (hx : ExitFacts P L X)
    (hi : ∀ c, HsInit L X c) (hinit : Rings.RingInit L X) {g k pc al : Nat}
    {s : TensorCopy.Spec} (he : X.get (g, k) = some ⟨pc, .tensorIssue al s⟩) {c : Nat}
    (hex : CtaExited L X c) (hc : c < L.grid) (hcg : c / 2 = ctaOf L g / 2) :
    ∃ o, X.tensor (g, k) = some o ∧ o.spec = s ∧ o.effects.notified = true ∧
      ∃ x ev, StageCausedBefore L X (.async (g, k) (.notify .load)) x ∧ X.get x = some ev ∧
        ReachesExit L X c x := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨b, c0, hbr, hm⟩ := ha.copy_ring he
  obtain ⟨hbf, hc0, -⟩ := hr.issue hg he hm hbr
  set p := ctaOf L g / 2 with hp
  have H := Rings.hyp hpre hX hr htm hinit hbf p
  have hmS : s.mbar = (Rings.slot L X p b).full := by
    rw [hm, hc0]
    rfl
  set h := (Rings.slot L X p b).cons 0 with hhdef
  obtain ⟨hch, hwh⟩ := Rings.leadOf_place (X := X) (cta := 2 * p) hpre (w := 12) (by decide)
  change ctaOf L h = 2 * p at hch
  change warpOf L h = 12 at hwh
  have h2p : 2 * p < L.grid := pair_lt hpre (cta_lt hg) (by omega)
  have hh : h < L.threads := thread_lt_of_cta hpre (by rw [hch]; exact h2p)
  obtain ⟨aa, pca, tx, cnt, haa, hreach⟩ :=
    lane_reach hpre hX htm hx hi hex hc hh hwh (by rw [hch]; omega)
  have hstart := ha.copy_started hg he hm hbf
  have hwork : workOf L h = workOf L g := by
    funext i
    unfold workOf
    rw [clusterOf_eq hpre, clusterOf_eq hpre, hch]
    omega
  have hpoll := hx.mma_full hh hwh (by rw [hch]; omega) haa hbf (by rw [hwork]; exact hstart)
  rw [hch] at hpoll
  obtain ⟨w, pcw, pw, acq, scw, hwa, hwget, hwcnt⟩ := MbarRing.UnitHandoff.exists_poll hpoll
  obtain ⟨-, -, -, -, hok⟩ := hr.poll hh hwget (Rings.isFull_ring hbf)
  obtain ⟨rfl, rfl⟩ := hok rfl
  have hfull : (Rings.slot L X p b).full = b.loc L (2 * p) := rfl
  have hc0p : c0 = 2 * p := by rw [hc0]; rfl
  have hobs := PairTmaRing.copy_observed hX H (b := 0) he hmS (j := w)
    (by rw [hfull]; exact hwget)
    (by rw [hfull, hwcnt, ← hfull, ← hmS, hm, hc0p]; rfl)
  have hsc : ScopesMeet L .cluster g .cluster h :=
    ⟨sameCluster_pair hpre hg hh (by rw [hch]; omega),
      sameCluster_pair hpre hh hg (by rw [hch]; omega)⟩
  have hpo : po X (h, w) (h, aa) :=
    po_of_source_not_access rfl hwa (len_of_get haa) (by rw [hwget]; rfl)
  have hcb := StageCausedBefore.of_copyRelease (Or.inr rfl) hobs hsc hpo
  obtain ⟨n, m, hn, -⟩ := hobs
  obtain ⟨-, o, al', hto, ⟨pco, hti⟩, -, hnot⟩ := hn
  have hspec : o.spec = s := by
    rw [hti] at he
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at he
    exact he.2.2
  exact ⟨o, hto, hspec, hnot, (h, aa), _, hcb, haa, hreach⟩

/-- **CopyFinished**: a tensor load's writes complete before an exit of its destination CTA, and
its completion before an exit of its mbarrier's CTA, once that CTA exited. -/
theorem copyFinished (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hr : RingFacts L X) (hcp : RingCopies P L X) (htm : TmemFacts L X) (ha : AsyncFacts P L X)
    (hx : ExitFacts P L X) (hi : ∀ c, HsInit L X c) (hinit : Rings.RingInit L X) :
    ∀ i a (s : TensorCopy.Spec), X.TensorIssue i a s →
      (∀ x y k, (TensorTransfer.slotAt s.descriptor x y k).isSome →
        CtaExited L X s.sharedBase.cta →
        SharedFinished L kernel asms X (.async i (.write (.load x y k))) s.sharedBase.cta) ∧
      (CtaExited L X s.mbar.cta →
        SharedFinished L kernel asms X (.async i (.notify .load)) s.mbar.cta) := by
  rintro ⟨g, k⟩ al s ⟨pc, he⟩
  have hg := Frame.lt_of_get hX he
  obtain ⟨b, c0, hbr, hm⟩ := ha.copy_ring he
  obtain ⟨hbf, hc0, -⟩ := hr.issue hg he hm hbr
  have hmc : s.mbar.cta = 2 * (ctaOf L g / 2) := by rw [hm, hc0]; rfl
  have hbase : s.sharedBase.cta = ctaOf L g := by
    rw [hcp.copy hg he hm hbf]
    rfl
  have notify : ∀ c, CtaExited L X c → c / 2 = ctaOf L g / 2 →
      ∃ o, X.tensor (g, k) = some o ∧ o.spec = s ∧ o.effects.notified = true ∧
        SharedFinished L kernel asms X (.async (g, k) (.notify .load)) c := by
    intro c hex hcg
    obtain ⟨o, hto, hspec, hnot, x, ev, hcb, hxe, hreach⟩ := notify_caused hpre hX hr htm ha hx hi
      hinit he hex (pair_lt hpre (cta_lt hg) hcg) hcg
    exact ⟨o, hto, hspec, hnot, SharedFinished.of_caused ⟨o, hto, hnot⟩ hcb hxe hreach⟩
  refine ⟨fun x y kk hsl hex => ?_, fun hex => ?_⟩
  · rw [hbase] at hex ⊢
    obtain ⟨o, hto, rfl, hnot, hfin⟩ := notify (ctaOf L g) hex rfl
    obtain ⟨slot, hslot⟩ := Option.isSome_iff_exists.mp hsl
    obtain ⟨v, hv⟩ := (hX.effectValidity.tensor (g, k) o hto).2.1.complete hnot slot
    have hwp : X.AsyncPresent (g, k) (.write (.load x y kk)) := ⟨o, slot, v, hto, hslot, hv⟩
    exact SharedFinished.of_stage (j := (g, k)) (q := .notify .load) hwp
      (.inr ⟨rfl, rfl, rfl, rfl, hwp, o, hto, hnot⟩) hfin
  · rw [hmc] at hex ⊢
    obtain ⟨-, -, -, -, hfin⟩ := notify _ hex (by omega)
    exact hfin

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Lifetime
