-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Kernels.TmlFa4Fwd.Proof.Mma.Open
public import Lemmas.Flow.PollSynced
import Kernels.TmlFa4Fwd.Proof.Lib.EvPc
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
import Kernels.TmlFa4Fwd.Proof.Progress.MmaPoll
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.SiteUse
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Sites
import Lemmas.Flow.PollRounds
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Two lanes of the MMA warp polling at one position -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- Two poll sites at one position have one place and poll one barrier in a round. -/
private theorem poll_site {s s' : Mma.Site} (h : Progress.isPoll s = true)
    (h' : Progress.isPoll s' = true) (hpc : s.pc = s'.pc) :
    s'.ord = s.ord ∧ ∀ r, Progress.pollO r s = Progress.pollO r s' := by
  cases s <;> simp only [Progress.isPoll, Bool.false_eq_true] at h <;>
    cases s' <;> simp only [Progress.isPoll, Bool.false_eq_true] at h'
  case wt.wt k k' =>
    have : ∀ a b : Fin 10, (Mma.Site.wt a).pc = (Mma.Site.wt b).pc → a = b := by decide
    obtain rfl := this k k' hpc
    exact ⟨rfl, fun _ => rfl⟩
  case mw.mw b ld b' ld' =>
    have : ∀ a b : Fin 4, (Mma.Site.mw a true).pc = (Mma.Site.mw b true).pc → a = b := by decide
    obtain rfl := this b b' hpc
    exact ⟨rfl, fun _ => rfl⟩
  case wt.mw k b ld =>
    have : ∀ (a : Fin 10) (b : Fin 4), (Mma.Site.wt a).pc ≠ (Mma.Site.mw b true).pc := by decide
    exact absurd hpc (this k b)
  case mw.wt b ld k =>
    have : ∀ (a : Fin 10) (b : Fin 4), (Mma.Site.wt a).pc ≠ (Mma.Site.mw b true).pc := by decide
    exact absurd hpc.symm (this k b)

/-- **Two lanes of the MMA warp polling at one position poll one barrier, or are ordered** (by
their elections). -/
theorem mma_poll_same (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 12) (hs : SameWarp L g h)
    {k k' pc par par' : Nat} {l l' : Loc} {ok acq ok' acq' : Bool} {sc sc' : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait l par ok acq sc⟩)
    (he' : X.get (h, k') = some ⟨pc, .wait l' par' ok' acq' sc'⟩) :
    l = l' ∨ PollBefore L kernel X (g, k) (h, k') ∨ PollBefore L kernel X (h, k') (g, k) := by
  have hwe : Prologue.warpIndex L g = Prologue.warpIndex L h := hs.2
  have key : ∀ {x j l par ok acq sc}, Prologue.warpIndex L x = 12 →
      X.get (x, j) = some ⟨pc, .wait l par ok acq sc⟩ → ∃ d n r w,
        Frame.stateAt (thread p L) X x j = some (some (Mma.minj p L x d n)) ∧
        Mma.RefQ p L x d.site.ord d.v (Mma.rc n) r w ∧ pc = d.site.pc ∧
        Progress.isPoll d.site = true ∧ l = Mma.bl L x (Progress.pollO r d.site) := by
    intro x j l par ok acq sc hx he
    rcases Mma.open_ev hp hX hFw hx he (fun f h => by cases h) with
      ⟨s, n, -, -, -, hi, hev⟩ | ⟨s, n, -, -, -, hev⟩ | ⟨d, n, hσ, h0, hR, -, hev⟩
    · exfalso
      obtain ⟨c, hc⟩ := start_mbar (l := l) hev hi.2 rfl
      cases hc
    · exfalso
      rcases hev with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
    · obtain ⟨r, w, hQ, -⟩ := (hR h0).1
      have hpc := ev_pc hp hX he hσ
      cases mma_use (l := l) hev rfl with
      | poll ok' hs hl hk =>
        exact ⟨d, n, r, w, hσ, hQ, hpc, hs, hl.trans (Progress.par_eq hp hQ hs).1⟩
      | commit _ _ _ hk => cases hk
  obtain ⟨d, n, r, w, hσ, hQ, hpc, hp1, hl⟩ := key hw he
  obtain ⟨d', n', r', w', hσ', hQ', hpc', hp2, hl'⟩ := key (hwe ▸ hw) he'
  have hsite := poll_site hp1 hp2 (hpc.symm.trans hpc')
  have hl1 := (List.getElem?_eq_some_iff.mp he).1
  have hl2 := (List.getElem?_eq_some_iff.mp he').1
  rcases Nat.lt_trichotomy (Mma.electAll d.site.ord r) (Mma.electAll d'.site.ord r') with
    hlt | heq | hlt
  · exact .inr (.inl (mma_meet hX hs hσ hQ hσ' hQ' he rfl hl2 hlt))
  · left
    rw [hsite.1] at heq
    rw [hl, hl', hsite.2, mma_round_eq heq]
    simp only [Mma.bl, hs.1.2.2]
  · exact .inr (.inr (mma_meet hX (SameWarp.symm hs) hσ' hQ' hσ hQ he' rfl hl1 hlt))

end
end PTX.Kernels.TmlFa4Fwd.Proof
