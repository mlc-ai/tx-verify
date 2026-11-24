-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsResid2LoaderUse
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsResid3Tmpl
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsPollsOn
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsWaits
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLagsMma
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoaderPollColl
public import Lemmas.Flow.CountFirst

@[expose] public section

/-! # The loader's polls: its start and its warp's elections

`LoaderPollFacts.started`: a thread at a loader poll site is at a role state whose site is not a
register request, so it has made its register request (`Cross.reg_made`), an event of a kind the
prologue does not make and not undefined behaviour.

`LoaderPollFacts.lane`: a thread `g` at a loader poll site has, at its trace's end, the loader's
counts (`end_good`, the site templates being well formed, `Cross.sitesTmplOk`): its successful
polls `P` of the polled empty barrier and its elections are those of its state. A lane `y` of its
warp with at least `copies * (P + 1)` copies on the pair's full barrier `loaderPollBar d` has a
copy with `copies * P` copies before it there. Every copy is an elected loader lane's copy of a
use (`Loader.copy_origin`), and the copies before it number `CopyId.before`, so this copy is in
round `P` of the barrier: a copy of the use `g` waits for. At the copy `y` has made more
elections than `g` at its poll (`Loader.lane_elects`), and it has made no fewer since. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`LoaderPollFacts.started`**. -/
theorem LoaderPollFacts_started (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (_ht : Frame.Tracked (code L) X) :
    ∀ {g : Nat} {d : Loader.D}, g < L.threads →
      St L X g (X.tr g).length = some (some (.inr (.loader d))) → loaderKind d.site = .wait →
        ∃ j ev, X.get (g, j) = some ev ∧ ¬ PreKind ev.kind ∧ ∀ f, ev.kind ≠ .ub f := by
  intro g d hg hσ hk
  have hnr : nextKind (.inr (.loader d)) ≠ .reg := by
    change loaderKind d.site ≠ .reg
    rw [hk]
    decide
  obtain ⟨x, hx, hr⟩ := Cross.reg_made hpre hX hg _ _ hσ hnr
  rw [List.take_length] at hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  refine ⟨j, _, List.getElem?_eq_getElem hj, ?_, ?_⟩
  all_goals
    revert hr
    generalize (X.tr g)[j] = ev
    obtain ⟨pc, kd⟩ := ev
    cases kd <;> simp [Cross.isReg, PreKind]

/-- A loader poll's full barrier has copies. -/
theorem loaderPollBar_copies (d : Loader.D) : 0 < (loaderPollBar d).copies := by
  unfold loaderPollBar
  split <;> simp only [FBar.copies] <;> (try split_ifs) <;> omega

/-- **`LoaderPollFacts.lane`**. -/
theorem LoaderPollFacts_lane (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g y : Nat} {d : Loader.D}, g < L.threads → y < L.threads → SameWarp L g y →
      St L X g (X.tr g).length = some (some (.inr (.loader d))) → loaderKind d.site = .wait →
      (loaderPollBar d).copies *
          (okPolls ((loaderPollBar d).partner.loc L (ctaOf L g)) (X.tr g) + 1) ≤
        (X.tr y).countP (issuesTo ((loaderPollBar d).loc L (pairBase L g))) →
        (X.tr g).countP isElectEv < (X.tr y).countP isElectEv := by
  intro g y d hg hy hsw hσ hk hcnt
  obtain ⟨hJ, hinv⟩ := end_good hpre hX ht (Cross.sitesTmplOk hpre) hg hσ
  change Loader.Counts L g d (X.tr g) at hJ
  change Loader.Inv L g d at hinv
  have hcta : ctaOf L y = ctaOf L g := hsw.1.2.2.symm
  have hT : Work.T L y = Work.T L g := Lag.T_eq_of_pair hpre (by rw [hcta])
  have hr : Loader.r0 L y = Loader.r0 L g := by simp only [Loader.r0, Work.rank, hcta]
  have hpos := loaderPollBar_copies d
  generalize hP : okPolls ((loaderPollBar d).partner.loc L (ctaOf L g)) (X.tr g) = np at hcnt
  -- the copy of `y` with `copies * np` copies before it on the barrier
  have hlt : (loaderPollBar d).copies * np <
      ((X.tr y).take (X.tr y).length).countP
        (issuesTo ((loaderPollBar d).loc L (pairBase L g))) := by
    rw [List.take_length, Nat.mul_succ] at *
    omega
  obtain ⟨k, -, e, hek, hie, hck⟩ := nth_countP hlt
  obtain ⟨pc, kd⟩ := e
  cases kd <;> simp only [issuesTo, Bool.false_eq_true, decide_eq_true_eq] at hie
  rename_i a sp
  obtain ⟨d', -, -, hJ', hi', -, u', j', hs', hci, hcnt'⟩ := Loader.copy_origin hpre hX ht hek
  obtain ⟨hb, -⟩ := FBar.loc_inj (hie.symm.trans hci.mbar)
  rw [hie, hck] at hcnt'
  obtain ⟨-, hj⟩ := Loader.copy_round hs' hJ' hi'
  have hround : Loader.CopyId.round L ⟨u', j', d'.i, d'.t⟩ = np := by
    rw [← (Loader.before_div hj).1, ← hcnt', ← hb, Nat.mul_div_cancel_left _ hpos]
  have hel := Loader.lane_elects (Lag.n_pos hpre) hT hr hinv hJ.ring.1 hk hi' hs' hb.symm hround
    (fun s hs => by rw [← hP, hs]; exact hJ.kvPoll s)
    (fun st hs => by rw [← hP, hs]; exact hJ.qPoll st)
  have hfe : Loader.isElectE = isElectEv := funext isElectE_eq_ev
  have hg' := hJ.elects
  have hy' := hJ'.elects
  rw [hfe] at hg' hy'
  rw [hg']
  exact lt_of_lt_of_le (hy' ▸ hel) ((List.take_sublist _ _).countP_le)

end
end PTX.Kernels.FlashAttn4Fwd.Proof
