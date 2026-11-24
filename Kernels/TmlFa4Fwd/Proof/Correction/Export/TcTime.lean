-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.TcCount
public import Kernels.TmlFa4Fwd.Proof.Correction.Order
public import Kernels.TmlFa4Fwd.Proof.Progress.Time
import Kernels.TmlFa4Fwd.Proof.Correction.Export.BarLag
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TcAgree
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TcEv
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TcOrder
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TcStates
import Kernels.TmlFa4Fwd.Proof.Common.Coll
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Correction.RefCases
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Pos
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Kernels.TmlFa4Fwd.Proof.Lib.ThreadTime
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Tc
import Lemmas.Kernel.Safety.Schedule
import Lemmas.Kernel.Source.WarpColl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The correction warps' warp-collective `tcgen05` events in the time table

The lanes of a warp receive one ballot at each rescale stage (`rb_agree`), so a lane with no
more
warp-collective `tcgen05` events than a lane of its warp before one is no later than it
(`corr_tcLag`); such an event leads to a later state (`corr_tcAfter`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (ptsOf passed before allSites mem_allSites nexts Reg
  ordK val valT tw pend finPts rvPts finc brv bnb vv)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h j k : Nat} {e : Event}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
include hp hX hFw hub hw hw1

omit hp hFw hw hw1 hX in
private theorem noUb (he : X.get (g, k) = some e) : ∀ f, e.kind ≠ .ub f := fun f hf =>
  hub ⟨(g, k), e.pc, f, by rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩

/-- The state of an event of a role, with its relation to the trace. -/
private theorem role_at {d : Correction.Control.D} {n : Cls → Nat} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n))) :
    Correction.Control.Ev p L g d e ∧ TcC X g k d.site n ∧
      CorrWarp.CFits p L g d.scheduler (n .shfl) (n .vote) := by
  have hg := Frame.lt_of_get hX he
  have hkl := (List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = some e from he)).1
  refine ⟨?_, ?_, ?_⟩
  · rcases CorrWarp.open_ev hp hX hFw hw hw1 he (noUb hub he) with ⟨s, n', hσ', -⟩ |
      ⟨d', n', hσ', -, -, -, hev, -⟩
    · rw [hσ] at hσ'; cases hσ'
    · rw [hσ] at hσ'; cases hσ'; exact hev
  · rcases corr_tcC hp hX hFw hub hg hw hw1 k hkl.le _ hσ with ⟨s, n', h1, -⟩ | ⟨d', n', h1, h2⟩
    · cases h1
    · cases h1; exact h2
  · rcases corr_place hp hX hFw hub hg hw hw1 hσ with ⟨-, s, n', h1⟩ | ⟨d', n', r, h1, -, -, hF, -⟩
    · cases h1
    · cases h1; exact hF

/-- The state of a class event of a correction lane. -/
private theorem open_class (he : X.get (g, k) = some e)
    (hcl : isTcColl e = true) :
    ∃ d n, Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n)) := by
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he (noUb hub he) with ⟨s, n', -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, -⟩
  · exact absurd hcl (start_not_tcColl hi.2 hev)
  · exact ⟨d, n, hσ⟩

/-! ### The lag -/

end

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
include hp hX hFw hub hw hw1

private theorem at_of (hg : g < L.threads) (hk : k ≤ (X.tr g).length) {R : Nat}
    (hR : CorrRounds p L g R) {d : Correction.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n))) :
    ∃ r, CorrTcAt p L X g k R d n r := by
  rcases corr_place hp hX hFw hub hg hw hw1 hσ with ⟨-, s, n', h1⟩ | ⟨d', n', r, h1, -, hc, hF, hr,
      -⟩
  · cases h1
  cases h1
  rcases corr_tcC hp hX hFw hub hg hw hw1 k hk _ hσ with ⟨s, n', h1, -⟩ | ⟨d', n', h1, hT⟩
  · cases h1
  cases h1
  exact ⟨r, hc, hF, (hr R hR).1, (hr R hR).2, hT⟩

/-- **A warp-collective `tcgen05` event of a correction lane** is at a place of its tile. -/
private theorem tc_at (hg : g < L.threads) (he : X.get (g, k) = some e) (hcl : isTcColl e = true)
    {σ : (thread p L g).D} (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    ∃ d n R r a, σ = CorrWarp.cinj p L g d n ∧ Correction.Control.Ev p L g d e ∧ 0 < tw
        d.scheduler.site ∧
      CorrRounds p L g R ∧ CorrTcAt p L X g k R d n r ∧ val d.scheduler.site = some a ∧
          d.scheduler.site.pc < 9089 := by
  obtain ⟨d, n, hσ'⟩ := open_class hp hX hFw hub hw hw1 he hcl
  rw [hσ] at hσ'
  cases hσ'
  obtain ⟨hev, -, hF⟩ := role_at hp hX hFw hub hw hw1 he hσ
  have htw := corr_tcSite hev (noUb hub he)
  rw [hcl] at htw
  have htw' : 0 < tw d.scheduler.site := of_decide_eq_true htw.symm
  have hchk := List.all_eq_true.mp corr_tcChk_all d.scheduler.site (mem_allSites _)
  simp only [corrTcChk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at hchk
  obtain ⟨⟨⟨⟨h2, -⟩, -⟩, hlt⟩, hep⟩ := hchk.resolve_left (by omega)
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h2
  obtain ⟨rv, -, -, hFE, -⟩ := hF
  simp only [Epilogue.Fits, CorrWarp.toE, hep] at hFE
  obtain ⟨R, bal, hC, -⟩ := hFE
  have hR : CorrRounds p L g _ := ⟨R, bal, hC.1, rfl⟩
  obtain ⟨r, hA⟩ := at_of hp hX hFw hub hw hw1 hg
    (List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = some e from he)).1.le hR hσ
  exact ⟨d, n, _, r, a, rfl, hev, htw', hR, hA, ha, hlt⟩

/-- **A correction lane with no more warp-collective `tcgen05` events than a lane of its warp before
one is no later than it.** -/
theorem corr_tcLag (hg : g < L.threads) (hs : SameWarp L g h) {c : Nat}
    {σ : (thread p L g).D} (hK : X.TcK (g, j) c)
    (hσ : Frame.stateAt (thread p L) X g j = some (some σ))
    (hle : (X.tr h).countP isTcColl ≤ c) :
    Sched.threadTime (Progress.timed p L) X h ≤ Progress.time p L g σ := by
  obtain ⟨⟨e, he, hcl⟩, hcnt⟩ := hK
  obtain ⟨d, n, R, r, a, rfl, hev, htw, hR, hA, ha, hlt9⟩ :=
    tc_at hp hX hFw hub hw hw1 hg he hcl hσ
  have hh := hs.1.2.1
  have hwh : Prologue.warpIndex L h = Prologue.warpIndex L g := hs.2.symm
  have hRh : CorrRounds p L h R := hR.cta hp hg hh hs.1.2.2.symm
  have hb := hR.bmax hp hg
  have hrR : r ≤ R := by have := hA.reg; unfold Reg at this; omega
  have ht : Progress.Cr.time p d.scheduler n = valT p r a := (corr_round_time hA.cnt ha).2 (by
      omega)
  have hpb : Progress.primeBase p + 1024 ≤ valT p r a := by
    unfold valT Progress.pipeBase; omega
  have hsp := Progress.scanBase_le_primeBase p
  show _ ≤ Progress.Cr.time p d.scheduler n
  rw [ht]
  -- every state of the lane
  have key : ∀ {k σ}, k ≤ (X.tr h).length → Frame.stateAt (thread p L) X h k = some (some σ) →
      Progress.time p L h σ < valT p r a ∨ ∃ d' n', σ = CorrWarp.cinj p L h d' n' ∧
        d'.scheduler.site = d.scheduler.site ∧ Progress.time p L h σ ≤ valT p r a ∧
        ((X.tr h).take k).countP isTcColl = c := by
    intro k σ hk hσ'
    have hkc : ((X.tr h).take k).countP isTcColl ≤ c :=
      le_trans (List.take_sublist _ _).countP_le hle
    rcases corr_place hp hX hFw hub hh (by omega) (by omega) hσ' with ⟨h1, -⟩ |
      ⟨d', n', r0, rfl, -⟩
    · left; omega
    obtain ⟨r', hA'⟩ := at_of (g := h) hp hX hFw hub (by omega) (by omega) hh hk hRh hσ'
    show Progress.Cr.time p d'.scheduler n' < _ ∨ ∃ d2 n2, _ ∧ _ ∧ Progress.Cr.time p d'.scheduler
        n' ≤ _ ∧ _
    rcases Nat.lt_trichotomy (ordK d'.scheduler.site r') (ordK d.scheduler.site r) with hK | hK | hK
    · left
      cases hv : val d'.scheduler.site with
      | some b =>
        have h1 := (corr_round_time (p := p) hA'.cnt hv).1
        have h2 := corr_val_lt_tc hv ha htw hA'.reg hA.reg hK p
        omega
      | none =>
        have := corr_early_val hp hA'.fits hv (by
          have h1 := hA'.reg
          have h2 := hA.reg
          have := Correction.pc_le d'.scheduler.site
          have := Correction.pc_le d.scheduler.site
          unfold ordK at hK
          unfold Reg at h1 h2
          omega)
        omega
    · have hpc : d'.scheduler.site.pc = d.scheduler.site.pc ∧ r' = r := by
        have := Correction.pc_le d'.scheduler.site
        have := Correction.pc_le d.scheduler.site
        unfold ordK at hK
        omega
      obtain ⟨hpc, rfl⟩ := hpc
      have hchk := List.all_eq_true.mp (List.all_eq_true.mp corr_pairChk_all
        d'.scheduler.site (mem_allSites _))
        d.scheduler.site (List.mem_filter.mpr ⟨mem_allSites _, by simpa using htw⟩)
      simp only [corrPairChk, Bool.and_eq_true] at hchk
      have hchk := hchk.2
      simp only [hpc, decide_true, Bool.not_true, Bool.false_or, hA'.tile, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq] at hchk
      have hrb : ((X.tr g).take j).countP isRb = ((X.tr h).take k).countP isRb := by
        rw [hA.ballots, hA'.ballots]
        simp only [passed]
        have : ∀ q, before d.scheduler.site q = before d'.scheduler.site q := fun q => by
          simp only [before, hA.tile, hA'.tile, hpc]
        simp only [funext this]
      have hrv : ((X.tr g).take j).countP isRv = ((X.tr h).take k).countP isRv := by
        have hag := fun i h1 h2 => rb_agree (N := i) (i := j) (j := k) hp hX hFw hub hs hw hw1
          h1 h2
        refine Nat.le_antisymm ?_ ?_
        · exact countP_le_of_ordinal (p := isRb) isRb_of_isRv hrb.le fun i hi => hag i hi (by omega)
        · exact countP_le_of_ordinal (p := isRb) isRb_of_isRv hrb.ge
            fun i hi => (hag i (by omega) hi).symm
      have t := hA.tcCount
      have t' := hA'.tcCount
      have hc' : ((X.tr g).take j).countP isTcColl = c := hcnt
      have hf : finPts.countP (before d'.scheduler.site) = finPts.countP (before d.scheduler.site)
          := by
        have : ∀ q, before d.scheduler.site q = before d'.scheduler.site q := fun q => by
          simp only [before, hA.tile, hA'.tile, hpc]
        simp only [funext this]
      rcases hchk with (hd | ⟨⟨hpd, -⟩, hv⟩) | ⟨hpd, -⟩
      · right
        refine ⟨d', n', rfl, hd, (corr_round_time hA'.cnt (by rw [hd]; exact ha)).1, ?_⟩
        rw [hd] at t'
        omega
      · left
        split at hv
        · rename_i b b' e1 e2
          simp only [decide_eq_true_eq] at hv
          rw [ha] at e2
          cases e2
          have h1 := (corr_round_time (p := p) hA'.cnt e1).1
          unfold valT at h1 ⊢
          omega
        · cases hv
      · exfalso
        omega
    · exfalso
      have hag := fun i h1 h2 => rb_agree (N := i) (i := j) (j := k) hp hX hFw hub hs hw hw1
          h1 h2
      have := corr_tc_lt hA hA' hag htw hK
      have hc' : ((X.tr g).take j).countP isTcColl = c := hcnt
      omega
  refine threadTime_le (fun σ hσ' => ?_) fun σ e' hσ' he' => ?_
  · rcases key le_rfl hσ' with h1 | ⟨_, _, -, -, h1, -⟩ <;> omega
  · rcases key (Nat.sub_le _ _) hσ' with h1 | ⟨d', n', rfl, hd, -, hc'⟩
    · omega
    · exfalso
      obtain ⟨hev', -, -⟩ := role_at (g := h) hp hX hFw hub (by omega) (by omega) he' hσ'
      have h1 := corr_tcSite hev' (noUb hub he')
      rw [show d'.site = d.site from hd] at h1
      have h2 : ((X.tr h).take ((X.tr h).length - 1)).countP isTcColl <
          (X.tr h).countP isTcColl :=
        Frame.countP_take_lt_countP (P := isTcColl) (es := X.tr h) he'
          (by rw [h1]; exact decide_eq_true htw)
      omega

private def nextChk (s s' : Correction.Site) : Bool :=
  match Progress.Cr.part s, Progress.Cr.part s' with
  | some (st, true), some (st', true) => decide (st = st') && decide
      ((Progress.Cr.tailOff s).getD (Progress.Cr.roundOff s) <
        (Progress.Cr.tailOff s').getD (Progress.Cr.roundOff s'))
  | _, _ => false

omit hp hX hFw hub hw hw1 in
private theorem next_chk : allSites.all (fun s => decide (tw s = 0) ||
    (nexts s).all (nextChk s)) = true := by decide +kernel

/-- **A warp-collective `tcgen05` event of a correction lane leads to a later state.** -/
theorem corr_tcAfter (hg : g < L.threads) (htr : Frame.Tracked (thread p L) X) {c : Nat}
    {σ : (thread p L g).D} (hK : X.TcK (g, j) c)
    (hσ : Frame.stateAt (thread p L) X g j = some (some σ)) :
    (∃ σ', Frame.stateAt (thread p L) X g (j + 1) = some (some σ') ∧
      Progress.time p L g σ < Progress.time p L g σ') ∨
      Frame.stateAt (thread p L) X g (j + 1) = none := by
  obtain ⟨⟨e, he, hcl⟩, -⟩ := hK
  obtain ⟨d, n, R, r, a, rfl, hev, htw, -⟩ := tc_at hp hX hFw hub hw hw1 hg he hcl hσ
  have hstep : Frame.stateAt (thread p L) X g (j + 1) =
      ((Correction.Control.succ p L g d e).map (Option.map fun d' => CorrWarp.cinj p L g d'
        (Code.bump (cls L g) n e))) := by
    rw [Frame.stateAt_succ (C := thread p L) (show (X.tr g)[j]? = some e from he), hσ]
    exact CorrWarp.next_cinj d n _
  have hnb : ∀ q, Code.bump (cls L g) n e (.corr (.nb q)) = n (.corr (.nb q)) := fun q => by
    obtain ⟨pc, kd⟩ := e
    cases kd <;> first | cases hcl | simp [Code.bump, cls, Correction.cls]
  rw [hstep]
  cases hs : Correction.Control.succ p L g d e with
  | none => exact .inr rfl
  | some o =>
    cases o with
    | none =>
      exfalso
      rw [hs] at hstep
      exact htr g (j + 1) hg hstep
    | some d' =>
      left
      refine ⟨_, rfl, ?_⟩
      show Progress.Cr.time p d.scheduler n < Progress.Cr.time p d'.scheduler (Code.bump (cls L g) n
          e)
      have hRef : Correction.Control.Ref p L g (d, CorrWarp.rc n) := by
        rcases CorrWarp.open_ev hp hX hFw hw hw1 he (noUb hub he) with ⟨s, n', hσ', -⟩ |
          ⟨d', n', hσ', h0, hR, -⟩
        · rw [hσ] at hσ'; cases hσ'
        · rw [hσ] at hσ'
          cases hσ'
          exact (hR h0).1.counts
      rcases corr_ctl_step hRef hev (noUb hub he) hs with ⟨-, ⟨_, _, _, _, hk⟩ | hf⟩ | hM
      · obtain ⟨pc, kd⟩ := e
        simp only at hk
        subst hk
        cases hcl
      · exfalso
        revert hf htw
        show 0 < tw d.site → _
        cases d.site <;> simp [Correction.Site.isFst, tw]
      · have h1 := List.all_eq_true.mp next_chk d.scheduler.site (mem_allSites _)
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
        have h2 := List.all_eq_true.mp (h1.resolve_left (by omega)) d'.scheduler.site hM.1
        unfold nextChk at h2
        split at h2
        · rename_i st st' e1 e2
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
          obtain ⟨rfl, h2⟩ := h2
          simp only [Progress.Cr.time, e1, e2, Progress.Cr.slot, hnb]
          unfold Progress.clk
          omega
        · cases h2

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
