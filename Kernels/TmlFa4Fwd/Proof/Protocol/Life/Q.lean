-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Def
public import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Handoff
public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Exit
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Count
import Kernels.TmlFa4Fwd.Proof.Mma.Export.QCommit
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Target
import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Order
import Kernels.TmlFa4Fwd.Proof.Protocol.S.Notify
import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Exit
import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Observed
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Hist
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Bytes
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Lag
import Lemmas.Flow.NthEv
import Lemmas.Kernel.CommitNextExit
import Lemmas.Order.GuardOrder
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The Q stages' asynchronous uses end before their CTA's exit

The elected lane of warp 14 polls the second Q stage's empty barrier a second time in its drain
(`ld_exit`), which observes the release of the stage by the MMA lane (`q_drain`). The lane's
release of the first stage, at pc 2537, is its commit before (`Mma.q_commits`), so it has arrived
and ends with it (the commit-order assumption, `commitOrder`). Both releases follow the MMA lane's
polls of the full barriers, which observe the stages' copies (`q_load_finished`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Life
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier MbarRing

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

omit hp hFw in
/-- The commit-order assumption's constraint. -/
theorem q_performed {g j j' : Nat} {sp : TcCommit.Spec} {r : Fin 16}
    (he : X.get (g, j) = some ⟨2537, .tc (.commit sp)⟩) (hjj : j < j')
    (hc : ∃ s, X.Commit (g, j') s) (hk : ∀ k, j < k → k < j' → ¬ ∃ s, X.Commit (g, k) s)
    (hr : r ∈ X.tcNotified (g, j')) : r ∈ X.tcNotified (g, j) := by
  have hw := hX.asm Assumptions.commitOrder
    (by simp [Assumptions.all, Assumptions.synchronization])
  exact hw g j j' 2537 sp r he (by decide) hjj hc hk hr

/-- **The drain of an elected loader lane with a packet**: its second poll of the second Q stage's
empty barrier observes the MMA lane's release, after the MMA lane's polls of both full barriers and
its release of the first stage. -/
theorem q_drain (hg : g < L.threads) (hx : CtaExited L X (g / L.block))
    (hcp : 1 ≤ (X.tr (tmaLane L X g)).countP cpCopy) :
    ∃ c i i0 pc s s0 rank, MmaIn L g c ∧ X.get (c, i) = some ⟨pc, .tc (.commit s)⟩ ∧
      s.mbar = qE L g 1 ∧ TcCommit.target s rank = some (qE L g 1) ∧ rank ∈ X.tcNotified (c, i) ∧
      X.get (c, i0) = some ⟨2537, .tc (.commit s0)⟩ ∧ s0.mbar = qE L g 0 ∧ i0 < i ∧
      (∀ j, i0 < j → j < i → ¬ ∃ s, X.Commit (c, j) s) ∧
      (∀ t : Fin 2, 1 ≤ okPolls (qF L g t) ((X.tr c).take i)) ∧
      ∃ j pcj par acq sc, X.get (tmaLane L X g, j) = some ⟨pcj, .wait (qE L g 1) par true acq sc⟩ ∧
        WaitObserves X (.async (c, i) (.tcNotify rank)) (tmaLane L X g, j) (qE L g 1) acq sc := by
  obtain ⟨hyc, hyw⟩ := tmaLane_in (X := X) hp g
  have hyl := thread_lt_of_cta hg hyc
  obtain ⟨pcx, hxy⟩ := exit_of_exited hx hyl hyc
  obtain ⟨A, -, -, hcnt, hq⟩ := ld_exit hp hX hFw (.inl hyw) hxy
  have hlast : (X.tr (tmaLane L X g)).countP cpCopy =
      ((X.tr (tmaLane L X g)).take ((X.tr (tmaLane L X g)).length - 1)).countP cpCopy := by
    have hl : (X.tr (tmaLane L X g)).length - 1 < (X.tr (tmaLane L X g)).length :=
      (List.getElem?_eq_some_iff.mp hxy).1
    conv_lhs => rw [← List.take_length (l := X.tr (tmaLane L X g)),
      show (X.tr (tmaLane L X g)).length = (X.tr (tmaLane L X g)).length - 1 + 1 by omega,
      List.take_add_one]
    have hxy' : (X.tr (tmaLane L X g))[(X.tr (tmaLane L X g)).length - 1]? =
        some ⟨pcx, .exit⟩ := hxy
    rw [hxy', Option.toList_some, List.countP_append]
    simp [cpCopy]
  have hp2 := hq hyw (by omega)
  rw [obj_cta hyc] at hp2
  obtain ⟨j, pcj, par, acq, sc, -, hje, hjn⟩ := nth_poll (X := X) (g := tmaLane L X g)
    (k := (X.tr (tmaLane L X g)).length - 1) (l := qE L g 1) (n := 1) hp2.ge
  obtain ⟨c, hc, -, -, -, hempty⟩ := qHandoff hp hX hFw (tmaBytes hp hX hFw) g hg 1
  obtain ⟨i, pci, sp, rank, hie, hmb, -, hpl, hob, -⟩ := hempty (u := 0) hje hjn
  obtain ⟨hr, pc2, s2, hg2, ht2⟩ := observed_notified hX hob
  rw [hie] at hg2
  cases hg2
  have hcta : c / L.block = g / L.block := hc.2.1
  have hmb' : sp.mbar = obj L c 24 := hmb.trans (obj_cta hcta 24).symm
  obtain ⟨hp0, i0, s0, hii, hi0, hm0, hnone⟩ := Mma.q_commits hp hX hFw hc.2.2 hie hmb'
  rw [obj_cta hcta] at hp0 hm0
  refine ⟨c, i, i0, _, sp, s0, rank, hc, hie, hmb, ht2, hr, hi0, hm0, by omega, hnone, fun t => ?_,
    j, pcj, par, acq, sc, hje, hob⟩
  fin_cases t
  · exact hp0
  · exact hpl

/-- **The Q stages' tensor loads end before their CTA's exit.** -/
theorem q_load_finished {i : EvId} {a : Nat} {sp : TensorCopy.Spec} (s : Fin 2)
    (hi : X.TensorIssue i a sp) (hm : sp.mbar = qF L i.1 s) (hx : CtaExited L X (i.1 / L.block)) :
    SharedFinished L kernel Assumptions.all X (.async i (.notify .load)) (i.1 / L.block) := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := hi
  simp only at hm hx ⊢
  have hg := Frame.lt_of_get hX he
  have ho : QOff (8 * s.val) := by unfold QOff; have := s.isLt; omega
  obtain ⟨-, hw, ⟨j, pc', mk, inst, hel⟩, hle⟩ := q_issue hp hX hFw (g := g) ho he hm
  obtain ⟨hgt, -⟩ := tma_copy hp hX hFw (g := g) (q_tmaOff s) he hm
  have hcp := ld_tma_copies hp hX hFw (.inl hw) he
  obtain ⟨c, ic, i0, pcc, sc1, s0, rank, hc, hce, hcm, -, -, h0e, h0m, -, -, hpolls, -⟩ :=
    q_drain hp hX hFw hg hx (by
      rw [← hgt]
      exact hcp.trans (List.take_sublist _ _).countP_le)
  -- the MMA lane's poll of the stage observes the copy
  obtain ⟨c', -, hcl, -, hfull, -⟩ := qHandoff hp hX hFw (tmaBytes hp hX hFw) g hg s
  obtain rfl : c = c' := by
    fin_cases s
    · exact hcl h0e ((commit_zero hp hX h0e).2.trans (congrArg some h0m))
    · exact hcl hce ((commit_zero hp hX hce).2.trans (congrArg some hcm))
  obtain ⟨j', pcj, par, acq, sc, -, hje, hjn⟩ := nth_poll (X := X) (g := c) (k := ic)
    (l := qF L g s) (n := 0) (hpolls s)
  have hlt : ((X.tr g).take k).countP (issuesTo (qF L g s)) < 2 := Nat.lt_succ_of_le hle
  obtain ⟨i, pci, al, sp', hi', hm', hcnt, -, hob⟩ := hfull hje hjn ⟨_, hlt⟩
  rw [← hgt] at hi' hcnt hob
  obtain rfl := nthEv_unique (p := issuesTo (qF L g s)) hi' (by simp [issuesTo, hm']) he
    (by simp only [issuesTo, decide_eq_true_eq]; exact hm) (by simpa using hcnt)
  obtain ⟨o, ho', hnot⟩ := observed_load hX hob
  exact of_observed hX (i := (g, i)) (q := .notify .load) (c := g / L.block) ⟨o, ho', hnot⟩
    hc.1 hc.2.1 hje hob hx

/-- **The Q stages' releases end before their CTA's exit.** -/
theorem q_empty_finished {h k pc : Nat} {sp : TcCommit.Spec} {rank : Fin 16} (s : Fin 2)
    (he : X.get (h, k) = some ⟨pc, .tc (.commit sp)⟩)
    (ht : TcCommit.target sp rank = some (qE L h s)) (hx : CtaExited L X (h / L.block)) :
    SharedFinished L kernel Assumptions.all X (.async (h, k) (.tcNotify rank)) (h / L.block) := by
  have ht0 := ht
  change TcCommit.target sp rank = some (obj L h (8 * s.val + 16)) at ht0
  obtain ⟨hg, -, hw, hmb, -⟩ := mma_commit_of hp hX hFw he ht0
  obtain ⟨hcnt, hkv⟩ := Mma.q_commit_one hp hX hFw hw s he hmb
  -- the elected loader lane made a packet
  obtain ⟨hyc, hyw⟩ := tmaLane_in (X := X) hp h
  have hcp : 1 ≤ (X.tr (tmaLane L X h)).countP cpCopy := by
    obtain ⟨i, e, -, hie, hce, -⟩ := exists_nthEv (X := X) (g := h) (k := k) (n := 0) hkv
    obtain ⟨pci, kd⟩ := e
    cases kd with
    | tc tk =>
      cases tk with
      | commit s' =>
        have hm' : s'.mbar = obj L h (56 + 8 * (0 : Fin 3).val) := by
          simpa [commitsTo] using hce
        have hpoll := mma_kv_commit hp hX hFw 0 hw hie hm'
        obtain ⟨j, pcj, par, acq, sc, -, hje, hjn⟩ := nth_poll (X := X) (g := h) (k := i)
          (l := kvF L h 0) (n := 0) (by
            change 0 + 1 ≤ okPolls (obj L h (32 + 8 * (0 : Fin 3).val)) _; omega)
        obtain ⟨c, -, hcm, -, hfull, -⟩ := kvHandoff hp hX hFw h hg 0
        obtain rfl : h = c := hcm hie ((commit_zero hp hX hie).2.trans (congrArg some hm'))
        obtain ⟨a, ha⟩ := ldLane_prod (L := L) (g := h) (h := tmaLane L X h)
          ⟨hyc, .inl hyw⟩
        obtain ⟨i', pci', hie', -⟩ := hfull hje hjn a
        rw [← ha, show kvF L h 0 = obj L (tmaLane L X h) (32 + 8 * (0 : Fin 3).val) from
          (obj_cta hyc _).symm] at hie'
        obtain ⟨-, j', pcj', sp', -, hcopy, -⟩ := ld_async_arr hp hX hFw (.inl hyw) 0 hie'
        exact List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? hcopy, rfl⟩
      | _ => simp [commitsTo] at hce
    | _ => simp [commitsTo] at hce
  obtain ⟨c, ic, i0, pcc, sc1, s0, r, hc, hce, hcm, htr, hr, h0e, h0m, hlt, hnone, -, j, pcj, par,
    acq, sc, hje, hob⟩ := q_drain hp hX hFw hg hx hcp
  have hyl := thread_lt_of_cta hg hyc
  have hr0 : r = 0 := commit_rank_zero hp hX hce htr
  have hrk : rank = 0 := commit_rank_zero hp hX he ht
  subst hr0 hrk
  have hE : ∀ (t : Fin 2) {i pci : Nat} {sq : TcCommit.Spec},
      X.get (c, i) = some ⟨pci, .tc (.commit sq)⟩ → sq.mbar = qE L h t →
      qE L h t = obj L h (8 * t.val + 16) ∧ TcCommit.target sq 0 = some (qE L h t) :=
    fun t i pci sq h1 h2 => ⟨rfl, (commit_zero hp hX h1).2.trans (congrArg some h2)⟩
  fin_cases s
  · obtain ⟨-, htq⟩ := hE 0 h0e h0m
    obtain rfl : c = h := mma_commit_lane hp hX hFw (g := h) (o := 16) h0e htq he ht0
    obtain ⟨hcnt', -⟩ := Mma.q_commit_one hp hX hFw hw 0 h0e h0m
    obtain rfl := nthEv_unique (p := commitsTo (obj L c (8 * (0 : Fin 2).val + 16))) h0e
      (by simp only [commitsTo, decide_eq_true_eq]; exact h0m) he
      (by simp only [commitsTo, decide_eq_true_eq]; exact hmb) (hcnt'.trans hcnt.symm)
    have hpres := q_performed hX h0e hlt ⟨sc1, pcc, hce⟩ hnone hr
    have hcn : CommitNext Assumptions.all X (.async (c, i0) (.tcNotify 0))
        (.async (c, ic) (.tcNotify 0)) :=
      ⟨rfl, rfl, hlt, hpres, hr, ⟨_, _, h0e, by decide⟩, ⟨sc1, pcc, hce⟩, hnone⟩
    obtain ⟨pch, hxh⟩ := exit_of_exited hx hyl hyc
    obtain ⟨hk, hl⟩ := before_exit hje (by simp) hxh
    obtain ⟨ex, hspin⟩ := poll_spin hX _ _ _ _ _ _ hje
    exact SharedFinished.of_commitNext
      (finish := (tmaLane L X c, (X.tr (tmaLane L X c)).length - 1)) hpres hcn
      (Witness.of_mbarObserved
        (mbarObserved_of_waitObserves hX.tma.2.2.1 hr hob))
      (.single (DepStep.of_resumes L (Resumes.of_spin hje hspin rfl hk hl)))
      ⟨hyl, hyc, pch, hxh⟩
  · obtain ⟨-, htq⟩ := hE 1 hce hcm
    obtain rfl : c = h := mma_commit_lane hp hX hFw (g := h) (o := 24) hce htq he ht0
    obtain ⟨hcnt', -⟩ := Mma.q_commit_one hp hX hFw hw 1 hce hcm
    obtain rfl := nthEv_unique (p := commitsTo (obj L c (8 * (1 : Fin 2).val + 16))) hce
      (by simp only [commitsTo, decide_eq_true_eq]; exact hcm) he
      (by simp only [commitsTo, decide_eq_true_eq]; exact hmb) (hcnt'.trans hcnt.symm)
    exact of_observed hX (i := (c, ic)) (q := .tcNotify 0) (c := c / L.block) hr hyl hyc hje hob hx

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Life
