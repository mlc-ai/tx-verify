-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0
public import Lemmas.Flow.Polls
public import Lemmas.Flow.Counted
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Pred
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.PSeq
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.ArmPred
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RefArith
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Objs
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Sites
import Lemmas.Flow.CountTake
import Lemmas.Flow.Arith32Norm

@[expose] public section

/-! # A block's end names its rescale arm

A lane of warpgroup 0 at its arrival on `soReady` (pc 1122) of block `r` was, 18 events before it,
at the vote's successor with the arm skipped, or 36 events before it at the vote with the arm run
(the block is not the first and the vote is true): the machine's sites are visited in a fixed
order (`Wg0.pred_fpx` to `Wg0.pred_ost0`), 16 probability stores, the arm's `rsf`, the four
chunks' load, wait, store, wait, `rsfb`, `fpx`. No site on the way fires an arrival: so the arm's
stores (`wg0_arm`: chunk `c`'s at `ia - 16 + 4 c`) have the arrival's counts. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

private theorem site_arrS (s : Wg0.Site) (h : s.pc = 1122) : s = .arrS := by
  revert h
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals decide

/-- The event of a state: its kind (not undefined behaviour) and pc. -/
private theorem evk (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {t : Nat} {d : Wg0.Control.D} {n : Cls → Nat}
    {e : Event} (hσ : Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    (he : X.get (y, t) = some e) (hr : 103 ≤ d.site.pc ∧ d.site.pc < 1842) :
    Wg0.EvK P L y (warpW L y) d e ∧ (∀ f, e.kind ≠ .ub f) ∧ e.pc = d.site.pc := by
  have hub := noUb_kind hnu he
  obtain ⟨σ, hσ', hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  rw [hσ] at hσ'
  cases hσ'
  have hpc' : e.pc = d.site.pc := hpc
  obtain ⟨d', n', h, -, hE, -⟩ := wg0_state hJ hi hev hpc (by omega)
  simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨hE.2, hub, hpc'⟩

/-- **A step back**: the state before a state of warpgroup 0 that is not the first. -/
private theorem back (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L y < 4)
    (hy : y < L.threads) {t : Nat} {d : Wg0.Control.D} {n : Cls → Nat}
    (ht : t ≤ (X.tr y).length)
    (hσ : Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    (hne : d.site ≠ .smr) :
    ∃ (t' : Nat) (d' : Wg0.Control.D) (n' : Cls → Nat) (e : Event), t = t' + 1 ∧
      X.get (y, t') = some e ∧
      Frame.stateAt (thread P L) X y t' = some (some (.inr ⟨.inl .wg0, d'⟩, n')) ∧
      Wg0.Control.succ P L y (warpW L y) d' e = some (some d) := by
  rcases wg0_pred hFw hnu hw hy ht hσ with ⟨t', ht', d', n', e, he, hs', hS⟩ | hs
  · exact ⟨t', d', n', e, ht', he, hs', hS⟩
  · exact absurd hs hne

/-- A step back off a site of the sequence below `17` leaves the arrivals unchanged. -/
private theorem back_arr (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {t' : Nat} {d' : Wg0.Control.D} {n' : Cls → Nat}
    {e : Event} {p : Nat} (he : X.get (y, t') = some e)
    (hσ : Frame.stateAt (thread P L) X y t' = some (some (.inr ⟨.inl .wg0, d'⟩, n')))
    (ho : Wg0.ppos d' = some p) (hp17 : p ≠ 17) :
    ∀ l, arrivals l ((X.tr y).take (t' + 1)) = arrivals l ((X.tr y).take t') := by
  obtain ⟨hE, hub, -⟩ := evk hp hX hFw hnu hσ he (Wg0.ppos_pc ho)
  intro l
  refine countP_take_succ_false he ?_
  have := Wg0.ppos_noArr ho hp17 hE
  obtain ⟨pc, kd⟩ := e
  cases kd <;> simp only [arrivesOn, sourceArrive]
  rename_i m' tx' n' rel' sc'
  simp only [decide_eq_false_iff_not]
  rintro rfl
  exact this _ tx' n' rel' sc' rfl


/-- The element of a probability store is below four. -/
private theorem ost_el (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {t : Nat} {d : Wg0.Control.D} {n : Cls → Nat}
    {e : Event} {k : Fin 4}
    (hσ : Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    (he : X.get (y, t) = some e) (hs : d.site = .ost k) : d.el < 4 := by
  obtain ⟨hE, -, -⟩ := evk hp hX hFw hnu hσ he (by rw [hs]; fin_cases k <;> decide)
  simp only [Wg0.EvK, hs] at hE
  exact hE.1

/-- **Back through the probability stores**: from the state at `ost k`, element `el`, the state
`4 k + el` events earlier is at `ost 0`, element `0`, with no arrival between. -/
private theorem back_ost (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L y < 4) (hy : y < L.threads) :
    ∀ (q : Nat) {t : Nat} {d : Wg0.Control.D} {n : Cls → Nat} {k : Fin 4},
    t < (X.tr y).length →
    Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n)) →
    d.site = .ost k → d.el < 4 → 4 * k.val + d.el = q →
    ∃ (d0 : Wg0.Control.D) (n0 : Cls → Nat), q ≤ t ∧
      Frame.stateAt (thread P L) X y (t - q) = some (some (.inr ⟨.inl .wg0, d0⟩, n0)) ∧
      d0.site = .ost 0 ∧ d0.el = 0 ∧ Wg0.ArmSame d d0 ∧
      ∀ l, arrivals l ((X.tr y).take (t - q)) = arrivals l ((X.tr y).take t) := by
  intro q
  induction q with
  | zero =>
    intro t d n k ht hσ hs hel hq
    have hk : k = 0 := by
      apply Fin.ext
      omega
    subst hk
    exact ⟨d, n, by omega, by simpa using hσ, hs, by omega, ⟨rfl, rfl⟩, fun _ => rfl⟩
  | succ q ih =>
    intro t d n k ht hσ hs hel hq
    obtain ⟨t', d', n', e, htt, he, hσ', hS⟩ := back hFw hnu hw hy ht.le hσ (by rw [hs]; simp)
    subst htt
    by_cases h0 : 0 < d.el
    · obtain ⟨hs', hel', hsm⟩ := Wg0.pred_ostEl hS hs h0
      have hel4 : d'.el < 4 := ost_el hp hX hFw hnu hσ' he hs'
      obtain ⟨d0, n0, hle, hσ0, hs0, he0, hsm0, hA⟩ :=
        ih (by omega) hσ' hs' hel4 (by omega)
      have hpp : Wg0.ppos d' = some (4 * k.val + min d'.el 3) := by simp [Wg0.ppos, hs']
      have hA' := back_arr hp hX hFw hnu he hσ' hpp (by omega)
      refine ⟨d0, n0, by omega, ?_, hs0, he0, ⟨hsm.1.trans hsm0.1, hsm.2.trans hsm0.2⟩, fun l => ?_⟩
      · rwa [show t' + 1 - (q + 1) = t' - q by omega]
      · rw [show t' + 1 - (q + 1) = t' - q by omega, hA l, hA' l]
    · have hel0 : d.el = 0 := by omega
      have hk1 : 1 ≤ k.val := by omega
      obtain ⟨k', hk', hs', hge, hsm1⟩ : ∃ k' : Fin 4, k'.val + 1 = k.val ∧ d'.site = .ost k' ∧
          3 ≤ d'.el ∧ Wg0.ArmSame d d' := by
        fin_cases k
        · simp at hq
          omega
        · exact ⟨0, rfl, Wg0.pred_ost1 hS hs hel0⟩
        · exact ⟨1, rfl, Wg0.pred_ost2 hS hs hel0⟩
        · exact ⟨2, rfl, Wg0.pred_ost3 hS hs hel0⟩
      have hel4 : d'.el < 4 := ost_el hp hX hFw hnu hσ' he hs'
      obtain ⟨d0, n0, hle, hσ0, hs0, he0, hsm0, hA⟩ :=
        ih (by omega) hσ' hs' hel4 (by omega)
      have hpp : Wg0.ppos d' = some (4 * k'.val + min d'.el 3) := by simp [Wg0.ppos, hs']
      have hA' := back_arr hp hX hFw hnu he hσ' hpp (by omega)
      refine ⟨d0, n0, by omega, ?_, hs0, he0, ⟨hsm1.1.trans hsm0.1, hsm1.2.trans hsm0.2⟩,
        fun l => ?_⟩
      · rwa [show t' + 1 - (q + 1) = t' - q by omega]
      · rw [show t' + 1 - (q + 1) = t' - q by omega, hA l, hA' l]


/-- **Back through a chunk of the arm**: from the state at `rstw c`, the store (`t - 1`), the wait
and the load, three events earlier at `rld c`; no arrival on the way. -/
private theorem back_chunk (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L y < 4) (hy : y < L.threads) {ia t : Nat}
    {d : Wg0.Control.D} {n : Cls → Nat} {c : Fin 4} (hlt : t < (X.tr y).length)
    (hσ : Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    (hs : d.site = .rstw c)
    (hA : ∀ l, arrivals l ((X.tr y).take t) = arrivals l ((X.tr y).take ia)) :
    ∃ (d3 : Wg0.Control.D) (n3 : Cls → Nat), 3 ≤ t ∧
      Frame.stateAt (thread P L) X y (t - 3) = some (some (.inr ⟨.inl .wg0, d3⟩, n3)) ∧
      d3.site = .rld c ∧ Wg0.ArmSame d d3 ∧
      (∃ a vals sh, X.get (y, t - 1) = some ⟨[814, 915, 1016, 1117].getD c.val 0,
        .tc (.st a vals sh)⟩) ∧
      (∀ l, arrivals l ((X.tr y).take (t - 1)) = arrivals l ((X.tr y).take ia)) ∧
      ∀ l, arrivals l ((X.tr y).take (t - 3)) = arrivals l ((X.tr y).take ia) := by
  obtain ⟨t1, d1, n1, e1, rfl, he1, hσ1, hS1⟩ := back hFw hnu hw hy hlt.le hσ (by rw [hs]; simp)
  obtain ⟨hs1, hsm1⟩ := Wg0.pred_rstw hS1 hs
  have hr1 : 103 ≤ d1.site.pc ∧ d1.site.pc < 1842 := by
    rw [hs1]; fin_cases c <;> decide
  obtain ⟨hE1, hub1, hpc1⟩ := evk hp hX hFw hnu hσ1 he1 hr1
  have hpp1 : Wg0.ppos d1 = some 16 := by simp [Wg0.ppos, hs1]
  have hA1 := back_arr hp hX hFw hnu he1 hσ1 hpp1 (by omega)
  have hA1' : ∀ l, arrivals l ((X.tr y).take t1) = arrivals l ((X.tr y).take ia) :=
    fun l => (hA1 l).symm.trans (hA l)
  obtain ⟨t2, d2, n2, e2, rfl, he2, hσ2, hS2⟩ :=
    back hFw hnu hw hy (by omega) hσ1 (by rw [hs1]; simp)
  obtain ⟨hs2, hsm2⟩ := Wg0.pred_rst hS2 hs1
  have hr2 : 103 ≤ d2.site.pc ∧ d2.site.pc < 1842 := by
    rw [hs2]; fin_cases c <;> decide
  have hpp2 : Wg0.ppos d2 = some 16 := by simp [Wg0.ppos, hs2]
  have hA2 := back_arr hp hX hFw hnu he2 hσ2 hpp2 (by omega)
  have hA2' : ∀ l, arrivals l ((X.tr y).take t2) = arrivals l ((X.tr y).take ia) :=
    fun l => (hA2 l).symm.trans (hA1' l)
  obtain ⟨t3, d3, n3, e3, rfl, he3, hσ3, hS3⟩ :=
    back hFw hnu hw hy (by omega) hσ2 (by rw [hs2]; simp)
  obtain ⟨hs3, hsm3⟩ := Wg0.pred_rldw hS3 hs2
  have hpp3 : Wg0.ppos d3 = some 16 := by simp [Wg0.ppos, hs3]
  have hA3 := back_arr hp hX hFw hnu he3 hσ3 hpp3 (by omega)
  have hA3' : ∀ l, arrivals l ((X.tr y).take t3) = arrivals l ((X.tr y).take ia) :=
    fun l => (hA3 l).symm.trans (hA2' l)
  refine ⟨d3, n3, by omega, ?_, hs3, ⟨hsm1.1.trans (hsm2.1.trans hsm3.1),
    hsm1.2.trans (hsm2.2.trans hsm3.2)⟩, ?_, ?_, ?_⟩
  · rwa [show t3 + 1 + 1 + 1 - 3 = t3 by omega]
  · obtain ⟨pc, kd⟩ := e1
    simp only [Wg0.EvK, hs1] at hE1
    rcases hE1 with ⟨vals, hk⟩ | ⟨f, hf⟩
    · simp only at hk hpc1
      refine ⟨64 * c.val, vals, .s32x32b, ?_⟩
      rw [show t3 + 1 + 1 + 1 - 1 = t3 + 1 + 1 by omega, he1, hk, hpc1, hs1]
      rfl
    · exact absurd hf (hub1 f)
  · intro l
    rw [show t3 + 1 + 1 + 1 - 1 = t3 + 1 + 1 by omega]
    exact hA1' l
  · intro l
    rw [show t3 + 1 + 1 + 1 - 3 = t3 by omega]
    exact hA3' l


/-- **A step back keeping the arrivals**: the step off a site of the sequence below `17`. -/
private theorem back16 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L y < 4) (hy : y < L.threads) {ia t : Nat}
    {d : Wg0.Control.D} {n : Cls → Nat} (hlt : t < (X.tr y).length)
    (hσ : Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    (hne : d.site ≠ .smr)
    (hpd : ∀ (d0 : Wg0.Control.D) (e0 : Event),
      Wg0.Control.succ P L y (warpW L y) d0 e0 = some (some d) →
        ∃ p, Wg0.ppos d0 = some p ∧ p ≠ 17)
    (hA : ∀ l, arrivals l ((X.tr y).take t) = arrivals l ((X.tr y).take ia)) :
    ∃ (t' : Nat) (d' : Wg0.Control.D) (n' : Cls → Nat) (e : Event), t = t' + 1 ∧
      X.get (y, t') = some e ∧
      Frame.stateAt (thread P L) X y t' = some (some (.inr ⟨.inl .wg0, d'⟩, n')) ∧
      Wg0.Control.succ P L y (warpW L y) d' e = some (some d) ∧
      ∀ l, arrivals l ((X.tr y).take t') = arrivals l ((X.tr y).take ia) := by
  obtain ⟨t', d', n', e, ht, he, hσ', hS⟩ := back hFw hnu hw hy hlt.le hσ hne
  obtain ⟨p, hp1, hp2⟩ := hpd d' e hS
  have := back_arr hp hX hFw hnu he hσ' hp1 hp2
  refine ⟨t', d', n', e, ht, he, hσ', hS, fun l => ?_⟩
  rw [← ht] at this
  exact (this l).symm.trans (hA l)

/-- **Back to the vote** from the first probability store. -/
private theorem back_vote (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L y < 4) (hy : y < L.threads) {t : Nat}
    {d : Wg0.Control.D} {n : Cls → Nat} (hlt : t < (X.tr y).length)
    (hσ : Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    (hs : d.site = .ost 0) (hel : d.el = 0) :
    ∃ t' q mm a r, t = t' + 1 ∧ X.get (y, t') = some ⟨578, .voteMode q mm a r⟩ ∧ d.vt = r := by
  obtain ⟨t', d', n', e, rfl, he, hσ', hS⟩ := back hFw hnu hw hy hlt.le hσ (by rw [hs]; simp)
  obtain ⟨hs', hvt, -⟩ := Wg0.pred_ost0 hS hs hel
  obtain ⟨hE, hub, hpc⟩ := evk hp hX hFw hnu hσ' he (by rw [hs']; decide)
  simp only [Wg0.EvK, hs'] at hE
  rcases hE with ⟨a, r, hk⟩ | ⟨f, hf⟩
  · obtain ⟨pc, kd⟩ := e
    simp only at hk hpc
    subst hk
    rw [hs'] at hpc
    exact ⟨t', _, _, a, r, rfl, by rw [he, hpc]; rfl, hvt _ _ _ _ rfl⟩
  · exact absurd hf (hub f)

/-- **A block's end names its rescale arm.** At the arrival on `soReady` at `ia` of block `r`
(the lane's arrivals there are the uses before `r`), the vote is 18 events before it and the arm
was skipped (the block is the first or the vote is false), or the vote is 36 events before it,
true, the block is not the first, and the four stores (chunk `c`'s at `ia - 16 + 4 c`) lie
between with the arrival's counts. -/
theorem wg0_arm (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L y < 4) {ia tx cnt : Nat} {l : Loc}
    {rel : Bool} {sc : MbarScope}
    (he : X.get (y, ia) = some ⟨1122, .arrive l tx cnt rel sc⟩) :
    ∃ r, (∀ j : Fin 2, arrivals (mbarLoc L (y / L.block) (.soReady j)) ((X.tr y).take ia) =
        ringUses 2 j r) ∧
      ((18 ≤ ia ∧ ∃ q mm a res, X.get (y, ia - 18) = some ⟨578, .voteMode q mm a res⟩ ∧
          (r = 0 ∨ res = false) ∧
          ∀ l', arrivals l' ((X.tr y).take (ia - 18)) = arrivals l' ((X.tr y).take ia)) ∨
       (36 ≤ ia ∧ 1 ≤ r ∧ (∃ q mm a, X.get (y, ia - 36) = some ⟨578, .voteMode q mm a true⟩) ∧
        ∀ c : Fin 4, ∃ a vals sh, X.get (y, ia - 16 + 4 * c.val) =
            some ⟨[814, 915, 1016, 1117].getD c.val 0, .tc (.st a vals sh)⟩ ∧
          ∀ l', arrivals l' ((X.tr y).take (ia - 16 + 4 * c.val)) =
            arrivals l' ((X.tr y).take ia))) := by
  have hy : y < L.threads := Frame.lt_of_get hX he
  have hil : ia < (X.tr y).length := (List.getElem?_eq_some_iff.mp he).1
  have hr : 103 ≤ 1122 ∧ (1122 : Nat) < 1842 := by omega
  have hub : ∀ f, (⟨1122, .arrive l tx cnt rel sc⟩ : Event).kind ≠ .ub f := fun _ h => by
    cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hRn, -, -⟩ := wg0_state hJ hi hev hpc hr
  have hs : d.site = .arrS := site_arrS _ hpc.symm
  have hR := hRn (state_ub hX hσ he)
  rw [show (fun c => n (.wg0 c)) = fun c => ((X.tr y).take ia).countP (Wg0.cls c) from
    funext fun c => state_count hσ (.wg0 c)] at hR
  obtain ⟨hc, -⟩ := hR (wg0_take_noUb hX he)
  simp only [Wg0.RefCore, hs, Wg0.Site.reg, Wg0.Site.idx, Wg0.RefAt] at hc
  obtain ⟨r, ⟨-, hRo, hrR, hbi, -⟩, hq, ha⟩ := hc
  simp only [Wg0.Control.D.words] at hbi hRo hrR
  have harr : ∀ j : Fin 2, arrivals (mbarLoc L (y / L.block) (.soReady j)) ((X.tr y).take ia) =
      ringUses 2 j r := fun j =>
    (wg0_arrivals hp hX hFw hw _ _).trans ((ha _).trans (Wg0.arr_so hp _ _ _ _))
  have hbr : scmpi .eq .b d.bi 1 = decide (r = 0) := by
    rw [hbi, scmpi_eq_b_W (n := 1) (by omega) (by omega) (by omega)]
    simp only [Int.toNat_one, decide_eq_decide]
    omega
  refine ⟨r, harr, ?_⟩
  obtain ⟨t1, d1, n1, e1, ht1, he1, hσ1, hS1⟩ := back hFw hnu hw hy hil.le hσ (by rw [hs]; simp)
  obtain ⟨hs1, hsm1⟩ := Wg0.pred_arrS_same hS1 hs
  have hpp1 : Wg0.ppos d1 = some 16 := by simp [Wg0.ppos, hs1]
  have hA1 := back_arr hp hX hFw hnu he1 hσ1 hpp1 (by omega)
  have hA1' : ∀ l, arrivals l ((X.tr y).take t1) = arrivals l ((X.tr y).take ia) := fun l => by
    rw [ht1]; exact (hA1 l).symm
  obtain ⟨t2, d2, n2, e2, ht2, he2, hσ2, hS2⟩ :=
    back hFw hnu hw hy (by omega) hσ1 (by rw [hs1]; simp)
  obtain ⟨hpre, hsm2⟩ := Wg0.pred_fpx hS2 hs1
  have hb2 : d.bi = d2.bi := hsm1.2.trans hsm2.2
  have hv2 : d.vt = d2.vt := hsm1.1.trans hsm2.1
  rcases hpre with hrsfb | ⟨hos, hge, hcond⟩
  · subst ht2
    have hpp2 : Wg0.ppos d2 = some 16 := by simp [Wg0.ppos, hrsfb]
    have hA2 : ∀ l, arrivals l ((X.tr y).take t2) = arrivals l ((X.tr y).take ia) := fun l =>
      ((back_arr hp hX hFw hnu he2 hσ2 hpp2 (by omega)) l).symm.trans (hA1' l)
    have hp16 : ∀ {s : Wg0.Site} {d0 : Wg0.Control.D}, d0.site = s →
        (s = .rsfb ∨ s = .rstw 0 ∨ s = .rstw 1 ∨ s = .rstw 2 ∨ s = .rstw 3 ∨ s = .rsf) →
        Wg0.ppos d0 = some 16 ∧ (16 : Nat) ≠ 17 := fun h hs => by
      refine ⟨?_, by omega⟩
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Wg0.ppos, h]
    -- rsfb, the last chunk's store wait
    obtain ⟨t3, d3, n3, e3, ht3, he3, hσ3, hS3, hA3⟩ := back16 hp hX hFw hnu hw hy (by omega) hσ2
      (by rw [hrsfb]; simp) (fun d0 e0 h => ⟨16, (hp16 (Wg0.pred_rsfb h hrsfb).1
        (.inr (.inr (.inr (.inr (.inl rfl)))))).1, by omega⟩) (fun l => (hA2 l))
    obtain ⟨hs3, hsm3⟩ := Wg0.pred_rsfb hS3 hrsfb
    -- chunk 3
    obtain ⟨d4, n4, h4, hσ4, hs4, hsm4, ⟨a3, v3, sh3, hst3⟩, hAs3, hA4⟩ :=
      back_chunk hp hX hFw hnu hw hy (ia := ia) (by omega) hσ3 hs3 hA3
    obtain ⟨t5, d5, n5, e5, ht5, he5, hσ5, hS5, hA5⟩ := back16 hp hX hFw hnu hw hy (by omega) hσ4
      (by rw [hs4]; simp) (fun d0 e0 h => ⟨16, (hp16 (Wg0.pred_rld3 h hs4).1
        (.inr (.inr (.inr (.inl rfl))))).1, by omega⟩) hA4
    obtain ⟨hs5, hsm5⟩ := Wg0.pred_rld3 hS5 hs4
    -- chunk 2
    obtain ⟨d6, n6, h6, hσ6, hs6, hsm6, ⟨a2, v2, sh2, hst2⟩, hAs2, hA6⟩ :=
      back_chunk hp hX hFw hnu hw hy (ia := ia) (by omega) hσ5 hs5 hA5
    obtain ⟨t7, d7, n7, e7, ht7, he7, hσ7, hS7, hA7⟩ := back16 hp hX hFw hnu hw hy (by omega) hσ6
      (by rw [hs6]; simp) (fun d0 e0 h => ⟨16, (hp16 (Wg0.pred_rld2 h hs6).1
        (.inr (.inr (.inl rfl)))).1, by omega⟩) hA6
    obtain ⟨hs7, hsm7⟩ := Wg0.pred_rld2 hS7 hs6
    -- chunk 1
    obtain ⟨d8, n8, h8, hσ8, hs8, hsm8, ⟨a1, v1, sh1, hst1⟩, hAs1, hA8⟩ :=
      back_chunk hp hX hFw hnu hw hy (ia := ia) (by omega) hσ7 hs7 hA7
    obtain ⟨t9, d9, n9, e9, ht9, he9, hσ9, hS9, hA9⟩ := back16 hp hX hFw hnu hw hy (by omega) hσ8
      (by rw [hs8]; simp) (fun d0 e0 h => ⟨16, (hp16 (Wg0.pred_rld1 h hs8).1
        (.inr (.inl rfl))).1, by omega⟩) hA8
    obtain ⟨hs9, hsm9⟩ := Wg0.pred_rld1 hS9 hs8
    -- chunk 0
    obtain ⟨d10, n10, h10, hσ10, hs10, hsm10, ⟨a0, v0, sh0, hst0⟩, hAs0, hA10⟩ :=
      back_chunk hp hX hFw hnu hw hy (ia := ia) (by omega) hσ9 hs9 hA9
    obtain ⟨t11, d11, n11, e11, ht11, he11, hσ11, hS11, hA11⟩ := back16 hp hX hFw hnu hw hy
      (by omega) hσ10 (by rw [hs10]; simp) (fun d0 e0 h => ⟨16, (hp16 (Wg0.pred_rld0 h hs10).1
        (.inr (.inr (.inr (.inr (.inr rfl)))))).1, by omega⟩) hA10
    obtain ⟨hs11, hsm11⟩ := Wg0.pred_rld0 hS11 hs10
    obtain ⟨t12, d12, n12, e12, ht12, he12, hσ12, hS12, hA12⟩ := back16 hp hX hFw hnu hw hy
      (by omega) hσ11 (by rw [hs11]; simp) (fun d0 e0 h => ⟨4 * 3 + min d0.el 3, by
        simp [Wg0.ppos, (Wg0.pred_rsf h hs11).1], by omega⟩) hA11
    obtain ⟨hos, hge, hcond, hsm12⟩ := Wg0.pred_rsf hS12 hs11
    have hel4 := ost_el hp hX hFw hnu hσ12 he12 hos
    obtain ⟨d0, n0, hle, hσ0, hs0, he0, hsm0, -⟩ :=
      back_ost hp hX hFw hnu hw hy (4 * 3 + d12.el) (by omega) hσ12 hos hel4 rfl
    obtain ⟨t', q, mm, a, res, ht', hv, hvt⟩ :=
      back_vote hp hX hFw hnu hw hy (by omega) hσ0 hs0 he0
    have hall : Wg0.ArmSame d d12 :=
      hsm1.trans (hsm2.trans (hsm3.trans (hsm4.trans (hsm5.trans (hsm6.trans (hsm7.trans
        (hsm8.trans (hsm9.trans (hsm10.trans (hsm11.trans hsm12))))))))))
    have hvd : d.vt = res := hall.1.trans (hsm0.1.trans hvt)
    rw [← hall.2, ← hall.1, hbr] at hcond
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not,
      Bool.not_false] at hcond
    right
    refine ⟨by omega, by omega, ⟨q, mm, a, ?_⟩, ?_⟩
    · rw [show ia - 36 = t' by omega, hv, ← hvd, hcond.2]
    · intro c
      obtain ⟨cv, hcv⟩ := c
      interval_cases cv
      · refine ⟨a0, v0, sh0, ?_, ?_⟩
        · dsimp only
          rw [show ia - 16 + 4 * 0 = t9 - 1 by omega]
          exact hst0
        · dsimp only
          rw [show ia - 16 + 4 * 0 = t9 - 1 by omega]
          exact hAs0
      · refine ⟨a1, v1, sh1, ?_, ?_⟩
        · dsimp only
          rw [show ia - 16 + 4 * 1 = t7 - 1 by omega]
          exact hst1
        · dsimp only
          rw [show ia - 16 + 4 * 1 = t7 - 1 by omega]
          exact hAs1
      · refine ⟨a2, v2, sh2, ?_, ?_⟩
        · dsimp only
          rw [show ia - 16 + 4 * 2 = t5 - 1 by omega]
          exact hst2
        · dsimp only
          rw [show ia - 16 + 4 * 2 = t5 - 1 by omega]
          exact hAs2
      · refine ⟨a3, v3, sh3, ?_, ?_⟩
        · dsimp only
          rw [show ia - 16 + 4 * 3 = t3 - 1 by omega]
          exact hst3
        · dsimp only
          rw [show ia - 16 + 4 * 3 = t3 - 1 by omega]
          exact hAs3
  · have hel4 := ost_el hp hX hFw hnu hσ2 he2 hos
    have hpp2 : Wg0.ppos d2 = some (4 * 3 + min d2.el 3) := by simp [Wg0.ppos, hos]
    have hA2 := back_arr hp hX hFw hnu he2 hσ2 hpp2 (by omega)
    obtain ⟨d0, n0, hle, hσ0, hs0, he0, hsm0, hA0⟩ :=
      back_ost hp hX hFw hnu hw hy (4 * 3 + d2.el) (by omega) hσ2 hos hel4 rfl
    obtain ⟨t', q, mm, a, res, ht', hv, hvt⟩ :=
      back_vote hp hX hFw hnu hw hy (by omega) hσ0 hs0 he0
    left
    have hvA : ∀ l, arrivals l ((X.tr y).take (t' + 1)) = arrivals l ((X.tr y).take t') :=
      fun l => countP_take_succ_false hv (by simp [arrivesOn, sourceArrive])
    refine ⟨by omega, q, mm, a, res, ?_, ?_, fun l => ?_⟩
    · rw [show ia - 18 = t' by omega]
      exact hv
    · rw [← hb2, hbr] at hcond
      have hvd : d.vt = res := hv2.trans (hsm0.1.trans hvt)
      rw [← hv2] at hcond
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hcond
      rcases hcond with h | h
      · exact .inl h
      · exact .inr (hvd.symm.trans h)
    · have i1 : t' + 1 = t2 - (4 * 3 + d2.el) := ht'.symm
      have i2 : t2 + 1 = t1 := by omega
      rw [show ia - 18 = t' by omega, ← hvA l, i1, hA0 l, ← hA2 l, i2]
      exact hA1' l

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
