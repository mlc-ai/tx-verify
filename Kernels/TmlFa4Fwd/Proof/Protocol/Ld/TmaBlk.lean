-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.TmaWait
public import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Channels
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Tma
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
import Kernels.TmlFa4Fwd.Proof.Mma.Export.QCommitLag
import Kernels.TmlFa4Fwd.Proof.Progress.Order
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Target
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Winner
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StageBar
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BiasPoll
import Lemmas.Protocol.KindRingLane
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Progress at the loader's waits of the TMA groups and the drain's Q wait

`tma_lag`: a blocked wait of a Bias group has lane 0 of a softmax warp short of its release of the
round, in the score part of that slot; the drain's Q wait has the MMA warp short of its release.
The first waits of a barrier are not blocked. The warp's other lanes poll in step with the electing
lane: its copies follow its elections, which every lane makes (`tma_pair`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.MbarRing

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The lanes of a warp, by index. -/
theorem sameWarp_of (hp : Pre p L m) {x y : Nat} (hx : x < L.threads) (hy : y < L.threads)
    (hc : x / L.block = y / L.block) (hw : Prologue.warpIndex L x = Prologue.warpIndex L y) :
    SameWarp L x y := by
  have hb := hp.block
  refine ⟨⟨hx, hy, hc⟩, ?_⟩
  simp only [Prologue.warpIndex] at hw
  omega

/-- The biased rounds after the first are below the time table's slots. -/
theorem stage_rounds_bound (hp : Pre p L m) {y B : Nat} (hy : y < L.threads)
    (hB : StageRounds p L y B) :
    ∃ R, MmaRounds p L y R ∧ B + 1 ≤ Progress.bmax p := by
  obtain ⟨R, bal, hP, rfl⟩ := hB
  have hT : SoftRounds p L y _ := ⟨R, bal, hP, rfl⟩
  have hR : MmaRounds p L y _ := ⟨R, bal, hP, rfl⟩
  have := hT.mma rfl hR
  have := mma_rounds_bmax hp hy hR
  exact ⟨_, hR, by omega⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- A tensor copy on a Q or Bias barrier is a lane's of warp 14 of the CTA. -/
theorem ld_copy_lane {z i o : Nat} (ho : LdTmaOff o) {pc a : Nat}
    {sp : TensorCopy.Spec} (he : X.get (z, i) = some ⟨pc, .tensorIssue a sp⟩)
    (hm : sp.mbar = obj L g o) : z / L.block = g / L.block ∧ Prologue.warpIndex L z = 14 := by
  obtain ⟨hc, hu⟩ := bar_use hp hX hFw he (show Frame.MbarOf _ _ from hm) (fun _ h => by cases h)
  refine ⟨hc, ?_⟩
  cases hu with
  | ldCopy _ _ hw _ _ _ =>
    rw [← obj_cta hc] at hm
    exact (ld_tma_copy hp hX hFw hw ho he hm).1
  | epiPoll _ _ _ _ hk _ | epiArr _ _ _ hk _ | corrArr _ _ hk | corrPoll _ _ _ hk
  | softArr _ _ _ _ hk | softPoll _ _ _ _ _ hk | mmaPoll _ _ _ hk | mmaCommit _ _ _ hk _ _ _
  | ldPoll _ _ _ _ hk | ldAsync _ _ hk | ldArr _ _ _ hk => cases hk

/-- A tensor copy's earlier ones are fewer than twice the lane's polls. -/
theorem ld_copy_polls {z i o : Nat} (hw : Prologue.warpIndex L z = 14)
    (ho : LdTmaOff o) {pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get (z, i) = some ⟨pc, .tensorIssue a sp⟩) (hm : sp.mbar = obj L z o) :
    ((X.tr z).take i).countP (issuesTo (obj L z o)) + 1 ≤
      2 * okPolls (obj L z (o + 16)) ((X.tr z).take i) :=
  (ld_tma_copy hp hX hFw (.inl hw) ho he hm).2.1

/-- **Every lane of the warp makes the elections before the electing lane's copies.** -/
theorem tma_pair {h z i o u : Nat} (ho : LdTmaOff o) (hh : h < L.threads)
    (hhc : h / L.block = g / L.block) (hh14 : Prologue.warpIndex L h = 14) {pc a : Nat}
    {sp : TensorCopy.Spec} (he : X.get (z, i) = some ⟨pc, .tensorIssue a sp⟩)
    (hm : sp.mbar = obj L g o) (hu : u + 1 ≤ okPolls (obj L g (o + 16)) ((X.tr z).take i)) :
    u + 1 ≤ ElectOrd.siteOrdinal (Loader.arrPcs o) X h (X.tr h).length := by
  obtain ⟨hzc, hzw⟩ := ld_copy_lane hp hX hFw ho he hm
  have hz := Frame.lt_of_get hX he
  rw [← obj_cta hzc] at hm hu
  have hord := tma_copy_ord hp hX hFw hzw ho he hm
  have hs : SameWarp L z h := sameWarp_of hp hz hh (hzc.trans hhc.symm) (hzw.trans hh14.symm)
  obtain ⟨y, hy, ⟨pcy, kd⟩, hget, hq, hcnt⟩ := Flow.exists_nth
    (ElectOrd.atSites (Loader.arrPcs o)) (X.tr z) (n := u) (k := i) (by
      change u < ElectOrd.siteOrdinal (Loader.arrPcs o) X z i
      omega)
  simp only [ElectOrd.atSites, Bool.and_eq_true] at hq
  obtain ⟨hk, hpc⟩ := hq
  cases kd <;> simp [isElectEv] at hk
  rename_i mask inst ld
  have hE : X.Elect (z, y) pcy mask inst ld := hget
  have hmem : ∀ {w j pc mask inst ld}, X.Elect (w, j) pc mask inst ld → ∀ v,
      electMember mask (laneOf L v) := by
    intro w j pc mask inst ld hel v
    have := elect_full hX hel
    subst this
    refine ⟨by unfold laneOf; omega, ?_⟩
    have hl : laneOf L v < 32 := by unfold laneOf; omega
    have key : ∀ l < 32, Nat.testBit 4294967295 l = true := by decide
    exact key _ hl
  obtain ⟨x, hP⟩ := ElectOrd.partner hX hs hE (hmem hE h)
  have heq := ElectOrd.siteOrdinal_eq hX (Loader.arrPcs o) hs
    (fun _ _ _ _ _ _ hel => hmem hel h) (fun _ _ _ _ _ _ hel => hmem hel z) hP
  obtain ⟨p1, p2, m1, m2, i1, l1, l2, e1, e2⟩ := hP
  obtain ⟨hpc', -⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ e1 e2 hs
  have hpy : p1 = pcy := by
    have e1' : X.get (z, y) = some ⟨p1, .elect m1 i1 l1⟩ := e1
    have hg' : X.get (z, y) = some ⟨pcy, .elect mask inst ld⟩ := hget
    rw [e1'] at hg'
    exact (Event.mk.inj (Option.some.inj hg')).1
  have hx : (X.tr h)[x]? = some ⟨p2, .elect m2 i1 l2⟩ := e2
  have hone : ElectOrd.siteOrdinal (Loader.arrPcs o) X h (x + 1) = u + 1 := by
    have h0 : ElectOrd.siteOrdinal (Loader.arrPcs o) X h x = u := by rw [← heq]; exact hcnt
    unfold ElectOrd.siteOrdinal at h0 ⊢
    rw [List.take_add_one, hx, List.countP_append, h0]
    simp [ElectOrd.atSites, isElectEv, ← hpc', hpy, hpc]
  have hlen := len_of_get (show X.get (h, x) = some _ from e2)
  rw [← hone]
  exact countP_take_mono _ (X.tr h) hlen

/-- An item of a Q or Bias stage follows elections of every lane of the warp. -/
theorem tma_item (hB : TmaBytes X) {h o : Nat} (ho : LdTmaOff o) (hh : h < L.threads)
    (hhc : h / L.block = g / L.block) (hh14 : Prologue.warpIndex L h = 14) {u : Nat}
    (hx : ((1 : Fin 3), u) ∈ TmaUnits.S X (obj L g o) (tmaLane L X g) 2 16384) :
    u + 1 ≤ ElectOrd.siteOrdinal (Loader.arrPcs o) X h (X.tr h).length := by
  obtain ⟨-, -, h1⟩ := (tmaFull hp hX hFw hB g ho).source hx
  obtain ⟨⟨pc, al, sp, hget, hm⟩, -⟩ := h1 (by simp)
  obtain ⟨i, hi, -, hpol⟩ := tmaFull_pol hp hX hFw hB g ho hx
  rw [hi] at hget
  exact tma_pair hp hX hFw ho hh hhc hh14 hget hm hpol

/-- A loader lane's polls of an empty barrier are at most the phase plus one. -/
theorem tma_polls_le {h o : Nat} (ho : LdTmaOff o) (hhc : h / L.block = g / L.block)
    (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    (hpc : ∀ q ∈ X.objects (obj L g (o + 16)), (∃ p ok, q.action = .pollParity p ok) →
      q.fault = none)
    (hni : MBarrier.NoInval (X.objects (obj L g (o + 16)))) {f : MBarrier.State}
    (hst : Final X (obj L g (o + 16)) f) :
    okPolls (obj L g (o + 16)) (X.tr h) ≤ f.phase + 1 := by
  refine okPolls_le_phase hX le_rfl hpc hni (fun k pc q acq sc he => ?_) hst
  rw [← obj_cta hhc] at he ⊢
  exact (ld_tma_empty_par hp hX hFw hw ho he).2

/-- **Q empty**, every lane of warp 14. -/
theorem qE_lane (hff : ∀ l, ∀ r ∈ X.objects l, r.fault = none) (hB : TmaBytes X)
    (hg : g < L.threads) (hg14 : Prologue.warpIndex L g = 14) (s : Fin 2)
    (hord : ElectOrd.siteOrdinal (Loader.arrPcs (8 * s.val)) X g (X.tr g).length =
      okPolls (qE L g s) (X.tr g)) {f : MBarrier.State}
    (hst : Final X (qE L g s) f)
    (hpar : f.phase % 2 = (okPolls (qE L g s) (X.tr g) + 1) % 2) :
    f.phase + 1 = okPolls (qE L g s) (X.tr g) ∧
      ((X.tr (qCons L X g s)).countP (commitsTo (qE L g s)) ≤ f.phase ∨ CommitOpen X) := by
  have N := qNotify hp hX hFw g s
  have hle : f.phase ≤ okPolls (qE L g s) (X.tr g) := by
    refine (qRing hp hX hFw hB g hg s).E_phase_of hX (by decide) N.init
      (fun r hr ha => ?_) (fun hr _ ha => (N.arrive_rec hr ha).1) (fun hr hf ha => ?_)
      (fun y hy => ?_) hst
    · cases N.src r hr with
      | init ha' | poll _ _ ha' | commit _ _ _ _ ha' => rw [ha] at ha'; cases ha'
    · obtain ⟨x, hx, hid⟩ := N.rec_S hr hf ha
      exact ⟨x, hx, hid⟩
    · rw [← hord]
      exact tma_item hp hX hFw hB (q_tmaOff s) hg rfl hg14
        ((qRing hp hX hFw hB g hg s).E_items hX hy 1)
  have hge := tma_polls_le hp hX hFw (q_tmaOff s) rfl (.inl hg14)
    (PairTmaRing.poll_clean hX N.init N.noInval) N.noInval hst
  exact ⟨by change okPolls (qE L g s) (X.tr g) ≤ _ at hge; omega, commit_short hp hX hff N hst⟩

/-- **Bias empty**, every lane of warp 14. -/
theorem bE_lane (hff : ∀ l, ∀ r ∈ X.objects l, r.fault = none) (hB : TmaBytes X)
    (hg : g < L.threads) (hg14 : Prologue.warpIndex L g = 14) (st : Fin 2)
    (hord : ElectOrd.siteOrdinal (Loader.arrPcs (320 + 8 * st.val)) X g (X.tr g).length =
      okPolls (bE L g st) (X.tr g)) {f : MBarrier.State}
    (hst : Final X (bE L g st) f)
    (hpar : f.phase % 2 = (okPolls (bE L g st) (X.tr g) + 1) % 2) :
    f.phase + 1 = okPolls (bE L g st) (X.tr g) ∧
      ∃ b, arrivals (bE L g st) (X.tr (biasLane L (g / L.block) st.val b)) ≤ f.phase := by
  have N := biasFreeHist hp hX hFw g st
  have O : Unit.Obj X (bE L g st) 4 (biasLane L (g / L.block) st.val) 1 :=
    { pos := N.pos, inj := N.inj, src := N.src, init := N.init, noInval := N.noInval
      parity := fun {h k pc par acq sc} he => by
        rcases biasFree_use hp hX hFw st he rfl (fun _ h => by cases h) with
          ⟨⟨hc, hw⟩, _⟩ | ⟨hk, _⟩
        · rw [← bE_eq] at he ⊢
          rw [← obj_cta hc] at he ⊢
          exact (ld_tma_empty_par hp hX hFw hw (b_tmaOff st) he).2
        · cases hk
      δ_le := le_rfl }
  have hle : f.phase ≤ okPolls (bE L g st) (X.tr g) := by
    refine (biasRing hp hX hFw hB g st).E_phase_of hX (by decide) N.init
      (fun r hr ha => ?_) (fun hr _ ha => (N.arrive_rec hr ha).1) (fun hr hf ha => ?_)
      (fun y hy => ?_) hst
    · cases N.src r hr with
      | init ha' | poll _ _ ha' | arrive _ _ _ ha' => rw [ha] at ha'; cases ha'
    · obtain ⟨x, hx, hid⟩ := N.rec_S hr hf ha
      exact ⟨x, hx, hid⟩
    · rw [← hord]
      exact tma_item hp hX hFw hB (b_tmaOff st) hg rfl hg14
        ((biasRing hp hX hFw hB g st).E_items hX hy 1)
  have hge := tma_polls_le hp hX hFw (g := g) (b_tmaOff st) rfl (.inl hg14)
    (by rw [bE_eq]; exact PairTmaRing.poll_clean hX N.init N.noInval)
    (by rw [bE_eq]; exact N.noInval) (by rw [bE_eq]; exact hst)
  rw [bE_eq] at hge
  refine ⟨by omega, ?_⟩
  obtain ⟨b, hb⟩ := O.blocked hX hst
  exact ⟨b, (Unit.arrivals_le_unitRec hX (hff _) _).trans hb⟩

/-- **A blocked wait of a TMA group or the drain's Q wait has an earlier blocker.** -/
theorem tma_lag (hff : ∀ l, ∀ r ∈ X.objects l, r.fault = none) (hub : ¬ HasUb X)
    (hB : TmaBytes X) (hg : g < L.threads) {b : Bool} {d : Loader.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (.inr ⟨.loader b, d⟩, n)))
    (hg14 : Prologue.warpIndex L g = 14) {o K : Nat}
    (hW : TmaWait p L X g (Progress.time p L g (.inr ⟨.loader b, d⟩, n)) o K)
    {f : MBarrier.State} (hst : Final X (obj L g (o + 16)) f)
    (hpar : f.phase % 2 = (K + 1) % 2) : Sched.Blk (Progress.timed p L) X g := by
  have hne : X.tr g ≠ [] := by
    intro h0
    rw [show (X.tr g).length = 0 by rw [h0]; rfl, Frame.stateAt_zero] at hσ
    simp [thread, glued, Code.glue, Code.counted, Code.enter, Startup.code, exit] at hσ
  obtain ⟨hoff, hok, hord, hlate⟩ := hW
  have hblk : ∀ {y : Nat}, y < L.threads → y / L.block = g / L.block →
      ((∀ k pc, X.get (y, k) ≠ some ⟨pc, .exit⟩) ∧ Sched.threadTime (Progress.timed p L) X y <
        Progress.time p L g (.inr ⟨.loader b, d⟩, n)) → Sched.Blk (Progress.timed p L) X g := by
    intro y hyt hyc h
    exact Sched.blk_of_lags hX hub hg hne hσ hyt (by rw [hyc]) fun _ => h
  have hcase : (∃ s : Fin 2, o = 8 * s.val) ∨ ∃ st : Fin 2, o = 320 + 8 * st.val := by
    rcases hoff with rfl | rfl | rfl | rfl
    · exact .inl ⟨0, rfl⟩
    · exact .inl ⟨1, rfl⟩
    · exact .inr ⟨0, rfl⟩
    · exact .inr ⟨1, rfl⟩
  rcases hcase with ⟨s, rfl⟩ | ⟨st, rfl⟩
  · have hok' : okPolls (qE L g s) (X.tr g) = K := hok
    obtain ⟨hph, hcm⟩ := qE_lane hp hX hFw hff hB hg hg14 s (by rw [hord, hok']) hst
      (by rw [hok']; exact hpar)
    rw [hok'] at hph
    rcases hlate with h0 | ⟨R, bal, hP, ⟨st, v, ho, -⟩ | ⟨ho, hK, ht⟩⟩
    · omega
    · have := s.isLt; cases st <;> simp [Loader.fOff] at ho <;> omega
    rcases hcm with h | h
    swap
    · exact .inl ⟨.commit, .inl rfl, h⟩
    have hR : MmaRounds p L g _ := ⟨R, bal, hP, rfl⟩
    obtain ⟨z, hzt, hzc, hzw, hwin⟩ := warp_winner hp hX hg (w := 12) (by omega)
    have hRz := hR.cta hzc.symm
    have hcnt : (X.tr z).countP (commitsTo (obj L z 24)) ≤ 0 := by
      rw [obj_cta hzc]
      by_contra hgt
      obtain ⟨e, he, hea⟩ := List.countP_pos_iff.mp
        (show 0 < (X.tr z).countP (commitsTo (obj L g 24)) by omega)
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
      have hget : X.get (z, j) = some ((X.tr z)[j]) := List.getElem?_eq_getElem hj
      generalize (X.tr z)[j] = e at hget hea
      obtain ⟨pc, kd⟩ := e
      unfold commitsTo at hea
      split at hea
      · rename_i sp hk
        obtain rfl : kd = .tc (.commit sp) := hk
        obtain ⟨rank, ht'⟩ := commit_self hp hX hget
        rw [of_decide_eq_true hea] at ht'
        have hz := commitLane_eq hp hX hFw hget ht'
        have hs1 : s.val = 1 := by omega
        simp only [qE, qCons, hs1] at h
        rw [← hz] at h
        change (X.tr z).countP (commitsTo (obj L g 24)) ≤ f.phase at h
        omega
      · cases hea
    have hbm := mma_rounds_bmax hp hg hR
    refine hblk hzt hzc ⟨fun k pc hx => ?_, ?_⟩
    · have h1 := mma_exit_commits hp hX hFw hub hzt hzw hwin hRz hx 24
      have h2 := qE_total ((Mma.Bs p L g (mmaRef p L g R bal)).toNat - 1)
      omega
    · refine (qE_commit_early hp hX hFw hub hzt hzw hwin hRz hcnt).trans_le ?_
      refine le_trans (le_of_lt (Progress.drain_order p ?_ (by decide))) ht
      omega
  · have hok' : okPolls (bE L g st) (X.tr g) = K := by rw [← bE_eq]; exact hok
    rw [bE_eq] at hst
    obtain ⟨hph, bb, ha⟩ := bE_lane hp hX hFw hff hB hg hg14 st (by rw [hord, hok']) hst
      (by rw [hok']; exact hpar)
    rw [hok'] at hph
    rcases hlate with h0 | ⟨R, bal, hP, ⟨st', v, ho, hK, hv, ht⟩ | ⟨ho, -⟩⟩
    · omega
    swap
    · omega
    have hst2 := st.isLt
    have hb4 := bb.isLt
    have hbk := hp.block
    obtain ⟨hyc, hyw, hyl⟩ : biasLane L (g / L.block) st.val bb / L.block = g / L.block ∧
        Prologue.warpIndex L (biasLane L (g / L.block) st.val bb) = 4 * st.val + bb.val ∧
        laneOf L (biasLane L (g / L.block) st.val bb) = 0 := by
      simp only [biasLane, Prologue.warpIndex, laneOf, hbk]
      omega
    generalize biasLane L (g / L.block) st.val bb = y at ha hyc hyw hyl
    have hyt : y < L.threads := by
      have h1 : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul (by omega)).mpr hg
      rw [← hyc] at h1
      exact (Nat.div_lt_iff_lt_mul (by omega)).mp h1
    have hPy := Epilogue.Picked.cta hyc.symm hP
    have hstg : Softmax.stg L y = st' := by
      have key : ∀ w < 8, Epilogue.scmpi .gt .s (BitVec.ofNat 64 w) 3 = decide (4 ≤ w) := by decide
      have : Softmax.stg L y = decide (4 ≤ Prologue.warpIndex L y) :=
        key (Prologue.warpIndex L y) (by omega)
      rw [this, hyw]
      have hv2 : st.val = if st' then 1 else 0 := by
        cases st' <;> simp only [Loader.fOff, Bool.false_eq_true, ↓reduceIte] at ho ⊢ <;> omega
      rw [hv2]
      cases st' <;> simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not,
        decide_eq_true_eq] <;> omega
    have hB' : StageRounds p L y (Softmax.nB p L y (softRef p L y R bal)).toNat :=
      ⟨R, bal, hPy, rfl⟩
    have hrounds := Loader.biasPick_rounds (p := p) (L := L) (y := g) (g := y) hyc.symm R bal
    rw [hstg] at hrounds
    generalize (Softmax.nB p L y (softRef p L y R bal)).toNat = B at hB' hrounds
    obtain ⟨R', hR', hle⟩ := stage_rounds_bound hp hyt hB'
    have hbm : v ≤ Progress.bmax p := by omega
    have hstage : Progress.Sm.stage L y = st.val := by
      unfold Progress.Sm.stage; split <;> omega
    have hsob : sobj L y 336 = bE L g st := by
      rw [sobj, obj_cta hyc, hyw]
      simp only [bE]
      congr 1
      omega
    obtain ⟨h1, h2⟩ := soft_free_early hp hX hFw hub hyt (by omega) (lz_of_lane hp hyl) hB'
      (v := v) (by omega) (by
        rw [hstage]
        refine le_of_lt (Progress.drain_order p (by omega) ?_)
        have : st.val = 0 ∨ st.val = 1 := by omega
        rcases this with h | h <;> rw [h] <;> decide)
      (by rw [hsob]; omega)
    refine hblk hyt hyc ⟨h1, h2.trans_le (le_trans ?_ ht)⟩
    rw [hstage, Progress.slotOf_eq hbm]
    have : Progress.bandS st.val + 41 ≤ Progress.bandL := by
      have : st.val = 0 ∨ st.val = 1 := by omega
      rcases this with h | h <;> rw [h] <;> decide
    unfold Progress.clk
    omega

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
