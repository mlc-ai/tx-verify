-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.MmaPoll
public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Obj
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Start
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Input
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Loader.Export.QGroup
import Kernels.TmlFa4Fwd.Proof.Loader.Export.QIssue
import Kernels.TmlFa4Fwd.Proof.Loader.Export.QTx
import Kernels.TmlFa4Fwd.Proof.Loader.Export.TimeLag
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
import Lemmas.Kernel.ElectSource
import Lemmas.Flow.NthEv
import Lemmas.Kernel.Progress.HandoffBlockers
import Lemmas.Protocol.TmaUnitCount
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Lag
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader half of the MMA warp's poll premise: the Q polls

A lane of warp 12 at a Q poll has polled the stage's full barrier successfully no time, so the poll
is blocked only in phase 0 (`MbarRing.TmaUnitObject.phase_le`: a completed phase takes two copies
of 16384 bytes, at most two complete on the stage, `q_issue`). The phase is complete when the
elected lane of warp 14 (`q_winner`) has made the group's arrival and both copies and no copy is
open (`Sched.blk_tmaUnit`); it has made them when it is past the first four TMA groups
(`Loader.q_done`), and before that it is before the pipeline (`Loader.group_early`). So the poll
is blocked by an open tensor copy or by that lane (`q_lag`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (RefQ)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A Q poll is at place 1 or 9, before any successful poll of its stage. -/
theorem q_poll {d : Mma.D} {n : Mma.Cnt → Nat} {r : Nat}
    (hs : Progress.isPoll d.site = true)
    (ho : Progress.pollO r d.site = 0 ∨ Progress.pollO r d.site = 8)
    (hpre : d.site.ord < 20 → r = 0)
    (hacq : ∀ o, n (.acquire (Mma.bl L g o)) = Mma.acqAt d.site.ord r o) :
    (d.site.ord = 1 ∨ d.site.ord = 9) ∧
      n (.acquire (Mma.bl L g (Progress.pollO r d.site))) = 0 := by
  have key : (d.site.ord = 1 ∧ Progress.pollO r d.site = 0) ∨
      (d.site.ord = 9 ∧ Progress.pollO r d.site = 8) := by
    clear hacq hpre
    obtain ⟨site, v⟩ := d
    cases site <;> simp only [Progress.isPoll, reduceCtorEq, Bool.false_eq_true] at hs
    case wt k =>
      fin_cases k <;> simp only [Progress.pollO, Mma.Site.ord, Fin.isValue, Fin.reduceFinMk,
        Fin.val_mk, List.getD_cons_succ, List.getD_cons_zero] at ho ⊢ <;>
          first | (simp; done) | omega
    case mw b ld =>
      simp only [Progress.pollO] at ho
      split at ho <;> omega
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨.inl h1, ?_⟩
    rw [hacq, h1, h2, hpre (by omega)]
    decide
  · refine ⟨.inr h1, ?_⟩
    rw [hacq, h1, h2, hpre (by omega)]
    decide

/-- **The lane of warp 14 that wins every election it makes**: the lane an election of the warp
returned, or any lane while there is none. Every lane that won an election is this lane. -/
theorem q_winner (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∃ z, z < L.threads ∧ z / L.block = g / L.block ∧ Prologue.warpIndex L z = 14 ∧
      (∀ j pc inst ld, X.get (z, j) = some ⟨pc, .elect (2 ^ 32 - 1) inst ld⟩ →
        ld = laneOf L z) ∧
      ∀ x j pc mk inst, x / L.block = g / L.block → Prologue.warpIndex L x = 14 →
        X.get (x, j) = some ⟨pc, .elect mk inst (laneOf L x)⟩ → x = z := by
  have hb := hp.block
  have hgr : g / 512 < L.grid := by
    have : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul (by omega)).mpr hg
    rwa [hb] at this
  have hbase : (g / 512 + 1) * 512 ≤ L.grid * 512 := Nat.mul_le_mul_right _ hgr
  -- the lanes of warp 14 of the CTA
  have hlane : ∀ l < 32, g / 512 * 512 + 448 + l < L.threads ∧
      (g / 512 * 512 + 448 + l) / L.block = g / L.block ∧
      Prologue.warpIndex L (g / 512 * 512 + 448 + l) = 14 ∧
      laneOf L (g / 512 * 512 + 448 + l) = l := by
    intro l hl
    simp only [Launch.threads, Prologue.warpIndex, laneOf, hb]
    omega
  have hx14 : ∀ x, x / L.block = g / L.block → Prologue.warpIndex L x = 14 →
      x = g / 512 * 512 + 448 + laneOf L x := by
    intro x h1 h2
    simp only [Prologue.warpIndex, laneOf, hb] at h1 h2 ⊢
    omega
  have hsame : ∀ x y, x < L.threads → y < L.threads → x / L.block = g / L.block →
      y / L.block = g / L.block → Prologue.warpIndex L x = 14 → Prologue.warpIndex L y = 14 →
      SameWarp L x y := fun x y h1 h2 h3 h4 h5 h6 =>
    ⟨⟨h1, h2, h3.trans h4.symm⟩, by simp only [Prologue.warpIndex] at h5 h6; omega⟩
  by_cases hE : ∃ x j pc inst ld, x / L.block = g / L.block ∧ Prologue.warpIndex L x = 14 ∧
      X.get (x, j) = some ⟨pc, .elect (2 ^ 32 - 1) inst ld⟩
  · obtain ⟨x, j, pc, inst, ld, hxc, hx, he⟩ := hE
    have hld : ld < 32 := ((hX.elect.1 (x, j) pc _ inst ld he).2.2).1
    obtain ⟨z1, z2, z3, z4⟩ := hlane ld hld
    have hxt := Frame.lt_of_get hX he
    refine ⟨_, z1, z2, z3, fun j' pc' inst' ld' he' => ?_, fun y j' pc' mk inst' hyc hy he' => ?_⟩
    · rw [z4]
      exact elect_leader hX he' he (hsame _ _ z1 hxt z2 hxc z3 hx)
    · have hm := elect_full hX (show X.Elect (y, j') pc' mk inst' (laneOf L y) from he')
      subst hm
      have := elect_leader hX he' he (hsame _ _ (Frame.lt_of_get hX he') hxt hyc hxc hy hx)
      rw [hx14 y hyc hy, this]
  · push Not at hE
    obtain ⟨z1, z2, z3, -⟩ := hlane 0 (by omega)
    refine ⟨_, z1, z2, z3, fun j pc inst ld he => absurd he (hE _ _ _ _ _ z2 z3),
      fun y j pc mk inst hyc hy he => ?_⟩
    have hm := elect_full hX (show X.Elect (y, j) pc mk inst (laneOf L y) from he)
    subst hm
    exact absurd he (hE _ _ _ _ _ hyc hy)

/-- A poll is in the pipeline. -/
theorem poll_pipe {s : Mma.Site} (hs : Progress.isPoll s = true) : s.pipe = true := by
  cases s <;> simp_all [Progress.isPoll, Mma.Site.pipe]

/-- **A copy that completes on a Q stage** is a lane of warp 14's, after it won an election, and
the lane has issued at most one such copy before. -/
theorem q_issue (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {o : Nat} (ho : QOff o) {h k pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get (h, k) = some ⟨pc, .tensorIssue a sp⟩) (hm : sp.mbar = obj L g o) :
    h / L.block = g / L.block ∧ Prologue.warpIndex L h = 14 ∧
      (∃ j pc' mk inst, X.get (h, j) = some ⟨pc', .elect mk inst (laneOf L h)⟩) ∧
      ((X.tr h).take k).countP (issuesTo (obj L g o)) ≤ 1 := by
  obtain ⟨hc, hu⟩ := bar_use hp hX hFw he (show MbarOf _ _ from hm) (fun _ h => by cases h)
  have hl : obj L h o = obj L g o := by simp only [obj, hc]
  refine ⟨hc, ?_⟩
  rw [← hl]
  have hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15 := by
    cases hu with
    | ldCopy _ _ hw _ _ _ => exact hw
    | epiPoll _ _ _ _ hk _ | epiArr _ _ _ hk _ | corrArr _ _ hk | corrPoll _ _ _ hk
    | softArr _ _ _ _ hk | softPoll _ _ _ _ _ hk | mmaPoll _ _ _ hk | mmaCommit _ _ _ hk _ _ _
    | ldPoll _ _ _ _ hk | ldAsync _ _ hk | ldArr _ _ _ hk => cases hk
  exact Loader.q_issue hp hX hFw ho hw he (hm.trans hl.symm)

set_option maxHeartbeats 4000000 in
/-- **The loader half of the MMA warp's poll premise at the Q polls**: an open tensor copy, or the
elected loader lane before the end of its groups. -/
theorem q_lag (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hfree : ∀ l, ∀ r ∈ X.objects l, r.fault = none) (hub : ¬ HasUb X)
    (hg : g < L.threads) (hg12 : Prologue.warpIndex L g = 12) {d : Mma.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (Mma.minj p L g d n)))
    (hs : Progress.isPoll d.site = true) {r : Nat} {w : Bool}
    (hQ : RefQ p L g d.site.ord d.v (Mma.rc n) r w)
    (ho : Progress.pollO r d.site = 0 ∨ Progress.pollO r d.site = 8) :
    ∃ before, MBarrier.stateBefore (X.objects (Mma.bl L g (Progress.pollO r d.site)))
        (X.objects (Mma.bl L g (Progress.pollO r d.site))).length = some before ∧
      (before.phase % 2 = n (.mma (.acquire (Mma.bl L g (Progress.pollO r d.site)))) % 2 →
        Sched.Blk (Progress.timed p L) X g) := by
  have hT := table_shape_of hp hFw
  have hFl := table_followed hp hX hFw
  have hb := hp.block
  obtain ⟨hq, hacq0⟩ := q_poll hs ho hQ.pre hQ.acq
  have hr : r = 0 := hQ.pre (by omega)
  set o := Progress.pollO r d.site with hodef
  have hoQ : QOff o := by rcases ho with h | h <;> simp [QOff, h]
  have O := qObj hp hX hFw hoQ g
  -- the history holds the startup's initialization
  have hlen : 0 < (X.tr g).length := by
    by_contra h0
    rw [show (X.tr g).length = 0 by omega, Frame.stateAt_zero] at hσ
    simp [thread, glued, Code.glue, Code.counted, Code.enter, Startup.code, exit] at hσ
  have hne : X.objects (obj L g o) ≠ [] := by
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[(X.tr g).length - 1]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hσ' : Frame.stateAt (thread p L) X g ((X.tr g).length - 1 + 1) =
        some (some (Mma.minj p L g d n)) := by
      rw [show (X.tr g).length - 1 + 1 = (X.tr g).length by omega]; exact hσ
    obtain ⟨⟨i, dr⟩, n0, hσ0⟩ := mma_prev he hσ'
    have hb0 := role_bar0 hp hX _ hσ0
    obtain ⟨j0, c, hinit, -⟩ := init_exists hp hX hT hFl hg (by omega) hb0 (o := o)
      (by rcases hoQ with h | h <;> rw [h] <;> decide)
    obtain ⟨i, r0, hi, -⟩ := init_record_of_consistent hX hinit
    intro h0
    rw [h0] at hi
    simp at hi
  obtain ⟨before, hst⟩ := MbarRing.Unit.final_of_init hX O.init O.noInval hne
  refine ⟨before, hst, fun hph => ?_⟩
  -- the elected loader lane, and the copies on the stage
  obtain ⟨z, hzt, hzc, hz14, hzwin, hzuniq⟩ := q_winner hp hX hg
  have hcomp : MBarrier.completedTxCount (X.objects (obj L g o)) ≤ 2 := by
    refine (O.completions_le_issues hX (z := z) fun ⟨h, k⟩ pc a sp he hm => ?_).trans ?_
    · obtain ⟨hc, hw, ⟨j, pc', mk, inst, hel⟩, -⟩ := q_issue hp hX hFw hoQ he hm
      exact hzuniq h j pc' mk inst hc hw hel
    · by_contra hgt
      obtain ⟨k, -, ⟨pc, kd⟩, hk, hq', hcnt⟩ := Flow.exists_nth (issuesTo (obj L g o)) (X.tr z)
        (n := 2) (k := (X.tr z).length) (by rw [List.take_length]; omega)
      cases kd <;> simp [issuesTo] at hq'
      rename_i a sp
      have := (q_issue hp hX hFw hoQ (h := z) (k := k) hk hq').2.2.2
      omega
  have hbyt : MBarrier.UniformCompletedTx (X.objects (obj L g o)) 16384 := by
    intro q hq' _ B hB
    cases O.source q hq' with
    | init h | poll h | arrive _ _ _ h => rw [hB] at h; cases h
    | tensor _ he _ h =>
      rw [hB] at h
      cases h
      exact input_bytes hp hX hFw he
  have harr : ∀ q ∈ X.objects (obj L g o), q.fault = none → ∀ c tx, q.action = .arrive c tx →
      c = 1 ∧ tx = 2 * 16384 := by
    intro q hq' _ c tx ha
    cases O.source q hq' with
    | init h | poll h | tensor _ _ _ h => rw [ha] at h; cases h
    | arrive _ hgl he h =>
      rw [ha] at h
      cases h
      exact ⟨rfl, ld_arr_tx hp hX hFw hgl.2 he⟩
  have hphase : before.phase = 0 := by
    have h1 := O.phase_le hX hst (n := 2) (B := 16384) (by norm_num)
      (fun q hq' hf c tx ha => (harr q hq' hf c tx ha).2) hbyt
    have h2 : n (.mma (.acquire (Mma.bl L g o))) = 0 := hacq0
    rw [h2] at hph
    omega
  -- the tile
  have hpipe := poll_pipe hs
  obtain ⟨-, hFm⟩ := Progress.mma_ref hp hX hub hg hg12 hσ
  obtain ⟨R, bal, hC, -⟩ := Mma.bs_ref (Mma.pmid_of hpipe) hFm
  have hPz := Epilogue.Picked.cta hzc.symm hC.1
  have htime : Progress.pipeBase p ≤ Progress.time p L g (Mma.minj p L g d n) := by
    simp only [Progress.time, Progress.roleTime, Progress.Mm.time, hpipe, ite_true,
      Progress.Mm.pipeT, Progress.clk]
    omega
  -- past the groups the lane made the stage's arrival and copies
  obtain ⟨t, ht, hto⟩ := Loader.q_grp hoQ
  have hobj : obj L z o = obj L g o := by simp only [obj, hzc]
  have hdone : ∀ k {b d' n'}, Frame.stateAt (thread p L) X z k =
      some (some (LdWarp.linj p L z b d' n')) → n' .ub = 0 →
      1000 ≤ Loader.ppos (decide (n' (.load .commit) = 0)) d'.site →
      ¬ (arrivals (obj L g o) (X.tr z) ≤ before.phase ∨
        (X.tr z).countP (issuesTo (obj L g o)) < 2 * (before.phase + 1)) := by
    intro k b d' n' hσ' h0 hpast hor
    have hd := Loader.q_done hp hX hzt hz14 hub hσ' h0 hpast hzwin (t := t)
      (by rcases ht with rfl | rfl <;> simp)
    rw [hto, show Loader.bl L z o = obj L g o from hobj] at hd
    have h1 : arrivals (obj L g o) ((X.tr z).take k) ≤ arrivals (obj L g o) (X.tr z) :=
      (List.take_sublist _ _).countP_le
    have h2 : ((X.tr z).take k).countP (issuesTo (obj L g o)) ≤
        (X.tr z).countP (issuesTo (obj L g o)) := (List.take_sublist _ _).countP_le
    omega
  refine Sched.blk_tmaUnit hX hub O (hfree _) (n := 2) (B := 16384) ?_ hbyt hst (by omega) hg
    (fun h => by rw [h] at hlen; simp at hlen) hσ hzt (by rw [hzc]) (fun hor _ => ?_)
  · rw [MBarrier.expectedTxBytes_unit harr]
  -- the lane is before the end of the groups
  have hcase : ∀ k σ, Frame.stateAt (thread p L) X z k = some (some σ) →
      Progress.time p L z σ + 1 < Progress.pipeBase p := by
    intro k σ hσ'
    rcases Loader.group_early hp hX hub hzt (.inl hz14) hPz hσ' with h | ⟨b, d', n', rfl, h0, hpast⟩
    · exact h
    · exact (hdone k hσ' h0 hpast hor).elim
  refine ⟨fun k pc hx => ?_, ?_⟩
  · obtain ⟨σ, hσ', h2⟩ := Loader.exit_late hp hX hzt (.inl hz14) hx
    have h1 := hcase k σ hσ'
    omega
  · have h0 : 0 < Progress.pipeBase p := by unfold Progress.pipeBase; omega
    refine lt_of_lt_of_le ?_ htime
    unfold Sched.threadTime
    split
    · rename_i d1 hd
      exact Nat.lt_of_succ_lt (hcase _ d1 hd)
    · exact h0
    · split
      · rename_i d1 hd
        exact hcase _ d1 hd
      · exact h0

end
end PTX.Kernels.TmlFa4Fwd.Proof
