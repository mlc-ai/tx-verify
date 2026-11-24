-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Mbar
public import Kernels.TmlFa4Fwd.Proof.Lib.BiasRounds
public import Kernels.TmlFa4Fwd.Proof.Loader.Export.TimeLag
public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.ArrAlt
import Kernels.TmlFa4Fwd.Proof.LdWarp.Page
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's Bias copies in the time table

`bias_lane`: the lane of warp 14 that wins its elections, short of group `u` of a Bias stage (its
arrival or its two copies on the stage's full barrier), is before slot `u`, if the tile takes the
group; it exits after all of them (`bias_exit`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {z : Nat}

/-- The Bias groups of stage `st` for block words `b`, `c`. -/
def biasOf (b c : BitVec 64) (st : Bool) : Nat :=
  1 + w0 b + if st = false ∧ 10 < sv b ∧ sv c < 0 then 1 else 0

theorem biasTot_of (v : V) (st : Bool) : biasTot v st = biasOf v.su.r28 v.su.r29 st := by
  unfold biasTot biasOf Last
  congr

/-- The other block word of the picked tile. -/
def r29Ref (p : Params) (L : Launch) (g R : Nat) (bal : BitVec 64) : BitVec 64 :=
  (setup p L g (refVL p L g R bal)).r29

/-- **The Bias groups of the picked tile.** -/
def biasPick (p : Params) (L : Launch) (g R : Nat) (bal : BitVec 64) (st : Bool) : Nat :=
  biasOf (r28Ref p L g R bal) (r29Ref p L g R bal) st

theorem biasPick_le (p : Params) (L : Launch) (g R : Nat) (bal : BitVec 64) (st : Bool) :
    biasPick p L g R bal st ≤ 1 + w0 (r28Ref p L g R bal) +
      if 10 < sv (r28Ref p L g R bal) then 1 else 0 := by
  unfold biasPick biasOf
  generalize r28Ref p L g R bal = b
  split_ifs with h1 h2 <;> omega

theorem SuS.pick {v : V} {g R : Nat} {bal : BitVec 64} (h : SuS p L g v)
    (hP : Epilogue.Picked p L g R bal) (st : Bool) : biasTot v st = biasPick p L g R bal st := by
  obtain ⟨R', bal', hP', e1, e2⟩ := h
  obtain ⟨rfl, rfl⟩ := hP'.unique hP
  rw [biasTot_of, e1, e2]
  rfl

/-- **The Bias groups are the softmax lanes' bias polls.** -/
theorem biasPick_rounds {y g : Nat} (hc : y / L.block = g / L.block) (R : Nat) (bal : BitVec 64) :
    biasPick p L y R bal (Softmax.stg L g) =
      1 + (Softmax.nB p L g (softRef p L g R bal)).toNat := by
  let su : Setup := ⟨0, 0, false, 0, 0, 0, 0, 0, 0, false, 0, 0, 0, 0, false, r28Ref p L y R bal,
    0, 0, false, r29Ref p L y R bal, false, 0, 0, 0, 0⟩
  have := bias_rounds (p := p) (L := L) (y := y) (g := g) hc R bal (v := { su := su }) rfl rfl
  rw [← this, biasTot_of]
  rfl

theorem r28Ref_ge (p : Params) (L : Launch) (g R : Nat) (bal : BitVec 64) :
    -2 ^ 24 ≤ sv (r28Ref p L g R bal) := r28_ge _

/-- The full barrier of stage `st`. -/
abbrev fOff (st : Bool) : Nat := if st then 328 else 320

/-- The sites with a group's arrival or copy to come, and the commits' forms. -/
private def lagChk (s : Site) : Bool :=
  [false, true].all fun st =>
    (!s.aft || (arrRem s (fOff st) == 0 && tcRem s (fOff st) == 0)) &&
    match biasForm st s with
    | some (true, e) => e + 1 + (inPkt s).2 ≥ 0 &&
        ((arrRem s (fOff st) == 0 && tcRem s (fOff st) == 0) || e ≥ 1)
    | some (false, c) => c ≤ 1 && (inPkt s).2 ≤ 1 && s.readsK == false && s.readsA == false &&
        arrAt s 0 0 ≤ 1
    | none => true

private theorem lag_chk : AllSites fun s => lagChk s = true := by
  unfold AllSites; decide +kernel

theorem rem_le (s : Site) (o : Nat) : arrRem s o ≤ 1 ∧ tcRem s o ≤ 2 := by
  cases s <;> simp only [arrRem, tcRem] <;> (try split_ifs) <;> omega

/-- **A state of the electing lane short of group `u`** is before slot `u`, and not past the
rounds. -/
theorem bias_state (hp : Pre p L m) {d : D} {n : Cls → Nat} {u : Nat} {st : Bool}
    (hJ : Ref p L z 14 (d, LdWarp.lcn n))
    (hF : LFits p L z d (n .shfl) (n .vote) (n (.load .commit)))
    (hN : BiasNum L z (d, LdWarp.lcn n)) (hS : SuPick p L z (d, LdWarp.lcn n))
    {R : Nat} {bal : BitVec 64}
    (hP : Epilogue.Picked p L z R bal) (hu : u < biasPick p L z R bal st)
    (hk : n (.load (nE L z st)) ≤ u ∨ n (.load (nE L z st)) = u + 1 ∧
      (arrRem d.site (fOff st) ≠ 0 ∨ tcRem d.site (fOff st) ≠ 0)) :
    d.site.aft = false ∧ Progress.Ld.time p d n + 1 < Progress.clk p u 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hN st
  have hchk := List.all_eq_true.mp (AllSites.ok lag_chk d.site) st (by cases st <;> simp)
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hchk
  obtain ⟨hc0, hc⟩ := hchk
  simp only [LdWarp.lcn] at h1 h2 h4
  have hpk : ∀ {v : V}, SuS p L z v → biasTot v st = biasPick p L z R bal st :=
    fun h => h.pick hP st
  have hself := AllSites.ok num_self d.site
  simp only [aftChk, Bool.and_eq_true, beq_iff_eq] at hself
  have hna : d.site.aft = false := by
    by_contra ha
    have ha : d.site.aft = true := by simpa using ha
    have hz := hc0.resolve_left (by simp [ha])
    have hk' : n (.load (nE L z st)) ≤ u := by
      rcases hk with hk | ⟨-, hk⟩
      · exact hk
      · simp [hz.1, hz.2] at hk
    rcases h4 ha with ⟨q1, q2, -⟩ | q
    · simp only [LFits, q1] at hF
      obtain ⟨l, -, hFE, hl, -⟩ := hF
      cases l with
      | false => exact noPick hFE hP
      | true =>
        have := (hl rfl).2
        have := pkts_two d.v.su.r28
        omega
    · have hb : SuS p L z d.v := by
        have hcl : lc d.site = .blk ∨ lc d.site = .p2 ∨ lc d.site = .drain := by
          have : AllSites fun s => (!s.aft || (lc s == .blk || lc s == .p2 || lc s == .drain)) =
              true := by unfold AllSites; decide +kernel
          have := AllSites.ok this d.site
          simp only [ha, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at this
          exact or_assoc.mp this
        rcases hcl with hcl | hcl | hcl
        · exact hS.1 (.inl hcl)
        · exact hS.1 (.inr hcl)
        · refine (hS.2 hcl).resolve_left fun h0 => ?_
          simp only [LFits, hcl] at hF
          obtain ⟨l, -, hFE, hl, -⟩ := hF
          cases l with
          | false => exact noPick hFE hP
          | true =>
            have := (hl rfl).2
            have := pkts_two d.v.su.r28
            simp only [LdWarp.lcn] at h0
            omega
      rw [hpk hb] at q
      omega
  refine ⟨hna, ?_⟩
  have hform : (biasForm st d.site).isSome = true := by
    have : d.site.aft = (biasForm st d.site).isNone := by
      cases st
      · exact hself.1.1.1.1
      · exact hself.1.1.1.2
    rw [hna] at this
    cases hf : biasForm st d.site with
    | none => rw [hf] at this; cases this
    | some _ => rfl
  -- the packets published
  have hpub : n (.load .commit) - (inPkt d.site).2 ≤ 2 * u + 1 := by
    cases hf : biasForm st d.site with
    | none => rw [hf] at hform; cases hform
    | some x =>
      obtain ⟨b, e⟩ := x
      rw [hf] at hc
      cases b
      · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        have hcm := hJ.commit
        simp only [LdWarp.lcn] at hcm
        have := (forms_pos (s := d.site) (k := 0) (A := 0) (k' := posK (d, LdWarp.lcn n))
          (A' := posA (d, LdWarp.lcn n)) (by simp [hc.1.1.2]) (by simp [hc.1.2])).1
        rw [this] at hcm
        omega
      · have := h2 e hf
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        rcases hk with hk | ⟨hk, hk'⟩
        · omega
        · have h1e := hc.2.resolve_left (by rintro ⟨q1, q2⟩; simp [q1, q2] at hk')
          omega
  have hlt : 2 * u + 1 < pkts (r28Ref p L z R bal) := by
    have hl := biasPick_le p L z R bal st
    have hge := r28Ref_ge p L z R bal
    generalize r28Ref p L z R bal = b at hl hge ⊢
    have hw9 := wRn_le b
    have hw0 : w0 b ≤ wRn b := by unfold w0; split <;> omega
    have hg : sv (addi b (-1)) = sv b - 1 := sv_addi_neg1 _ (by omega)
    unfold pkts
    rw [hg]
    split_ifs at hl <;> omega
  have := state_early hp hJ hF hP hlt hpub
  refine this.trans_le ?_
  unfold Progress.Ld.bound
  split_ifs with h
  · rw [show u = 0 by omega]; unfold Progress.clk; omega
  · have : Progress.slotOf p ((2 * u + 1 - 2) / 2) + 1 ≤ u := by
      unfold Progress.slotOf; omega
    have := Nat.mul_le_mul_left Progress.span this
    unfold Progress.clk
    omega

/-- The state of a loader lane's exit is past the drain. -/
theorem exit_done (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : z < L.threads) (hw : Prologue.warpIndex L z = 14 ∨ Prologue.warpIndex L z = 15)
    {k pc : Nat} (hx : X.get (z, k) = some ⟨pc, .exit⟩) :
    ∃ σ, Frame.stateAt (thread p L) X z k = some (some σ) ∧
      Progress.doneBase p ≤ Progress.time p L z σ := by
  obtain ⟨σ, hσ, hJ⟩ := good_state hp hX hx (by intro _ _ h; cases h)
    (LdWarp.good hp hX hw hg rfl k)
  refine ⟨σ, hσ, ?_⟩
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨i, d⟩
  · exfalso
    obtain ⟨hev, hx, -⟩ := start_fired hp hX hx hσ
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | sh j => fin_cases j <;> simp [Startup.Ev] at hev
    | elect j => simp [Startup.Ev] at hev
    | init q => simp [Startup.Ev] at hev
    | fence => simp [Startup.Ev] at hev
    | bar => simp [Startup.Ev] at hev
    | enter r => simp [exit] at hx
  cases i with
  | loader b =>
    have hev := (LdWarp.lfired hp hX hx hσ).1
    obtain ⟨site, v, kk⟩ := d
    cases site
    case exit =>
      simp only [Progress.time, Progress.roleTime, Progress.Ld.time]
      omega
    all_goals exfalso
    all_goals simp only [Loader.Ev, Epilogue.Ev, Loader.Site.toE] at hev
    all_goals simp at hev
  | _ => exact hJ.elim

/-- In a warm round or at the last Bias group the polls are at most the round's groups. -/
private def leChk (s : Site) : Bool :=
  [false, true].all fun st => match biasForm st s with
    | some (true, e) => (bc s == some .warm && e + inBlk s ≤ 2) ||
        (s.lastGrp && bc s == some .tma6 && inBlk s == 0 && e ≤ (if st then 0 else 2))
    | some (false, c) => c ≤ 1
    | none => s.aft

private theorem le_chk : AllSites fun s => leChk s = true := by
  unfold AllSites; decide +kernel

/-- **The Bias groups so far are at most the picked tile's.** -/
theorem bias_le (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hz : z < L.threads) (hw : Prologue.warpIndex L z = 14) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X z k = some (some (LdWarp.linj p L z b d n)))
    (hub0 : n .ub = 0) (hF : LFits p L z d (n .shfl) (n .vote) (n (.load .commit)))
    (hb : d.site.blk = true) (st : Bool) :
    ∃ R bal, Epilogue.Picked p L z R bal ∧
      n (.load (nE L z st)) ≤ biasPick p L z R bal st := by
  obtain ⟨-, -, -, ⟨-, hR⟩, -⟩ := lfits_blk_of hb hF
  have hS := (su_pick hp hX hz (.inl hw) hσ hub0).1 (.inl (lc_blk.mpr hb))
  obtain ⟨R, bal, hP, e1, e2⟩ := id hS
  refine ⟨R, bal, hP, ?_⟩
  rw [← hS.pick hP st]
  obtain ⟨h1, h2, h3, h4⟩ := bias_num hp hX hz hw hσ hub0 st
  simp only [LdWarp.lcn] at h1 h2 h3 h4
  have hc := List.all_eq_true.mp (AllSites.ok le_chk d.site) st (by cases st <;> simp)
  cases hf : biasForm st d.site with
  | none =>
    rw [hf] at hc
    rcases h4 hc with ⟨q, -⟩ | q
    · rw [lc_blk.mpr hb] at q; cases q
    · exact q.le
  | some x =>
    obtain ⟨c, e⟩ := x
    rw [hf] at hc
    cases c
    · have := h1 _ hf
      simp only [decide_eq_true_eq] at hc
      unfold biasTot
      omega
    · have := h2 _ hf
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      rcases hc with ⟨q1, q2⟩ | ⟨⟨⟨q1, q2⟩, q3⟩, q4⟩
      · rw [q1] at hR
        obtain ⟨r, -, hr2, hlt, hnc⟩ := hR
        rw [biasTot, w0_of hr2]
        omega
      · rw [q2, q3] at hR
        obtain ⟨-, hr2, hnc⟩ := hR
        have hL : Last d.v := h3 q1
        rw [biasTot, w0_of hr2]
        cases st <;> simp [hL] at q4 ⊢ <;> omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
  (hub : ¬ HasUb X) (hz : z < L.threads) (hw : Prologue.warpIndex L z = 14)
  (hwon : ∀ k pc mask inst ld, X.get (z, k) = some ⟨pc, .elect mask inst ld⟩ → ld = laneOf L z)
  {R : Nat} {bal : BitVec 64} (hP : Epilogue.Picked p L z R bal)
include hp hX hub hz hw hwon hP

/-- **A lane short of group `u`** at a state: before slot `u`. -/
theorem bias_at {u k : Nat} {st : Bool} (hu : u < biasPick p L z R bal st)
    (hs : arrivals (obj L z (fOff st)) ((X.tr z).take k) ≤ u ∨
      ((X.tr z).take k).countP (issuesTo (obj L z (fOff st))) < 2 * (u + 1))
    {σ : (thread p L z).D} (hσ : Frame.stateAt (thread p L) X z k = some (some σ)) :
    Progress.time p L z σ + 1 < Progress.clk p u 0 := by
  have hpc : Progress.pipeBase p ≤ Progress.clk p u 0 := by unfold Progress.clk; omega
  rcases lane_cases hp hX hub hz (.inl hw) hσ with h | ⟨b, d, n, rfl, hub0, hJ, hF⟩
  · unfold Progress.pipeBase at hpc; omega
  · rw [hw] at hJ
    have ho : fOff st ∈ [0, 320, 328] := by cases st <;> simp
    have h1 := arr_alt ho hp hX hz hwon (.inl hw) hσ hub0
    have h2 := tc_alt ho hp hX hz hwon (.inl hw) hσ hub0
    have h3 : arrivals (obj L z (fOff st)) ((X.tr z).take k) =
        n (.load (.arrive (bl L z (fOff st)))) := count hσ (.load (.arrive (bl L z (fOff st))))
    have h4 : ((X.tr z).take k).countP (issuesTo (obj L z (fOff st))) =
        ((X.tr z).take k).countP (isTc L z (fOff st)) := rfl
    have hn : nE L z st = .acquire (bl L z (fOff st + 16)) := by cases st <;> rfl
    have hr := rem_le d.site (fOff st)
    simp only [TcAlt, LdWarp.lcn] at h2
    rw [h3, h4] at hs
    exact (bias_state hp hJ hF (bias_num hp hX hz hw hσ hub0)
      (su_pick hp hX hz (.inl hw) hσ hub0) hP hu (by rw [hn]; omega)).2

/-- **The electing lane short of group `u`** has not exited and is before slot `u`. -/
theorem bias_lane {u : Nat} {st : Bool} (hu : u < biasPick p L z R bal st)
    (hd : Progress.clk p u 0 ≤ Progress.doneBase p)
    (hs : arrivals (obj L z (fOff st)) (X.tr z) ≤ u ∨
      (X.tr z).countP (issuesTo (obj L z (fOff st))) < 2 * (u + 1)) :
    (∀ k pc, X.get (z, k) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (Progress.timed p L) X z < Progress.clk p u 0 := by
  have key : ∀ k σ, Frame.stateAt (thread p L) X z k = some (some σ) →
      Progress.time p L z σ + 1 < Progress.clk p u 0 := by
    intro k σ hσ
    refine bias_at hp hX hub hz hw hwon hP hu ?_ hσ
    have h1 : arrivals (obj L z (fOff st)) ((X.tr z).take k) ≤
        arrivals (obj L z (fOff st)) (X.tr z) := (List.take_sublist _ _).countP_le
    have h2 : ((X.tr z).take k).countP (issuesTo (obj L z (fOff st))) ≤
        (X.tr z).countP (issuesTo (obj L z (fOff st))) := (List.take_sublist _ _).countP_le
    omega
  refine ⟨fun k pc hx => ?_, ?_⟩
  · obtain ⟨σ, hσ, hle⟩ := exit_done hp hX hz (.inl hw) hx
    have := key _ _ hσ
    omega
  · have h0 : 0 < Progress.clk p u 0 := by unfold Progress.clk Progress.pipeBase; omega
    unfold Sched.threadTime
    split
    · rename_i d hd; exact Nat.lt_of_succ_lt (key _ d hd)
    · exact h0
    · split
      · rename_i d hd; exact key _ d hd
      · exact h0

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
