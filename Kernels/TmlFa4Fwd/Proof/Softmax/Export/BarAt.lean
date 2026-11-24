-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BarLag
import Kernels.TmlFa4Fwd.Proof.Lib.NoPicked
import Kernels.TmlFa4Fwd.Proof.SmWarp.Counts
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A softmax lane's barrier events in the time table

`soft_bar_at`: a barrier event of a softmax lane at a role state is its first or last on barrier 2,
or on a named barrier at a place of its tile, whose time is the state's; `soft_bar_next`: it leads
to
a later state. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (ptsOf passed before allSites mem_allSites Reg ordK
  val valT sm)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

private theorem at_tab : [false, true].all (fun b =>
    decide (passed (ptsOf b .bar2) .bar1 0 0 = 0) &&
    [false, true].all fun l => decide ((ptsOf b .bar2).countP (before (.barEnd l)) = 1)) = true :=
        by
  decide +kernel

private theorem bar2_rnd (b : Bool) : (ptsOf b .bar2).countP Softmax.inBias = 0 ∧
    (ptsOf b .bar2).countP Softmax.inPlain = 0 := by cases b <;> decide +kernel

private def nbChk (st : Nat) (s : Softmax.Site) : Bool :=
  match Softmax.sig s with
  | some .nb | some .sb => (val st s).isSome && decide (s.pos ≤ 15232) && s.hasUk && !s.noTile
  | _ => true

private theorem nb_chk : [0, 1].all (fun st => allSites.all (nbChk st)) = true := by
  decide +kernel

private theorem picked_of_fits {d : Softmax.D} {ns nv : Nat} (hF : SmWarp.SFits p L g d ns nv)
    (huk : d.site.hasUk = true) : ∃ R bal, Epilogue.Picked p L g R bal := by
  have hFE := hF.1
  have hep : SmWarp.epi d.site = .ready 0 := by
    revert huk
    cases d.site <;> simp [Softmax.Site.hasUk, Softmax.Site.rgn, SmWarp.epi]
  simp only [Epilogue.Fits, SmWarp.toE, hep] at hFE
  obtain ⟨R, bal, hC, -⟩ := hFE
  exact ⟨R, bal, hC.1⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hw : Prologue.warpIndex L g < 8)
include hp hX hFw hub hw

/-- **A barrier event of a softmax lane at a role state.** -/
theorem soft_bar_at {pc id : Nat} {cnt : Option Nat} {md : BarMode} {d : Softmax.Control.D}
    {n : Cls → Nat} (he : X.get (g, k) = some ⟨pc, .bar id cnt md⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (SmWarp.sinj p L g d n))) :
    (id = 2 ∧ md = .sync ∧ d.scheduler.site = .bar1 ∧
        ((X.tr g).take k).countP (Execution.isBarId id) = 0 ∧
        Progress.Sm.time p L g d.scheduler n = Progress.scanBase + 3) ∨
    (∃ l, id = 2 ∧ md = .arrive ∧ d.scheduler.site = .barEnd l ∧
        ((X.tr g).take k).countP (Execution.isBarId id) = 1 ∧
        (l = true ↔ ∃ R bal, Epilogue.Picked p L g R bal) ∧
        Progress.Sm.time p L g d.scheduler n = Progress.endT p l 4) ∨
    ∃ c B P rb rp a, (c = .nb ∨ c = .sb) ∧ id = softBarId L g c ∧ (c = .sb → md = .sync) ∧
      (c = .nb → md = .arrive) ∧ SoftTile p L g B P ∧
      Softmax.sig d.scheduler.site = some c ∧ val (Progress.Sm.stage L g) d.scheduler.site = some a
          ∧
      Reg B P d.scheduler.site rb rp ∧ d.scheduler.site.noTile = false ∧ d.scheduler.site.pos ≤
          15232 ∧
      Progress.Sm.time p L g d.scheduler n = valT p (rb + rp) a ∧
      ((X.tr g).take k).countP (Execution.isBarId id) =
        passed (ptsOf (Softmax.lz L g) c) d.scheduler.site rb rp := by
  have hg := Frame.lt_of_get hX he
  have hst : Progress.Sm.stage L g = 0 ∨ Progress.Sm.stage L g = 1 := by
    unfold Progress.Sm.stage; split <;> simp
  have hev : Softmax.Ev p L g d.scheduler ⟨pc, .bar id cnt md⟩ := by
    rcases SmWarp.open_ev hp hX hFw hw he (fun f h => by cases h) with ⟨s, n', hσ', -⟩ |
      ⟨d', n', hσ', -, -, -, hev⟩
    · rw [hσ] at hσ'; cases hσ'
    · rw [hσ] at hσ'; cases hσ'; exact hev.1
  rcases soft_place hp hX hFw hub hg hw hσ with ⟨-, s, n', h1, -⟩ |
    ⟨d', n', rb, rp, h1, -, h3, hc, hwt, hF, hreg, hno⟩
  · cases h1
  cases h1
  -- a named barrier's place
  have named : ∀ c, (c = .nb ∨ c = .sb) → Softmax.sig d.scheduler.site = some c →
      id = softBarId L g c → (c = .sb → md = .sync) → (c = .nb → md = .arrive) →
      ∃ c B P rb rp a, (c = Softmax.Cnt.nb ∨ c = .sb) ∧ id = softBarId L g c ∧
      (c = .sb → md = .sync) ∧ (c = .nb → md = .arrive) ∧ SoftTile p L g B P ∧
      Softmax.sig d.scheduler.site = some c ∧ val (Progress.Sm.stage L g) d.scheduler.site = some a
          ∧
      Reg B P d.scheduler.site rb rp ∧ d.scheduler.site.noTile = false ∧ d.scheduler.site.pos ≤
          15232 ∧
      Progress.Sm.time p L g d.scheduler n = valT p (rb + rp) a ∧
      ((X.tr g).take k).countP (Execution.isBarId id) =
        passed (ptsOf (Softmax.lz L g) c) d.scheduler.site rb rp := by
    intro c hcc hs hid hm1 hm2
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp nb_chk (Progress.Sm.stage L g) (by
      rcases hst with h | h <;> simp [h])) d.scheduler.site (mem_allSites _)
    have h2 : (val (Progress.Sm.stage L g) d.scheduler.site).isSome = true ∧ d.scheduler.site.pos ≤
        15232 ∧
        d.scheduler.site.hasUk = true := by
      unfold nbChk at h1
      rw [hs] at h1
      rcases hcc with rfl | rfl <;>
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
          exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2⟩
    obtain ⟨h2, h4, huk⟩ := h2
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h2
    obtain ⟨B, P, hT⟩ := exists_softTile (picked_of_fits hF huk)
    obtain ⟨hr, ht⟩ := hreg B P hT
    have hA : SoftAt p L g B P d.scheduler n rb rp := ⟨h3, hc, hwt, hF, hr, ht⟩
    have hsub : Progress.Sm.subOff d.scheduler = 0 := by
      unfold Progress.Sm.subOff
      split
      all_goals first
        | rfl
        | (rename_i hs'
           rw [hs'] at hs
           rcases hcc with rfl | rfl <;> cases hs)
    have htm := (soft_round_time hA ha).2 (hT.bmax hp hg)
    rw [hsub, Nat.add_zero] at htm
    have hc3 : c = .nb ∨ c = .sb ∨ c = .bar2 := by rcases hcc with h | h <;> simp [h]
    refine ⟨c, B, P, rb, rp, a, hcc, hid, hm1, hm2, hT, hs, ha, hr, ht, h4, htm, ?_⟩
    rw [hid, ← soft_bar_cls hw hc3, count hσ]
    exact hc c (by rcases hcc with rfl | rfl <;> rfl)
  have hcount2 : id = 2 → ((X.tr g).take k).countP (Execution.isBarId id) =
      passed (ptsOf (Softmax.lz L g) .bar2) d.scheduler.site rb rp := by
    rintro rfl
    rw [← hc .bar2 rfl, ← count hσ]
    exact soft_isBar2 hw
  have htab := List.all_eq_true.mp at_tab (Softmax.lz L g) (by cases Softmax.lz L g <;> simp)
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at htab
  obtain ⟨t1, t2⟩ := bar2_rnd (Softmax.lz L g)
  obtain ⟨s, v, kk, acc⟩ := d
  cases s
  all_goals try simp only [Softmax.Control.D.scheduler] at hev
  case bar1 =>
    simp only [Softmax.Ev, Kind.bar.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    left
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · rw [hcount2 rfl]
      have := htab.1
      simp only [passed, t1, t2, Nat.mul_zero, Nat.add_zero] at this ⊢
      exact this
    · simp [Softmax.Control.D.scheduler, Progress.Sm.time, Progress.Sm.place, Progress.Sm.pre,
        Progress.Sm.endOff]
  case barEnd l =>
    simp only [Softmax.Ev, Kind.bar.injEq, reduceCtorEq, exists_false, or_false] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    right; left
    refine ⟨l, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · rw [hcount2 rfl]
      simp only [passed, t1, t2, Nat.mul_zero, Nat.add_zero]
      exact htab.2 l (by cases l <;> simp)
    · cases l with
      | true =>
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        by_contra hn
        rcases hno hn with h | h
        · exact absurd h (by simp [Softmax.Control.D.scheduler, Softmax.Site.pos, Softmax.Site.pc])
        · cases h
      | false =>
        refine ⟨fun h => (by cases h), fun h => ?_⟩
        obtain ⟨B, P, hT⟩ := exists_softTile h
        have := (hreg B P hT).2
        cases this
    · simp [Softmax.Control.D.scheduler, Progress.Sm.time, Progress.Sm.place, Progress.Sm.pre,
        Progress.Sm.endOff]
  case bsync b =>
    simp only [Softmax.Ev, Kind.bar.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    exact .inr (.inr (named .sb (.inr rfl) rfl (soft_stage_id hw) (fun _ => rfl)
      (fun h => by cases h)))
  case narr r =>
    simp only [Softmax.Ev, Kind.bar.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    exact .inr (.inr (named .nb (.inl rfl) rfl (soft_nbW hw) (fun h => by cases h)
      (fun _ => rfl)))
  case finarr =>
    simp only [Softmax.Ev, Kind.bar.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    exact .inr (.inr (named .nb (.inl rfl) rfl (soft_nbW hw) (fun h => by cases h)
      (fun _ => rfl)))
  all_goals exfalso
  all_goals simp only [Softmax.Ev, Softmax.rdOrUb, Softmax.tcLdOrUb, Epilogue.Ev, Softmax.Site.toE]
      at hev
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals cases ‹Kind.bar _ _ _ = _›

omit hub in
/-- **An event of a softmax lane** is fired from the startup or from a role state. -/
theorem soft_fired {e : Event} (he : X.get (g, k) = some e) (hne : ∀ f, e.kind ≠ .ub f)
    {σ : (thread p L g).D} (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    (∃ s n, σ = (.inl s, n) ∧ exit L g s = none ∧ Startup.Ev L g s e) ∨
      ∃ d n, σ = SmWarp.sinj p L g d n := by
  rcases SmWarp.open_ev hp hX hFw hw he hne with ⟨s, n, hσ', -, -, hi, hev⟩ | ⟨d, n, hσ', -⟩
  · rw [hσ] at hσ'; cases hσ'; exact .inl ⟨s, n, rfl, hi.2, hev⟩
  · rw [hσ] at hσ'; cases hσ'; exact .inr ⟨d, n, rfl⟩

/-- **A barrier event of a softmax lane leads to a later state.** -/
theorem soft_bar_next {pc id : Nat} {cnt : Option Nat} {md : BarMode} {d : Softmax.Control.D}
    {n : Cls → Nat} (he : X.get (g, k) = some ⟨pc, .bar id cnt md⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (SmWarp.sinj p L g d n))) :
    ∃ σ', Frame.stateAt (thread p L) X g (k + 1) = some (some σ') ∧
      Progress.Sm.time p L g d.scheduler n < Progress.time p L g σ' := by
  have hctl : Softmax.Control.succ p L g d ⟨pc, .bar id cnt md⟩ =
      (Softmax.succ p L g d.scheduler ⟨pc, .bar id cnt md⟩).map
        (Option.map Softmax.Control.erase) := by
    have hcl : d.site = .bar1 ∨ (∃ l, d.site = .barEnd l) ∨ Softmax.sig d.site = some .nb ∨
        Softmax.sig d.site = some .sb := by
      rcases soft_bar_at hp hX hFw hub hw he hσ with ⟨-, -, hs, -⟩ | ⟨l, -, -, hs, -⟩ |
        ⟨c, _, _, _, _, _, hc, -, -, -, -, hs, -⟩
      · exact .inl hs
      · exact .inr (.inl ⟨l, hs⟩)
      · rcases hc with rfl | rfl
        · exact .inr (.inr (.inl hs))
        · exact .inr (.inr (.inr hs))
    obtain ⟨s, v, kk, acc⟩ := d
    cases s <;> rfl
  have hstep : ∀ d', Softmax.succ p L g d.scheduler ⟨pc, .bar id cnt md⟩ = some (some d') →
      Frame.stateAt (thread p L) X g (k + 1) = some (some (SmWarp.sinj p L g
        (Softmax.Control.erase d')
        (Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩))) := fun d' h => by
    rw [Frame.stateAt_succ (C := thread p L) (show (X.tr g)[k]? = _ from he), hσ]
    refine (SmWarp.next_sinj d n _).trans ?_
    rw [hctl, h]
    rfl
  have hshfl : d.scheduler.site = .bar1 → 3 ≤ n .shfl := fun _ => by
    rcases soft_place hp hX hFw hub (Frame.lt_of_get hX he) hw hσ with ⟨-, s, n', h1, -⟩ |
      ⟨d', n', rb, rp, h1, -, h3, -⟩
    · cases h1
    · cases h1; exact h3
  have hb : Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩ .shfl = n .shfl := by
    simp [Code.bump, cls, Execution.isShfl]
  have h80 : Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩ (.soft (.acquire 80)) =
      n (.soft (.acquire 80)) := by
    simp [Code.bump, cls, Softmax.cls]
  have hst : Progress.Sm.stage L g = 0 ∨ Progress.Sm.stage L g = 1 := by
    unfold Progress.Sm.stage; split <;> simp
  have hps : ∀ late, (Softmax.passStart p L g late d.scheduler).site =
        .down (if late then .second else .first) ∨
      (Softmax.passStart p L g late d.scheduler).site = .word (if late then .second else .first) :=
          by
    intro late
    cases late <;> simp only [Softmax.passStart, Softmax.D.ite, Bool.false_eq_true, ite_false,
      ite_true]
    all_goals
      split
      · exact .inl rfl
      · exact .inr rfl
  -- a move inside the slot
  have slot : ∀ s' b1 b2 o1 o2, Progress.Sm.place (Progress.Sm.stage L g) d.scheduler.site =
      some (b1, true, o1) → Progress.Sm.place (Progress.Sm.stage L g) s' = some (b2, true, o2) →
      Progress.Sm.subOff d.scheduler = 0 → b1 + o1 < b2 + o2 →
      Softmax.succ p L g d.scheduler ⟨pc, .bar id cnt md⟩ = some (some (Softmax.D.mk' s'
          d.scheduler.v)) →
      ∃ σ', Frame.stateAt (thread p L) X g (k + 1) = some (some σ') ∧
        Progress.Sm.time p L g d.scheduler n < Progress.time p L g σ' := by
    intro s' b1 b2 o1 o2 h1 h2 h3 h4 h5
    refine ⟨_, hstep _ h5, ?_⟩
    show Progress.Sm.time p L g d.scheduler n < Progress.Sm.time p L g (Softmax.D.mk' s'
        d.scheduler.v)
      (Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩)
    simp only [Progress.Sm.time, h1, h2, h80, h3]
    unfold Progress.clk
    omega
  rcases soft_bar_at hp hX hFw hub hw he hσ with ⟨-, -, hs, -⟩ | ⟨l, -, -, hs, -⟩ |
    ⟨c, B, P, rb, rp, a, hc, -, -, -, -, hs, -⟩
  · -- the first barrier
    have hsc : Softmax.succ p L g d.scheduler ⟨pc, .bar id cnt md⟩ =
        some (some (Softmax.passStart p L g false d.scheduler)) := by
      simp only [Softmax.succ, hs]
    refine ⟨_, hstep _ hsc, ?_⟩
    have h3 := hshfl hs
    have hps' := hps false
    have h1 : Progress.Sm.time p L g d.scheduler n = Progress.scanBase + 3 := by
      simp [Progress.Sm.time, hs, Progress.Sm.place, Progress.Sm.pre, Progress.Sm.endOff]
    rw [h1]
    show _ < Progress.Sm.time p L g (Softmax.passStart p L g false d.scheduler)
      (Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩)
    generalize Softmax.passStart p L g false d.scheduler = d' at hps'
    rcases hps' with h | h <;>
      simp [Progress.Sm.time, h, Progress.Sm.place, Progress.Sm.pre,
        Progress.Sm.endOff, Progress.Sm.late, Progress.passTime, hb, Progress.Out.ballots,
        Progress.Out.coll, Progress.Sm.toE, Epilogue.Scan.late] <;> (try split_ifs) <;> omega
  · have hsc : Softmax.succ p L g d.scheduler ⟨pc, .bar id cnt md⟩ =
        some (some (Softmax.D.mk' (.exit l) d.scheduler.v)) := by
      simp only [Softmax.succ, hs]
    refine ⟨_, hstep _ hsc, ?_⟩
    show Progress.Sm.time p L g d.scheduler n < Progress.Sm.time p L g (Softmax.D.mk' (.exit l)
        d.scheduler.v)
      (Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩)
    simp only [Progress.Sm.time, hs, Progress.Sm.place, Progress.Sm.pre, Progress.Sm.endOff]
    unfold Progress.endT
    split <;> omega
  · obtain ⟨s, v, kk, acc⟩ := d
    cases s <;> try (rcases hc with rfl | rfl <;> cases hs; done)
    case bsync b =>
      cases hcn : Epilogue.scmpi .ne .b (Epilogue.andi (Softmax.tidW L g) 31) 0 with
      | true =>
        cases b with
        | true =>
          refine slot (.stat false) _ _ _ _ rfl rfl rfl (by omega) ?_
          simp [Softmax.Control.D.scheduler, Softmax.succ, hcn, Softmax.D.ite]
        | false =>
          refine slot (.narr .first) _ _ _ _ rfl rfl rfl (by omega) ?_
          simp [Softmax.Control.D.scheduler, Softmax.succ, hcn, Softmax.D.ite]
      | false =>
        refine slot (.barr b) _ _ _ _ rfl rfl rfl (by omega) ?_
        simp [Softmax.Control.D.scheduler, Softmax.succ, hcn, Softmax.D.ite]
    case narr r =>
      refine slot (.pst r 0) _ _ _ _ rfl rfl rfl ?_ rfl
      rcases hst with h | h <;> rw [h] <;> decide
    case finarr =>
      refine ⟨_, hstep _ rfl, ?_⟩
      have h1 : Progress.Sm.time p L g ⟨.finarr, v.scheduler, kk, acc⟩ n < Progress.tailBase p := by
        rcases hst with h | h <;>
          · simp only [Progress.Sm.time, h, Progress.Sm.place, ite_true, one_ne_zero, ite_false,
              Progress.Sm.subOff]
            exact Progress.clk_lt_tail (by decide)
      refine h1.trans_le ?_
      have htl : Progress.tailBase p + 1 ≤ Progress.endBase p := by
        unfold Progress.endBase Progress.span; omega
      show _ ≤ Progress.Sm.time p L g (Softmax.passStart p L g true _)
        (Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩)
      have hps' := hps true
      generalize Softmax.passStart p L g true _ = d' at hps' ⊢
      rcases hps' with h | h <;>
        simp [Progress.Sm.time, h, Progress.Sm.place, Progress.Sm.pre,
          Progress.Sm.endOff, Progress.Sm.late, Progress.passTime, hb, Progress.Out.ballots,
          Progress.Out.coll, Progress.Sm.toE, Epilogue.Scan.late] <;> (try split_ifs) <;> omega

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
