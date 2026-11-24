-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.TcTime
import Kernels.TmlFa4Fwd.Proof.Common.Migrated
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Lib.ThreadTime
import Kernels.TmlFa4Fwd.Proof.Mma.Open
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Match
import Kernels.TmlFa4Fwd.Proof.Top.Table
import Lemmas.Flow.GlueStep
import Lemmas.Kernel.Safety.CountInv
import Lemmas.Kernel.Safety.StateInvU
import Lemmas.Kernel.Safety.Schedule
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The MMA warp's barrier-2 events in the time table

An MMA lane makes its first barrier-2 event at `bar1` and its second at `bar2` (`mma_bar2_count`),
so
a lane with no barrier-2 event is no later than `bar1`, and one with at most one no later than
`bar2`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (scanBase endBase primeBase doneBase passTime endT)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- The barrier-2 events before a site. -/
def bt : Site → Nat
  | .bar1 => 0
  | .dealloc _ | .exit _ => 2
  | _ => 1

/-- The barrier-2 events at a site. -/
def bt1 : Site → Nat
  | .bar1 | .bar2 _ => 1
  | _ => 0

private theorem bt_wtNext : ∀ k, bt (wtNext k) = 1 := by decide
private theorem bt_shNext : ∀ k, bt (shNext k) = 1 := by decide
private theorem bt_qkDone : ∀ k, bt (qkDone k) = 1 := by decide
private theorem bt_pvDone : ∀ k, bt (pvDone k) = 1 := by decide

private theorem bt_passStart (late : Bool) (d : D) : bt (passStart p L g late d).site = 1 := by
  cases late <;> simp only [passStart] <;> split_ifs <;> rfl

private theorem bt_ceNext (d : D) (c : Fin 12) : bt (ceNext p L g d c).site = 1 := by
  fin_cases c <;> simp only [ceNext, enterLoop, loopEnd, bt_passStart] <;>
    (try split) <;> rfl

private theorem bt_afterTotal (k : Epilogue.Scan) (d : D) (x : BitVec 64) :
    bt (afterTotal p L g k d x).site = 1 := by
  cases k <;> simp only [afterTotal, scanExit, loopHead] <;> split_ifs <;> rfl

private theorem bt_afterTiles {d d' : D} {x : BitVec 64}
    (h : afterTiles p L g d x = some d') : bt d'.site = 1 := by
  dsimp only [afterTiles] at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> rfl

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- A step passes exactly its site's barrier-2 event. -/
private theorem succ_bt {d d' : D} {e : Event} (h : succ p L g d e = some (some d')) :
    bt d'.site = bt d.site + bt1 d.site := by
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [succ, word32] at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; done)
    | (simp only [Option.some.injEq, reduceCtorEq] at h; subst h; rfl)
    | (simp only [Option.some.injEq] at h; subst h; rw [bt_afterTotal]; rfl)
    | (simp only [Option.map_eq_some_iff, Option.some.injEq] at h
       obtain ⟨d0, h0, rfl⟩ := h
       rw [bt_afterTiles h0]; rfl)
    | (simp only [Option.some.injEq, reduceCtorEq] at h; subst h
       simp only [scAt, afterTiles, afterTotal, bt_wtNext, bt_shNext, bt_qkDone, bt_pvDone,
         bt_ceNext, bt_passStart]
       try simp only [bt, bt1]
       repeat' split
       all_goals first | rfl | (simp_all; done))

set_option maxHeartbeats 4000000 in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- A barrier event is at a barrier site. -/
theorem mma_bar_site {d : D} {pc id : Nat} {cnt : Option Nat} {md : BarMode}
    (hev : Ev p L g d ⟨pc, .bar id cnt md⟩) : bt1 d.site = 1 := by
  obtain ⟨s, rest⟩ := d
  cases s <;> first | rfl | (exfalso; simp only [Ev, Epilogue.Ev, Site.toE] at hev)
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals cases ‹Kind.bar _ _ _ = _›

/-- The barrier-2 events before a thread state of the MMA warp. -/
def BtInv (p : Params) (L : Launch) (g : Nat) : (thread p L g).D → Nat → Prop
  | (.inr ⟨.mma, .inr ⟨_, d⟩⟩, _), n => n = bt d.site
  | (.inr ⟨.mma, .inl _⟩, _), n => n = 0
  | (.inl _, _), n => n = 0
  | _, _ => True

private theorem bt_init : bt (code p L g (ent p L)).init.site = 0 := rfl

/-- **The barrier-2 events before a state of an MMA lane.** -/
theorem mma_bar2_count (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hub : ¬ HasUb X) (hg : g < L.threads) :
    ∀ k σ, Frame.stateAt (thread p L) X g k = some (some σ) →
      BtInv p L g σ (((X.tr g).take k).countP (Execution.isBarId 2)) := by
  refine fun k σ => Frame.RoleTable.countInvU (T := table p L) (S := fun g => g < L.threads)
    (fun g hg => thread_sound hp hg) hX (table_shape_of hp hFw)
    (table_followed hp hX hFw) hg (Execution.isBarId 2) (P := fun σ n => BtInv p L g σ n) rfl ?_
    k σ (by rintro j _ ⟨pc, _⟩ he f rfl; exact hub ⟨_, pc, f, he⟩)
  rintro ⟨σ1, nn⟩ e ⟨σ1', nn'⟩ n hJ hi hev hB hn hJ'
  obtain ⟨h1, rfl⟩ := Code.counted_next_some (C := glued p L g) hn
  have hent : ∀ σ : (glued p L g).D, (∃ r, σ = .inr ⟨r, (frag p L g r).init⟩) →
      BtInv p L g (σ, Code.bump (Proof.cls L g) nn e) 0 := by
    rintro σ ⟨r, rfl⟩
    cases r <;> trivial
  rcases σ1 with s | ⟨i, d⟩
  · have hB0 : n = 0 := hB
    have hb : Execution.isBarId 2 e = false := by
      obtain ⟨pc, kd⟩ := e
      cases kd <;> try rfl
      rename_i id cnt md
      have := start_barOps hJ hev
      simp only [Prod.mk.injEq] at this
      rw [this.1]
      rfl
    simp only [hb, hB0, Bool.false_eq_true, ite_false]
    obtain ⟨s', -, rfl⟩ := Code.glue_inl_some h1
    unfold Code.enter
    split
    · exact hent _ ⟨_, rfl⟩
    · rfl
  · simp only [glued, Code.glue] at h1
    cases hr : (frag p L g i).next d e with
    | none => rw [hr] at h1; simp at h1
    | some o =>
      cases o with
      | none => rw [hr] at h1; simp at h1
      | some d1 =>
        rw [hr] at h1
        simp only [Option.map_some, Option.some.injEq] at h1
        subst h1
        cases i with
        | mma =>
          rcases d with s0 | ⟨⟨⟩, d⟩
          · have hB0 : n = 0 := hB
            have hP : PreEv e := hev
            have hb : Execution.isBarId 2 e = false := by
              obtain ⟨pc, kd⟩ := e
              rcases hP with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;>
                (simp only at hk; subst hk; rfl)
            simp only [hb, hB0, Bool.false_eq_true, ite_false]
            simp only [frag, Mma.M, Mma.G, Mma.S] at hr
            cases s0 with
            | set =>
              simp only [Option.map_some, Option.some.injEq] at hr
              subst hr
              rfl
            | alloc =>
              simp only [Option.map_some, Option.some.injEq] at hr
              subst hr
              by_cases hl : laneOf L g = 0 <;> simp only [hl, ite_true, ite_false] <;> rfl
            | wr =>
              simp only [Option.map_some, Option.some.injEq] at hr
              subst hr
              rfl
            | enter => exact absurd hi.2 (by simp [Mma.Start.exit])
          · have hBd : n = bt d.site := hB
            have hEv : Ev p L g d e := hev
            simp only [frag, Mma.M, Mma.G] at hr
            cases hs : succ p L g d e with
            | none => simp [hs] at hr
            | some o' =>
              cases o' with
              | none => simp [hs] at hr
              | some d' =>
                simp only [hs, Option.map_some, Option.some.injEq] at hr
                subst hr
                show n + _ = bt d'.site
                rw [succ_bt hs, hBd]
                congr 1
                by_cases hb : Execution.isBarId 2 e = true
                · obtain ⟨pc, kd⟩ := e
                  cases kd <;> simp only [Execution.isBarId, Bool.false_eq_true, beq_iff_eq] at hb
                  subst hb
                  have := mma_bar_site hEv
                  simp [Execution.isBarId, this]
                · have : bt1 d.site = 0 := by
                    obtain ⟨site, v⟩ := d
                    cases site <;> first | rfl | (exfalso; simp only [Ev] at hEv)
                    all_goals exact hb (by simp [Execution.isBarId, hEv])
                  simp [hb, this]
        | _ => trivial

/-- An exit is at the exit site. -/
theorem mma_exit_site {d : D} {pc : Nat} (hev : Ev p L g d ⟨pc, .exit⟩) : ∃ l, d.site = .exit l :=
    by
  obtain ⟨s, rest⟩ := d
  cases s <;> first | exact ⟨_, rfl⟩ | (exfalso; simp only [Ev, Epilogue.Ev, Site.toE] at hev)
  all_goals shape_destruct hev
  all_goals cases ‹Kind.exit = _›

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) (hw : Prologue.warpIndex L g = 12)
include hp hX hFw hub hg hw

private theorem no_exit (h : (X.tr g).countP (Execution.isBarId 2) ≤ 1) :
    ∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩ := by
  intro j pc hx
  rcases Mma.open_ev hp hX hFw hw hx (fun f h => by cases h) with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨s, n, -, -, -, hev⟩ | ⟨d, n, hσ, -, -, -, hev⟩
  · have hx : exit L g s = none := hi.2
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | sh j => fin_cases j <;> simp [Startup.Ev] at hev
    | elect j => simp [Startup.Ev] at hev
    | init q => simp [Startup.Ev] at hev
    | fence => simp [Startup.Ev] at hev
    | bar => simp [Startup.Ev] at hev
    | enter r => simp [exit] at hx
  · rcases hev with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  · obtain ⟨l, hs⟩ := mma_exit_site hev
    have h1 : _ = bt d.site := mma_bar2_count hp hX hFw hub hg j _ hσ
    rw [hs] at h1
    have h2 := (List.take_sublist j (X.tr g)).countP_le (p := Execution.isBarId 2)
    have h3 : bt (.exit l) = 2 := rfl
    omega

omit hFw hub hg hw in
/-- The event of a role state. -/
private theorem ev_of {d : D} {n : Cls → Nat} {e : Event}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (he : X.get (g, k) = some e) : Ev p L g d e := (Mma.mfired hp hX he hσ).1

omit hub hg in
/-- **A barrier event of an MMA lane** is fired from the startup or from a role state. -/
theorem mma_bar_open {pc id : Nat} {cnt : Option Nat} {md : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt md⟩)
    {σ : (thread p L g).D} (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    (∃ s n, σ = (.inl s, n) ∧ exit L g s = none ∧ Startup.Ev L g s ⟨pc, .bar id cnt md⟩) ∨
      ∃ d n, σ = minj p L g d n := by
  rcases Mma.open_ev hp hX hFw hw he (fun f h => by cases h) with ⟨s, n, hσ', -, -, hi, hev⟩ |
    ⟨s, n, -, -, -, hev⟩ | ⟨d, n, hσ', -⟩
  · rw [hσ] at hσ'; cases hσ'; exact .inl ⟨s, n, rfl, hi.2, hev⟩
  · rcases hev with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  · rw [hσ] at hσ'; cases hσ'; exact .inr ⟨d, n, rfl⟩

omit hg in
/-- **A barrier event of an MMA lane at a role state.** -/
theorem mma_bar_at {pc id : Nat} {cnt : Option Nat} {md : BarMode} {d : D} {n : Cls → Nat}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt md⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n))) :
    (id = 2 ∧ d.site = .bar1 ∧ ((X.tr g).take k).countP (Execution.isBarId id) = 0 ∧
        Progress.Mm.time p d n = scanBase + 3) ∨
    ∃ l, id = 2 ∧ d.site = .bar2 l ∧ ((X.tr g).take k).countP (Execution.isBarId id) = 1 ∧
        (l = true ↔ ∃ R bal, Epilogue.Picked p L g R bal) ∧
        Progress.Mm.time p d n = endT p l 4 := by
  have hg := Frame.lt_of_get hX he
  have hev := ev_of hp hX hσ he
  have hc : _ = bt d.site := mma_bar2_count hp hX hFw hub hg k _ hσ
  have hb := mma_bar_site hev
  have hend := fun l => mma_end_picked (l := l) hp hX hub hg hw hσ
  obtain ⟨s, v⟩ := d
  cases s <;> try (cases hb; done)
  · simp only [Ev, Kind.bar.injEq] at hev
    obtain ⟨rfl, -, -⟩ := hev
    exact .inl ⟨rfl, rfl, hc, rfl⟩
  · simp only [Ev, Kind.bar.injEq] at hev
    obtain ⟨rfl, -, -⟩ := hev
    exact .inr ⟨_, rfl, rfl, hc, hend _ rfl, rfl⟩

omit hg in
/-- **A barrier event of an MMA lane leads to a later state.** -/
theorem mma_bar_next {pc id : Nat} {cnt : Option Nat} {md : BarMode} {d : D} {n : Cls → Nat}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt md⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n))) :
    ∃ σ', Frame.stateAt (thread p L) X g (k + 1) = some (some σ') ∧
      Progress.Mm.time p d n < Progress.time p L g σ' := by
  have hstep : ∀ d', succ p L g d ⟨pc, .bar id cnt md⟩ = some (some d') →
      Frame.stateAt (thread p L) X g (k + 1) = some (some (minj p L g d'
        (Code.bump (Proof.cls L g) n ⟨pc, .bar id cnt md⟩))) := fun d' h => by
    rw [Frame.stateAt_succ (C := thread p L) (show (X.tr g)[k]? = _ from he), hσ]
    refine (next_minj d n _).trans ?_
    rw [show (code p L g (ent p L)).next d _ = some (some d') from h]
    rfl
  have hb : Code.bump (Proof.cls L g) n ⟨pc, .bar id cnt md⟩ .shfl = n .shfl := by
    simp [Code.bump, Proof.cls, Execution.isShfl]
  have hg := Frame.lt_of_get hX he
  have hub0 : n .ub = 0 := ub_zero hX he hσ
  have hR := (Mma.good hp hX (cuQReadsFromLaunch hp hX) hg hw k).2 _ hσ
  obtain ⟨-, hF⟩ := hR hub0
  rcases mma_bar_at hp hX hFw hub hw he hσ with ⟨-, hs, -, ht⟩ | ⟨l, -, hs, -, -, ht⟩
  · rw [ht]
    simp only [MFits, hs, Site.early, ite_true] at hF
    obtain ⟨h3, -, hps⟩ := hF
    refine ⟨_, hstep ⟨.ldAlloc, d.v⟩ (by simp only [succ, hs]), ?_⟩
    show _ < Progress.Mm.time p ⟨.ldAlloc, d.v⟩ (Code.bump (Proof.cls L g) n ⟨pc, .bar id cnt md⟩)
    simp [Progress.Mm.time, Site.pipe, Progress.Mm.endOff, Progress.Mm.scans, Progress.Mm.coll, hb,
      h3, hps, passTime, Site.late]
    split <;> omega
  · refine ⟨_, hstep ⟨.dealloc l, d.v⟩ (by simp only [succ, hs]), ?_⟩
    rw [ht]
    show _ < endT p l 6
    unfold endT
    split <;> omega

/-- **An MMA lane with no barrier-2 event** is no later than its first. -/
theorem mma_bar2_first (h : (X.tr g).countP (Execution.isBarId 2) = 0) :
    (∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (Progress.timed p L) X g ≤ scanBase + 3 := by
  have key : ∀ {k σ}, Frame.stateAt (thread p L) X g k = some (some σ) →
      Progress.time p L g σ < scanBase + 3 ∨ ∃ d n, σ = minj p L g d n ∧
        d.site = .bar1 ∧ Progress.time p L g σ = scanBase + 3 := by
    intro k σ hσ
    have hR := (Mma.good hp hX (cuQReadsFromLaunch hp hX) hg hw k).2 _ hσ
    have hc := mma_bar2_count hp hX hFw hub hg k _ hσ
    have hk := (List.take_sublist k (X.tr g)).countP_le (p := Execution.isBarId 2)
    obtain ⟨σ, n⟩ := σ
    rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
    · left
      obtain ⟨hS, -⟩ := hR
      have hx : ∀ r, s.site ≠ .enter r := by
        intro r he
        simp only [StartAt, he] at hS
      have := Progress.startTime_lt hx
      simp only [Progress.time]
      omega
    · rcases d with s | ⟨u, d⟩
      · left
        simp only [Progress.time, Progress.roleTime, Progress.Mm.startT]
        split <;> omega
      · have hc' : _ = bt d.site := hc
        right
        refine ⟨d, n, rfl, ?_⟩
        have hb : bt d.site = 0 := by omega
        obtain ⟨s, v⟩ := d
        cases s <;> first | (cases hb; done) | exact ⟨rfl, rfl⟩
  refine ⟨no_exit hp hX hFw hub hg hw (by omega), threadTime_le (fun σ hσ => ?_) fun σ e hσ he =>
      ?_⟩
  · rcases key hσ with h | ⟨_, _, -, -, h⟩ <;> omega
  · rcases key hσ with h | ⟨d, n, rfl, hs, h⟩
    · omega
    · exfalso
      have hev := ev_of hp hX hσ he
      simp only [Ev, hs] at hev
      have h2 : ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 2) <
          (X.tr g).countP (Execution.isBarId 2) :=
        Frame.countP_take_lt_countP (P := Execution.isBarId 2) (es := X.tr g) he
          (by simp [Execution.isBarId, hev])
      omega

/-- **An MMA lane with at most one barrier-2 event** is no later than its last, the second pass's
exactly when its CTA picked a tile. -/
theorem mma_bar2_end {l : Bool} (hl : l = true ↔ ∃ R bal, Epilogue.Picked p L g R bal)
    (h : (X.tr g).countP (Execution.isBarId 2) ≤ 1) :
    (∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (Progress.timed p L) X g ≤ endT p l 4 := by
  have hdone : doneBase p ≤ endT p true 0 := by simp [endT]
  have hT : ∀ a b, a < b → endT p l a < endT p l b := fun a b hab => by
    unfold endT; split <;> omega
  have h04 := hT 0 4 (by omega)
  have key : ∀ {k σ}, Frame.stateAt (thread p L) X g k = some (some σ) →
      Progress.time p L g σ < endT p l 4 ∨ ∃ d n l', σ = minj p L g d n ∧
        d.site = .bar2 l' ∧ Progress.time p L g σ = endT p l 4 ∧
        ((X.tr g).take k).countP (Execution.isBarId 2) = 1 := by
    intro k σ hσ
    by_cases hend : ∃ d n, σ = minj p L g d n ∧ d.site.isEnd ≠ none
    · obtain ⟨d, n, rfl, hd⟩ := hend
      obtain ⟨l', hl'⟩ := Option.ne_none_iff_exists'.mp hd
      have hll : l' = l := by
        have h1 := (mma_end_picked hp hX hub hg hw hσ hl').trans hl.symm
        cases l <;> cases l' <;> simp_all
      subst hll
      have hc : _ = bt d.site := mma_bar2_count hp hX hFw hub hg k _ hσ
      have hk := (List.take_sublist k (X.tr g)).countP_le (p := Execution.isBarId 2)
      obtain ⟨s, v⟩ := d
      cases s <;> simp only [Site.isEnd, Option.some.injEq, reduceCtorEq] at hl' <;> subst hl'
      · left; exact h04
      · right; exact ⟨_, _, _, rfl, rfl, rfl, hc⟩
      · exfalso; change _ = 2 at hc; omega
      · exfalso; change _ = 2 at hc; omega
    · left
      push Not at hend
      obtain ⟨t1, t2⟩ := mma_end_time hp hX hub hg hw hσ hend
      cases l with
      | true => omega
      | false =>
        have := t2 fun h => by have := hl.mpr h; cases this
        omega
  refine ⟨no_exit hp hX hFw hub hg hw h, threadTime_le (fun σ hσ => ?_) fun σ e hσ he => ?_⟩
  · rcases key hσ with h | ⟨_, _, _, -, -, h, -⟩ <;> omega
  · rcases key hσ with h | ⟨d, n, l', rfl, hs, h', hc⟩
    · omega
    · exfalso
      have hev := ev_of hp hX hσ he
      simp only [Ev, hs] at hev
      have h2 : ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 2) <
          (X.tr g).countP (Execution.isBarId 2) :=
        Frame.countP_take_lt_countP (P := Execution.isBarId 2) (es := X.tr g) he
          (by simp [Execution.isBarId, hev])
      omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
