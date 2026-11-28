-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.CurStep
public import Kernels.InklingRelDecode.Proof.Softmax.Soft.WinMax
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ScaleEv
public import Kernels.InklingRelDecode.Proof.Lib.WinHalf
public import Kernels.InklingRelDecode.Proof.Lib.LaneFold
import Kernels.InklingRelDecode.Proof.Softmax.Data.MExact
import Kernels.InklingRelDecode.Proof.Lib.ShuffleEvent
import Kernels.InklingRelDecode.Proof.Softmax.PollStep

@[expose] public section

/-! # The carried maximum and the round's new maximum are exact

Along the trace the value state's running maximum (register 1914), the maximum before the round's
update and the round's new maximum (register 1522) read as the fold's: the state after the rounds
before, and the maximum of that state's and the block's. The words the shuffles of pc 1838 send and
bring are the halves' maxima (trace-level hypothesis `hW`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow Control Data

variable {Q : Params} {L : Launch} {g : Nat} {ent : Control.Entry}

def afterW : Site → Bool
  | .setMaxReg | .bar0 | .pre _ | .nxt _ | .waitS | .shfl4 | .ldS | .waitLd | .shfl5
  | .epilogue => false
  | _ => true

def updS : Site → Bool
  | .bar20 | .tmemSt | .tmemWait | .bar21 | .arrive => true
  | _ => false

theorem loop_flags (e : Control.Entry) (t i : Nat) :
    afterW (loopSite e t i) = false ∧ updS (loopSite e t i) = false := by
  unfold loopSite
  split <;> first | exact ⟨rfl, rfl⟩ | (split <;> exact ⟨rfl, rfl⟩)

/-- The control step either keeps the round's phase or is one of the two word-setting steps. -/
theorem next_mx {d dn : Control.D} {ev : Event}
    (step : Control.next ent L g d ev = some (some dn)) :
    (d.site = .shfl5 ∧ dn.site = .shfl6 ∧ dn.i = d.i) ∨
    ((d.site = .shfl6 ∨ d.site = .shfl12 ∨ d.site = .waitStO) ∧ dn.site = .bar20 ∧
      dn.i = d.i) ∨
    (d.site ≠ .shfl5 ∧ ¬((d.site = .shfl6 ∨ d.site = .shfl12 ∨ d.site = .waitStO) ∧
      dn.site = .bar20) ∧
      ((dn.i = d.i ∧ updS dn.site = updS d.site ∧ (afterW dn.site = true → afterW d.site = true)) ∨
      (updS d.site = true ∧ dn.i = d.i + 1 ∧ updS dn.site = false ∧
        afterW dn.site = false))) := by
  obtain ⟨s, i, v⟩ := d
  cases s <;> simp only [Control.next, advance] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals (try simp only [loop_flags])
  all_goals simp [afterW, updS]

theorem rec_keep_mm {d : Data.D} {e : Event} {s : Site} (h5 : d.c.site ≠ .shfl5)
    (h6 : ¬((d.c.site = .shfl6 ∨ d.c.site = .shfl12 ∨ d.c.site = .waitStO) ∧ s = .bar20))
    (h4 : ¬((d.c.site = .bar0 ∨ ∃ j, d.c.site = .pre j) ∧ loopB s)) :
    (record L d e s).m = d.v.m ∧ (record L d e s).mp = d.v.mp ∧ (record L d e s).mx = d.v.mx := by
  obtain ⟨⟨s0, i, hh⟩, v⟩ := d
  unfold record
  dsimp only at *
  split <;> (try split) <;> simp_all [loopB]

theorem rec_5 {d : Data.D} {e : Event} {s : Site} {mode sent b c recv ok}
    (h : d.c.site = .shfl5) (hk : e.kind = .shfl mode sent b c recv ok) :
    (record L d e s).m = d.v.m ∧ (record L d e s).mp = d.v.mp ∧
      (record L d e s).mx = Lib.mxWord d.v.m sent recv := by
  obtain ⟨⟨s0, i, hh⟩, v⟩ := d
  unfold record
  dsimp only at *
  subst h
  simp [hk]

theorem rec_6 {d : Data.D} {e : Event} {s : Site}
    (h : d.c.site = .shfl6 ∨ d.c.site = .shfl12 ∨ d.c.site = .waitStO) (hs : s = .bar20) :
    (record L d e s).m = Lib.mNext (scaleW L) d.v.m d.v.mx ∧ (record L d e s).mp = d.v.m ∧
      (record L d e s).mx = d.v.mx := by
  obtain ⟨⟨s0, i, hh⟩, v⟩ := d
  unfold record
  dsimp only at *
  subst hs
  rcases h with h | h | h <;> subst h <;> simp

theorem rec_4 {d : Data.D} {e : Event} {s : Site}
    (h : d.c.site = .bar0 ∨ ∃ j, d.c.site = .pre j) (hl : loopB s)
    (hk : ∀ j, d.c.site = .pre j → ∃ a bs, e.kind = .rd a bs) :
    (record L d e s).m = b32 4286578688 ∧ (record L d e s).mp = d.v.mp ∧
      (record L d e s).mx = d.v.mx := by
  obtain ⟨⟨s0, i, hh⟩, v⟩ := d
  unfold record
  dsimp only at *
  rcases h with h | ⟨j, h⟩
  · subst h; simp [hl]
  · subst h
    obtain ⟨a, bs, hk⟩ := hk j rfl
    simp [hk, hl]

/-- **The maxima of a state**: the carried maximum, the one before the round's update and the
round's new maximum. -/
structure MEx (Q : Params) (L : Launch) (g : Nat) (y : Data.D) : Prop where
  m : Ev y.v.m (Lib.laneSt Q L g (y.c.i + (updS y.c.site).toNat)).m
  mp : updS y.c.site = true → Ev y.v.mp (Lib.laneSt Q L g y.c.i).m
  mx : afterW y.c.site = true → Ev y.v.mx
    (max (Lib.laneSt Q L g y.c.i).m (Lib.SoftFold.blockMax (Lib.laneBlk Q L g y.c.i)))

/-- **The step keeps the maxima exact.** -/
theorem mex_step {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (hW : ∀ k mode sent b c recv ok, X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ →
      ∃ aE bE, Ev sent aE ∧ Ev recv bE ∧ max aE bE =
        Lib.SoftFold.blockMax (Lib.laneBlk Q L g (pollRound 1257 ((X.tr g).take k) - 1)))
    {k : Nat} {old y : Data.D} {e : Event} (he : X.get (g, k) = some e)
    (hu : ∀ f, e.kind ≠ .ub f) (fd : Fired ent L g old e)
    (pc : e.pc = old.c.site.pc) (hn : succ ent L g old e = some (some y))
    (led : Led X g k old) (inv : Control.Inv ent (g % L.block) old.c) (J : MEx Q L g old) :
    MEx Q L g y := by
  have hc := scaleW_ev hp
  have hpos : 0 < Q.scale * log2eF32 := mul_pos hp.scalePos (by unfold log2eF32; norm_num)
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  rcases next_mx hnc with ⟨h5, hd, hi⟩ | ⟨h6, hd, hi⟩ | ⟨h5, h6, K⟩
  · -- the shuffle of pc 1838
    have p : e.pc = 1838 := by rw [pc, h5]; rfl
    have iss : Execution.isShfl e = true := by
      rw [Lib.shfl_event hX he hu, p]; decide
    obtain ⟨pc0, kind⟩ := e
    cases kind <;> simp [Execution.isShfl] at iss
    change pc0 = 1838 at p
    subst p
    rename_i mode sent b c recv ok
    obtain ⟨hm, hmp, hmx⟩ := rec_5 (L := L) (d := old) (e := ⟨1838, .shfl mode sent b c recv ok⟩)
      (s := c'.site) h5 rfl
    obtain ⟨aE, bE, ha, hb, hmax⟩ := hW k mode sent b c recv ok he
    have pr : pollRound 1257 ((X.tr g).take k) - 1 = old.c.i := by
      have := led
      simp only [Led, h5, Site.afterS, Bool.toNat_true] at this
      omega
    rw [pr] at hmax
    have a0 : updS old.c.site = false := by rw [h5]; rfl
    have a1 := J.m
    simp only [a0, Bool.toNat_false, Nat.add_zero] at a1
    refine ⟨?_, (fun h => absurd h (by rw [hd]; decide)), fun _ => ?_⟩
    · rw [hm, hi, hd]
      simpa [updS] using a1
    · rw [hmx, hi]
      have := mxWord_ev a1 ha hb
      rwa [max_assoc, hmax] at this
  · -- the update of the maximum
    obtain ⟨hm, hmp, hmx⟩ := rec_6 (L := L) (d := old) (e := e) h6 hd
    have a0 : updS old.c.site = false := by rcases h6 with h | h | h <;> rw [h] <;> rfl
    have a1 : afterW old.c.site = true := by rcases h6 with h | h | h <;> rw [h] <;> rfl
    have jm := J.m
    simp only [a0, Bool.toNat_false, Nat.add_zero] at jm
    have jx := J.mx a1
    refine ⟨?_, fun _ => ?_, fun _ => ?_⟩
    · have e1 : (updS Site.bar20).toNat = 1 := rfl
      rw [hm, hi, hd, e1, Lib.laneSt_succ]
      exact mNext_ev hc hpos jm jx
    · rw [hmp, hi]; exact jm
    · rw [hmx, hi]; exact jx
  · -- the other steps keep the maxima
    by_cases c4 : (old.c.site = .bar0 ∨ ∃ j, old.c.site = .pre j) ∧ loopB c'.site
    · obtain ⟨hm, hmp, hmx⟩ := rec_4 (L := L) (d := old) (e := e) c4.1 c4.2
        (fun j hj => bias_kind fd hu (.inl ⟨j, hj⟩))
      have i0 : old.c.i = 0 := by
        rcases c4.1 with h | ⟨j, h⟩
        · exact inv.init (Or.inr h)
        · exact (inv.pre j h).1
      have a0 : updS old.c.site = false := by
        rcases c4.1 with h | ⟨j, h⟩ <;> rw [h] <;> rfl
      have a1 : afterW old.c.site = false := by
        rcases c4.1 with h | ⟨j, h⟩ <;> rw [h] <;> rfl
      rcases K with ⟨hi, hu', hw⟩ | ⟨hu', -⟩
      · refine ⟨?_, fun h => absurd (hu'.symm.trans h) (by rw [a0]; decide), fun h => ?_⟩
        · rw [hm, hi, hu', a0, i0]
          exact ev_bot
        · exact absurd (hw h) (by rw [a1]; decide)
      · rw [a0] at hu'; cases hu'
    · obtain ⟨hm, hmp, hmx⟩ := rec_keep_mm (L := L) (d := old) (e := e) (s := c'.site) h5 h6 c4
      rcases K with ⟨hi, hu', hw⟩ | ⟨hu', hi, hu2, hw⟩
      · refine ⟨?_, fun h => ?_, fun h => ?_⟩
        · rw [hm, hi, hu']; exact J.m
        · rw [hmp, hi]; exact J.mp (hu'.symm.trans h)
        · rw [hmx, hi]; exact J.mx (hw h)
      · refine ⟨?_, (fun h => by rw [hu2] at h; cases h), (fun h => by rw [hw] at h; cases h)⟩
        rw [hm, hi, hu2]
        have := J.m
        simpa [hu'] using this

/-- **The maxima of the value state along the trace.** -/
theorem soft_mex {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (hW : ∀ k mode sent b c recv ok, X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ →
      ∃ aE bE, Ev sent aE ∧ Ev recv bE ∧ max aE bE =
        Lib.SoftFold.blockMax (Lib.laneBlk Q L g (pollRound 1257 ((X.tr g).take k) - 1))) :
    ∀ k, k ≤ (X.tr g).length → ∀ s, Frame.stateAt (threadD Q L) X g k = some (some s) →
      Frame.NoUbBefore X g k → ∀ w ent y n, s = softDState w ent y n → ent.Ok →
        MEx Q L g y := by
  intro k hk s hs nub w ent y n hsd ok
  exact (soft_ind hp hX (fun _ _ y => MEx Q L g y)
    (fun _ _ _ _ => ⟨ev_bot, (fun h => by cases h), (fun h => by cases h)⟩)
    (fun k ent old y e ok he hu fd pc hn led inv J => mex_step hp hX hW he hu fd pc hn led inv J)
    k hk s hs nub).2 w ent y n hsd ok |>.2.2

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
