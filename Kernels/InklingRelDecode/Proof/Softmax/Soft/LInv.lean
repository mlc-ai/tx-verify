-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.MxInv
public import Kernels.InklingRelDecode.Proof.Softmax.Data.LStep
public import Kernels.InklingRelDecode.Proof.Lib.LaneSum
import Kernels.InklingRelDecode.Proof.Softmax.Data.LExact
import Kernels.InklingRelDecode.Proof.Lib.ShuffleEvent

@[expose] public section

/-! # The carried sum and the round's row sum are exact

Along the trace the value state's running sum (register 1915) reads as the fold's sum after the
rounds before, and the round's row sum (register 1531), from the shuffle of pc 2234 to the
update, is the exact sum of the round's block relative to the maximum the round uses. The words
the shuffle of pc 2234 sends and brings are the two halves' sums (trace-level hypothesis `hP`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow Control Data

variable {Q : Params} {L : Launch} {g : Nat} {ent : Control.Entry}

/-- A word that reads as `x`, and is exactly the float of `x` once a round has added to it. -/
def LV (v : Value) (n : Nat) (x : EReal) : Prop := Rd v x ∧ (0 < n → Ev v x)

/-- **The sum of a state**: the carried sum and the round's row sum. -/
structure LEx (Q : Params) (L : Launch) (g : Nat) (y : Data.D) : Prop where
  l : LV y.v.l (y.c.i + (updS y.c.site).toNat)
    ((Lib.laneSt Q L g (y.c.i + (updS y.c.site).toNat)).l : EReal)
  ps : psB y.c.site = true → Ev y.v.ps ((Lib.laneSum Q L g y.c.i : ℝ) : EReal)

theorem psB_chk (s : Site) :
    ((succs s).all fun z => !psB z || psB s || decide (s = .shfl6)) = true := by
  cases s with
  | pre j => revert j; decide +kernel
  | nxt j => revert j; decide +kernel
  | _ => decide +kernel

theorem psB_succ {s z : Site} (hz : z ∈ succs s) (hp : psB z = true) (hs : s ≠ .shfl6) :
    psB s = true := by
  have := psB_chk s
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
  rcases this z hz with (h | h) | h
  · simp [hp] at h
  · exact h
  · exact absurd h hs

theorem rec_l_keep {d : Data.D} {e : Event} {s : Site} (h6 : d.c.site ≠ .shfl6)
    (h12 : d.c.site ≠ .shfl12) (hw : d.c.site ≠ .waitStO)
    (h4 : ¬((d.c.site = .bar0 ∨ ∃ j, d.c.site = .pre j) ∧ loopB s)) :
    (record L d e s).l = d.v.l ∧ (record L d e s).ps = d.v.ps := by
  obtain ⟨⟨s0, i, hh⟩, v⟩ := d
  unfold record
  dsimp only at *
  split <;> (try split) <;> simp_all [loopB]

theorem rec_l_init {d : Data.D} {e : Event} {s : Site}
    (h : d.c.site = .bar0 ∨ ∃ j, d.c.site = .pre j) (hl : loopB s)
    (hk : ∀ j, d.c.site = .pre j → ∃ a bs, e.kind = .rd a bs) :
    (record L d e s).l = b32 0 := by
  obtain ⟨⟨s0, i, hh⟩, v⟩ := d
  unfold record
  dsimp only at *
  rcases h with h | ⟨j, h⟩
  · subst h; simp [hl]
  · subst h
    obtain ⟨a, bs, hk⟩ := hk j rfl
    simp [hk, hl]

/-- The row sum a round's update takes is the exact sum of the round's block. -/
theorem ps_q {m : Mem0} {X : Execution} (hX : Consistent L kernel Assumptions.all m X)
    (hP : ∀ k mode sent b c recv ok, X.get (g, k) = some ⟨2234, .shfl mode sent b c recv ok⟩ →
      ∃ u v : ℝ, Ev sent u ∧ Ev recv v ∧ u + v =
        Lib.laneSum Q L g (pollRound 1257 ((X.tr g).take k) - 1))
    {k : Nat} {old : Data.D} {e : Event} (he : X.get (g, k) = some e) (hu : ∀ f, e.kind ≠ .ub f)
    (pc : e.pc = old.c.site.pc) (led : Led X g k old) (J : LEx Q L g old)
    (hs : old.c.site = .shfl6 ∨ old.c.site = .shfl12 ∨ old.c.site = .waitStO) :
    ∃ q, q = (if old.c.site = .shfl6 then psOf e.kind old.v.ps else old.v.ps) ∧
      Ev q ((Lib.laneSum Q L g old.c.i : ℝ) : EReal) := by
  rcases hs with h | h | h
  · have p : e.pc = 2234 := by rw [pc, h]; rfl
    have iss : Execution.isShfl e = true := by
      rw [Lib.shfl_event hX he hu, p]; decide
    obtain ⟨pc0, kind⟩ := e
    cases kind <;> simp [Execution.isShfl] at iss
    change pc0 = 2234 at p
    subst p
    rename_i mode sent b c recv ok
    obtain ⟨u, v, hs, hr, hsum⟩ := hP k mode sent b c recv ok he
    have pr : pollRound 1257 ((X.tr g).take k) - 1 = old.c.i := by
      have := led
      simp only [Led, h, Site.afterS, Bool.toNat_true] at this
      omega
    refine ⟨Lib.psWord sent recv, by simp [h, psOf], ?_⟩
    have := ev_add (fz := false) (d := b32 0) hs hr
    rw [hsum, pr] at this
    exact this
  · exact ⟨old.v.ps, by simp [h], J.ps (by rw [h]; rfl)⟩
  · exact ⟨old.v.ps, by simp [h], J.ps (by rw [h]; rfl)⟩

/-- **The step keeps the sum exact.** -/
theorem lex_step {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (hP : ∀ k mode sent b c recv ok, X.get (g, k) = some ⟨2234, .shfl mode sent b c recv ok⟩ →
      ∃ u v : ℝ, Ev sent u ∧ Ev recv v ∧ u + v =
        Lib.laneSum Q L g (pollRound 1257 ((X.tr g).take k) - 1))
    {k : Nat} {old y : Data.D} {e : Event} (he : X.get (g, k) = some e)
    (hu : ∀ f, e.kind ≠ .ub f) (fd : Fired ent L g old e) (pc : e.pc = old.c.site.pc)
    (hn : succ ent L g old e = some (some y)) (led : Led X g k old)
    (inv : Control.Inv ent (g % L.block) old.c) (M : MEx Q L g old) (J : LEx Q L g old) :
    LEx Q L g y := by
  have hc := scaleW_ev hp
  have hpos : 0 < Q.scale * log2eF32 := mul_pos hp.scalePos (by unfold log2eF32; norm_num)
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  rcases next_mx hnc with ⟨h5, hd, hi⟩ | ⟨h6, hd, hi⟩ | ⟨h5, h6, K⟩
  · -- the shuffle of pc 1838
    obtain ⟨hl, hps⟩ := rec_l_keep (L := L) (d := old) (e := e) (s := c'.site)
      (by rw [h5]; nofun) (by rw [h5]; nofun) (by rw [h5]; nofun) (by rw [h5]; simp [loopB])
    have a0 : updS old.c.site = false := by rw [h5]; rfl
    have a1 := J.l
    simp only [a0, Bool.toNat_false, Nat.add_zero] at a1
    refine ⟨?_, fun h => absurd h (by rw [hd]; decide)⟩
    show LV (record L old e c'.site).l _ _
    rw [hl, hi, hd]
    simpa [updS] using a1
  · -- the update of the sum
    obtain ⟨q, hq, hqe⟩ := ps_q hX hP he hu pc led J (by rcases h6 with h | h | h <;> simp [h])
    have a0 : updS old.c.site = false := by rcases h6 with h | h | h <;> rw [h] <;> rfl
    have a1 : afterW old.c.site = true := by rcases h6 with h | h | h <;> rw [h] <;> rfl
    have jm := M.m
    simp only [a0, Bool.toNat_false, Nat.add_zero] at jm
    have jx := M.mx a1
    have jl := J.l.1
    simp only [a0, Bool.toNat_false, Nat.add_zero] at jl
    obtain ⟨-, -, hal⟩ := alpha_exact hc hpos jm jx
    have hfe := ev_fma_rr (fz := false) (d := b32 0) jl hal hqe.read
    have hr := (lrec_cross (L := L) (d := old) (ev := e) (z := c'.site) h6 hq).1 hd
    refine ⟨?_, fun h => absurd h (by rw [hd]; decide)⟩
    show LV (record L old e c'.site).l _ _
    have e1 : (updS Site.bar20).toNat = 1 := rfl
    rw [hr, hi, hd, e1, Lib.laneSt_succ, Lib.step_l]
    exact ⟨hfe.read, fun _ => hfe⟩
  · -- the other steps
    by_cases hs3 : old.c.site = .shfl6 ∨ old.c.site = .shfl12 ∨ old.c.site = .waitStO
    · obtain ⟨q, hq, hqe⟩ := ps_q hX hP he hu pc led J hs3
      have nb : c'.site ≠ .bar20 := fun h => h6 ⟨hs3, h⟩
      obtain ⟨hl, hps⟩ := (lrec_cross (L := L) (d := old) (ev := e) (z := c'.site) hs3 hq).2 nb
      have a0 : updS old.c.site = false := by rcases hs3 with h | h | h <;> rw [h] <;> rfl
      rcases K with ⟨hi, hu', hw⟩ | ⟨hu', -⟩
      · have jl := J.l
        simp only [a0, Bool.toNat_false, Nat.add_zero] at jl
        refine ⟨?_, fun h => ?_⟩
        · show LV (record L old e c'.site).l _ _
          rw [hl, hi, hu', a0]
          simpa using jl
        · show Ev (record L old e c'.site).ps _
          rw [hps, hi]
          exact hqe
      · rw [a0] at hu'; cases hu'
    · by_cases c4 : (old.c.site = .bar0 ∨ ∃ j, old.c.site = .pre j) ∧ loopB c'.site
      · have hl := rec_l_init (L := L) (d := old) (e := e) c4.1 c4.2
          (fun j hj => bias_kind fd hu (.inl ⟨j, hj⟩))
        have i0 : old.c.i = 0 := by
          rcases c4.1 with h | ⟨j, h⟩
          · exact inv.init (Or.inr h)
          · exact (inv.pre j h).1
        have a0 : updS old.c.site = false := by
          rcases c4.1 with h | ⟨j, h⟩ <;> rw [h] <;> rfl
        have b0 : updS c'.site = false := by
          rcases c4.2 with h | h | h <;> rw [h] <;> rfl
        have b1 : psB c'.site = false := by
          rcases c4.2 with h | h | h <;> rw [h] <;> rfl
        rcases K with ⟨hi, hu', hw⟩ | ⟨hu', -⟩
        · refine ⟨?_, fun h => by rw [b1] at h; cases h⟩
          show LV (record L old e c'.site).l _ _
          rw [hl, hi, i0, b0]
          exact ⟨rd_zero, fun h => absurd h (by simp)⟩
        · rw [a0] at hu'; cases hu'
      · have h6' : old.c.site ≠ .shfl6 := fun h => hs3 (.inl h)
        have h12 : old.c.site ≠ .shfl12 := fun h => hs3 (.inr (.inl h))
        have hw : old.c.site ≠ .waitStO := fun h => hs3 (.inr (.inr h))
        obtain ⟨hl, hps⟩ := rec_l_keep (L := L) (d := old) (e := e) (s := c'.site) h6' h12 hw c4
        rcases K with ⟨hi, hu', hw'⟩ | ⟨hu', hi, hu2, hw'⟩
        · refine ⟨?_, fun h => ?_⟩
          · show LV (record L old e c'.site).l _ _
            rw [hl, hi, hu']
            exact J.l
          · show Ev (record L old e c'.site).ps _
            rw [hps, hi]
            exact J.ps (psB_succ (next_mem (e := ent) (L := L) (g := g) (ev := e) hnc) h h6')
        · refine ⟨?_, fun h => ?_⟩
          · show LV (record L old e c'.site).l _ _
            rw [hl, hu2]
            have := J.l
            simpa [hu', hi] using this
          · have : psB old.c.site = true :=
              psB_succ (next_mem (e := ent) (L := L) (g := g) (ev := e) hnc) h h6'
            have pb : psB old.c.site = false := by
              cases hs : old.c.site <;> simp_all [updS, psB]
            rw [pb] at this
            cases this

/-- **The maxima and the sums of the value state along the trace.** -/
theorem soft_lex {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (hW : ∀ k mode sent b c recv ok, X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ →
      ∃ aE bE, Ev sent aE ∧ Ev recv bE ∧ max aE bE =
        Lib.SoftFold.blockMax (Lib.laneBlk Q L g (pollRound 1257 ((X.tr g).take k) - 1)))
    (hP : ∀ k mode sent b c recv ok, X.get (g, k) = some ⟨2234, .shfl mode sent b c recv ok⟩ →
      ∃ u v : ℝ, Ev sent u ∧ Ev recv v ∧ u + v =
        Lib.laneSum Q L g (pollRound 1257 ((X.tr g).take k) - 1)) :
    ∀ k, k ≤ (X.tr g).length → ∀ s, Frame.stateAt (threadD Q L) X g k = some (some s) →
      Frame.NoUbBefore X g k → ∀ w ent y n, s = softDState w ent y n → ent.Ok →
        MEx Q L g y ∧ LEx Q L g y := by
  intro k hk s hs nub w ent y n hsd ok
  exact (soft_ind hp hX (fun _ _ y => MEx Q L g y ∧ LEx Q L g y)
    (fun _ _ _ _ => ⟨⟨ev_bot, (fun h => by cases h), (fun h => by cases h)⟩,
      ⟨⟨rd_zero, fun h => absurd h (by decide)⟩, fun h => by cases h⟩⟩)
    (fun k ent old y e ok he hu fd pc hn led inv J =>
      ⟨mex_step hp hX hW he hu fd pc hn led inv J.1,
        lex_step hp hX hP he hu fd pc hn led inv J.1 J.2⟩)
    k hk s hs nub).2 w ent y n hsd ok |>.2.2

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
