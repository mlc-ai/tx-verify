-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Softmax.Export.RecvHalf
public import Kernels.InklingRelDecode.Proof.Lib.LaneSum
public import Kernels.InklingRelDecode.Proof.Lib.ShuffleRounds
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
import Kernels.InklingRelDecode.Proof.Softmax.Soft.SumEx
import Kernels.InklingRelDecode.Proof.Softmax.Soft.LInv
import Kernels.InklingRelDecode.Proof.Softmax.Export.WordsEv
import Kernels.InklingRelDecode.Proof.Softmax.Export.SumWord
import Kernels.InklingRelDecode.Proof.Softmax.Export.SentRound
import Kernels.InklingRelDecode.Proof.Softmax.Export.ShufflePartner
import Kernels.InklingRelDecode.Proof.Softmax.Soft.WinState
import Kernels.InklingRelDecode.Proof.Softmax.Soft.EntGlue
import Kernels.InklingRelDecode.Proof.Common.SoftmaxEntry
import Kernels.InklingRelDecode.Proof.Common.ValueThread
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Proof.Lib.Rows
import Kernels.InklingRelDecode.Proof.Lib.ShuffleOperand
import Kernels.InklingRelDecode.Proof.Softmax.Operand
import Kernels.InklingRelDecode.Flow.Code.Part035

/-! # The words of the shuffle of pc 2234 are the halves' sums

The word a lane sends at pc 2234 is register 1529 of its value state, the sum of the exact
probabilities of its half of the round's block; the lane 16 away sends the other half's, in the
same round. Together they add up to the block's sum (`Lib.laneSum`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Control Data Soft

variable {Q : Params} {L : Launch} {g : Nat}

private theorem site_2234' (s : Site) (h : s.pc = 2234) : s = .shfl6 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **The word sent at pc 2234 is the half's sum**, and the shuffles before it count its round. -/
public theorem sent_sumv {m : Mem0} {X : Execution} {k : Nat} {mode : ShflMode} {b c : Nat}
    {recv : Value} {ok : Bool} {sent : Value} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hB : ∀ g, Lib.BiasEv Q L g X) (hS : ∀ g, Lib.ScoreEv Q L g X) (lane : g % L.block < 128)
    (hv : Lib.QRowValid Q L (g / L.block) (Lib.softRow (g % L.block)))
    (get : X.get (g, k) = some ⟨2234, .shfl mode sent b c recv ok⟩) :
    (mode = .bfly ∧ b = 16 ∧ c = 31) ∧
    ((X.tr g).take k).countP Execution.isShfl = 1 + Iface.preloadCount Q L (g / L.block) +
      Lib.shflBase (pollRound 1257 ((X.tr g).take k) - 1) + 2 ∧
    0 < pollRound 1257 ((X.tr g).take k) ∧
    pollRound 1257 ((X.tr g).take k) - 1 < Q.numIters ((L.ctaidOf (g / L.block)).get .z)
      ((L.ctaidOf (g / L.block)).get .x) ∧
    Lib.Ev sent ((∑ c ∈ Finset.range 64, Lib.lanePw Q L g
      (pollRound 1257 ((X.tr g).take k) - 1) c : ℝ) : EReal) := by
  have clean : ∀ f, (Event.mk 2234 (.shfl mode sent b c recv ok)).kind ≠ .ub f := fun _ => nofun
  obtain ⟨w, ent, d, n, t, ins, u, hsc, -, inv, atpc, -, -⟩ := softmax_event_entry hp hX hf get
    clean (by show 574 < 2234; omega) (by show 2234 < 2331; omega)
  obtain ⟨s, hs, hshape⟩ := value_state hsc
  obtain ⟨y, hy, rfl⟩ := softD_shape hshape
  have hg := Frame.lt_of_get hX get
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nub := Frame.noUbBefore_of_get hX get
  have site : y.c.site = .shfl6 := by
    refine site_2234' _ ?_
    have := atpc
    rw [← hy] at this
    exact this.symm
  obtain ⟨E, hP, lim, hq⟩ := ent_glue hp hX hg len hsc
  obtain ⟨hx, hy', hz⟩ := Lib.coordinate_bounds hp hg
  have vrow := valid_row hq (hp.qLenLe _ hz) hv
  obtain ⟨ledg, inv', cur, sc⟩ := soft_win hp hX (hB g) k len _ hs nub w ent y n rfl inv.entry E
  have M := soft_mex hp hX (words_ev hp hX hf hB hS lane hv) k len _ hs nub w ent y n rfl
    inv.entry
  obtain ⟨k', a', sh', hk', hg', hpr⟩ := sc.ev (by rw [site]; rfl)
  have hsx : ∀ j < 64, y.v.s[j]? = some (.float .f32 (Lib.laneScore Q L g y.c.i j)) := by
    intro j hj
    have := hS g k' a' y.v.s sh' hg' hv j hj
    rwa [hpr, Nat.add_sub_cancel] at this
  have hcx := (cur vrow).cur (by rw [site]; rfl)
  have hlim : y.c.i < ent.limit := inv'.loop (by rw [site]; decide) (by rw [site]; decide)
    (by rw [site]; decide) (fun j => by rw [site]; nofun)
  rw [lim] at hlim
  have hn := Lib.blk_lt hp.splitsPos hlim
  have hnb : Q.splits * y.c.i + (L.ctaidOf (g / L.block)).get .x <
      Q.blocks ((L.ctaidOf (g / L.block)).get .z) := by
    have := Nat.mul_comm Q.splits y.c.i
    omega
  have rd : pollRound 1257 ((X.tr g).take k) - 1 = y.c.i := by
    have := ledg
    simp only [Led, site, Site.afterS, Bool.toNat_true] at this
    omega
  have hpos : 0 < Q.scale * log2eF32 := mul_pos hp.scalePos (by unfold log2eF32; norm_num)
  have hmp : Ev (m0 y) (Lib.laneSt Q L g y.c.i).m := by
    have := M.m
    simpa [m0, site, updS] using this
  obtain ⟨hE, X1⟩ := exp_in_x hp E hP inv'.thread hnb (hp.seqRange _ hz) hsx hcx hmp
    (M.mx (by rw [site]; rfl))
  obtain ⟨t', ins', o, ht, -, hc, fire⟩ := Frame.fired_siteU (fun g h => threadD_sound hp h) hX get
    hs (fun f h => by cases h)
  change (Data.codeS ent L g).AtD y t' at ht
  obtain ⟨-, -, -, -, regs⟩ := ht
  change kernel.code[y.c.site.pc]? = some ins' at hc
  change Fires y.c.site.pc (eventTmpl Assumptions.all L g t' ins'.op) _ o at fire
  have h7 : y.c.site.pc = 2234 := by rw [site]; rfl
  rw [h7] at hc fire
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_6)
  obtain ⟨same, hmd, hbb, hcc⟩ := Lib.shfl_operand (n := 16) (m := (16 : Nat)) (bv := 16) rfl rfl
    fire rfl
  have hF := atS_xF regs
  rw [xF_round (by rw [site]; rfl) hE] at hF
  have k1 : 1529 ∈ xKeys := by decide +kernel
  have hreg := holds_mem hF (mem_factsFrom (val := xE ent L g y) k1)
  have hshapent : sent = .float .f32 (∑ c ∈ Finset.range 64, Lib.lanePw Q L g y.c.i c) := by
    rw [Option.some.inj (same.symm.trans hreg)]
    exact row_sum_word hpos X1
  have total := shfl_ordinal hp hX len hsc nub
  have ref := (reached_table hf hg nub hsc).2
  change Softmax.Ref _ d (softCounts n) at ref
  have score := congrArg Cnt.s ref.ledger
  change n (.poll 1257) = d.i + d.site.afterS.toNat at score
  have cnt (key : Cls) : n key = ((X.tr g).take k).countP (cls key) := fcount hsc key
  rw [cnt] at score total
  have as : d.site.afterS.toNat = 1 := by rw [← hy, site]; rfl
  have ir : shflInRound d.site d.i = 2 := by rw [← hy, site]; rfl
  simp only [shflCount, ir] at total
  change pollRound 1257 ((X.tr g).take k) = d.i + d.site.afterS.toNat at score
  have hi : d.i = y.c.i := by rw [← hy]
  refine ⟨⟨hmd, hbb, hcc⟩, ?_, by omega, by omega, ?_⟩
  · refine total.trans ?_
    rw [rd, ← hi]
    omega
  rw [rd, hshapent]
  exact ⟨erealValue_coe .f32 _ |>.symm, EReal.coe_ne_top _⟩

private theorem xor16' : ∀ a < 32, (a ^^^ 16) < 32 ∧ (a ^^^ 16) % 16 = a % 16 ∧
    (a ^^^ 16) / 16 = 1 - a / 16 := by decide

/-- **The words of a shuffle of pc 2234 are the halves' sums**: the lane's and its partner's add up
to the sum of the round's block. -/
public theorem sum_ev {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hB : ∀ g, Lib.BiasEv Q L g X) (hS : ∀ g, Lib.ScoreEv Q L g X) (lane : g % L.block < 128)
    (hv : Lib.QRowValid Q L (g / L.block) (Lib.softRow (g % L.block))) :
    ∀ k mode sent b c recv ok, X.get (g, k) = some ⟨2234, .shfl mode sent b c recv ok⟩ →
      ∃ u v : ℝ, Lib.Ev sent u ∧ Lib.Ev recv v ∧ u + v =
        Lib.laneSum Q L g (pollRound 1257 ((X.tr g).take k) - 1) := by
  intro k mode sent b c recv ok get
  obtain ⟨⟨rfl, rfl, rfl⟩, c1, p1, hlim, h1⟩ := sent_sumv hp hX hf hB hS lane hv get
  obtain ⟨j, b', c', r', o', got, low, cta, cnt⟩ :=
    late_partner hp hX hf get (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
      (by decide) lane
  set gp := g - g % 32 + (g % 32 ^^^ 16) with hgp
  have hb : L.block = 256 := hp.block
  obtain ⟨x1, x2, x3⟩ := xor16' (g % 32) (Nat.mod_lt _ (by decide))
  have row : Lib.softRow (gp % L.block) = Lib.softRow (g % L.block) := by
    unfold Lib.softRow; rw [hgp, hb]; omega
  have half : gp % L.block / 16 % 2 = 1 - g % L.block / 16 % 2 := by
    rw [hgp, hb]; omega
  have hvp : Lib.QRowValid Q L (gp / L.block) (Lib.softRow (gp % L.block)) := by
    rw [cta, row]; exact hv
  obtain ⟨-, c2, p2, -, h2⟩ := sent_sumv hp hX hf hB hS low hvp got
  rw [cnt, cta, c1] at c2
  have eq : pollRound 1257 ((X.tr gp).take j) = pollRound 1257 ((X.tr g).take k) := by
    have e : Lib.shflBase (pollRound 1257 ((X.tr g).take k) - 1) =
        Lib.shflBase (pollRound 1257 ((X.tr gp).take j) - 1) := by omega
    rcases lt_trichotomy (pollRound 1257 ((X.tr g).take k) - 1)
      (pollRound 1257 ((X.tr gp).take j) - 1) with h | h | h
    · have := Lib.shflBase_lt h; omega
    · omega
    · have := Lib.shflBase_lt h; omega
  rw [eq] at h2
  refine ⟨_, _, h1, h2, ?_⟩
  exact Lib.laneSum_halves Q L _ hp.splitsPos hp.scalePos hlim cta row half

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
