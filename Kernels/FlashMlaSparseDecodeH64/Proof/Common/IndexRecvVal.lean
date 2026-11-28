-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIxAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIxN
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexRecv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictIndex
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictIndexRecv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictIndexSrc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictOperand
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.ValInv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexOk
public import Lemmas.Flow.Arith32Wide
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIxCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIxFacts
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLive
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexVal
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictIndexOrigin
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # The words an index lane receives are its partners' validity bits

`vbit P L y b e`: the validity of the slot at position `e` (0 or 1) of lane `y`'s pair in block `b`
(the main cache's slot `64 b + 2 lane + e`, from the main cache's block count on the extra
cache's `64 (b - M) + 2 lane + e`). A lane's first shuffle of block `b` (its `3 + 2 b`-th)
receives the word its partner `lane ^^^ 1` sent, the cvt of its quad word of `vbit`s
(`ix_recv1`); the second receives its partner `lane ^^^ 2`'s `or` of its quad word with the
first word it received (`ix_recv2`). -/

/-! # The validity tests of an index lane's state

At a state of the index warp's block `b` past the poll (`sA1`, `sA2`, `stA`, `bA`: the main
cache's blocks, `sB1`, `sB2`, `stB`, `bB`: the extra cache's), the shuffles made are `3 + 2 b`
and the site's, and the two tests of the lane's positions (`okM0`, `okM1`; `okE0`, `okE1`) are
the validity of the slots at the lane's positions `64 b + 2 lane + e` of the main cache (of the
extra cache, `64 (b - M) + 2 lane + e`), `M` the main cache's blocks. -/

/-! # The source of a received word of an index lane

`ix_recvSrc`: a word a lane of the index warp received as its `cnt`-th shuffle (`3 ≤ cnt`) is the
word its partner lane's shuffle of the same count sent, the partner (`lane ^^^ b`, `b` the
distance of the lane's own shuffle site) being a lane of the warp at a shuffle site, and the word
the operand fact of that site. -/

/-! # The word an index lane's shuffle sends

`ix_sent`: the shuffle of an index lane at a state (a shuffle site) sends the word its operand
register's fact names, `ixVal c (sendReg site)` (`ix_shflSends`), a butterfly of the site's
distance over the full warp. Every shuffle of a lane's window has well-formed receives
(`ix_shRecv`), so the strict state before it is good. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow Index

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A shuffle of an index lane sends the word of its site's fact.** -/
theorem ix_sent (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {h i : Nat} {n : Cls → Nat} {d : Index.D} {e : Event} {md : ShflMode}
    {a : Value} {b cc : Nat} {r : Value} {ok : Bool} (hh : h < L.threads) (hw : warpOf L h = 7)
    (he : X.get (h, i) = some e) (hk : e.kind = .shfl md a b cc r ok)
    (hσ : Frame.stateAt (thread P L) X h i = some (some (idxState P L h d n))) :
    (d.site = .sA1 ∨ d.site = .sA2 ∨ d.site = .sB1 ∨ d.site = .sB2) ∧
      a = ixVal P L h d.c (sendReg d.site) ∧ b = sendDist d.site ∧ cc = 31 ∧ md = .bfly := by
  obtain ⟨k0, n0, hlt, hk0⟩ := index_origin hσ
  have hW := ix_win hp hX hFw (ix_shRecv hp hX hFw _) hh hw hk0 (i - k0)
    (by rw [show k0 + (i - k0) = i by omega])
  rw [show k0 + (i - k0) = i by omega] at hW
  obtain ⟨-, t1, o', hgood, hq, hes⟩ := ix_windowAt hp hX hh (subOk_of_warp hw) hk0 hlt hσ he hW
  obtain ⟨ins, hc', hf⟩ := Code.fired_of_good (thread_sound hp) hgood hes
  have hub : ∀ f, e.kind ≠ .ub f := fun f hf => by rw [hk] at hf; cases hf
  obtain ⟨hev, -, -⟩ := ix_evAt hp hX hFw he hub hσ
  have hsite := ix_shflSite hev hk
  have hse : Execution.isShfl e = true := by
    obtain ⟨pc, kd⟩ := e; simp only at hk; subst hk; rfl
  obtain ⟨-, -, -, -, hF⟩ := hgood.1
  obtain ⟨recv, ok', he'⟩ := ix_shflSends (P := P) hF hsite hc' hf hse
  rw [he'] at hk
  obtain ⟨h1, h2, h3, h4, -⟩ := Kind.shfl.inj hk
  exact ⟨hsite, h2.symm, h3.symm, h4.symm, h1.symm⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow Index

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A shuffle of an index lane is at an index state** (past the three first shuffles). -/
theorem ix_stateAtShfl (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {h j pc : Nat} {md : ShflMode} {a : Value} {b cc : Nat} {r : Value}
    {ok : Bool} (hh : h < L.threads) (hw : warpOf L h = 7)
    (he : X.get (h, j) = some ⟨pc, .shfl md a b cc r ok⟩)
    (hc : 3 ≤ ((X.tr h).take j).countP Execution.isShfl) :
    ∃ d n, Frame.stateAt (thread P L) X h j = some (some (idxState P L h d n)) := by
  have hub : ∀ f, (⟨pc, .shfl md a b cc r ok⟩ : Event).kind ≠ .ub f := fun f hf => by cases hf
  obtain ⟨σ, hσ, -⟩ := ev_at hp hX hFw he hub
  rcases ix_cls2 hFw hh hw hσ with ⟨ds, ns, rfl, hRW, -⟩ | ⟨s, ns, rfl, -, hn2⟩ | ⟨ds, ns, rfl⟩
  · have h1 := refW_le hRW
    have h2 : ns .shfl = ((X.tr h).take j).countP Execution.isShfl := state_count hσ .shfl
    omega
  · have h2 : ns .shfl = ((X.tr h).take j).countP Execution.isShfl := state_count hσ .shfl
    omega
  · exact ⟨ds, ns, hσ⟩

/-- The source lane of a full-warp butterfly of a distance below 32. -/
theorem shflSource_bfly {lane b : Nat} (hl : lane < 32) (hb : b < 32) :
    (shflSource .bfly lane b 31).1 = lane ^^^ b := by
  have hx : lane ^^^ b < 32 := Nat.xor_lt_two_pow (n := 5) hl hb
  have e1 : b % 32 = b := Nat.mod_eq_of_lt hb
  simp only [shflSource, e1]
  have e2 : (31 : Nat) % 32 = 31 := rfl
  have e3 : (31 : Nat) / 256 % 32 = 0 := rfl
  rw [e2, e3]
  have e4 : (lane &&& 0) ||| (31 &&& (31 - 0)) = 31 := by simp
  rw [e4]
  simp only [show lane ^^^ b ≤ 31 by omega, ↓reduceIte]

/-- **The source of a received word.** -/
theorem ix_recvSrc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g cnt : Nat} {v : Value} (hx : g < L.threads) (hw : warpOf L g = 7)
    (hcnt : 3 ≤ cnt) (hr : RecvAt X g cnt v) :
    ∃ j d n, Frame.stateAt (thread P L) X g j = some (some (idxState P L g d n)) ∧
      NoUbBefore X g j ∧ ((X.tr g).take j).countP Execution.isShfl = cnt ∧
      (d.site = .sA1 ∨ d.site = .sA2 ∨ d.site = .sB1 ∨ d.site = .sB2) ∧
      ∃ gp jp dp np, gp = g - PTX.laneOf L g + (PTX.laneOf L g ^^^ sendDist d.site) ∧
        gp < L.threads ∧ warpOf L gp = 7 ∧
        Frame.stateAt (thread P L) X gp jp = some (some (idxState P L gp dp np)) ∧
        NoUbBefore X gp jp ∧ ((X.tr gp).take jp).countP Execution.isShfl = cnt ∧
        (dp.site = .sA1 ∨ dp.site = .sA2 ∨ dp.site = .sB1 ∨ dp.site = .sB2) ∧
        v = ixVal P L gp dp.c (sendReg dp.site) := by
  obtain ⟨j, pc, md, a, b, cc, ok, hget, hc⟩ := hr
  obtain ⟨d, n, hσ⟩ := ix_stateAtShfl hp hX hFw hx hw hget (by omega)
  obtain ⟨hs, ha, hb, hcc, hmd⟩ := ix_sent hp hX hFw hx hw hget rfl hσ
  subst hmd hcc
  obtain ⟨jp, pc', b', c', r', o', hsj, -, hcs, hsT, hsW⟩ := ix_shflSrc hp hX hFw hget hσ
  have hl : PTX.laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have hb32 : b < 32 := by
    rw [hb]; rcases hs with h | h | h | h <;> rw [h] <;> decide
  rw [shflSource_bfly hl hb32] at hsj hcs hsT hsW
  refine ⟨j, d, n, hσ, noUbBefore_of_get hX hget, hc, hs,
    g - PTX.laneOf L g + (PTX.laneOf L g ^^^ b), jp, ?_⟩
  rw [hc] at hcs
  obtain ⟨dp, np, hσp⟩ := ix_stateAtShfl hp hX hFw hsT hsW hsj (by omega)
  obtain ⟨hsp, hap, -⟩ := ix_sent hp hX hFw hsT hsW hsj rfl hσp
  exact ⟨dp, np, by rw [hb], hsT, hsW, hσp, noUbBefore_of_get hX hsj, hcs, hsp, hap⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The tests of a state in the main cache's blocks.** -/
def MainOk (P : Params) (L : Launch) (g : Nat) (d : Index.D) (b : Nat) : Prop :=
  b < FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g)) ∧
    (okM0 d.c = true ↔ slotValid P (ctaidY L g) (ctaidX L g) false
      (64 * b + Index.lane2 L g)) ∧
    (okM1 d.c = true ↔ slotValid P (ctaidY L g) (ctaidX L g) false
      (64 * b + Index.lane2 L g + 1))

/-- **The tests of a state in the extra cache's blocks.** -/
def ExtraOk (P : Params) (L : Launch) (g : Nat) (d : Index.D) (b : Nat) : Prop :=
  FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g)) ≤ b ∧
    (okE0 d.c = true ↔ slotValid P (ctaidY L g) (ctaidX L g) true
      (64 * (b - FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g))) +
        Index.lane2 L g)) ∧
    (okE1 d.c = true ↔ slotValid P (ctaidY L g) (ctaidX L g) true
      (64 * (b - FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g))) +
        Index.lane2 L g + 1))

/-- **The shuffles and tests of an index state in a block's main or extra part.** -/
theorem ix_blk (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat} (hub : NoUbBefore X g k) {d : Index.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g k = some (some (idxState P L g d n)))
    (hx : g < L.threads) (hw : warpOf L g = 7) :
    ∃ b, n .shfl = 3 + 2 * b + Index.soff d.site ∧
      n (.index .st) = (2 + Index.sgB L g) * b + Index.stDone L g d.site d.el ∧
      ((d.site = .bA ∨ d.site = .bB) → ixSkipB L g = false) ∧
      ((d.site = .sA1 ∨ d.site = .sA2 ∨ d.site = .stA ∨ d.site = .bA) → MainOk P L g d b) ∧
      ((d.site = .sB1 ∨ d.site = .sB2 ∨ d.site = .stB ∨ d.site = .bB) → ExtraOk P L g d b) := by
  obtain ⟨b, hn, hbl, -⟩ := ix_facts hp hX hFw hub hσ hx hw
  have hJ := (follow_iff.mp hFw g hx k).2 _ hσ
  obtain ⟨-, hR, -, -⟩ := hJ
  obtain ⟨-, -, hR'⟩ : 3 ≤ n .shfl ∧ subOk L g .index = true ∧
      (n .ub = 0 → Index.Ref P L g d (fun c => n (.index c))) := hR
  obtain ⟨i, -, -, -, hc, hct, hst⟩ := hR' (state_noUb hub hσ) (state_noUbIx hub hσ)
  have hbi : b = i := hbl.symm.trans (Index.blockOf_eq' hc)
  subst hbi
  obtain ⟨iv, hctv, hV⟩ := ix_val hp hX hFw hσ
  obtain ⟨hok, -, -⟩ := ix_ok hp hX hσ d n rfl
  obtain ⟨hwa, hwb, -, -, -⟩ := len_words hp (g / L.block)
  rw [rowOf_cta] at hwa hwb
  have hl2 : Index.lane2 L g < 64 := by
    have := Nat.mod_lt (tidOf L g) (show 0 < 32 by norm_num)
    simp only [Index.lane2]; omega
  obtain ⟨site, el, ac, c⟩ := d
  obtain ⟨hst1, -, hst2⟩ := hst
  refine ⟨b, hn, hst1, hst2, fun hs => ?_, fun hs => ?_⟩
  · dsimp only at hs
    have hA : site ≠ .lenA := by rcases hs with h | h | h | h <;> rw [h] <;> simp
    have hB : site ≠ .lenB := by rcases hs with h | h | h | h <;> rw [h] <;> simp
    obtain ⟨h0, h1⟩ := ix_words_of (d := ⟨site, el, ac, c⟩) hA hB hok
    dsimp only at h0 h1
    have hm : Index.MainW P L g c b := by
      rcases hs with h | h | h | h <;> subst h <;> exact hct
    have hmv : Index.MainW P L g c iv := by
      rcases hs with h | h | h | h <;> subst h <;> exact hctv
    obtain rfl : iv = b := Index.mainW_inj hmv hm
    have hrow : Index.MRow P L g c iv := by
      rcases hs with h | h | h | h <;> subst h <;> exact hV.1
    obtain ⟨hr0, hr1, hrw⟩ := hrow
    have hMn : Index.nMain c.l0 = FlashMlaSparseDecodeH64.numOrigBlocks
        (P.topkLen (ctaidY L g)) := nMain_lane hp h0
    have hbnd := (Index.nMain_bnd c.l0).2.1
    have hlt := hm.1
    have hmin : Index.nMin c.l0 c.l1 ≤ Index.nMain c.l0 := Nat.min_le_left _ _
    have hlen : c.l0 = W (P.topkLen (ctaidY L g)) := h0.trans hwa
    refine ⟨by omega, ?_, ?_⟩
    · refine ixOk_main_iff hp hr0 ?_ hlen (by omega)
      have e1 := addi_negW (a := Index.lane2 L g + 1 + 64 * iv) (k := 1) (by omega) (by omega)
      rw [show Index.lane2 L g + 1 + 64 * iv - 1 = 64 * iv + Index.lane2 L g by omega] at e1
      rw [hrw]
      exact e1
    · refine ixOk_main_iff hp hr1 ?_ hlen (by omega)
      rw [hrw, show Index.lane2 L g + 1 + 64 * iv = 64 * iv + Index.lane2 L g + 1 by omega]
  · dsimp only at hs
    have hA : site ≠ .lenA := by rcases hs with h | h | h | h <;> rw [h] <;> simp
    have hB : site ≠ .lenB := by rcases hs with h | h | h | h <;> rw [h] <;> simp
    obtain ⟨h0, h1⟩ := ix_words_of (d := ⟨site, el, ac, c⟩) hA hB hok
    dsimp only at h0 h1
    have hx0 : Index.XW L g c b := by
      rcases hs with h | h | h | h <;> subst h <;> exact hct
    have hxv : Index.XW L g c iv := by
      rcases hs with h | h | h | h <;> subst h <;> exact hctv
    obtain rfl : iv = b := Index.xw_inj hxv hx0
    have hrow : Index.ERow P L g c (iv - Index.nMain c.l0) := by
      rcases hs with h | h | h | h <;> subst h <;> exact hV.1
    obtain ⟨hr0, hr1⟩ := hrow
    have hMn : Index.nMain c.l0 = FlashMlaSparseDecodeH64.numOrigBlocks
        (P.topkLen (ctaidY L g)) := nMain_lane hp h0
    obtain ⟨-, hge, hlr, -, -, hxa⟩ := hx0
    have hrl := Index.rounds_lt c.l0 c.l1
    have hxa' : c.xa = W (Index.lane2 L g + 64 + 64 * (iv - Index.nMain c.l0)) := by
      rw [hxa, ixXa0_val hp g, toNat_W (by omega)]
      show W _ = W _
      rw [Nat.mod_eq_of_lt (by simp only [Index.lane2] at hl2 ⊢; omega)]
      simp only [Index.lane2]
      rw [show tidOf L g % 32 * 2 = 2 * (tidOf L g % 32) by omega]
    have hlen : c.l1 = W (P.extraTopkLen (ctaidY L g)) := h1.trans hwb
    refine ⟨by omega, ?_, ?_⟩
    · rw [← hMn]
      refine ixOk_extra_iff hp hr0 ?_ hlen (by omega)
      have e1 := addi_negW (a := Index.lane2 L g + 64 + 64 * (iv - Index.nMain c.l0)) (k := 64)
        (by omega) (by omega)
      rw [show Index.lane2 L g + 64 + 64 * (iv - Index.nMain c.l0) - 64 =
        64 * (iv - Index.nMain c.l0) + Index.lane2 L g by omega] at e1
      rw [hxa']
      exact e1
    · rw [← hMn]
      refine ixOk_extra_iff hp hr1 ?_ hlen (by omega)
      have e1 := addi_negW (a := Index.lane2 L g + 64 + 64 * (iv - Index.nMain c.l0)) (k := 63)
        (by omega) (by omega)
      rw [show Index.lane2 L g + 64 + 64 * (iv - Index.nMain c.l0) - 63 =
        64 * (iv - Index.nMain c.l0) + Index.lane2 L g + 1 by omega] at e1
      rw [hxa']
      exact e1

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Index

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The validity of the slot of lane `y`'s position `e` in block `b`. -/
def vbit (P : Params) (L : Launch) (y b e : Nat) : Bool :=
  if b < FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L y)) then
    decide (slotValid P (ctaidY L y) (ctaidX L y) false (64 * b + Index.lane2 L y + e))
  else
    decide (slotValid P (ctaidY L y) (ctaidX L y) true
      (64 * (b - FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L y))) +
        Index.lane2 L y + e))

theorem ixVal_606 {g : Nat} (c : IxCtl) :
    ixVal P L g c 606 = cvts8 (ixQuadW L g (okM0 c) (okM1 c)) := rfl

theorem ixVal_609 {g : Nat} (c : IxCtl) :
    ixVal P L g c 609 = cvts8 (or32 (rvw c.rv1) (ixQuadW L g (okM0 c) (okM1 c))) := rfl

theorem ixVal_645 {g : Nat} (c : IxCtl) :
    ixVal P L g c 645 = cvts8 (ixQuadW L g (okE0 c) (okE1 c)) := rfl

theorem ixVal_648 {g : Nat} (c : IxCtl) :
    ixVal P L g c 648 = cvts8 (or32 (rvw c.rv1) (ixQuadW L g (okE0 c) (okE1 c))) := rfl

theorem okMain_vbit {y b : Nat} {d : Index.D} (h : MainOk P L y d b) :
    okM0 d.c = vbit P L y b 0 ∧ okM1 d.c = vbit P L y b 1 := by
  obtain ⟨hl, h0, h1⟩ := h
  simp only [vbit, hl, ↓reduceIte, Nat.add_zero]
  exact ⟨Bool.eq_iff_iff.mpr (by simpa using h0), Bool.eq_iff_iff.mpr (by simpa using h1)⟩

theorem okExtra_vbit {y b : Nat} {d : Index.D} (h : ExtraOk P L y d b) :
    okE0 d.c = vbit P L y b 0 ∧ okE1 d.c = vbit P L y b 1 := by
  obtain ⟨hl, h0, h1⟩ := h
  simp only [vbit, show ¬ b < FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L y))
    from by omega, ↓reduceIte, Nat.add_zero]
  exact ⟨Bool.eq_iff_iff.mpr (by simpa using h0), Bool.eq_iff_iff.mpr (by simpa using h1)⟩

/-- **The first shuffle of block `b` receives the partner's quad word.** -/
theorem ix_recv1 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g b : Nat} {v : Value} (hx : g < L.threads) (hw : warpOf L g = 7)
    (hr : RecvAt X g (3 + 2 * b) v) :
    ∃ y, y = g - PTX.laneOf L g + (PTX.laneOf L g ^^^ 1) ∧ y < L.threads ∧ warpOf L y = 7 ∧
      v = cvts8 (ixQuadW L y (vbit P L y b 0) (vbit P L y b 1)) := by
  obtain ⟨j, d, n, hσ, hnu, hc, hs, gp, jp, dp, np, hgp, hxp, hwp, hσp, hnup, hcp, hsp, hv⟩ :=
    ix_recvSrc hp hX hFw hx hw (by omega) hr
  obtain ⟨b0, hn0, -, -, -, -⟩ := ix_blk hp hX hFw hnu hσ hx hw
  have hcn : n .shfl = 3 + 2 * b := (state_count hσ .shfl).trans hc
  have hsd : sendDist d.site = 1 := by
    rcases hs with h | h | h | h <;> simp only [h, sendDist, Index.soff_sA1, Index.soff_sA2,
      Index.soff_sB1, Index.soff_sB2] at hn0 ⊢ <;> omega
  obtain ⟨b1, hn1, -, -, hM, hE⟩ := ix_blk hp hX hFw hnup hσp hxp hwp
  have hcn1 : np .shfl = 3 + 2 * b := (state_count hσp .shfl).trans hcp
  refine ⟨gp, by rw [hgp, hsd], hxp, hwp, ?_⟩
  rw [hv]
  rcases hsp with h | h | h | h
  · rw [h] at hn1
    simp only [Index.soff_sA1] at hn1
    obtain rfl : b1 = b := by omega
    obtain ⟨e0, e1⟩ := okMain_vbit (hM (Or.inl h))
    rw [h]
    show ixVal P L gp dp.c 606 = _
    rw [ixVal_606, e0, e1]
  · rw [h] at hn1
    simp only [Index.soff_sA2] at hn1
    omega
  · rw [h] at hn1
    simp only [Index.soff_sB1] at hn1
    obtain rfl : b1 = b := by omega
    obtain ⟨e0, e1⟩ := okExtra_vbit (hE (Or.inl h))
    rw [h]
    show ixVal P L gp dp.c 645 = _
    rw [ixVal_645, e0, e1]
  · rw [h] at hn1
    simp only [Index.soff_sB2] at hn1
    omega

/-- **The second shuffle of block `b` receives the partner's `or`**: of its quad word with the
first word it received from its own partner. -/
theorem ix_recv2 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g b : Nat} {v : Value} (hx : g < L.threads) (hw : warpOf L g = 7)
    (hr : RecvAt X g (3 + 2 * b + 1) v) :
    ∃ y z, y = g - PTX.laneOf L g + (PTX.laneOf L g ^^^ 2) ∧
      z = y - PTX.laneOf L y + (PTX.laneOf L y ^^^ 1) ∧ y < L.threads ∧ z < L.threads ∧
      warpOf L y = 7 ∧ warpOf L z = 7 ∧
      v = cvts8 (or32 (rvw (cvts8 (ixQuadW L z (vbit P L z b 0) (vbit P L z b 1))))
        (ixQuadW L y (vbit P L y b 0) (vbit P L y b 1))) := by
  obtain ⟨j, d, n, hσ, hnu, hc, hs, gp, jp, dp, np, hgp, hxp, hwp, hσp, hnup, hcp, hsp, hv⟩ :=
    ix_recvSrc hp hX hFw hx hw (by omega) hr
  obtain ⟨b0, hn0, -, -, -, -⟩ := ix_blk hp hX hFw hnu hσ hx hw
  have hcn : n .shfl = 3 + 2 * b + 1 := (state_count hσ .shfl).trans hc
  have hsd : sendDist d.site = 2 := by
    rcases hs with h | h | h | h <;> simp only [h, sendDist, Index.soff_sA1, Index.soff_sA2,
      Index.soff_sB1, Index.soff_sB2] at hn0 ⊢ <;> omega
  obtain ⟨b1, hn1, -, -, hM, hE⟩ := ix_blk hp hX hFw hnup hσp hxp hwp
  have hcn1 : np .shfl = 3 + 2 * b + 1 := (state_count hσp .shfl).trans hcp
  have hrv := (ix_rv hp hX hFw hnup hσp).1
  rw [hcp] at hrv
  rcases hsp with h | h | h | h
  · rw [h] at hn1
    simp only [Index.soff_sA1] at hn1
    omega
  · rw [h] at hn1
    simp only [Index.soff_sA2] at hn1
    obtain rfl : b1 = b := by omega
    obtain ⟨e0, e1⟩ := okMain_vbit (hM (Or.inr (Or.inl h)))
    have hr1 := hrv (by rw [h]; simp)
    rw [h] at hr1
    simp only [Index.soff_sA2, show 3 + 2 * b1 + 1 - 1 = 3 + 2 * b1 from rfl] at hr1
    obtain ⟨z, hz, hzt, hzw, hvz⟩ := ix_recv1 hp hX hFw hxp hwp hr1
    refine ⟨gp, z, by rw [hgp, hsd], hz, hxp, hzt, hwp, hzw, ?_⟩
    rw [hv, h]
    show ixVal P L gp dp.c 609 = _
    rw [ixVal_609, e0, e1, hvz]
  · rw [h] at hn1
    simp only [Index.soff_sB1] at hn1
    omega
  · rw [h] at hn1
    simp only [Index.soff_sB2] at hn1
    obtain rfl : b1 = b := by omega
    obtain ⟨e0, e1⟩ := okExtra_vbit (hE (Or.inr (Or.inl h)))
    have hr1 := hrv (by rw [h]; simp)
    rw [h] at hr1
    simp only [Index.soff_sB2, show 3 + 2 * b1 + 1 - 1 = 3 + 2 * b1 from rfl] at hr1
    obtain ⟨z, hz, hzt, hzw, hvz⟩ := ix_recv1 hp hX hFw hxp hwp hr1
    refine ⟨gp, z, by rw [hgp, hsd], hz, hxp, hzt, hwp, hzw, ?_⟩
    rw [hv, h]
    show ixVal P L gp dp.c 648 = _
    rw [ixVal_648, e0, e1, hvz]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
