-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.GlobalReads
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Occurs
public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.SoftmaxEntry
import Kernels.InklingRelDecode.Proof.Common.BiasEntry
import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
import Kernels.InklingRelDecode.Proof.Softmax.BiasValue
public import Kernels.InklingRelDecode.Proof.Lib.GlobalLoad
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Proof.Lib.Geometry
import Kernels.InklingRelDecode.Proof.Lib.Rows
import Kernels.InklingRelDecode.Proof.Lib.WideBits
import Kernels.InklingRelDecode.Proof.Softmax.TcCount
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.TcCount
import all Kernels.InklingRelDecode.Proof.Common.Follow

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Flow PTX.Proof Control

public theorem bias_pre_load :
    ∀ j : Fin 64, Lib.globalLoad (680 + 2 * j.val) (2141 + j.val) 16 = true := by
  decide +kernel

public theorem bias_nxt_load : ∀ j : Fin 64,
    Lib.globalLoad (1124 + 2 * j.val) (2211 + j.val) 16 = true := by
  decide +kernel

private theorem pre_live : ∀ j : Fin 64, 2141 + j.val ∈ ctlLive (680 + 2 * j.val) := by
  decide +kernel

private theorem nxt_live : ∀ j : Fin 64, 2211 + j.val ∈ ctlLive (1124 + 2 * j.val) := by
  decide +kernel

private theorem mem_sites (s : Site) : s ∈ allSites := by
  cases s <;> simp [allSites]

private theorem site_inj {s s' : Site} (h : s.pc = s'.pc) : s = s' :=
  List.inj_on_of_nodup_map sites_nodup (mem_sites s) (mem_sites s') h

private theorem sx_offset {bo : Nat} (h : bo * 128 < 2 ^ 31) :
    sx (1280 + 2 ^ 32 - bo * 128) + bo * 128 = 1280 + 2 ^ 64 ∨
      (sx (1280 + 2 ^ 32 - bo * 128) + bo * 128 = 1280 ∧ bo * 128 ≤ 1280) := by
  unfold Lib.sx
  omega

private theorem head_small : ∀ t : Nat, t < 256 → headInGroup t < 6 := by decide +kernel

/-- **A bias byte is an input byte.** -/
private theorem bias_input {Q L m} (hp : Pre Q L m) {e : Entry} {t B j z y : Nat}
    (hz : z < Q.b) (hy : y < kvHeads) (ht : t < 256) (hfirst : e.firstToken = Q.qStart z)
    (hstride : e.stride = Q.strideRel) (hrel : e.rel = Q.relBase) (hhead : e.head = y * 6)
    (hoff : e.biasOffset = Q.blocks z * 128) (hnb : e.nbias = Q.nBias z)
    (hvalid : validRow e t = true) (hqlen : e.qlen = Q.qLen z) (hB : B < Q.blocks z)
    (hnbB : e.nbias ≤ B) (hj : j < 64) :
    token t < Q.qLen z ∧ y * 6 + headInGroup t < heads ∧
      B * 128 + 64 * (t / 16 % 2) + j + relPad - Q.blocks z * 128 < relPad ∧
      (sx (B * 128) * 2 + biasBase e t + 2 * j) % 2 ^ 64 = Q.relBase + 2 * ((Q.qStart z
        + token t) * Q.strideRel + (y * 6 + headInGroup t) * relPad + (B * 128 + 64 * (t / 16 % 2)
        + j + relPad - Q.blocks z * 128)) := by
  have tok : token t < Q.qLen z := by
    simp only [validRow, tokenFits, Bool.and_eq_true, decide_eq_true_eq] at hvalid
    have := hvalid.2.1
    omega
  have hig := head_small t ht
  have hsc := hp.scalarsRange
  have hrange := Lib.token_lt hp hz tok
  have hnt := hp.nTokRange
  have hseq := hp.seqRange z hz
  have hb := Lib.blocks_le_nBias (hp.qLenLe z hz) (hp.qLenSeq z hz)
  have hbl : Q.blocks z * 128 < 2 ^ 31 := by unfold Params.blocks; omega
  have hcol : Q.nBias z * 128 ≤ B * 128 + 64 * (t / 16 % 2) + j := by omega
  have hhd : y * 6 + headInGroup t < heads := by
    have : y < 2 := hy
    unfold heads; omega
  have hcr : B * 128 + 64 * (t / 16 % 2) + j + relPad - Q.blocks z * 128 < relPad := by
    unfold relPad; omega
  have hlt := hp.readsRange _ (.inr (.inl ⟨z, hz, token t, tok, y * 6 + headInGroup t, hhd,
    B * 128 + 64 * (t / 16 % 2) + j + relPad - Q.blocks z * 128, hcr, 1, by norm_num, rfl⟩))
  have key : (sx (B * 128) * 2 + biasBase e t + 2 * j) % 2 ^ 64 = Q.relBase + 2 * ((Q.qStart z
      + token t) * Q.strideRel + (y * 6 + headInGroup t) * relPad + (B * 128 + 64 * (t / 16 % 2)
      + j + relPad - Q.blocks z * 128)) := by
    unfold biasBase
    rw [hfirst, hstride, hrel, hhead, hoff, Lib.sx_small (by omega : B * 128 < 2 ^ 31),
      Lib.sx_small (by omega : Q.qStart z + token t < 2 ^ 31), Lib.sx_small hsc.2.1,
      Nat.mod_eq_of_lt (show (y * 6 + headInGroup t) * 1280 < 2 ^ 32 by
        have : y * 6 + headInGroup t < 12 := hhd
        omega)]
    have sxd := sx_offset hbl
    unfold relPad at hlt ⊢
    generalize (Q.qStart z + token t) * Q.strideRel = P at *
    generalize sx (1280 + 2 ^ 32 - Q.blocks z * 128) = S at *
    generalize Q.blocks z = nb at *
    generalize y * 6 + headInGroup t = hh at *
    rcases sxd with sxd | sxd <;> omega
  exact ⟨tok, hhd, hcr, key⟩

private theorem first_token {Q L m z} (hp : Pre Q L m) (hz : z < Q.b) :
    (Lib.word (b32 (Q.qStart z))).toNat = Q.qStart z := by
  have := Lib.qStart_mono hp (r := z) (r' := Q.b) hz.le le_rfl
  have := hp.cuEnd
  have := hp.nTokRange
  simp only [Lib.word, Value.regBits, b32, truncBits, Option.getD_some, BitVec.toNat_ofNat]
  omega

/-- **A bias load of the Softmax region reads the two bytes of an element of `Rel`**, the one of
the block `x + R * splits` (preloads, `R = 0`) or `x + (R + 1) * splits` (the loop's loads), `R`
the polls of `s_ready` before it. -/
public theorem bias_at {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : Occurs L X g k ⟨pc,.rd a bs⟩)
    (site : (∃ j : Fin 64, pc = 680 + 2 * j.val) ∨ ∃ j : Fin 64, pc = 1124 + 2 * j.val) :
    ∃ z x y j B : Nat, z = (L.ctaidOf (g / L.block)).get .z ∧ x = (L.ctaidOf (g / L.block)).get .x ∧
      y = (L.ctaidOf (g / L.block)).get .y ∧ z < Q.b ∧ j < 64 ∧ B < Q.blocks z ∧
      Q.nBias z ≤ B ∧ token (g % L.block) < Q.qLen z ∧ y * 6 + headInGroup (g % L.block) < heads ∧
      B * 128 + 64 * (g % L.block / 16 % 2) + j + relPad - Q.blocks z * 128 < relPad ∧
      ((pc = 680 + 2 * j ∧ B = x + pollRound 1257 ((X.tr g).take k) * Q.splits) ∨
        (pc = 1124 + 2 * j ∧ B = x + (pollRound 1257 ((X.tr g).take k) + 1) * Q.splits)) ∧
      a.loc = ⟨.global, 0, Q.relBase + 2 * ((Q.qStart z + token (g % L.block)) * Q.strideRel +
        (y * 6 + headInGroup (g % L.block)) * relPad +
        (B * 128 + 64 * (g % L.block / 16 % 2) + j + relPad - Q.blocks z * 128))⟩ ∧
      a.size = 2 := by
  have hg := he.lt hX
  have hk : k ≤ (X.tr g).length := he.le
  have range : 574 < pc ∧ pc < 2331 := by
    rcases site with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;> have := j.isLt <;> omega
  obtain ⟨w,ent,d,n,t,ins,u,hs,ht,inv,pce,hc,fire⟩ :=
    softmax_occ_entry hp hX hf he (by simp) range.1 range.2
  have nums := reached_numbers hp hX hg hk hs
  have words := reached_words hp hX hg hk hs
  have lim : ent.limit = Q.numIters ((L.ctaidOf (g/L.block)).get .z)
      ((L.ctaidOf (g/L.block)).get .x) := reached_limit hp hX hg hk hs
  obtain ⟨-, first, qlen⟩ := nums
  obtain ⟨d1, h1, seq, last⟩ := words
  have first' : d1.first = b32 (Q.qStart ((L.ctaidOf (g/L.block)).get .z)) := by
    rw [h1] at first; exact first
  obtain ⟨hnb, hoff⟩ := entry_nbias hp hg first' last seq
  rw [← h1] at hnb hoff
  obtain ⟨hx, hy, hz⟩ := Lib.coordinate_bounds hp hg
  have hsplit : ent.split = (L.ctaidOf (g/L.block)).get .x := by rw [h1]; rfl
  have hsplits : ent.splits = Q.splits := by rw [h1]; rfl
  have hhead : ent.head = (L.ctaidOf (g/L.block)).get .y * 6 := by rw [h1]; rfl
  have hstride : ent.stride = Q.strideRel := by rw [h1]; rfl
  have hrel : ent.rel = Q.relBase := by rw [h1]; rfl
  have hfirst : ent.firstToken = Q.qStart ((L.ctaidOf (g/L.block)).get .z) := by
    unfold Entry.firstToken
    rw [first]
    exact first_token hp hz
  have ok := inv.entry
  have hblocks : ent.blocks < 2 ^ 31 → ent.blocks = Q.numIters ((L.ctaidOf (g/L.block)).get .z)
      ((L.ctaidOf (g/L.block)).get .x) := by
    intro h
    rw [← lim, ok.limitEq]
    split_ifs
    · rfl
  have htid : g % L.block < 256 := by rw [hp.block]; exact Nat.mod_lt _ (by norm_num)
  obtain ⟨_, sub, _, _, regs⟩ := ht
  have hsub : t.sub = 0 := sub
  have hy2 : (L.ctaidOf (g/L.block)).get .y < kvHeads := hy
  have nu := he.noUb hX
  have tbl := reached_table hf hg nu hs
  have cnt (key : Cls) : n key = ((X.tr g).take k).countP (cls key) := fcount hs key
  have ref := tbl.2
  change Softmax.Ref _ d (softCounts n) at ref
  have sc := congrArg Softmax.Cnt.s ref.ledger
  change n (.poll 1257) = d.i + d.site.afterS.toNat at sc
  rw [cnt] at sc
  change pollRound 1257 ((X.tr g).take k) = d.i + d.site.afterS.toNat at sc
  rcases site with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hsite : d.site = .pre j := site_inj (by rw [← pce]; exact hj)
    obtain ⟨hi0, hen⟩ := inv.pre j hsite
    simp only [preEnabled, Bool.and_eq_true, decide_eq_true_eq] at hen
    obtain ⟨hvalid, hpos, hlt31, hnbs⟩ := hen
    have reg := holds_mem regs (mem_factsFrom (by rw [hsite]; exact pre_live j))
    rw [value_pre ent L g d (by omega) (by have := j.isLt; omega)] at reg
    have pcs : d.site.pc = 680 + 2 * j.val := pce.symm.trans hj
    rw [pcs] at hc fire
    obtain ⟨loc, size⟩ := Lib.global_load_loc (base := 2141 + j.val) (w := 16) hc (bias_pre_load j)
      hsub reg (Nat.mod_lt _ (by norm_num)) fire rfl
    have hB : ent.split + d.i * ent.splits < Q.blocks ((L.ctaidOf (g/L.block)).get .z) := by
      have := Lib.blk_lt (r := (L.ctaidOf (g/L.block)).get .z)
        (s := (L.ctaidOf (g/L.block)).get .x) (i := d.i) hp.splitsPos
        (by rw [← hblocks hlt31]; omega)
      rw [hsplit, hsplits]
      exact this
    obtain ⟨tok, hh, hc, key⟩ := bias_input hp (e := ent) (t := g % L.block)
      (B := ent.split + d.i * ent.splits) (j := j.val) (z := (L.ctaidOf (g/L.block)).get .z)
      (y := (L.ctaidOf (g/L.block)).get .y) hz hy2 htid hfirst hstride hrel hhead
      hoff hnb hvalid qlen hB (by omega) j.isLt
    refine ⟨_, _, _, j.val, _, rfl, rfl, rfl, hz, j.isLt, hB, (by rw [← hnb]; omega), tok, hh, hc,
      .inl ⟨hj, ?_⟩, ?_, size⟩
    · rw [hsplit, hsplits, ← hsplits, sc, hsite, hi0]; simp [Site.afterS]
    · rw [loc]
      simp only [Nat.add_sub_cancel_left] at key ⊢
      rw [key]
  · have hsite : d.site = .nxt j := site_inj (by rw [← pce]; exact hj)
    have hen := inv.nxt j hsite
    simp only [nextEnabled, Bool.and_eq_true, decide_eq_true_eq] at hen
    obtain ⟨hvalid, hnext, hlt31, hnbs⟩ := hen
    have reg := holds_mem regs (mem_factsFrom (by rw [hsite]; exact nxt_live j))
    rw [value_nxt ent L g d (by omega) (by have := j.isLt; omega)] at reg
    have pcs : d.site.pc = 1124 + 2 * j.val := pce.symm.trans hj
    rw [pcs] at hc fire
    obtain ⟨loc, size⟩ := Lib.global_load_loc (base := 2211 + j.val) (w := 16) hc (bias_nxt_load j)
      hsub reg (Nat.mod_lt _ (by norm_num)) fire rfl
    have hB : ent.splits + (ent.split + d.i * ent.splits) <
        Q.blocks ((L.ctaidOf (g/L.block)).get .z) := by
      have := Lib.blk_lt (r := (L.ctaidOf (g/L.block)).get .z)
        (s := (L.ctaidOf (g/L.block)).get .x) (i := d.i + 1) hp.splitsPos
        (by rw [← hblocks hlt31]; omega)
      rw [Nat.succ_mul] at this
      rw [hsplit, hsplits]
      omega
    obtain ⟨tok, hh, hc, key⟩ := bias_input hp (e := ent) (t := g % L.block)
      (B := ent.splits + (ent.split + d.i * ent.splits)) (j := j.val)
      (z := (L.ctaidOf (g/L.block)).get .z) (y := (L.ctaidOf (g/L.block)).get .y)
      hz hy2 htid hfirst hstride hrel hhead hoff hnb hvalid qlen hB (by omega) j.isLt
    refine ⟨_, _, _, j.val, _, rfl, rfl, rfl, hz, j.isLt, hB, (by rw [← hnb]; omega), tok, hh, hc,
      .inr ⟨hj, ?_⟩, ?_, size⟩
    · rw [hsplit, hsplits, sc, hsite]; simp [Site.afterS]; ring
    · rw [loc]
      simp only [Nat.add_sub_cancel_left] at key ⊢
      rw [key]

end PTX.Kernels.InklingRelDecode.Proof.Softmax
