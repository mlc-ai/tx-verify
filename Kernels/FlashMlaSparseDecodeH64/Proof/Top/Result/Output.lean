-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.GlobalCls
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.StoreUnique
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MmaSlot
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Reads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.OutCol
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.OutStage
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.OutWord
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvChain
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.Lse
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.PvEnv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.PvTele
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.ScoreRead
public import Lemmas.Kernel.Goals
public import Lemmas.Kernel.Memory
public import Lemmas.Tcgen05.MemFloat
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Async
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.TensorOrigin
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.OutGeom
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.OutLdLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.OutWrite
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RoundsPos
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdExists
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Writers
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.EpiPin
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.ResultFloat
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RowMaxSum
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.VoteAgree
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Store
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.EpiFree
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.OfPc
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.OldAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Out
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SinkRd
import Lemmas.Flow.OutKinds
import Lemmas.Tcgen05.AccumulateStored

@[expose] public section

/-! # The stored output values and the untouched global bytes

The first and the fourth conjunct of the Spec's `Post`: every element of O is the attention
(`Res.OutValues`), and every global byte outside O and LSE keeps its launch value
(`Res.OutFrame`). `Res.output` proves both for a complete, followed execution: the staged words
are `out_read` (`Top/Result/OutReadProof.lean`), the scores and masks `score_read` and
`Res.Lse.mask`, the frame `frame_of`. -/

/-! # The untouched global bytes

Every write that covers a global byte is an LSE store or a slot of an output tensor store
(`global_at`), so it covers a byte of the LSE output or of the output tensor. A global byte
outside both keeps its launch content (`IsFinal.unwritten`). -/

/-! # The staged words of warpgroup 0 (`OutRead`)

At a staging store `ost2 c j` the lane's accumulator words are the chunk's load of the last block
(`w0_epiO_old`), each the end of the PV chain of its column (`old_ld_word`); the chain's end times
`2 ^ M` is the sum over the blocks of `weight * value` (`pv_total`), with all blocks finished
(`PairEpi`, from the row-sum exchange `rmax_peer_sum`). The sink word reads as the reference's
(`wg0_sink_rd`). -/

/-! # The words an output load of warpgroup 0 reads

A register `j` of an epilogue load of warpgroup 0 (column `a ≤ 192`) holds the single-precision
number that PV MMA `6 + p` of the last block (`p = (a + j) / 128`) leaves at the cell of its lane
and column `a + j` (`ld_pin_epi`, `load_word`): the end of the PV chain of the block (`PvChain`),
base plus the sum of the slices' products (`old_ld_word`). -/

/-! # The final bytes of the output elements

A byte `z` of the element `(e, q, h, d)` of O is the byte of the output tensor store of the CTA's
warp `w` and chunk `c` (`d = 128 w + off c + i`) that its slot `(i, h, z)` writes. That store
exists (`wg0_outStore`), its slot reads the byte `lsrc` of the staging area (`wg0_store_readEq`)
and its final byte is that of the staging store covering `lsrc` (`out_slot_final`), which is
the store `ost2 c (i / 8)` of thread `64 w + h` of the CTA (`out_geom`), whose bytes are the
`attn` pair (`w0_out_word`). So the memory after the execution holds byte `z` of the number
`attn` there (`out_byte`). -/

/-! # The final byte of an output slot is the staging store's byte

A tensor store's slot write covering a global byte is the only write of it: the slot's byte
determines the CTA, the warp, the chunk and the slot (`slot_inj`), so two stores covering it are
one event (`store_unique`); an LSE store is apart from the output tensor (`Pre`). So the memory
after the execution holds the byte the store writes (`IsFinal.unique`), which is the byte of the
staging store that the store read (`out_slot_byte`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The column `128 w + offset c + x` of a slot determines the warp, the chunk and the column. -/
theorem slot_col_inj {w w' c c' x x' : Nat} (hw : w < 2) (hw' : w' < 2) (hc : c < 4)
    (hc' : c' < 4) (hx : x < 64) (hx' : x' < 64)
    (h : 128 * w + [0, 64, 256, 320].getD c 0 + x =
      128 * w' + [0, 64, 256, 320].getD c' 0 + x') :
    w = w' ∧ c = c' ∧ x = x' := by
  interval_cases c <;> interval_cases c' <;>
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h <;> omega

/-- A chunk's column offset is at most 320. -/
theorem slot_off_le {c : Nat} (hc : c < 4) : [0, 64, 256, 320].getD c 0 ≤ 320 := by
  interval_cases c <;> simp

/-- **An output slot's write is the only write of its byte**: a thread-less write covering the
global byte `l` of the slot `(x, y, z)` of the store `i` is the slot write itself. -/
private theorem slot_write_unique (hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    {i : EvId} {x y z : Nat} {a a' : Acc} {l : Loc} {w' : AsyncCopy.Ref} {bs' : List Byte}
    (hi : X.Intent (.async i (.write (.store x y z))) a true) (hc : a.Covers l)
    (hw' : X.MemWrites w' a' bs') (hc' : a'.Covers l) (hl : l.space = .global) :
    w' = .async i (.write (.store x y z)) := by
  have hns : l.space ≠ .shared := by rw [hl]; exact nofun
  have hG := global_at hp hX hFw hnu hi hc hns
  have hG' := global_at hp hX hFw hnu hw'.intent hc' hns
  cases hG with
  | @store i x y z addr c s hs hw2 hc4 ho hx hy hz hl1 hb =>
    cases hG' with
    | lse hget2 htid2 hb2 hlo2 hhi2 =>
      obtain ⟨-, -, h1, h2⟩ := hb
      obtain ⟨-, -, h3, h4⟩ := hb2
      rcases hp.outApartLse with h | h <;> omega
    | @store i' x' y' z' addr' c' s' hs' hw2' hc4' ho' hx' hy' hz' hl2 hb' =>
      have hadr := congrArg Loc.addr (hl1.symm.trans hl2)
      simp only at hadr
      have o1 := slot_off_le hc4
      have o2 := slot_off_le hc4'
      have hcol : 128 * MbarRow.warp L i.1 + [0, 64, 256, 320].getD c 0 + x =
          128 * MbarRow.warp L i'.1 + [0, 64, 256, 320].getD c' 0 + x' ∧
          (ctaOf L i.1 * 64 + y) = (ctaOf L i'.1 * 64 + y') ∧ z = z' := by omega
      obtain ⟨hcol, hR, hzz⟩ := hcol
      obtain ⟨hw, hcc, hxx⟩ := slot_col_inj hw2 hw2' hc4 hc4' hx hx' hcol
      have hcta : i.1 / L.block = i'.1 / L.block := by
        simp only [ctaOf] at hR
        omega
      have hyy : y = y' := by omega
      subst hcc hxx hyy hzz
      obtain ⟨h1, h2⟩ := store_unique hp hX hFw hnu hs hs' hcta hw (by rw [ho, ho', hw])
      obtain rfl : i = i' := Prod.ext h1 h2
      rfl

/-- **The final byte of an output slot** (complete execution): the memory after the execution
holds, at the global byte `lw` that the slot `(x, y, z)` of the tensor store at `(g, k)` writes,
the byte `b` that one staging store of warpgroup 0 wrote at the byte `lsrc` the slot reads. -/
theorem out_slot_final (hp : Pre P L mem0) {X : Execution} {mf : FinalMem}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
    (hBar : BarRows P L X) (hO : OutRows P L X) (hC : Complete L X) (hF : IsFinal L mem0 X mf)
    {g k pcT addr x y z : Nat} {s : TensorStore.Spec} {lsrc lw : Loc}
    (hT : X.get (g, k) = some ⟨pcT, .tensorStore addr s⟩) (hat : Wg0At L g pcT)
    (hrl : TensorStore.readLoc s x y z = some lsrc)
    (hwl : TensorStore.writeLoc s x y z = some lw) (hlw : lw.space = .global) :
    ∃ b gS kS pcS ac bs, mf lw = some (some b) ∧ X.get (gS, kS) = some ⟨pcS, .wr ac bs⟩ ∧
      Wg0At L gS pcS ∧ MemRow.Wg0Stage L gS pcS ac ∧ ac.Covers lsrc ∧
      some b = wbyte ac bs lsrc := by
  obtain ⟨b, gS, kS, pcS, ac, bs, hmw, hget, hatS, hst, hcov, hb⟩ :=
    out_slot_byte hp hX hFw hR hI hB hN hnu hBar hO hC hT hat hrl hwl
  have hcw : (⟨lw, 1, false, false, .cta, 0, false⟩ : Acc).Covers lw := by
    have := Acc.covers_at (a := (⟨lw, 1, false, false, .cta, 0, false⟩ : Acc)) (k := 0)
      Nat.one_pos
    simpa [Loc.at] using this
  have hf := hF.unique hmw hcw fun w' a' bs' hw' hc' =>
    slot_write_unique hp hX hFw hnu hmw.intent hcw hw' hc' hlw
  refine ⟨b, gS, kS, pcS, ac, bs, ?_, hget, hatS, hst, hcov, hb⟩
  simpa [wbyte] using hf

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- A row-major index with column `x < s` determines the column and the row. -/
private theorem rowcol_eq {s x q y e : Nat} (hx : x < s) (hq : q < s)
    (h : y * s + x = e * s + q) : x = q ∧ y = e := by
  have h1 : (y * s + x) % s = x := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  have h2 : (e * s + q) % s = q := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
  have hs : 0 < s := by omega
  have h3 : (y * s + x) / s = y := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt hx, Nat.zero_add]
  have h4 : (e * s + q) / s = e := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt hq, Nat.zero_add]
  rw [h] at h1 h3
  exact ⟨h1.symm.trans h2, h3.symm.trans h4⟩

/-- **The coordinates of a lane of CTA `e s_q + q`** are `(q, e)`. -/
theorem lane_coords (hp : Pre P L mem0) {g e q : Nat} (hg : g < L.threads)
    (hc : g / L.block = e * P.s_q + q) (hq : q < P.s_q) :
    w0Query L g = q ∧ w0Batch L g = e := by
  have hrow := ctaOf_row hp hg
  have hlt := ctaid_lt hp g
  have hc' : ctaOf L g = e * P.s_q + q := hc
  rw [hc'] at hrow
  exact rowcol_eq hlt.1 hq hrow.symm

/-- **The final byte of an output element** (valid rows, complete): byte `z` of the global
element `(e, q, h, d)` of O is byte `z` of the number `attn`. -/
theorem out_byte (hp : Pre P L mem0) {X : Execution} {mf : FinalMem}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    (hC : Complete L X) (hF : IsFinal L mem0 X mf) (hV : W0Rows P L X)
    (hS : ScoreRead P L X hV) (hM : MaskRead P L X hV) (hOR : OutRead P L X hV)
    {e q h d z : Nat} (he : e < P.b) (hq : q < P.s_q) (hh : h < 64) (hd : d < 512) (hz : z < 2) :
    mf ((oLoc P e q h d).at z) = some (some (.float .bf16 (attn P e q h d), z)) := by
  have hIn := Inputs.of_pre hp
  have hBar := hIn.bar hp X hX hFw
  obtain ⟨w, c, i, hw, hc, hi, hdd⟩ := col_decomp hd
  have hcta : (e * P.s_q + q) * L.block < L.threads := by
    have hb : L.block = 384 := hp.block
    have hth : L.threads = L.grid * 384 := by simp only [Launch.threads, hb]
    have h1 := Nat.mul_le_mul_right P.s_q (Nat.succ_le_of_lt he)
    rw [Nat.succ_mul] at h1
    rw [hb, hth, hp.grid, Nat.mul_comm P.s_q P.b]
    omega
  obtain ⟨gT, kT, a, s, hgT, hwT, hget⟩ := wg0_outStore hp hX hFw hnu hC hcta hw hc
  have hgTl := Frame.lt_of_get hX hget
  have hiss : X.TensorStoreIssue (gT, kT) a s := ⟨_, hget⟩
  obtain ⟨hw2, hrows, c', hc', hget', hor⟩ :=
    tensor_store_origin hp hX hFw (noUbInner hX) hiss
  rw [hget] at hget'
  have hcc : c' = c := by
    have h1 := congrArg Event.pc (Option.some.inj hget')
    simp only at h1
    interval_cases c <;> interval_cases c' <;> simp_all
  subst hcc
  obtain ⟨hcx, hcy⟩ := lane_coords hp hgTl hgT hq
  have hor' : BoxOrigin s.origin [128 * w + [0, 64, 256, 320].getD c' 0, 0, q, e] := by
    rw [← hwT]
    exact hcx ▸ hcy ▸ hor
  have hoff : [0, 64, 256, 320].getD c' 0 ≤ 320 := slot_off_le hc
  have hdesc := tensor_store_map hp hX hFw hiss
  obtain ⟨lw, hwl⟩ := out_writeLoc_some hdesc hor' hrows (by omega) hq he (x := i) hi hh hz
  obtain ⟨-, -, -, -, -, -, hloc⟩ := out_dest hdesc hor' hrows hwl
  have hat : Wg0At L gT ([1358, 1516, 1673, 1831].getD c' 0) := by
    refine ⟨by omega, ?_⟩
    interval_cases c' <;> simp
  obtain ⟨c'', hc'', hpc'', hread⟩ := wg0_store_readEq hp hX hFw hget hat rfl
  have hc3 : c'' = c' := by
    simp only at hpc''
    interval_cases c' <;> interval_cases c'' <;> simp_all
  have hc3' : c' = c'' := hc3.symm
  subst hc3'
  have hrl := hread i h z hi hh hz
  obtain ⟨b, gS, kS, pcS, ac, bs, hmf, hgS, hatS, hst, hcov, hb⟩ := out_slot_final hp hX hFw hnu
    (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw) (hIn.bar0 hp X hX hFw)
    (hIn.dequant hp X hX hFw) hBar (Prog.outRows hp hX hFw hnu) hC hF hget hat hrl hwl
    (by rw [hloc])
  obtain ⟨c2, hc2, k2, hk2, el2, hel2, hpcS, -⟩ := hst
  have hgSl := Frame.lt_of_get hX hgS
  have hwS : warp L gS < 4 := hatS.1
  have hpcS' : (⟨pcS, .wr ac bs⟩ : Event).pc = Wg0.ost2Base ⟨c2, hc2⟩ + (⟨k2, hk2⟩ : Fin 8).val :=
    hpcS
  obtain ⟨q', hq', hsz, hlocS, hbs⟩ := w0_out_word hp hX hFw hnu hBar hC hV hS hM hOR hwS hgSl hgS
    hpcS' ac bs rfl
  obtain ⟨hsp, hct, hlo, hhi⟩ := hcov
  rw [hlocS] at hlo hhi hct
  rw [hsz] at hhi
  simp only [wsLoc] at hct hlo hhi
  have ht128 : tidOf L gS < 128 := MemRow.wg0_tid hwS
  obtain ⟨s', hs'⟩ := Nat.exists_eq_add_of_le hlo
  have hs4 : s' < 4 := by omega
  have hkey : 16384 * w + MemRow.wg0OutOff c' + (128 * h +
      16 * ((i / 8) ^^^ (h % 8)) + 2 * (i % 8) + z) = 16384 * (tidOf L gS / 64) +
      128 * (tidOf L gS % 64) + 16 * (k2 ^^^ tidOf L gS % 8) + MemRow.wg0OutOff c2 + 4 * q' +
      s' := by omega
  obtain ⟨ht64, hth, hcc2, hk, hel, hsv⟩ := out_geom hw hc hc2 hi hh hz ht128 hk2 hq' hs4 hkey
  obtain ⟨hqS, hbS⟩ := lane_coords hp hgSl (hct.symm.trans hgT) hq
  have hHalf : w0Half L gS = w := ht64
  have hHead : w0Head L gS = h := by
    show tidOf L gS % 64 = h
    exact hth
  have hlwe : lw = (oLoc P e q h d).at z := by
    rw [hloc]
    simp only [oLoc, Loc.at, Loc.mk.injEq, true_and]
    rw [hdd]
  have hb2 : some b = bs[s']? := by
    rw [hb]
    unfold wbyte
    congr 2
    rw [hlocS]
    simp only [wsLoc]
    omega
  rw [hbs, pair_byte _ _ (by omega)] at hb2
  rw [← hlwe, hmf, Option.some.injEq]
  simp only [hqS, hbS, hHead, hHalf] at hb2
  rcases col_word (i := i) hz with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have hs2 : s' < 2 := by omega
    simp only [hs2, ↓reduceIte, Option.some.injEq] at hb2
    rw [hb2]
    have : 128 * w + [0, 64, 256, 320].getD c2 0 + 2 * (4 * k2 + q') = d := by
      rw [hcc2]; omega
    rw [this, show s' = z by omega]
  · have hs2 : ¬ s' < 2 := by omega
    simp only [hs2, ↓reduceIte, Option.some.injEq] at hb2
    rw [hb2]
    have : 128 * w + [0, 64, 256, 320].getD c2 0 + (2 * (4 * k2 + q') + 1) = d := by
      rw [hcc2]; omega
    rw [this, show s' - 2 = z by omega]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **An output load's word is the end of the last block's PV chain** (valid rows). -/
theorem old_ld_word (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hR : Safe.W0TraceValid P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    {h k pc a j jw p0 : Nat} {vals : List Value} {sh : TcShape}
    (he : X.get (h, k) = some ⟨pc, .tc (.ld a vals sh)⟩) (ha : a ≤ 192) (hj : j < vals.length)
    (hjw : jw < k)
    (hpoll : X.get (h, jw) = some ⟨1184, .wait (mbarLoc L (h / L.block)
      (.svDone (slot2 (blocksOf P L (h / L.block) - 1)))) p0 true true .cta⟩) :
    ∃ (i : Nat) (x : ℝ), vals[j]? = some (.float .f32 x) ∧
      mmaIssues ((X.tr (mmaLane L X (h / L.block))).take i) =
        24 * (blocksOf P L (h / L.block) - 1) + 16 + (6 + (a + j) / 128) ∧
      X.async.mmaDone (mmaLane L X (h / L.block), i) = true ∧
      TmRace.PvChain L X (mmaLane L X (h / L.block)) i (6 + (a + j) / 128)
        (tcDataCell L h .s32x32b a j) (.float .f32 x) := by
  have E := pvEnv hp hIn hR hX hFw hnu
  have hld : X.TLd (h, k) a vals sh := ⟨pc, he⟩
  obtain ⟨hat, hsh, ha', -⟩ := TmRace.ld_class hp hX hFw he
  subst hsh
  have hlc : TcMma.LoadCell L X (h, k) j (tcDataCell L h .s32x32b a j) :=
    ⟨a, vals, .s32x32b, hld, hj, rfl⟩
  obtain ⟨src, hs⟩ := TmRace.ld_source hp hX hFw E.hMb E.hI E.hB E.hN E.hBr E.hPS E.hG E.ht
    hlc (TmRace.ld_write hp hX hFw E.hMb E.hI E.hB E.hN hld hj rfl)
  obtain ⟨i, sx, mask, hsrc, hget, hiss, hdone, hmc⟩ :=
    TmRace.ld_pin_epi hp hX hFw E.hMb E.hI E.hB E.hN E.hG he ha hj rfl hjw hpoll hs
  subst hsrc
  obtain ⟨hcta, hlane, hcol⟩ := dataCell hp hat.1 ha' (j := j)
  rw [hcol] at hget
  have hiss' := hiss
  rw [hcol] at hiss'
  have hlen := ldLen hp hX he rfl
  have hk6 : (6 + (a + j) / 128) % 2 = (a + j) / 128 := by omega
  obtain ⟨x, hx, hch⟩ :=
    ld_word_pv hp hX hFw E (kk := 6 + (a + j) / 128) hld hlc hs rfl (by omega)
    (by rw [hk6]; exact hget) hdone hmc
  exact ⟨i, x, hx, hiss', hdone, hch⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **The words the lanes of warpgroup 0 staged** (complete, followed execution). -/
theorem out_read (hp : Pre P L mem0) (hRn : Safe.W0TraceValid P L mem0)
    {X : Execution} (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    (hnu : ¬ HasUb X) (hC : Complete L X) : ∃ hV : W0Rows P L X, OutRead P L X hV := by
  obtain ⟨hV, hM⟩ := Res.Lse.mask hp hRn.w0Trace hX hFw hnu
  have hIn := Inputs.of_pre hp
  have hS : ScoreRead P L X hV := score_read hp hIn hRn hX hFw hnu hV
  have hBar := hIn.bar hp X hX hFw
  refine ⟨hV, fun g k e c j hg he hpc => ?_⟩
  have hpr : ∀ c' : Fin 4, 1331 ≤ Wg0.ost2Base c' ∧ Wg0.ost2Base c' + 7 ≤ 1813 := by decide
  have hj8 := j.isLt
  have hpr' := hpr c
  have hw : warp L g < 4 := wg0_warp_of_pc hp hX hFw hnu he ⟨by omega, by omega⟩
  have hv0 : W0Trace P X g := w0Trace_of_rows hV hX hw
  obtain ⟨-, hwh, -, -⟩ := w0Partner_facts hp hw hg
  have hvh : W0Trace P X (w0Partner L g) := w0Trace_of_rows hV hX hwh
  obtain ⟨kp, f, a', bs', rP, kq, e', hf, hf1157, hfk, hkp, hfirst, hq, hq1157, hqlen, -, -,
    -, hlen⟩ := rmax_peer_sum hp hX hFw hnu hBar hw hv0 hvh hC he (by omega) (by omega)
  have hKl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hEp : PairEpi P L X g := by
    intro y hy
    rcases hy with h | h <;> subst h
    · exact ⟨kp, f, hf, hf1157, by
        rw [← w0_fin_epi hp hX hFw hw hv0 hf hf1157 hfk hkp hKl hfirst]; exact hlen⟩
    · exact ⟨kq, e', hq, hq1157, hqlen⟩
  obtain ⟨kl, jw, p, a, vals, hkl, hget, ha, hjw, hpoll, hvals⟩ :=
    w0_epiO_old hp hX hFw hnu hw hv0 he hpc
  have hc4 := c.isLt
  have hvlen : vals.length = 64 := by
    refine outLdLen hp hX hget rfl ?_
    have : ∀ c' : Fin 4, [1201, 1361, 1519, 1676].getD c'.val 0 ∈ [1201, 1361, 1519, 1676] := by
      decide
    exact this c
  refine ⟨by rw [hvals]; exact hvlen, wg0_sink_rd hp hX hFw hnu hw hv0 he (by omega),
    fun i hi => ?_⟩
  obtain ⟨i', x, hvx, hiss, hdone, hch⟩ := old_ld_word hp hIn hRn hX hFw hnu hget
    (a := a) (by omega) (j := i) (by omega) hjw hpoll
  subst ha
  have hT := blocksOf_pos hp (g / L.block)
  have hpt := pv_total hp hIn hRn hX hFw hnu hC hV hS hM hw hg hEp hc4 hi
    (p := (64 * c.val + i) / 128) rfl (blocksOf P L (g / L.block) - 1) (by omega) i' x hch
    hiss hdone
  have hT1 : blocksOf P L (g / L.block) - 1 + 1 = blocksOf P L (g / L.block) := by omega
  rw [hT1] at hpt
  have hfeat : ∀ c' : Nat, c' < 4 → 128 * (g % 384 / 64) + 128 * ((64 * c' + i) / 128) +
      (64 * c' + i) = 128 * (g % 384 / 64) + [0, 64, 256, 320].getD c' 0 + i := by
    intro c' hc'
    interval_cases c' <;> simp <;> omega
  have hhalf : w0Half L g = g % 384 / 64 := by simp only [w0Half, tidOf_x_eq hp]
  have hfin := fin_take_eq hp hX hFw hnu (k := k) hw
  rw [hlen] at hfin
  refine ⟨x, ?_, ?_⟩
  · rw [hvals, List.getD_eq_getElem?_getD, hvx]
    exact ⟨PTX.Flow.clean_float x, PTX.Flow.readEReal_float x, Or.inl ⟨x, rfl⟩⟩
  · rw [hlen, hhalf, ← hfeat c.val hc4, hfin, ← hpt]
    rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **The frame**: a global byte outside the output tensor and the LSE output keeps its launch
content. -/
theorem frame_of (hp : Pre P L mem0) {X : Execution} {mf : FinalMem}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    (hF : IsFinal L mem0 X mf) (l : Loc) (hl : l.space = .global)
    (hO : ¬ (P.outBase ≤ l.addr ∧ l.addr < P.outBase + tensorBytes P))
    (hS : ¬ (P.lseBase ≤ l.addr ∧ l.addr < P.lseBase + lseBytes P)) : mf l = mem0 l := by
  refine hF.unwritten fun w a bs hw hc => ?_
  have hns : l.space ≠ .shared := by rw [hl]; exact nofun
  cases global_at hp hX hFw hnu hw.intent hc hns with
  | lse _ _ hb _ _ =>
    obtain ⟨-, -, h1, h2⟩ := hb
    exact hS ⟨h1, h2⟩
  | store _ _ _ _ _ _ _ _ hb =>
    obtain ⟨-, -, h1, h2⟩ := hb
    exact hO ⟨h1, h2⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The first conjunct of `Post`: element `(e, q, h, d)` of O is `attn`. -/
def Res.OutValues (P : Params) (mf : FinalMem) : Prop :=
  ∀ e < P.b, ∀ q < P.s_q, ∀ h < 64, ∀ d < 512,
    memFloat .bf16 mf (oLoc P e q h d) = .ok (attn P e q h d)

/-- The fourth conjunct of `Post`: every global byte outside O and LSE is preserved. -/
def Res.OutFrame (P : Params) (mem0 : Mem0) (mf : FinalMem) : Prop :=
  ∀ l, l.space = .global →
    ¬ (P.outBase ≤ l.addr ∧ l.addr < P.outBase + tensorBytes P) →
    ¬ (P.lseBase ≤ l.addr ∧ l.addr < P.lseBase + lseBytes P) → mf l = mem0 l

/-- **The output elements** of a complete, followed execution, from the staged words, scores and
masks. -/
theorem out_values (hp : Pre P L mem0)
    (hRn : Safe.W0TraceValid P L mem0) {X : Execution} {mf : FinalMem}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    (hC : Complete L X) (hF : IsFinal L mem0 X mf) : Res.OutValues P mf := by
  obtain ⟨hV, hOR⟩ := out_read hp hRn hX hFw hnu hC
  obtain ⟨hV2, hM'⟩ := Res.Lse.mask hp hRn.w0Trace hX hFw hnu
  have hM : MaskRead P L X hV := hM'
  have hS' : ScoreRead P L X hV := score_read hp (Inputs.of_pre hp) hRn hX hFw hnu hV
  intro e he q hq h hh d hd
  refine memFloat_float fun kk hkk => ?_
  exact out_byte hp hX hFw hnu hC hF hV hS' hM hOR he hq hh hd
    (by simpa [FloatFmt.bytes] using hkk)

/-- **The output values and the frame of a complete, followed execution.** -/
theorem Res.output (hp : Pre P L mem0)
    (hRn : Safe.W0TraceValid P L mem0) {X : Execution}
    {mf : FinalMem} (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    (hnu : ¬ HasUb X) (hC : Complete L X) (hF : IsFinal L mem0 X mf) :
    Res.OutValues P mf ∧ Res.OutFrame P mem0 mf :=
  ⟨out_values hp hRn hX hFw hnu hC hF, fun l hl hO hS => frame_of hp hX hFw hnu hF l hl hO hS⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
