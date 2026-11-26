-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.PvWordAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MmaSlot
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Reads
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RsPin
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.EpiPin
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.RldRst
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdExists

@[expose] public section

/-! # The words of the accumulator loads, per event

A register `j` of a rescale load (`rs_ld_word_at`) or an output load (`old_ld_word_at`) of
warpgroup 0 holds a single-precision number (the end of a PV chain), from the words of the events
before the load in the tcgen05 order and the operand elements below it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **A rescale load's word is the end of the previous block's PV chain**, per event. -/
theorem rs_ld_word_at (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {h k a j r : Nat} {c : Fin 4} {vals : List Value} {sh : TcShape}
    (hbelow : ∀ w e', X.get w = some e' → Relation.TransGen (TcMma.TcStep L X) w (h, k) →
      TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w)
    (hEb : ∀ w, (w = (h, k) ∨ Relation.TransGen (TcMma.TcStep L X) w (h, k)) →
      MmaElemAt X w)
    (he : X.get (h, k) = some ⟨[716, 817, 918, 1019].getD c.val 0, .tc (.ld a vals sh)⟩)
    (hj : j < vals.length) (h1r : 1 ≤ r)
    (hr : ∀ b : Fin 2, okPolls (mbarLoc L (h / L.block) (.qkDone b)) ((X.tr h).take k) =
        ringUses 2 b.val (r + 1) ∧ arrivals (mbarLoc L (h / L.block) (.soReady b))
        ((X.tr h).take k) = ringUses 2 b.val r) :
    ∃ (i : Nat) (x : ℝ), vals[j]? = some (.float .f32 x) ∧
      mmaIssues ((X.tr (mmaLane L X (h / L.block))).take i) =
        24 * (r - 1) + 16 + (6 + (a + j) / 128) ∧
      X.async.mmaDone (mmaLane L X (h / L.block), i) = true ∧
      TmRace.PvChain L X (mmaLane L X (h / L.block)) i (6 + (a + j) / 128)
        (tcDataCell L h .s32x32b a j) (.float .f32 x) := by
  have hT : TmemRows P L X := tmem_rows hp hX hFw
  have hMb := hIn.mbar hp X hX hFw
  have hI := hIn.initRows hp X hX hFw
  have hB := hIn.bar0 hp X hX hFw
  have hN := hIn.dequant hp X hX hFw
  have hBr := hIn.bar hp X hX hFw
  have hPS := Safe.pvStore hp hIn hX hFw
  have hG := Safe.guarded hp hIn hX hFw
  have ht := Safe.tmemOne hp hIn hX hFw
  have hld : X.TLd (h, k) a vals sh := ⟨_, he⟩
  obtain ⟨hat, hsh, ha', -⟩ := TmRace.ld_class hp hX hFw he
  subst hsh
  obtain ⟨hca, -⟩ := wg0_rld_addr hp hX hFw hat.1 he
  have hlen := ldLen hp hX he rfl
  have hc4 := c.isLt
  have hlc : TcMma.LoadCell L X (h, k) j (tcDataCell L h .s32x32b a j) :=
    ⟨a, vals, .s32x32b, hld, hj, rfl⟩
  obtain ⟨src, hs⟩ := TmRace.ld_source hp hX hFw hMb hI hB hN hBr hPS hG ht
    hlc (TmRace.ld_write hp hX hFw hMb hI hB hN hld hj rfl)
  obtain ⟨i, sx, mask, hsrc, hget, hiss, hdone, hmc⟩ :=
    TmRace.ld_pin_rs hp hX hFw hMb hI hB hG he hj rfl h1r hr hs
  obtain ⟨hcta, hlane, hcol⟩ := dataCell hp hat.1 ha' (j := j)
  rw [hcol] at hget hiss
  have hk6 : (6 + (a + j) / 128) % 2 = (a + j) / 128 := by omega
  obtain ⟨x, hx, hch⟩ := ld_word_pv_at hp hIn hX hFw hbelow hEb (kk := 6 + (a + j) / 128)
    hld hlc hs hsrc (by omega) (by rw [hk6]; exact hget) hdone hmc
  exact ⟨i, x, hx, hiss, hsrc ▸ hdone, hch⟩

/-- **An output load's word is the end of the last block's PV chain**, per event. -/
theorem old_ld_word_at (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {h k pc a j jw p0 : Nat} {vals : List Value} {sh : TcShape}
    (hbelow : ∀ w e', X.get w = some e' → Relation.TransGen (TcMma.TcStep L X) w (h, k) →
      TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w)
    (hEb : ∀ w, (w = (h, k) ∨ Relation.TransGen (TcMma.TcStep L X) w (h, k)) →
      MmaElemAt X w)
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
  have hT : TmemRows P L X := tmem_rows hp hX hFw
  have hMb := hIn.mbar hp X hX hFw
  have hI := hIn.initRows hp X hX hFw
  have hB := hIn.bar0 hp X hX hFw
  have hN := hIn.dequant hp X hX hFw
  have hBr := hIn.bar hp X hX hFw
  have hPS := Safe.pvStore hp hIn hX hFw
  have hG := Safe.guarded hp hIn hX hFw
  have ht := Safe.tmemOne hp hIn hX hFw
  have hld : X.TLd (h, k) a vals sh := ⟨pc, he⟩
  obtain ⟨hat, hsh, ha', -⟩ := TmRace.ld_class hp hX hFw he
  subst hsh
  have hlc : TcMma.LoadCell L X (h, k) j (tcDataCell L h .s32x32b a j) :=
    ⟨a, vals, .s32x32b, hld, hj, rfl⟩
  obtain ⟨src, hs⟩ := TmRace.ld_source hp hX hFw hMb hI hB hN hBr hPS hG ht
    hlc (TmRace.ld_write hp hX hFw hMb hI hB hN hld hj rfl)
  obtain ⟨i, sx, mask, hsrc, hget, hiss, hdone, hmc⟩ :=
    TmRace.ld_pin_epi hp hX hFw hMb hI hB hN hG he ha hj rfl hjw hpoll hs
  subst hsrc
  obtain ⟨hcta, hlane, hcol⟩ := dataCell hp hat.1 ha' (j := j)
  rw [hcol] at hget
  have hiss' := hiss
  rw [hcol] at hiss'
  have hlen := ldLen hp hX he rfl
  have hk6 : (6 + (a + j) / 128) % 2 = (a + j) / 128 := by omega
  obtain ⟨x, hx, hch⟩ :=
    ld_word_pv_at hp hIn hX hFw hbelow hEb (kk := 6 + (a + j) / 128) hld hlc hs rfl
    (by omega) (by rw [hk6]; exact hget) hdone hmc
  exact ⟨i, x, hx, hiss', hdone, hch⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
