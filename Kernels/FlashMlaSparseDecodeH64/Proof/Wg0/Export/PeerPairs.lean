-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Closed
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceBase
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PldEl
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PfNth

@[expose] public section

/-! # The two peer reads of a block

The reads at the peer pc `477 + 5 k0` of a block of a lane of warpgroup 0 are the entries of the
block's `w0Pf`; the last two of the even-truncated list (`w0Peer`) are the trace's events with an
even and an odd number of such reads before them, that is the elements 0 and 1 of the lane's slot
(`w0_pld_el`), and they carry the ring counts and the pair-barrier counts of the block
(`pex_cnt`). A block whose pair is valid has at least two reads. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {l : List Event}

/-- A read that reads as a pair has that pair as its first element. -/
theorem w0A0_of_rdVal {e : Event} {x y : Value} (h : w0RdVal e = some (.pair x y)) :
    w0A0 e = .pair x y := by
  obtain ⟨pc, kd⟩ := e
  cases kd <;> simp [w0RdVal, w0A0] at h ⊢
  rename_i a bs
  cases hr : rebuild 3 bs with
  | error f => simp [hr, Except.toOption] at h
  | ok v => simp [hr] at h ⊢; exact h

/-- The default pair is not a valid peer pair. -/
theorem not_peerOk_default : ¬ W0PeerOk (.pred false, .pred false) := by
  intro h
  obtain ⟨h1, -⟩ := h
  obtain ⟨x, hx⟩ := h1
  simp only [splitValue, valFloat] at hx
  rw [bitsAsFloat_eq (by intro f h; cases h)] at hx
  simp [Value.bitPattern] at hx

/-- **The last two entries of an even-truncated list** of at least two entries. -/
private theorem w0PeerOf_entries {F : List Event} (h : 2 ≤ F.length) :
    ∃ x y, F[2 * (F.length / 2) - 2]? = some x ∧ F[2 * (F.length / 2) - 1]? = some y ∧
      Wg0.Data.w0PeerOf F = (w0A0 x, (w0RdVal y).getD (.pred false)) := by
  have hm : 2 ≤ 2 * (F.length / 2) := by omega
  have hl : (F.take (2 * (F.length / 2))).length = 2 * (F.length / 2) := by
    simp only [List.length_take]; omega
  have hd : ((F.take (2 * (F.length / 2))).drop (2 * (F.length / 2) - 2)).length = 2 := by
    simp only [List.length_drop, hl]; omega
  obtain ⟨x, y, hxy⟩ := List.length_eq_two.mp hd
  have h0 : F[2 * (F.length / 2) - 2]? = some x := by
    have := congrArg (fun l => l[0]?) hxy
    simp only [List.getElem?_drop, List.getElem?_cons_zero] at this
    rw [List.getElem?_take_of_lt (by omega)] at this
    rw [show 2 * (F.length / 2) - 2 + 0 = 2 * (F.length / 2) - 2 by omega] at this
    exact this
  have h1 : F[2 * (F.length / 2) - 1]? = some y := by
    have := congrArg (fun l => l[1]?) hxy
    simp only [List.getElem?_drop, List.getElem?_cons_succ, List.getElem?_cons_zero] at this
    rw [List.getElem?_take_of_lt (by omega)] at this
    rw [show 2 * (F.length / 2) - 2 + 1 = 2 * (F.length / 2) - 1 by omega] at this
    exact this
  refine ⟨x, y, h0, h1, ?_⟩
  unfold Wg0.Data.w0PeerOf
  have : lastN 2 (F.take (2 * (F.length / 2))) = [x, y] := by
    unfold lastN
    rw [hl]
    exact hxy
  rw [this]


/-- A block whose peer pair `k0` is valid has at least two peer reads. -/
theorem w0_peer_len {K0 k0 : Nat} (hk0 : k0 < 8)
    (hOk : W0PeerOk ((w0Words (w0Fin (l.take K0)).2).pw k0)) :
    2 ≤ ((w0Scan (l.take K0)).2.filter fun e =>
      e.pc = 477 + 5 * k0 && (w0RdVal e).isSome).length := by
  by_contra hlt
  have hlt : ¬ 2 ≤ (Wg0.Data.w0Pf (w0Scan (l.take K0)).2 k0).length := hlt
  set F := Wg0.Data.w0Pf (w0Scan (l.take K0)).2 k0 with hF
  have hd : Wg0.Data.w0PeerOf F = (.pred false, .pred false) := by
    unfold Wg0.Data.w0PeerOf
    have : 2 * (F.length / 2) = 0 := by omega
    rw [this]
    simp [lastN]
  apply not_peerOk_default
  have : (w0Words (w0Fin (l.take K0)).2).pw k0 = w0Peer (w0Fin (l.take K0)).2 k0 := by
    simp [w0Words, hk0]
  have hpe : w0Peer (w0Fin (l.take K0)).2 k0 =
      Wg0.Data.w0PeerOf (Wg0.Data.w0Pf (w0Scan (l.take K0)).2 k0) := by
    rw [w0Fin_snd]; rfl
  rw [this, hpe, ← hF, hd] at hOk
  exact hOk

/-- **The two peer reads of a block** (valid rows): a block of the prefix `K0` whose peer pair
`k0` is valid has two reads at the pc `477 + 5 k0`, of its block, the elements 0 and 1 of the
lane's slot, and its peer pair is the first's value and the second's. -/
theorem w0_peer_events (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : MbarRow.warp L g < 4) {N : Nat}
    (hv : W0Valid P.scale ((X.tr g).take N)) {K0 k0 : Nat} (hk0 : k0 < 8) (hN : K0 ≤ N + 1)
    (hn2 : 2 ≤ ((w0Scan ((X.tr g).take K0)).2.filter fun e =>
      e.pc = 477 + 5 * k0 && (w0RdVal e).isSome).length)
    (hal : LaneUbFree X g K0) :
    ∃ j0 j1 x y a0 b0 a1 b1, j0 < K0 ∧ j1 < K0 ∧ X.get (g, j0) = some x ∧
      X.get (g, j1) = some y ∧ w0Closed ((X.tr g).take j0) = w0Closed ((X.tr g).take K0) ∧
      w0Closed ((X.tr g).take j1) = w0Closed ((X.tr g).take K0) ∧
      x.kind = .rd a0 b0 ∧ y.kind = .rd a1 b1 ∧ x.pc = 477 + 5 * k0 ∧ y.pc = 477 + 5 * k0 ∧
      MemRow.WsAcc L (g / L.block) (204800 + 4096 * (tidOf L g / 32) + 16 * (tidOf L g % 32) +
        512 * k0 + 8 * 0) 8 a0 ∧
      MemRow.WsAcc L (g / L.block) (204800 + 4096 * (tidOf L g / 32) + 16 * (tidOf L g % 32) +
        512 * k0 + 8 * 1) 8 a1 ∧
      w0Peer (w0Fin ((X.tr g).take K0)).2 k0 = (w0A0 x, (w0RdVal y).getD (.pred false)) := by
  have hpe : w0Peer (w0Fin ((X.tr g).take K0)).2 k0 =
      Wg0.Data.w0PeerOf (Wg0.Data.w0Pf (w0Scan ((X.tr g).take K0)).2 k0) := by
    rw [w0Fin_snd]; rfl
  set F := Wg0.Data.w0Pf (w0Scan ((X.tr g).take K0)).2 k0 with hF
  have hn2' : 2 ≤ F.length := hn2
  obtain ⟨x, y, hx, hy, hpo⟩ := w0PeerOf_entries hn2'
  have hi1 : 2 * (F.length / 2) - 1 = (2 * (F.length / 2) - 2) + 1 := by omega
  rw [hi1] at hy
  have hev : ∀ i z, F[i]? = some z → i % 2 = 0 ∨ i % 2 = 1 → ∃ j a bs, j < K0 ∧
      X.get (g, j) = some z ∧ w0Closed ((X.tr g).take j) = w0Closed ((X.tr g).take K0) ∧
      z.kind = .rd a bs ∧ z.pc = 477 + 5 * k0 ∧
      MemRow.WsAcc L (g / L.block) (204800 + 4096 * (tidOf L g / 32) + 16 * (tidOf L g % 32) +
        512 * k0 + 8 * (i % 2)) 8 a := by
    intro i z hz _
    obtain ⟨j, hj, hget, hcl, hlen⟩ := w0Pf_nth X g k0 K0 i z hz
    have hmz : z ∈ F := List.mem_of_getElem? hz
    simp only [hF, Wg0.Data.w0Pf, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hmz
    obtain ⟨-, hpcz, hsome⟩ := hmz
    obtain ⟨a, bs, el, hk, hel, hws, hpar⟩ := w0_pld_el hp hX hFw hw
      (Wg0.W0Valid.take_le hv (by omega)) hk0 hget (hal.ne hj hget) hpcz
    rw [w0Fin_snd, hlen] at hpar
    rw [← hpar] at hws
    exact ⟨j, a, bs, hj, hget, hcl, hk, hpcz, hws⟩
  obtain ⟨j0, a0, b0, hj0, hg0, hc0, hk0', hp0, hw0⟩ := hev _ x hx (by omega)
  obtain ⟨j1, a1, b1, hj1, hg1, hc1, hk1', hp1, hw1⟩ := hev _ y hy (by omega)
  refine ⟨j0, j1, x, y, a0, b0, a1, b1, hj0, hj1, hg0, hg1, hc0, hc1, hk0', hk1', hp0, hp1,
    ?_, ?_, ?_⟩
  · have : (2 * (F.length / 2) - 2) % 2 = 0 := by omega
    rw [this] at hw0
    exact hw0
  · have : (2 * (F.length / 2) - 2 + 1) % 2 = 1 := by omega
    rw [this] at hw1
    exact hw1
  · rw [hpe, hpo]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
