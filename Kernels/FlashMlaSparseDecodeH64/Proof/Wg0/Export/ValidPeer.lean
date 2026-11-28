-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidSnoc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceBase
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PldEl
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime

@[expose] public section

/-! # A peer read keeps warpgroup 0's early words valid

A read at the peer pc `477 + 5 k0` changes only the block's peer pair `k0`
(`w0Words_snoc_peer`). The first element of the pair (an even number of such reads before it)
changes no word (`W0Early.snoc_peer_eq`); the second finishes the pair
(`W0Early.snoc_peer_new`), which has to be a valid pair. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

variable {l : List Event} {f : Event}

/-- **The element of a peer load** (`w0_pld_el`), the parity as a count of the block's
reads. -/
theorem w0_peer_el {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}
    (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
    (hw : MbarRow.warp L g < 4) {j k0 : Nat} {e : Event}
    (hv : W0Valid P.scale ((X.tr g).take j)) (hk0 : k0 < 8) (he : X.get (g, j) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) (hpc : e.pc = 477 + 5 * k0) :
    ∃ a bs el, e.kind = .rd a bs ∧ el < 2 ∧
      MemRow.WsAcc L (g / L.block) (204800 + 4096 * (tidOf L g / 32) + 16 * (tidOf L g % 32) +
        512 * k0 + 8 * el) 8 a ∧
      ((w0Scan ((X.tr g).take j)).2.filter fun e =>
        e.pc = 477 + 5 * k0 && (w0RdVal e).isSome).length % 2 = el := by
  obtain ⟨a, bs, el, hk, hel, hws, hpar⟩ := w0_pld_el hp hX hFw hw hv hk0 he hub hpc
  refine ⟨a, bs, el, hk, hel, hws, ?_⟩
  rw [w0Fin_snd] at hpar
  exact hpar

/-- **The words after a peer read**: only the pairs change, and only the pair `k0`. -/
theorem w0Words_snoc_peer {seg : List Event} {k0 : Nat} (hk0 : k0 < 8) (hpc : f.pc = 477 + 5 * k0) :
    w0Words (seg ++ [f]) = { w0Words seg with
      pw := fun k => if k < 8 then w0Peer (seg ++ [f]) k else (.pred false, .pred false) } := by
  have hlo : f.pc ∉ [280, 283] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, hpc]; omega
  have hhi : f.pc ∉ [278, 285] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, hpc]; omega
  have hmw : f.pc ∉ [289] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, hpc]; omega
  have hpm : f.pc ∉ [572] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, hpc]; omega
  have hvt : f.pc ∉ [578] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, hpc]; omega
  unfold w0Words
  simp only [w0Last_snoc_quiet _ hlo, w0Last_snoc_quiet _ hhi, w0Last_snoc_quiet _ hmw,
    w0Last_snoc_quiet _ hpm, w0Last_snoc_quiet _ hvt]

theorem w0Peer_snoc_ne {seg : List Event} {k k0 : Nat} (hpc : f.pc = 477 + 5 * k0)
    (hk : k ≠ k0) : w0Peer (seg ++ [f]) k = w0Peer seg k := by
  have : f.pc ≠ 477 + 5 * k := by omega
  simp [w0Peer, List.filter_append, this]

/-- The first element of a pair leaves the block's pair unchanged. -/
theorem w0Peer_snoc_first {seg : List Event} {k0 : Nat} (hpc : f.pc = 477 + 5 * k0)
    (hr : (w0RdVal f).isSome) (hev : (seg.filter fun e =>
      e.pc = 477 + 5 * k0 && (w0RdVal e).isSome).length % 2 = 0) :
    w0Peer (seg ++ [f]) k0 = w0Peer seg k0 := by
  have e1 : ∀ s : List Event, w0Peer s k0 = Wg0.Data.w0PeerOf (Wg0.Data.w0Pf s k0) :=
    fun _ => rfl
  have hev' : (Wg0.Data.w0Pf seg k0).length % 2 = 0 := hev
  rw [e1, e1]
  have : Wg0.Data.w0Pf (seg ++ [f]) k0 = Wg0.Data.w0Pf seg k0 ++ [f] := by
    simp [Wg0.Data.w0Pf, List.filter_append, hpc, hr]
  rw [this]
  exact Wg0.Data.w0PeerOf_even_snoc _ _ hev'

/-- **The second element of a pair finishes a valid pair** from the typing of the two elements'
words: the block's reads at the pc before the new one are odd in number, the last of them `x`. -/
theorem w0Peer_second_ok {seg : List Event} {k0 : Nat} {x : Event} {a0 a1 : Acc}
    {b0 b1 : List (Option Byte)} (hpc : f.pc = 477 + 5 * k0) (hfk : f.kind = .rd a1 b1)
    (hxk : x.kind = .rd a0 b0)
    (hodd : (seg.filter fun e => e.pc = 477 + 5 * k0 && (w0RdVal e).isSome).length % 2 = 1)
    (hx : (seg.filter fun e => e.pc = 477 + 5 * k0 && (w0RdVal e).isSome).getLast? = some x)
    (px : ∃ v, rebuild 3 b0 = .ok v ∧ W0Fin (splitValue 64 v).1 ∧ W0Fin (splitValue 64 v).2)
    (pf : ∃ v, rebuild 3 b1 = .ok v ∧ W0Fin (splitValue 64 v).1 ∧ W0Fin (splitValue 64 v).2) :
    W0PeerOk (w0Peer (seg ++ [f]) k0) := by
  obtain ⟨v0, hr0, h01, h02⟩ := px
  obtain ⟨v1, hr1, h11, h12⟩ := pf
  have hr : (w0RdVal f).isSome := by simp [w0RdVal, hfk]
  have e1 : w0Peer (seg ++ [f]) k0 = Wg0.Data.w0PeerOf (Wg0.Data.w0Pf (seg ++ [f]) k0) := rfl
  have hpf : Wg0.Data.w0Pf (seg ++ [f]) k0 = Wg0.Data.w0Pf seg k0 ++ [f] := by
    simp [Wg0.Data.w0Pf, List.filter_append, hpc, hr]
  have e2 := Wg0.Data.w0PeerOf_odd_snoc (Wg0.Data.w0Pf seg k0) f x hodd hx
  rw [e1, hpf, e2]
  have ha0 : w0A0 x = v0 := by
    obtain ⟨pc, kd⟩ := x
    simp only at hxk
    subst hxk
    simp [w0A0, hr0]; rfl
  have hv1 : (w0RdVal f).getD (.pred false) = v1 := by simp [w0RdVal, hfk, hr1]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [ha0, hv1] <;> assumption


/-- A block's words with the pair `k0` replaced. -/
def W0Words.setPw (w : W0Words) (k0 : Nat) (p : Value × Value) : W0Words :=
  { w with pw := fun k => if k = k0 then p else w.pw k }

theorem W0Ok.setPw {sc : ℝ} {w : W0Words} (h : W0Ok sc w) {k0 : Nat} {p : Value × Value}
    (hp : W0PeerOk p) : W0Ok sc (w.setPw k0 p) :=
  ⟨h.scale, h.hiLen, h.hi, h.loLen, h.lo, h.mask, fun k hk => by
    by_cases hkk : k = k0
    · simp [W0Words.setPw, hkk, hp]
    · simp [W0Words.setPw, hkk, h.peer k hk], h.pm⟩

/-- **The early words after a peer read**: the block's pair `k0` is unchanged (the first element)
or a valid pair (the second). -/
theorem W0Early.snoc_peer {sc : ℝ} (hsc : 0 < sc) (hc : f.pc ≠ w0ArrSPc ∧ f.pc ≠ w0ArrLPc)
    {k0 : Nat} (hk0 : k0 < 8) (hpc : f.pc = 477 + 5 * k0)
    (hnew : w0Peer ((w0Fin l).2 ++ [f]) k0 = w0Peer (w0Fin l).2 k0 ∨
      W0PeerOk (w0Peer ((w0Fin l).2 ++ [f]) k0)) (h : W0Early sc l) :
    W0Early sc (l ++ [f]) := by
  obtain ⟨w', hw', hlo, hhi, hmw, hpw, hpm⟩ : ∃ w' : W0Words, W0Ok sc w' ∧
      ((w0Words (w0Fin l).2).lo = [] ∨ (w0Words (w0Fin l).2).lo = w'.lo) ∧
      ((w0Words (w0Fin l).2).hi = [] ∨ (w0Words (w0Fin l).2).hi = w'.hi) ∧
      ((w0Words (w0Fin l).2).mw = .pred false ∨ (w0Words (w0Fin l).2).mw = w'.mw) ∧
      (∀ k < 8, (w0Words (w0Fin l).2).pw k = (.pred false, .pred false) ∨
        (w0Words (w0Fin l).2).pw k = w'.pw k) ∧
      ((w0Words (w0Fin l).2).pm = .pred false ∨ (w0Words (w0Fin l).2).pm = w'.pm) := by
    rcases h with h0 | h1
    · obtain ⟨w', hw'⟩ := w0Ok_canon hsc
      obtain ⟨hlo, hhi, hmw, hpw, hpm⟩ := w0Words_nil
      rw [h0]
      exact ⟨w', hw', Or.inl hlo, Or.inl hhi, Or.inl hmw, fun k hk => Or.inl (hpw k hk),
        Or.inl hpm⟩
    · exact h1
  unfold W0Early
  rw [w0Fin_snoc_quiet hc, w0Words_snoc_peer hk0 hpc]
  simp only [List.append_eq_nil_iff, List.cons_ne_nil, and_false, false_or]
  have hold : ∀ k, k < 8 → k ≠ k0 → w0Peer ((w0Fin l).2 ++ [f]) k = (w0Words (w0Fin l).2).pw k := by
    intro k hk hkk
    simp [w0Words, hk, w0Peer_snoc_ne hpc hkk]
  rcases hnew with hn | hn
  · refine ⟨w', hw', hlo, hhi, hmw, fun k hk => ?_, hpm⟩
    simp only [hk, ite_true]
    by_cases hkk : k = k0
    · subst hkk
      rw [hn]
      simpa [w0Words, hk] using hpw k hk
    · rw [hold k hk hkk]
      exact hpw k hk
  · refine ⟨w'.setPw k0 _, hw'.setPw hn, hlo, hhi, hmw, fun k hk => ?_, hpm⟩
    simp only [hk, ite_true]
    by_cases hkk : k = k0
    · subst hkk
      exact Or.inr (by simp [W0Words.setPw])
    · rw [hold k hk hkk]
      simpa [W0Words.setPw, hkk] using hpw k hk

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
