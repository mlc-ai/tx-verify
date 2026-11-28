-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WinCond
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceBase
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.PcBound
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Ok
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Carry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceSk
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceE
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Loaded
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Payloads

@[expose] public section

/-! # A canonical valid block behind the words a state has loaded

At a site of the loop, the words the state's block has loaded are those of one valid block
(`WCtx.canon`): the early facts of the valid trace after the event (`W0Early`) name a valid
block `w'`, and the words the event leaves in place are, once loaded (`W0Loaded`), the words
of `w'`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

/-- A word that reads as a finite number is not the default word. -/
theorem w0Fin_ne_pred {v : Value} (h : W0Fin v) : v ≠ .pred false := by
  rintro rfl
  obtain ⟨x, hx⟩ := h
  simp only [valFloat] at hx
  rw [bitsAsFloat_eq (by intro f h; cases h)] at hx
  simp [Value.bitPattern] at hx

/-- The words of a block are, where read, those of the valid block `w`. -/
structure EarlyEq (w u : W0Words) : Prop where
  lo : u.lo = [] ∨ u.lo = w.lo
  hi : u.hi = [] ∨ u.hi = w.hi
  mw : u.mw = .pred false ∨ u.mw = w.mw
  pw : ∀ k < 8, u.pw k = (.pred false, .pred false) ∨ u.pw k = w.pw k
  pm : u.pm = .pred false ∨ u.pm = w.pm

theorem wlo_snoc (seg : List Event) (e : Event) (h1 : e.pc ≠ 280) (h2 : e.pc ≠ 283) :
    (w0Words (seg ++ [e])).lo = (w0Words seg).lo := by
  simp [w0Words, w0Last_snoc, h1, h2]

theorem whi_snoc (seg : List Event) (e : Event) (h1 : e.pc ≠ 278) (h2 : e.pc ≠ 285) :
    (w0Words (seg ++ [e])).hi = (w0Words seg).hi := by
  simp [w0Words, w0Last_snoc, h1, h2]

theorem wmw_snoc (seg : List Event) (e : Event) (h1 : e.pc ≠ 289) :
    (w0Words (seg ++ [e])).mw = (w0Words seg).mw := by
  simp [w0Words, w0Last_snoc, h1]

theorem wpm_snoc (seg : List Event) (e : Event) (h1 : e.pc ≠ 572) :
    (w0Words (seg ++ [e])).pm = (w0Words seg).pm := by
  simp [w0Words, w0Last_snoc, h1]

theorem wpw_snoc (seg : List Event) (e : Event) {j : Nat} (hj : j < 8) (h1 : e.pc ≠ 477 + 5 * j) :
    (w0Words (seg ++ [e])).pw j = (w0Words seg).pw j := by
  simp only [w0Words, hj, ite_true, w0Peer_eq_pf, w0Pf_snoc]
  simp [h1]

/-- **A valid block behind the words of the trace after an event** (not the block's end). -/
theorem w0_early_snoc {sc : ℝ} {l : List Event} {e : Event} (hv : W0Valid sc (l ++ [e]))
    (h : e.pc ≠ w0ArrSPc) :
    ∃ w', W0Ok sc w' ∧ EarlyEq w' (w0Words ((w0Fin l).2 ++ [e])) := by
  have hE := hv.early
  unfold W0Early at hE
  rw [w0Fin_snoc_snd l e h] at hE
  rcases hE with h0 | ⟨w', hw', h1, h2, h3, h4, h5⟩
  · exact absurd h0 (by simp)
  · exact ⟨w', hw', ⟨h1, h2, h3, h4, h5⟩⟩


end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The pieces of a word payload, by name. -/
theorem W0EvPayload.scoreHi {sc : ℝ} {l : List Event} {e : Event} (h : W0EvPayload sc l e) :
    ∀ vals, w0TcVals e = some vals → (e.pc = 278 ∨ e.pc = 285) →
    vals.length = 32 ∧ ∀ c < 32,
      PTX.Flow.Clean (vals.getD c (.pred false)) ∧ W0Fin (vals.getD c (.pred false)) := by
  obtain ⟨h1, -⟩ := h
  exact h1

theorem W0EvPayload.mask {sc : ℝ} {l : List Event} {e : Event} (h : W0EvPayload sc l e) :
    ∀ x bs, e.kind = .rd x bs → e.pc = 289 →
    ∃ n < 2 ^ 32, rebuild 3 bs = .ok (.bits 32 (BitVec.ofNat 64 n)) := by
  obtain ⟨-, -, -, h4, -⟩ := h
  exact h4

theorem W0EvPayload.peer {sc : ℝ} {l : List Event} {e : Event} (h : W0EvPayload sc l e) :
    ∀ x bs, e.kind = .rd x bs → (∃ k < 8, e.pc = 477 + 5 * k) →
    ∃ v, rebuild 3 bs = .ok v ∧ W0Fin (splitValue 64 v).1 ∧ W0Fin (splitValue 64 v).2 := by
  obtain ⟨-, -, -, -, h5, -⟩ := h
  exact h5

theorem W0EvPayload.peerMax {sc : ℝ} {l : List Event} {e : Event} (h : W0EvPayload sc l e) :
    ∀ x bs, e.kind = .rd x bs → e.pc = 572 →
    ∃ v, rebuild 3 bs = .ok v ∧ PTX.Flow.Clean v ∧ (W0Fin v ∨ v = w0NegInf) := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := h
  exact h6

theorem W0EvPayload.sink {sc : ℝ} {l : List Event} {e : Event} (h : W0EvPayload sc l e) :
    ∀ x bs, e.kind = .nc x bs → e.pc = 156 →
    ∃ (bits : Nat) (q : ℚ), bits < 2 ^ 32 ∧ f32Value bits = some q ∧
      rebuild 3 bs = .ok (b32 bits) := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := h
  exact h7

theorem W0EvPayload.rowSum {sc : ℝ} {l : List Event} {e : Event} (h : W0EvPayload sc l e) :
    ∀ x bs, e.kind = .rd x bs → e.pc = 1157 →
    ∃ (v : Value) (p : ℝ), rebuild 3 bs = .ok v ∧ 0 ≤ p ∧ Rd v p ∧
      (w0MxCarry sc (w0Fin l).1 = ⊥ → p = 0) := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := h
  exact h8

theorem W0EvPayload.length {sc : ℝ} {l : List Event} {e : Event} (h : W0EvPayload sc l e) :
    ∀ x bs, e.kind = .nc x bs → (e.pc = 168 ∨ e.pc = 181) → ∃ v, rebuild 3 bs = .ok v := by
  obtain ⟨-, -, h3, -⟩ := h
  exact h3

theorem W0EvPayload.acc {sc : ℝ} {l : List Event} {e : Event} (h : W0EvPayload sc l e) :
    ∀ vals, w0TcVals e = some vals → e.pc ∈ w0OPcs →
    vals.length = 64 ∧ ∃ O : Nat → ℝ, ∀ i < 64, Rd (vals.getD i (.pred false)) (O i) := by
  obtain ⟨-, -, -, -, -, -, -, -, h9⟩ := h
  exact h9

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

/-- **The context of a window's condition**: the state `d` after the events `l`, the event `e`
fired at its site, in a valid trace with its typed words and the words its block has loaded. -/
structure WCtx (L : Launch) (g : Nat) (sc : ℝ) (l : List Event) (d : D) (e : Event) : Prop where
  hx : Rd (.bits 32 (scX L)) (sc : EReal)
  hI : InvW l d
  hOk : OkInv d
  hC : CarryW sc l d
  hSk : InvSk l d
  hE : InvE l d
  hpc : e.pc = d.c.site.pc
  hel : d.c.el < Control.elems d.c.site
  hv : W0Valid sc (l ++ [e])
  hpay : W0EvPayload sc l e
  hld : W0Loaded l e.pc

theorem WCtx.fields {L : Launch} {g : Nat} {sc : ℝ} {l : List Event} {d : D} {e : Event}
    (c : WCtx L g sc l d e) :
    d.b.lo = (w0Words (w0Fin l).2).lo ∧ d.b.hi = (w0Words (w0Fin l).2).hi ∧
      d.b.mw = (w0Words (w0Fin l).2).mw ∧ (∀ j, d.b.pw j = (w0Words (w0Fin l).2).pw j) ∧
      d.b.pm = (w0Words (w0Fin l).2).pm := by
  rw [w0Fin_snd]
  exact ⟨c.hI.lo, c.hI.hi, c.hI.mw, c.hI.pw, c.hI.pm⟩

/-- **The block behind a site of the loop**: the words the state has loaded are those of one valid
block `w'`. -/
theorem WCtx.canon {L : Launch} {g : Nat} {sc : ℝ} {l : List Event} {d : D} {e : Event}
    (c : WCtx L g sc l d e) (h1 : 289 ≤ e.pc) (h2 : e.pc < 1122) :
    ∃ w', W0Ok sc w' ∧ EarlyEq w' (w0Words ((w0Fin l).2 ++ [e])) ∧ d.b.lo = w'.lo ∧
      d.b.hi = w'.hi ∧ (289 < e.pc → d.b.mw = w'.mw) ∧
      (∀ j < 8, 477 + 5 * j < e.pc → d.b.pw j = w'.pw j) ∧
      (572 < e.pc → d.b.pm = w'.pm) := by
  obtain ⟨w', hw', hE⟩ := w0_early_snoc c.hv (by unfold w0ArrSPc; omega)
  obtain ⟨hlo, hhi, hmw, hpw, hpm⟩ := c.fields
  have hlo' := c.hld.score h1 (by omega)
  refine ⟨w', hw', hE, ?_, ?_, fun h => ?_, fun j hj h => ?_, fun h => ?_⟩
  · rw [hlo]
    have e1 := hE.lo
    rw [wlo_snoc _ _ (by omega) (by omega)] at e1
    exact e1.resolve_left hlo'.1
  · rw [hhi]
    have e2 := hE.hi
    rw [whi_snoc _ _ (by omega) (by omega)] at e2
    exact e2.resolve_left hlo'.2
  · rw [hmw]
    have e3 := hE.mw
    rw [wmw_snoc _ _ (by omega)] at e3
    exact e3.resolve_left (c.hld.mask h (by omega))
  · rw [hpw]
    have e4' := hE.pw j hj
    rw [wpw_snoc _ _ hj (by omega)] at e4'
    exact e4'.resolve_left (c.hld.pair j hj h (by omega))
  · rw [hpm]
    have e5 := hE.pm
    rw [wpm_snoc _ _ (by omega)] at e5
    exact e5.resolve_left (c.hld.peerMax h (by omega))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
