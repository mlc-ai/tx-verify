-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.OkSite
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value

@[expose] public section

/-! # The data machine along the trace: the invariant

`InvW l d`: a data state `d` after the events `l` of its lane holds what the trace's loads read:
the block's words (`lo`, `hi`, `mw`, `pw`, `pm`, `vt`) are `w0Words` of the block in progress
(`w0Scan l`), the peer reads at pc `477 + 5 k` are in pairs (an odd number exactly at the
control state's second element of `pld k`) and the first element of the pair in the control state
(`a0`) is that of the last read. This file holds the invariant, the steps off the watched sites
(`invW_unwatched`) and the control machine's entry into the peer loads (`w0PldEnter`); the watched
sites are in `TraceSite.lean`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem succOk_pldSite {c c' : Control.D} {k' : Fin 8} (h : succOk c c' = true)
    (hp : c'.site = .pld k') : c.site = .bar1 ∨ ∃ k, c.site = .pld k := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := c
  obtain ⟨s', el', a0', l0', l1', cnt', bi', vs', pv', sl', ps', vt'⟩ := c'
  dsimp only at hp ⊢
  subst hp
  cases s <;> simp [succOk] at h ⊢
  all_goals (rename_i k; fin_cases k <;> simp at h)

/-! ### The trace's side -/

def w0Pf (seg : List Event) (k : Nat) : List Event :=
  seg.filter fun e => e.pc = 477 + 5 * k && (w0RdVal e).isSome

theorem w0Last_snoc {α : Type} (f : Event → Option α) (pcs : List Nat) (seg : List Event)
    (e : Event) : w0Last f pcs (seg ++ [e]) =
      if e.pc ∈ pcs then (match f e with | some x => some x | none => w0Last f pcs seg)
      else w0Last f pcs seg := by
  unfold w0Last
  rw [List.filterMap_append]
  by_cases h : e.pc ∈ pcs
  · cases hf : f e <;> simp [h, hf]
  · simp [h]

theorem w0Pf_snoc (seg : List Event) (e : Event) (k : Nat) :
    w0Pf (seg ++ [e]) k =
      w0Pf seg k ++ (if e.pc = 477 + 5 * k ∧ (w0RdVal e).isSome then [e] else []) := by
  unfold w0Pf; rw [List.filter_append]
  by_cases h : e.pc = 477 + 5 * k ∧ (w0RdVal e).isSome = true <;> simp_all

theorem w0PldEnter {c c' : Control.D} {e : Event} {k' : Fin 8}
    (hc : Control.succ P L g w c e = some (some c')) (hp : c'.site = .pld k') :
    (c.site = .bar1 ∧ c'.el = 0) ∨ (c.site = .pld k' ∧ c.el = 0 ∧ c'.el = 1) ∨
      (∃ k, c.site = .pld k ∧ c.el ≠ 0 ∧ c'.el = 0) := by
  have hin : innerSite c'.site = true := by simp [innerSite, onChain, hp, isStart]
  have hs : succOk c c' = true := by
    by_cases hch : onChain c.site = true
    · by_cases harr : c.site = .arrS
      · simp only [Control.succ, harr] at hc
        split at hc <;> cases hc <;> simp_all
      · exact (okc_chain hch harr hc).resolve_right (by rw [hin]; simp)
    · have := okc_off (by simpa using hch) hc
      rw [hin] at this; cases this
  rcases succOk_pldSite hs hp with hb | ⟨k, hk⟩
  · left
    refine ⟨hb, ?_⟩
    simp only [Control.succ, hb] at hc; cases hc; rfl
  · simp only [Control.succ, hk] at hc
    split at hc
    · by_cases h0 : c.el = 0
      · simp only [h0, ite_true] at hc; cases hc
        right; left; simp_all
      · simp only [h0, ite_false] at hc; cases hc
        right; right; exact ⟨k, hk, h0, rfl⟩
    · cases hc

/-- The watched pcs: the pcs of the sites that record or are read as a block's words. -/
def w0Watched (p : Nat) : Bool :=
  p == 278 || p == 280 || p == 283 || p == 285 || p == 289 || p == 572 || p == 578 ||
    p == 1122 || (477 ≤ p && p ≤ 512 && (p - 477) % 5 == 0)

theorem w0Site_watched (s : Site) (h : w0Watched s.pc = true) :
    (∃ a k, s = .sld a k) ∨ s = .vm ∨ (∃ k, s = .pld k) ∨ s = .mld ∨ s = .vote ∨ s = .arrS := by
  cases s
  all_goals first
    | (exfalso; revert h; simp [Site.pc, w0Watched]; done)
    | (simp; done)
    | (rename_i k; fin_cases k <;> (exfalso; revert h; simp [Site.pc, w0Watched]; done))
    | (rename_i c k; fin_cases c <;> fin_cases k <;>
        (exfalso; revert h; simp [Site.pc, ost2Base, w0Watched]))

def w0PeerOf (p : List Event) : Value × Value :=
  match lastN 2 (p.take (2 * (p.length / 2))) with
  | [e0, e1] => (w0A0 e0, (w0RdVal e1).getD (.pred false))
  | _ => (.pred false, .pred false)

theorem w0PeerOf_even_snoc (p : List Event) (e : Event) (h : p.length % 2 = 0) :
    w0PeerOf (p ++ [e]) = w0PeerOf p := by
  unfold w0PeerOf
  have h1 : 2 * ((p ++ [e]).length / 2) = p.length := by simp; omega
  have h2 : 2 * (p.length / 2) = p.length := by omega
  rw [h1, h2, List.take_left', List.take_length]
  rfl

theorem w0PeerOf_odd_snoc (p : List Event) (e e0 : Event) (h : p.length % 2 = 1)
    (hl : p.getLast? = some e0) :
    w0PeerOf (p ++ [e]) = (w0A0 e0, (w0RdVal e).getD (.pred false)) := by
  obtain ⟨q, rfl⟩ := List.getLast?_eq_some_iff.mp hl
  unfold w0PeerOf
  have h1 : 2 * ((q ++ [e0] ++ [e]).length / 2) = (q ++ [e0] ++ [e]).length := by
    simp at h ⊢; omega
  rw [h1, List.take_length]
  simp [lastN]

theorem w0Peer_eq_pf (seg : List Event) (k : Nat) : w0Peer seg k = w0PeerOf (w0Pf seg k) := rfl

theorem w0Words_unwatched (seg : List Event) (e : Event) (h : w0Watched e.pc = false) :
    w0Words (seg ++ [e]) = w0Words seg := by
  have hp : ∀ k, k < 8 → w0Pf (seg ++ [e]) k = w0Pf seg k := fun k hk => by
    rw [w0Pf_snoc]
    have : e.pc ≠ 477 + 5 * k := fun h' => by
      simp [w0Watched, h'] at h; omega
    simp [this]
  have h1 : ∀ p : Nat, p ∈ [278, 280, 283, 285, 289, 572, 578] → e.pc ≠ p := fun p hp h' => by
    rw [h'] at h; simp at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [w0Watched] at h
  unfold w0Words
  simp only [w0Last_snoc]
  have := h1 280; have := h1 283; have := h1 278; have := h1 285; have := h1 289
  have := h1 572; have := h1 578
  simp_all
  funext k
  simp only [w0Peer_eq_pf]
  split_ifs with hk
  · rw [hp k hk]
  · rfl

structure InvW (l : List Event) (d : D) : Prop where
  lo : d.b.lo = (w0Words (w0Scan l).2).lo
  hi : d.b.hi = (w0Words (w0Scan l).2).hi
  mw : d.b.mw = (w0Words (w0Scan l).2).mw
  pw : ∀ j, d.b.pw j = (w0Words (w0Scan l).2).pw j
  pm : d.b.pm = (w0Words (w0Scan l).2).pm
  vt : d.b.vt = (w0Words (w0Scan l).2).vt
  par : ∀ k : Fin 8, (w0Pf (w0Scan l).2 k).length % 2 = 1 ↔ (d.c.site = .pld k ∧ d.c.el = 1)
  a0 : ∀ k : Fin 8, d.c.site = .pld k → d.c.el = 1 →
    ∃ e0, (w0Pf (w0Scan l).2 k).getLast? = some e0 ∧ d.c.a0 = w0A0 e0

theorem w0NoPld1 {c c' : Control.D} {e : Event} (hp : ∀ k, c.site ≠ .pld k)
    (hc : Control.succ P L g w c e = some (some c')) (k : Fin 8) :
    ¬ (c'.site = .pld k ∧ c'.el = 1) := fun ⟨h1, h2⟩ => by
  rcases w0PldEnter hc h1 with ⟨-, h3⟩ | ⟨h3, -⟩ | ⟨k2, h3, -⟩
  · omega
  · exact hp _ h3
  · exact hp _ h3

/-- A step off the peer loads: the six words' fields are given, the rest is kept. -/
theorem invW_gen {l : List Event} {d : D} {c' : Control.D} {e : Event} (hI : InvW l d)
    (hna : d.c.site ≠ .arrS) (hp : ∀ k, d.c.site ≠ .pld k)
    (h1122 : e.pc ≠ w0ArrSPc) (hnp : ∀ k : Nat, k < 8 → e.pc ≠ 477 + 5 * k)
    (hc : Control.succ P L g w d.c e = some (some c'))
    (hlo : (record d.c e d.b).lo = (w0Words ((w0Scan l).2 ++ [e])).lo)
    (hhi : (record d.c e d.b).hi = (w0Words ((w0Scan l).2 ++ [e])).hi)
    (hmw : (record d.c e d.b).mw = (w0Words ((w0Scan l).2 ++ [e])).mw)
    (hpw : (record d.c e d.b).pw = (w0Words ((w0Scan l).2 ++ [e])).pw)
    (hpm : (record d.c e d.b).pm = (w0Words ((w0Scan l).2 ++ [e])).pm)
    (hvt : (record d.c e d.b).vt = (w0Words ((w0Scan l).2 ++ [e])).vt) :
    InvW (l ++ [e]) (dataNext L d c' e) := by
  rw [dataNext_eq hna]
  have hsc : (w0Scan (l ++ [e])).2 = (w0Scan l).2 ++ [e] := by
    simp [w0Scan_snoc, h1122]
  have hnp' : ∀ k : Fin 8, w0Pf ((w0Scan l).2 ++ [e]) k = w0Pf (w0Scan l).2 k := fun k => by
    rw [w0Pf_snoc]; simp [hnp k k.isLt]
  refine ⟨?_, ?_, ?_, fun j => ?_, ?_, ?_, fun k => ?_, fun k h _ => ?_⟩
  · dsimp only; rw [hsc]; exact hlo
  · dsimp only; rw [hsc]; exact hhi
  · dsimp only; rw [hsc]; exact hmw
  · dsimp only; rw [hsc]; exact congrFun hpw j
  · dsimp only; rw [hsc]; exact hpm
  · dsimp only; rw [hsc]; exact hvt
  · dsimp only; rw [hsc, hnp' k]
    refine (hI.par k).trans ?_
    constructor
    · rintro ⟨h1, -⟩; exact absurd h1 (hp k)
    · intro h; exact absurd h (w0NoPld1 hp hc k)
  · exact absurd ⟨h, ‹_›⟩ (w0NoPld1 hp hc k)

theorem invW_unwatched {l : List Event} {d : D} {c' : Control.D} {e : Event}
    (hI : InvW l d) (hpc : e.pc = d.c.site.pc) (hw : w0Watched d.c.site.pc = false)
    (hc : Control.succ P L g w d.c e = some (some c')) :
    InvW (l ++ [e]) (dataNext L d c' e) := by
  have hna : d.c.site ≠ .arrS := fun h => by simp [h, Site.pc, w0Watched] at hw
  have h1122 : e.pc ≠ w0ArrSPc := fun h => by
    have h2 : w0Watched e.pc = true := by rw [h]; decide
    rw [hpc, hw] at h2; cases h2
  have hnp : ∀ k : Nat, k < 8 → e.pc ≠ 477 + 5 * k := fun k hk h => by
    rw [hpc] at h
    simp [w0Watched] at hw
    omega
  have hn1 : ∀ a k, d.c.site ≠ .sld a k := fun a k h => by
    rw [h] at hw; fin_cases k <;> cases a <;> simp [Site.pc, w0Watched] at hw
  have hn3 : ∀ k : Fin 8, d.c.site ≠ .pld k := fun k h => by
    rw [h] at hw; fin_cases k <;> simp [Site.pc, w0Watched] at hw
  have hn2 : d.c.site ≠ .vm := fun h => by rw [h] at hw; simp [Site.pc, w0Watched] at hw
  have hn4 : d.c.site ≠ .mld := fun h => by rw [h] at hw; simp [Site.pc, w0Watched] at hw
  have hn5 : d.c.site ≠ .vote := fun h => by rw [h] at hw; simp [Site.pc, w0Watched] at hw
  have hrec : (record d.c e d.b).lo = d.b.lo ∧ (record d.c e d.b).hi = d.b.hi ∧
      (record d.c e d.b).mw = d.b.mw ∧ (record d.c e d.b).pw = d.b.pw ∧
      (record d.c e d.b).pm = d.b.pm ∧ (record d.c e d.b).vt = d.b.vt := by
    unfold record
    split <;> first | (exfalso; simp_all; done) | simp
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hrec
  have hww := w0Words_unwatched (w0Scan l).2 e (by rw [hpc]; exact hw)
  refine invW_gen hI hna hn3 h1122 hnp hc ?_ ?_ ?_ ?_ ?_ ?_
  · rw [r1, hww]; exact hI.lo
  · rw [r2, hww]; exact hI.hi
  · rw [r3, hww]; exact hI.mw
  · rw [r4, hww]; exact funext hI.pw
  · rw [r5, hww]; exact hI.pm
  · rw [r6, hww]; exact hI.vt

theorem w0Words_pw_miss (seg : List Event) (e : Event) (h : ∀ k : Nat, k < 8 → e.pc ≠ 477 + 5 * k) :
    (w0Words (seg ++ [e])).pw = (w0Words seg).pw := by
  funext k
  unfold w0Words
  simp only [w0Peer_eq_pf]
  split_ifs with hk
  · rw [w0Pf_snoc]; simp [h k hk]
  · rfl


end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
