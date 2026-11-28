-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.BarSite
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Addr

@[expose] public section

/-! # Warpgroup 0's P-store sequence

The P stores of a block (`ost k`, element `el`) are consecutive in the machine (positions
`4 k + el`, `0` to `15`), followed by the rest of the block up to its arrival on `soReady`: the
rescale arm's sites, which fire no arrival (position `16`), then the arrival's site `arrS`
(position `17`). A state at a position above `0` follows a state at the position before it, or at
position `16` when it is at `16` (`ppos_pred`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

/-- **The position of a state in its block's P-store sequence**. -/
def ppos (d : D) : Option Nat :=
  match d.site with
  | .ost k => some (4 * k.val + min d.el 3)
  | .rsf | .rld _ | .rldw _ | .rst _ | .rstw _ | .rsfb | .fpx => some 16
  | .arrS => some 17
  | _ => none

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

set_option linter.unusedSimpArgs false in
/-- **The state before a position above `0`** is at the position before it, or at `16` when it is
at `16`. -/
theorem ppos_pred {d d' : D} {e : Event} {q : Nat}
    (hn : succ P L g w d e = some (some d')) (ho : ppos d' = some q) (hq : 0 < q) :
    ∃ p, ppos d = some p ∧ (p + 1 = q ∨ (p = 16 ∧ q = 16)) := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals simp only [succ, dataRd, ncWord, poll, tcLoad, afterSmr, afterSink, afterA,
    afterEld, elemNext, loopEntry, advance, afterOst, finish, nextChunk, afterObar] at hn ⊢
  all_goals (repeat' split at hn)
  all_goals simp only [Option.some.injEq, reduceCtorEq] at hn
  all_goals try subst hn
  all_goals try (simp_all [ppos]; done)
  all_goals (simp only [ppos, Option.some.injEq] at ho ⊢; exact ⟨_, rfl, .inl (by omega)⟩)

/-- **The sites of the positions below `16`** are the P stores. -/
theorem ppos_ost {d : D} {p : Nat} (h : ppos d = some p) (hp : p < 16) :
    ∃ k : Fin 4, d.site = .ost k ∧ p = 4 * k.val + min d.el 3 := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases s <;> simp only [ppos, reduceCtorEq, Option.some.injEq] at h
  all_goals first | omega | exact ⟨_, rfl, h.symm⟩

/-- The sequence's sites are at pcs of the role. -/
theorem ppos_pc {d : D} {p : Nat} (h : ppos d = some p) :
    103 ≤ d.site.pc ∧ d.site.pc < 1842 := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases s <;> simp only [ppos, reduceCtorEq] at h
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals simp [Site.pc]

/-- Positions are at most `17`. -/
theorem ppos_le {d : D} {p : Nat} (h : ppos d = some p) : p ≤ 17 := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases s <;> simp only [ppos, reduceCtorEq, Option.some.injEq] at h
  all_goals omega

/-- **No site of the sequence below `17` fires an arrival.** -/
theorem ppos_noArr {d : D} {e : Event} {p : Nat} (h : ppos d = some p) (hp : p ≠ 17)
    (hev : EvK P L g w d e) (l : Loc) (tx n : Nat) (rel : Bool)
    (sc : MbarScope) : e.kind ≠ .arrive l tx n rel sc := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  intro hk
  cases s <;> simp only [ppos, reduceCtorEq, Option.some.injEq] at h
  all_goals try omega
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals simp [EvK, TcLdEv, TcStEv, WrAt] at hev
  all_goals first | (rcases hev with h1 | ⟨f, hf⟩ <;> simp_all) | simp_all

/-- **A P store writes its four bytes** (element `el` of store `k` of thread `t`), or faults. -/
theorem ost_acc {m : Mem0} (hp : Pre P L m) (ht : tidOf L g < 128) {d : D} {k : Fin 4}
    {e : Event} (hs : d.site = .ost k) (hev : EvK P L g (warpW L g) d e)
    (hub : ∀ f, e.kind ≠ .ub f) :
    d.el < 4 ∧ ∃ a bs, e.kind = .wr a bs ∧ a.size = 4 ∧ a.loc = wsLoc L (g / L.block)
      (204800 + 4096 * (tidOf L g / 32 / 2) + 512 * (tidOf L g / 32 % 2) +
        16 * (tidOf L g % 32) + 1024 * k.val + 4 * d.el) := by
  unfold EvK at hev
  rw [hs] at hev
  obtain ⟨hel, hE⟩ := hev
  rcases hE with ⟨a, bs, hk, hl, hz⟩ | ⟨f, hf⟩
  · refine ⟨hel, a, bs, hk, hz, ?_⟩
    rw [hl, r16_loc hp ht k.isLt]
    simp only [Loc.at, wsLoc, Loc.mk.injEq, true_and]
    omega
  · exact absurd hf (hub f)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
