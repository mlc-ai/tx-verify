-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem

@[expose] public section

/-! # The region of a thread's shared access, by role

`access_region`: a shared byte a thread's memory access covers is a byte of the thread's CTA in
one of its role's regions (the rows of `Iface/MemRows/`): the startup's in the allocation word,
warpgroup 0's in the token-validity bytes, the P exchange, the row maxima or the output staging
(dequantized tile 1), the TMA warp's in the coordinates, the index warp's in the coordinates or
the token-validity bytes, and warpgroup 2's in a raw or a dequantized tile. The asynchronous
half is `Common/Export/Async.lean`'s `async_region`. `locIn_eq`: a byte is in one region. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A byte is in one region** of one CTA. -/
theorem locIn_eq {c c' : Nat} {r r' : Region} {l : Loc} (h : MemRow.LocIn L c r l)
    (h' : MemRow.LocIn L c' r' l) : c = c' ∧ r = r' := by
  obtain ⟨-, hc, h1, h2⟩ := h
  obtain ⟨-, hc', h1', h2'⟩ := h'
  refine ⟨hc.symm.trans hc', Region.disjoint (off := l.addr - L.sharedBase) ⟨?_, ?_⟩ ⟨?_, ?_⟩⟩ <;>
    omega

/-- A byte an access in a region covers is in the region. -/
theorem MemRow.SharedIn.locIn {c : Nat} {r : Region} {a : Acc} {b : Loc}
    (h : MemRow.SharedIn L c r a) (hc : a.Covers b) : MemRow.LocIn L c r b := by
  obtain ⟨hs, hcta, hlo, hhi⟩ := h
  obtain ⟨hbs, hbc, hblo, hbhi⟩ := hc
  have hbs' : b.space = a.loc.space := hbs
  have hbc' : b.cta = a.loc.cta := hbc
  have hblo' : a.loc.addr ≤ b.addr := hblo
  have hbhi' : b.addr < a.loc.addr + a.size := hbhi
  exact ⟨hbs'.trans hs, hbc'.trans hcta, by omega, by omega⟩

/-- **The region of a thread's shared access**, by the role of its event. -/
theorem access_region (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {a : Acc} {w : Bool} (hI : X.Access (g, k) a w) {b : Loc}
    (hc : a.Covers b) (hs : b.space = .shared) :
    ∃ e, X.get (g, k) = some e ∧
      ((StartupAt e.pc ∧ MemRow.LocIn L (g / L.block) .tmemWord b) ∨
      (Wg0At L g e.pc ∧ ((MemRow.LocIn L (g / L.block) .tokenValid b ∨
        MemRow.LocIn L (g / L.block) .pExchange b ∨ MemRow.LocIn L (g / L.block) .rowMax b) ∨
        MemRow.LocIn L (g / L.block) (.dequant 1) b)) ∨
      (TmaAt L g e.pc ∧ MemRow.LocIn L (g / L.block) .tmaCoord b) ∨
      (IndexAt L g e.pc ∧ (MemRow.LocIn L (g / L.block) .tmaCoord b ∨
        MemRow.LocIn L (g / L.block) .tokenValid b)) ∨
      (DequantAt L g e.pc ∧ ∃ r, MemRow.LocIn L (g / L.block) (.raw r) b ∨
        MemRow.LocIn L (g / L.block) (.dequant r) b)) := by
  obtain ⟨ev, hget, hk, hm⟩ := access_event hI
  have hrd : ∀ {a' : Acc} {bs}, ev.kind = .rd a' bs → a' = a := by
    intro a' bs h
    rcases hk with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, _, h'⟩ <;> rw [h'] at h <;> cases h
    rfl
  have hwr : ∀ {a' : Acc} {bs}, ev.kind = .wr a' bs → a' = a := by
    intro a' bs h
    rcases hk with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, _, h'⟩ <;> rw [h'] at h <;> cases h
    rfl
  have hnc : ∀ {a' : Acc} {bs}, ev.kind ≠ .nc a' bs := by
    intro a' bs h
    rcases hk with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, _, h'⟩ <;> rw [h'] at h <;> cases h
  have hg := Frame.lt_of_get hX hget
  have hR := mem_rows hp hX hFw
  refine ⟨ev, hget, ?_⟩
  rcases hR.place hg hget hm with h | h | h | h | h | h | h
  · refine .inl ⟨h, ?_⟩
    have hin : ∀ {a' : Acc}, MemRow.WsAcc L (g / L.block) Region.tmemWord.lo 4 a' →
        MemRow.SharedIn L (g / L.block) .tmemWord a' := fun h' =>
      MemRow.wsAcc_in h' (Nat.le_refl _) (by simp only [Region.lo, Region.size]; omega)
    obtain ⟨-, ⟨a', bs, hk', hws⟩ | ⟨-, a', bs, hk', hws⟩⟩ := hR.startup hg hget h hm
    · rw [hwr hk'] at hws
      exact (hin hws).locIn hc
    · rw [hrd hk'] at hws
      exact (hin hws).locIn hc
  · refine .inr (.inl ⟨h, ?_⟩)
    rcases wg0_mem_region hp hX hFw hg hget h hm with ⟨_, _, h1⟩ | ⟨a', bs, hk', -, hl, -⟩ |
      ⟨a', r, hk', hr, hS⟩
    · exact (hnc h1).elim
    · rw [hwr hk'] at hl
      have : b.space = a.loc.space := hc.1
      rw [hl] at this
      rw [hs] at this
      cases this
    · have ha : a' = a := by
        rcases hk' with ⟨_, h1⟩ | ⟨_, h1⟩
        · exact hrd h1
        · exact hwr h1
      subst ha
      rcases hr with (rfl | rfl | rfl) | rfl
      · exact .inl (.inl (hS.locIn hc))
      · exact .inl (.inr (.inl (hS.locIn hc)))
      · exact .inl (.inr (.inr (hS.locIn hc)))
      · exact .inr (hS.locIn hc)
  · obtain ⟨_, _, h1⟩ := hR.wg1 hg hget h hm
    exact (hnc h1).elim
  · obtain ⟨_, _, h1⟩ := hR.mma hg hget h hm
    exact (hnc h1).elim
  · rcases hR.tma hg hget h hm with ⟨_, _, h1⟩ | ⟨a', bs, hk', hT⟩
    · exact (hnc h1).elim
    · rw [hrd hk'] at hT
      exact .inr (.inr (.inl ⟨h, (MemRow.tmaRd_in hT).locIn hc⟩))
  · rcases hR.index hg hget h hm with ⟨_, _, h1⟩ | ⟨a', bs, hk', hT⟩
    · exact (hnc h1).elim
    · rw [hwr hk'] at hT
      refine .inr (.inr (.inr (.inl ⟨h, ?_⟩)))
      rcases MemRow.ixWr_in hT with h1 | h1
      · exact .inl (h1.locIn hc)
      · exact .inr (h1.locIn hc)
  · refine .inr (.inr (.inr (.inr ⟨h, ?_⟩)))
    rcases hR.dequant hg hget h hm with ⟨_, _, h1⟩ | ⟨a', bs, r, hk', hS⟩ |
      ⟨a', bs, r, q, s, hk', hws⟩
    · exact (hnc h1).elim
    · rw [hrd hk'] at hS
      exact ⟨r, .inl (hS.locIn hc)⟩
    · rw [hwr hk'] at hws
      have hlt := MemRow.dqChunk_lt (i := g % 128) (Nat.mod_lt _ (by decide)) q.isLt s.isLt
      refine ⟨r, .inr (MemRow.SharedIn.locIn (MemRow.wsAcc_in hws (Nat.le_add_right _ _) ?_) hc)⟩
      simp only [Region.size]
      omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
