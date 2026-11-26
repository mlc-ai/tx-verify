-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.BarSite
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Addr

@[expose] public section

/-! # Warpgroup 0's output sequence

Output chunk `c`'s sites from its first staging store on are consecutive in the machine: the
32 staging stores (`ost2 c k`, element `el`), the proxy fence, barrier 9, the election and the
elected lane's TMA store (`opos`: positions `4 k + el`, `32` to `35`). A state at a position
above `0` follows a state at the position before it (`opos_pred`), and the election follows the
barrier only in warps 0 and 1 (the warp word is at most `1`). The barrier site of the epilogue's
ordinal `2 + c` is `obar c` (`obar_site`); a staging store writes its swizzled word
(`ost2_acc`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

/-- **The position of a state in its output chunk's sequence**. -/
def opos (d : D) : Option (Fin 4 × Nat) :=
  match d.site with
  | .ost2 c k => some (c, 4 * k.val + min d.el 3)
  | .ofpx c => some (c, 32)
  | .obar c => some (c, 33)
  | .oel c => some (c, 34)
  | .otma c => some (c, 35)
  | _ => none

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

private theorem opos_nextChunk (k : Fin 4) (d : D) : opos (nextChunk k d) = none := by
  unfold nextChunk opos; fin_cases k <;> simp

private theorem tcLoad_eq {e : Event} {d d' : D} {s : Site} (h : tcLoad e d s = some (some d')) :
    d' = { d with site := s } := by
  unfold tcLoad at h; split at h
  · exact (Option.some.inj (Option.some.inj h)).symm
  · cases h

set_option linter.unusedSimpArgs false in
/-- **The state before a position above `0`** is at the position before it; the election
follows the barrier only for a warp word at most `1`. -/
theorem opos_pred {d d' : D} {e : Event} {c : Fin 4} {i : Nat}
    (hn : succ P L g w d e = some (some d')) (ho : opos d' = some (c, i + 1)) :
    opos d = some (c, i) ∧ (d'.site = .oel c → scmpi .gt .s w 1 = false) := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  have nn : ∀ {x : Option (Option D)}, x = some (some d') → opos d' = some (c, i + 1) →
      (∀ y, x = some (some y) → opos y = none) → False := fun hx ho hy => by
    rw [hy _ hx] at ho; cases ho
  cases s
  case exit => simp [succ] at hn
  case sink =>
    exfalso; refine nn hn ho fun y hy => ?_
    simp only [succ, dataRd] at hy; split at hy <;>
      simp only [Option.some.injEq, reduceCtorEq] at hy
    all_goals subst hy; unfold afterSink afterA finish; split_ifs <;> simp [opos]
  case vm | mld =>
    exfalso; refine nn hn ho fun y hy => ?_
    simp only [succ, dataRd] at hy; split at hy <;>
      simp only [Option.some.injEq, reduceCtorEq] at hy
    all_goals subst hy; simp [opos]
  case eld =>
    exfalso; refine nn hn ho fun y hy => ?_
    simp only [succ, dataRd] at hy; split at hy <;>
      simp only [Option.some.injEq, reduceCtorEq] at hy
    all_goals subst hy; unfold afterEld; split_ifs <;> simp [opos]
  case lenA | lenB =>
    exfalso; refine nn hn ho fun y hy => ?_
    simp only [succ, ncWord] at hy; split at hy
    · split at hy <;>
      simp only [Option.some.injEq, reduceCtorEq] at hy
      subst hy
      (try unfold afterA); (try split_ifs) <;> simp [opos]
    · cases hy
  case wv | wq | wsv =>
    exfalso; refine nn hn ho fun y hy => ?_
    simp only [succ, poll] at hy; split at hy <;>
      simp only [Option.some.injEq, reduceCtorEq] at hy
    subst hy; split_ifs <;> simp [opos]
  case sld a k =>
    exfalso; refine nn hn ho fun y hy => ?_
    fin_cases k <;> simp only [succ] at hy <;> rw [tcLoad_eq hy] <;> simp [opos]
  case rld k | old k =>
    exfalso; refine nn hn ho fun y hy => ?_
    simp only [succ] at hy; rw [tcLoad_eq hy]; simp [opos]
  case pld k =>
    exfalso; refine nn hn ho fun y hy => ?_
    simp only [succ] at hy; split at hy
    · split at hy <;> simp only [Option.some.injEq] at hy <;> subst hy
      · simp [opos]
      · fin_cases k <;> simp [opos]
    · cases hy
  case vote =>
    exfalso; refine nn hn ho fun y hy => ?_
    simp only [succ] at hy; split at hy <;>
      simp only [Option.some.injEq, reduceCtorEq] at hy
    subst hy; simp [opos]
  case oel k =>
    simp only [succ] at hn; split at hn
    · cases hn
      split_ifs at ho ⊢ with hl
      · simp only [opos, Option.some.injEq, Prod.mk.injEq] at ho
        obtain ⟨rfl, hi⟩ := ho
        exact ⟨by simp [opos]; omega, fun h => by cases h⟩
      · rw [opos_nextChunk] at ho; cases ho
    · cases hn
  case arrS =>
    exfalso; refine nn hn ho fun y hy => ?_
    simp only [succ] at hy; split at hy <;> simp only [Option.some.injEq] at hy <;> subst hy <;>
      simp [opos]
  all_goals simp only [succ, Option.some.injEq] at hn
  all_goals subst hn
  case smr =>
    exfalso; revert ho; unfold afterSmr afterSink afterA finish
    split_ifs <;> simp [opos]
  case arrL => exfalso; revert ho; unfold loopEntry; split_ifs <;> simp [opos]
  case pst k => exfalso; revert ho; fin_cases k <;> simp [opos]
  case ost k =>
    exfalso; revert ho; unfold elemNext afterOst
    fin_cases k <;> split_ifs <;> simp [opos]
  case rstw k => exfalso; revert ho; fin_cases k <;> simp [opos]
  case oldw k => simp [opos] at ho
  case ost2 cc k =>
    unfold elemNext at ho ⊢
    split_ifs at ho ⊢ with hel <;> simp only at hel
    · simp only [opos, Option.some.injEq, Prod.mk.injEq] at ho ⊢
      exact ⟨⟨ho.1, by omega⟩, fun h => absurd h (by simp)⟩
    · fin_cases k <;> simp only [opos, Option.some.injEq, Prod.mk.injEq, List.getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Option.getD_none,
        List.getElem?_nil] at ho ⊢ <;> exact ⟨⟨ho.1, by omega⟩, fun h => absurd h (by simp)⟩
  case ofpx k =>
    simp only [opos, Option.some.injEq, Prod.mk.injEq] at ho ⊢
    exact ⟨⟨ho.1, by omega⟩, by simp⟩
  case obar k =>
    unfold afterObar at ho ⊢
    split_ifs at ho with hw
    · rw [opos_nextChunk] at ho; cases ho
    · simp only [opos, Option.some.injEq, Prod.mk.injEq] at ho ⊢
      exact ⟨⟨ho.1, by omega⟩, fun _ => by simpa using hw⟩
  case otma k => exfalso; rw [opos_nextChunk] at ho; cases ho
  case ebar => exfalso; revert ho; unfold finish; split_ifs <;> simp [opos]
  all_goals exfalso; simp [opos] at ho

/-- The output sequence's sites are at pcs of the role. -/
theorem opos_pc {d : D} {p : Fin 4 × Nat} (h : opos d = some p) :
    103 ≤ d.site.pc ∧ d.site.pc < 1842 := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases s <;> simp only [opos, reduceCtorEq] at h
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals simp [Site.pc, ost2Base]

/-- **The epilogue's barrier site of ordinal `2 + c`** is chunk `c`'s. -/
theorem obar_site {s : Site} {c : Nat} (hc : c < 4) (hs : s.isBar = true) (hr : s.reg = .epi)
    (hb : s.bidx = 2 + c) : s = .obar ⟨c, hc⟩ := by
  cases s <;> simp only [Site.isBar, Site.reg, Site.bidx, Bool.false_eq_true,
    reduceCtorEq] at hs hr hb
  all_goals first | omega | (congr 1; ext; simp only; omega)

/-- **The sites of the positions**: the staging stores below `32`, then the fence, the barrier,
the election, the TMA store. -/
theorem opos_inv {d : D} {c : Fin 4} {p : Nat} (h : opos d = some (c, p)) :
    (∃ k : Fin 8, d.site = .ost2 c k ∧ p = 4 * k.val + min d.el 3) ∨
      (p = 32 ∧ d.site = .ofpx c) ∨ (p = 33 ∧ d.site = .obar c) ∨ (p = 34 ∧ d.site = .oel c) ∨
      (p = 35 ∧ d.site = .otma c) := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases s <;> simp only [opos, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  all_goals simp

/-- **Only the TMA store's site fires a tensor store.** -/
theorem otma_of_ev {d : D} {e : Event} {a : Nat} {s : TensorStore.Spec}
    (hev : EvK P L g w d e) (hk : e.kind = .tensorStore a s) : ∃ c, d.site = .otma c := by
  obtain ⟨st, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hk
  subst hk
  cases st
  case otma c => exact ⟨c, rfl⟩
  all_goals simp [EvK, TcLdEv, TcStEv, NcEv, PollEv, ArrEv, RdAt, WrAt, GenWrAt, GWrAt] at hev

/-- **The election's leader is the lane that stores**: the state after the election of chunk `c`
is its TMA store only when the elected lane is this lane. -/
theorem oel_leader {d d' : D} {e : Event} {c : Fin 4}
    (hn : succ P L g w d e = some (some d')) (hd : d.site = .oel c) (hd' : d'.site = .otma c)
    {mask inst ld : Nat} (hk : e.kind = .elect mask inst ld) : PTX.laneOf L g = ld := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  simp only at hd
  subst hd
  simp only [succ, hk] at hn
  by_contra hne
  simp only [hne, ↓reduceIte, Option.some.injEq] at hn
  subst hn
  have h := opos_nextChunk c
    ⟨.oel c, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩
  simp only [opos, hd'] at h
  cases h

/-- **A staging store writes its swizzled word** (element `el` of store `k` of chunk `c` of thread
`t`), or faults. -/
theorem ost2_acc {m : Mem0} (hp : Pre P L m) (ht : tidOf L g < 128) {d : D} {c : Fin 4}
    {k : Fin 8} {e : Event} (hs : d.site = .ost2 c k) (hev : EvK P L g w d e) :
    d.el < 4 ∧ ((∃ a bs, e.kind = .wr a bs ∧ a.size = 4 ∧ a.loc = wsLoc L (g / L.block)
      (65536 + 16384 * (tidOf L g / 64) + 128 * (tidOf L g % 64) + 16 * (k.val ^^^ tidOf L g % 8) +
        MemRow.wg0OutOff c.val + 4 * d.el)) ∨ ∃ f, e.kind = .ub f) := by
  unfold EvK at hev
  rw [hs] at hev
  obtain ⟨hel, hE⟩ := hev
  refine ⟨hel, ?_⟩
  rcases hE with ⟨a, bs, hk, hl, hz⟩ | hu
  · refine .inl ⟨a, bs, hk, hz, ?_⟩
    have e := stW_eq hp ht k.isLt
    have ho : ost2Off c = MemRow.wg0OutOff c.val := rfl
    rw [hl, e, ho]
    simp only [Loc.at, wsLoc, Loc.mk.injEq, true_and]
    omega
  · exact .inr hu

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
