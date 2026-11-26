-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ev
public import Lemmas.Tmem.PairProtocol

@[expose] public section

/-! # Warpgroup 0's paired Tensor Memory operations

`TmemAt w d t`: at state `d` of the machine of warp word `w`, with `t` paired Tensor Memory
operations (`Tmem.Pair.isTmemOp`) among the thread's events before it. Warp 0 (`w = 0`) comes
with the startup's two (allocation, relinquishment), makes its third at the deallocation (pc
1840) and returns after it; the other warps make none. Only the end of the warpgroup (`finish`)
leads to the deallocation or the return (`succ_end`), and only the deallocation's event is a
paired operation (`tmemOp_site`). `tmemAt_step`: a step without undefined behaviour keeps it at
the count bumped by its event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

/-- **Warpgroup 0's count of paired Tensor Memory operations.** -/
def TmemAt (w : BitVec 64) (d : D) (t : Nat) : Prop :=
  if d.site = .dealloc then scmpi .ne .b w 0 = false ∧ t = 2
  else if d.site = .exit then t = if scmpi .ne .b w 0 then 0 else 3
  else t = if scmpi .ne .b w 0 then 0 else 2

/-- A site before the end: neither the deallocation nor the return. -/
abbrev Mid (s : Site) : Prop := s ≠ .dealloc ∧ s ≠ .exit

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

private theorem afterA_mid (d : D) : Mid (afterA P d).site := by
  unfold afterA; split_ifs <;> constructor <;> simp

private theorem afterSink_mid (d : D) :
    Mid (afterSink P L g w d).site ∨ afterSink P L g w d = finish w d := by
  unfold afterSink
  split_ifs
  · exact .inr rfl
  · exact .inl (afterA_mid _)
  · exact .inl ⟨by simp, by simp⟩

private theorem afterSmr_mid (d : D) :
    Mid (afterSmr P L g w d).site ∨ afterSmr P L g w d = finish w d := by
  unfold afterSmr
  split_ifs
  · exact afterSink_mid _
  · exact .inl ⟨by simp, by simp⟩

private theorem nextChunk_mid (k : Fin 4) (d : D) : Mid (nextChunk k d).site := by
  unfold nextChunk; fin_cases k <;> constructor <;> simp

private theorem afterObar_mid (k : Fin 4) (d : D) : Mid (afterObar w k d).site := by
  unfold afterObar; split_ifs
  · exact nextChunk_mid k d
  · constructor <;> simp

private theorem afterEld_mid (d : D) : Mid (afterEld L g d).site := by
  unfold afterEld; split_ifs <;> constructor <;> simp

private theorem loopEntry_mid (d : D) : Mid (loopEntry d).site := by
  unfold loopEntry; split_ifs <;> constructor <;> simp

private theorem afterOst_mid (d : D) : Mid (afterOst d) := by
  unfold afterOst; split_ifs <;> constructor <;> simp

private theorem getD_mid {l : List Site} {i : Nat} {s : Site} (hl : ∀ x ∈ l, Mid x) (hs : Mid s) :
    Mid (l.getD i s) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact hs
  | some x => exact hl x (List.mem_of_getElem? h)

private theorem elemNext_mid {d : D} {n : Nat} {s : Site} (hd : Mid d.site) (hs : Mid s) :
    Mid (elemNext d n s).site := by
  unfold elemNext; split_ifs
  · exact hd
  · exact hs

private theorem dataRd_eq {e : Event} {x d' : D} (h : dataRd e x = some (some d')) : d' = x := by
  unfold dataRd at h
  split at h <;> first | exact (Option.some.inj (Option.some.inj h)).symm | cases h

private theorem ncWord_eq {e : Event} {f : BitVec 64 → D} {d' : D}
    (h : ncWord e f = some (some d')) : ∃ x, d' = f x := by
  unfold ncWord at h; split at h
  · split at h
    · exact ⟨_, (Option.some.inj (Option.some.inj h)).symm⟩
    · cases h
    · cases h
  · cases h

private theorem poll_eq {e : Event} {d d' : D} {s : Site} (h : poll e d s = some (some d')) :
    d' = d ∨ d' = { d with site := s } := by
  unfold poll at h; split at h
  · obtain rfl := Option.some.inj (Option.some.inj h)
    split
    · exact .inr rfl
    · exact .inl rfl
  · cases h

private theorem tcLoad_eq {e : Event} {d d' : D} {s : Site} (h : tcLoad e d s = some (some d')) :
    d' = { d with site := s } := by
  unfold tcLoad at h; split at h
  · exact (Option.some.inj (Option.some.inj h)).symm
  · cases h

/-- **Only the end of the warpgroup leads to the deallocation or the return.** -/
theorem succ_end {d d' : D} {e : Event} (hn : succ P L g w d e = some (some d'))
    (hd : d.site ≠ .dealloc) : Mid d'.site ∨ d' = finish w d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases s
  case dealloc => exact absurd rfl hd
  case exit => simp [succ] at hn
  case sink => obtain rfl := dataRd_eq hn; exact afterSink_mid _
  case vm | mld => obtain rfl := dataRd_eq hn; exact .inl ⟨by simp, by simp⟩
  case eld => obtain rfl := dataRd_eq hn; exact .inl (afterEld_mid _)
  case lenA => obtain ⟨x, rfl⟩ := ncWord_eq hn; exact .inl (afterA_mid _)
  case lenB => obtain ⟨x, rfl⟩ := ncWord_eq hn; exact .inl ⟨by simp, by simp⟩
  case wv | wq | wsv => rcases poll_eq hn with rfl | rfl <;> exact .inl ⟨by simp, by simp⟩
  case sld a k =>
    fin_cases k <;> simp only [succ] at hn <;> obtain rfl := tcLoad_eq hn <;>
      exact .inl ⟨by simp, by simp⟩
  case rld c | old c => obtain rfl := tcLoad_eq hn; exact .inl ⟨by simp, by simp⟩
  case pld k =>
    simp only [succ] at hn
    split at hn
    · split at hn <;> obtain rfl := Option.some.inj (Option.some.inj hn)
      · exact .inl ⟨by simp, by simp⟩
      · exact .inl (getD_mid (by decide) (by decide))
    · cases hn
  case vote =>
    simp only [succ] at hn
    split at hn
    · obtain rfl := Option.some.inj (Option.some.inj hn); exact .inl ⟨by simp, by simp⟩
    · cases hn
  case oel k =>
    simp only [succ] at hn
    split at hn
    · obtain rfl := Option.some.inj (Option.some.inj hn)
      split
      · exact .inl ⟨by simp, by simp⟩
      · exact .inl (nextChunk_mid _ _)
    · cases hn
  case arrS =>
    simp only [succ] at hn
    split at hn <;> obtain rfl := Option.some.inj (Option.some.inj hn) <;>
      exact .inl ⟨by simp, by simp⟩
  all_goals simp only [succ, Option.some.injEq] at hn
  all_goals subst hn
  case smr => exact afterSmr_mid _
  case arrL => exact .inl (loopEntry_mid _)
  case pst k => exact .inl (getD_mid (by decide) (by decide))
  case ost k => exact .inl (elemNext_mid ⟨by simp, by simp⟩ (getD_mid (by decide) (afterOst_mid _)))
  case rstw k => exact .inl (getD_mid (by decide) (by decide))
  case ost2 c k =>
    exact .inl (elemNext_mid ⟨by simp, by simp⟩ (getD_mid (by simp [Mid]) ⟨by simp, by simp⟩))
  case obar k => exact .inl (afterObar_mid _ _)
  case otma k => exact .inl (nextChunk_mid _ _)
  case ebar => exact .inr rfl
  all_goals exact .inl ⟨by simp, by simp⟩

/-- **Only the deallocation's event is a paired operation.** -/
theorem tmemOp_site {d : D} {e : Event} (hev : Ev P L g w d e) (h : Tmem.Pair.isTmemOp e = true) :
    d.site = .dealloc := by
  obtain ⟨pc, kd⟩ := e
  obtain ⟨grp, dst, act, rfl⟩ : ∃ grp dst act, kd = .tc (.resource grp dst act) := by
    cases kd <;> simp [Tmem.Pair.isTmemOp] at h
    rename_i c
    cases c <;> simp at h
    exact ⟨_, _, _, rfl⟩
  obtain ⟨-, hE⟩ := hev
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases s <;> simp [EvK, TcLdEv, TcStEv, GWrAt, RdAt, WrAt, GenWrAt, NcEv, PollEv, ArrEv] at hE ⊢

/-- **The count is kept by every step without undefined behaviour.** -/
theorem tmemAt_step {d d' : D} {e : Event} {t : Nat} (hT : TmemAt w d t) (hev : Ev P L g w d e)
    (hn : succ P L g w d e = some (some d')) (hub : ∀ f, e.kind ≠ .ub f) :
    TmemAt w d' (t + if Tmem.Pair.isTmemOp e then 1 else 0) := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  by_cases hd : s = .dealloc
  · subst hd
    have hk : Tmem.Pair.isTmemOp e = true := by
      obtain ⟨-, hE⟩ := hev
      rcases hE with hk | ⟨f, hk⟩
      · simp [Tmem.Pair.isTmemOp, hk]
      · exact absurd hk (hub f)
    simp only [succ, Option.some.injEq] at hn
    subst hn
    obtain ⟨hc, rfl⟩ := hT
    simp [TmemAt, hk, hc]
  · have hk : Tmem.Pair.isTmemOp e = false := by
      cases h : Tmem.Pair.isTmemOp e
      · rfl
      · exact absurd (tmemOp_site hev h) hd
    have hx : s ≠ .exit := by
      rintro rfl
      simp [succ] at hn
    simp only [TmemAt, hd, hx, ↓reduceIte, hk, Bool.false_eq_true, Nat.add_zero] at hT ⊢
    rcases succ_end hn hd with ⟨h1, h2⟩ | rfl
    · simp [h1, h2, hT]
    · unfold finish
      cases hc : scmpi .ne .b w 0 <;> simp [hT, hc]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
