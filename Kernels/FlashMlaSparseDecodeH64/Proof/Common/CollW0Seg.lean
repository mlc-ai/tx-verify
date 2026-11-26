-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollList

@[expose] public section

/-! # The elections of warpgroup 0 between its sites

The output chunks' elections are the warps 0 and 1's last four collectives, at the pcs
`1350, 1507, 1664, 1822` (`oel c`). A site's `seg` is the number of them before its pc
(`segOf_site`). A step of the machine adds one exactly at an election (`succ_seg`, for the warps
0 and 1, whose word `w` is at most `1`; a CTA is inside the batch); an election is reached only
from the same chunk's barrier, by the warps 0 and 1 (`succ_oel`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

/-- The number of the output chunks' elections before a pc. -/
def segOf (pc : Nat) : Nat := (([1350, 1507, 1664, 1822] : List Nat).filter (· < pc)).length

/-- A site is an election site. -/
def Site.isOel : Site → Bool
  | .oel _ => true
  | _ => false

/-- The chunk a site is in: the elections before it. -/
def Site.seg : Site → Nat
  | .old c | .oldw c | .ost2 c _ | .ofpx c | .obar c | .oel c => c.val
  | .otma c => c.val + 1
  | .commit | .ebar | .dealloc | .exit => 4
  | _ => 0

theorem segOf_site (s : Site) : segOf s.pc = s.seg := by
  cases s with
  | sld arm k => cases arm <;> fin_cases k <;> simp [segOf, Site.pc, Site.seg]
  | ost2 c k => fin_cases c <;> fin_cases k <;> simp [segOf, Site.pc, Site.seg, ost2Base]
  | pst k | pld k | ost k => fin_cases k <;> simp [segOf, Site.pc, Site.seg]
  | rld c | rldw c | rst c | rstw c | old c | oldw c | ofpx c | obar c | oel c | otma c =>
    fin_cases c <;> simp [segOf, Site.pc, Site.seg]
  | _ => simp [segOf, Site.pc, Site.seg]

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem dataRd_eq {e : Event} {d d' : D} (h : dataRd e d = some (some d')) : d' = d := by
  unfold dataRd at h
  split at h <;> simp_all

theorem poll_eq {e : Event} {d d' : D} {s : Site} (h : poll e d s = some (some d')) :
    d' = d ∨ d' = { d with site := s } := by
  obtain ⟨pc, kd⟩ := e
  cases kd <;> simp only [poll, reduceCtorEq, Option.some.injEq] at h
  split_ifs at h
  · exact .inr h.symm
  · exact .inl h.symm

theorem tcLoad_eq {e : Event} {d d' : D} {s : Site} (h : tcLoad e d s = some (some d')) :
    d' = { d with site := s } := by
  unfold tcLoad at h
  split at h <;> simp_all

theorem ncWord_eq {e : Event} {f : BitVec 64 → D} {d' : D} (h : ncWord e f = some (some d')) :
    ∃ x, d' = f x := by
  unfold ncWord at h
  split at h
  · split at h
    · rename_i x _
      simp only [Option.some.injEq] at h
      exact ⟨x, h.symm⟩
    · cases h
    · cases h
  · cases h

theorem nextChunk_seg (k : Fin 4) (d : D) : (nextChunk k d).site.seg = k.val + 1 := by
  fin_cases k <;> rfl

theorem getD_seg (l : List Site) (d : Site) (k a : Nat) (hl : ∀ s ∈ l, s.seg = a)
    (hd : d.seg = a) : (l.getD k d).seg = a := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : l[k]? with
  | none => simpa using hd
  | some s => simpa using hl s (List.mem_of_getElem? hk)

theorem succ_seg {d d' : D} {e : Event} (hw : scmpi .gt .s w 1 = false)
    (hb : scmp .ge .s (r2W L g) (pw P.b) = false) (h : succ P L g w d e = some (some d')) :
    d'.site.seg = d.site.seg + if d.site.isOel then 1 else 0 := by
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases site <;> simp only [succ] at h
  all_goals try (obtain rfl := dataRd_eq h)
  all_goals try (obtain rfl | rfl := poll_eq h)
  all_goals try (obtain rfl := tcLoad_eq h)
  all_goals try (obtain ⟨x, rfl⟩ := ncWord_eq h)
  all_goals try (simp only [Option.some.injEq] at h; subst h)
  all_goals simp only [afterSmr, afterSink, afterA, loopEntry, finish, afterObar,
    afterEld, elemNext, afterOst, hw, hb, Bool.false_eq_true, ite_false]
  all_goals simp only [Site.isOel, Bool.false_eq_true, ite_false, Nat.add_zero, ite_true]
  all_goals try (simp [Site.seg]; done)
  all_goals try (rw [getD_seg _ _ _ 0 (by simp [Site.seg]) (by simp [Site.seg])]
                 simp [Site.seg])
  all_goals try (split_ifs <;> simp [Site.seg]; done)
  all_goals try (split_ifs <;> first
    | (dsimp only; rw [getD_seg _ _ _ 0 (by simp [Site.seg]) (by simp [Site.seg])];
       simp [Site.seg]; done)
    | (simp [Site.seg]; done))
  case sld =>
    rename_i arm k
    revert h
    fin_cases k <;> intro h <;> simp only at h <;> (obtain rfl := tcLoad_eq h) <;>
      simp [Site.seg]
  case pld =>
    rename_i k
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp only [reduceCtorEq] at h
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
      first
      | (rw [getD_seg _ _ _ 0 (by simp [Site.seg]) (by simp [Site.seg])]; simp [Site.seg])
      | simp [Site.seg]
  case vote =>
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp only [reduceCtorEq] at h
    simp only [Option.some.injEq] at h
    subst h
    simp [Site.seg]
  case arrS =>
    simp only [advance] at h ⊢
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> simp [Site.seg]
  case ost2 =>
    rename_i c k
    split_ifs
    · simp [Site.seg]
    · dsimp only
      rw [getD_seg _ _ _ c.val (by simp [Site.seg]) (by simp [Site.seg])]
      simp [Site.seg]
  case oel =>
    rename_i c
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp only [reduceCtorEq] at h
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
      first
      | (rw [nextChunk_seg]; simp [Site.seg])
      | simp [Site.seg]
  case otma =>
    rw [nextChunk_seg]
    simp [Site.seg]
  case exit => cases h

/-- A site is an output chunk's barrier. -/
def Site.isObar : Site → Bool
  | .obar _ => true
  | _ => false

theorem getD_notOel (l : List Site) (d : Site) (k : Nat) (hl : ∀ s ∈ l, s.isOel = false)
    (hd : d.isOel = false) : (l.getD k d).isOel = false := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : l[k]? with
  | none => simpa using hd
  | some s => simpa using hl s (List.mem_of_getElem? hk)

theorem nextChunk_notOel (c : Fin 4) (d : D) : (nextChunk c d).site.isOel = false := by
  fin_cases c <;> rfl

/-- **Only the barrier of a chunk leads to its election**, in the warps 0 and 1. -/
theorem succ_oel {d d' : D} {e : Event} (hb : scmp .ge .s (r2W L g) (pw P.b) = false)
    (h : succ P L g w d e = some (some d')) (ho : d'.site.isOel = true) :
    d.site.isObar = true ∧ scmpi .gt .s w 1 = false := by
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases site <;> simp only [succ] at h
  all_goals try (obtain rfl := dataRd_eq h)
  all_goals try (obtain rfl | rfl := poll_eq h)
  all_goals try (obtain rfl := tcLoad_eq h)
  all_goals try (obtain ⟨x, rfl⟩ := ncWord_eq h)
  all_goals try (simp only [Option.some.injEq] at h; subst h)
  all_goals simp only [afterSmr, afterSink, afterA, loopEntry, finish, afterObar, nextChunk,
    afterEld, elemNext, afterOst, hb, Bool.false_eq_true, ite_false] at ho ⊢
  all_goals try (simp [Site.isOel, Site.isObar] at ho ⊢; done)
  all_goals try (split_ifs at ho <;> simp [Site.isOel, Site.isObar] at ho ⊢; done)
  all_goals try (split_ifs at ho <;> first
    | (dsimp only at ho
       rw [getD_notOel _ _ _ (by simp [Site.isOel]) (by simp [Site.isOel])] at ho
       cases ho)
    | (simp [Site.isOel] at ho; done))
  case sld =>
    rename_i arm k
    revert h
    fin_cases k <;> intro h <;> simp only at h <;> (obtain rfl := tcLoad_eq h) <;>
      simp [Site.isOel] at ho
  case pst =>
    rw [getD_notOel _ _ _ (by simp [Site.isOel]) (by simp [Site.isOel])] at ho
    cases ho
  case pld =>
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp only [reduceCtorEq] at h
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> (try dsimp only at ho) <;>
      first
      | (rw [getD_notOel _ _ _ (by simp [Site.isOel]) (by simp [Site.isOel])] at ho; cases ho)
      | simp [Site.isOel] at ho
  case vote =>
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp only [reduceCtorEq] at h
    simp only [Option.some.injEq] at h
    subst h
    simp [Site.isOel] at ho
  case rstw =>
    rw [getD_notOel _ _ _ (by simp [Site.isOel]) (by simp [Site.isOel])] at ho
    cases ho
  case arrS =>
    simp only [advance] at h
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> simp [Site.isOel] at ho
  case obar =>
    rename_i c
    split_ifs at ho with hh
    · dsimp only at ho
      rw [getD_notOel _ _ _ (by simp [Site.isOel]) (by simp [Site.isOel])] at ho
      cases ho
    · exact ⟨rfl, by simpa using hh⟩
  case oel =>
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp only [reduceCtorEq] at h
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
      first
      | (rw [nextChunk_notOel] at ho; cases ho)
      | simp [Site.isOel] at ho
  case otma =>
    rw [getD_notOel _ _ _ (by simp [Site.isOel]) (by simp [Site.isOel])] at ho
    cases ho
  case exit => cases h

/-- The barrier of a chunk leads to its election, in the warps 0 and 1. -/
theorem succ_obar {d d' : D} {e : Event} {c : Fin 4} (hw : scmpi .gt .s w 1 = false)
    (hs : d.site = .obar c) (h : succ P L g w d e = some (some d')) : d'.site = .oel c := by
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  simp only at hs
  subst hs
  simp only [succ, afterObar, hw, Bool.false_eq_true, ite_false, Option.some.injEq] at h
  subst h
  rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
