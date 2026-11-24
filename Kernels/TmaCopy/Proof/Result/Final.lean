-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmaCopy.Proof.Values
public import Lemmas.Kernel.Memory
public import Lemmas.Clc.ClcExecution

@[expose] public section

/-! # The output of a complete execution

In a complete execution thread 0 has exited (no cluster is canceled: no cancellation request is
issued), after its issue events, failed polls, a successful poll, the read of `buf`, which
returns the word `x`, and the write of `x` to `B` (`complete_trace`). That write is the only
write of `B` (`gB_unique`), so the final memory holds `x` there (`IsFinal.unique`), and no write
touches global memory outside `B` (`IsFinal.unwritten`): `Post` holds (`result`). -/

namespace PTX.Kernels.TmaCopy.Proof
open PTX PTX.Proof AsyncCopy
noncomputable section
variable {L : Launch} {A B : Nat} {x : Value} {mem0 : Mem0} {X : Execution}

theorem idx_tail {α : Type} (p t : List α) (w : α) (n k : Nat) :
    (p ++ List.replicate n w ++ t)[p.length + n + k]? = t[k]? := by
  rw [List.getElem?_append_right (by simp)]; simp

section
variable (hpre : Pre L A B x mem0) (ht : ThreadFacts L A B X) (hX : Consistent L kernel [] mem0 X)
include hpre ht hX

/-- **In a complete execution, thread 0 copied, polled, read and wrote `B` once, then exited.** -/
theorem complete_trace (hc : Complete L X) :
    ∃ n cs, X.tr 0 = issue A L.sharedBase ++ List.replicate n (waitE L.sharedBase false) ++
      [waitE L.sharedBase true, rdE L.sharedBase cs, wrE B x, exE] := by
  have h0 := threads_pos hpre
  obtain ⟨pc, hlast⟩ : ∃ pc, (X.tr 0).getLast? = some ⟨pc, .exit⟩ := by
    rcases hc.1 0 h0 with ⟨-, req, ho⟩ | h
    · obtain ⟨i, s, targets, -, hi, -⟩ := ClcOk.canceled_has_issue hX.clc ho
      exact (no_clc ht hX hi).elim
    · exact h
  have hget : X.get (0, (X.tr 0).length - 1) = some ⟨pc, .exit⟩ := by
    change (X.tr 0)[(X.tr 0).length - 1]? = _
    rw [← List.getLast?_eq_getElem?, hlast]
  have hk := get_lt hget
  rcases state_cases ht hX hget with ⟨s, hσ⟩ | hσ
  · have hev := ht.event h0 hget hσ
    have hJ := ht.along h0 hk.le hσ
    cases s with
    | exit =>
      rcases hJ with ⟨hne, -⟩ | ⟨-, n, cs, v, hp, hv, hb⟩
      · exact absurd rfl hne
      have htr : X.tr 0 = issue A L.sharedBase ++ List.replicate n (waitE L.sharedBase false) ++
          [waitE L.sharedBase true, rdE L.sharedBase cs, wrE B v, exE] := by
        have h1 := List.take_append_getLast (X.tr 0) (List.ne_nil_of_length_pos (by omega))
        rw [List.getLast_eq_getElem] at h1
        rw [← h1, List.take_eq_take_iff.mpr rfl, hp]
        have : (X.tr 0)[(X.tr 0).length - 1] = exE := by
          have := hget
          change (X.tr 0)[(X.tr 0).length - 1]? = _ at this
          rw [List.getElem?_eq_getElem (by omega)] at this
          rw [Option.some.inj this]
          exact hev
        simp [this]
      have hrd : X.get (0, 4 + n + 1) = some (rdE L.sharedBase cs) := by
        show (X.tr 0)[4 + n + 1]? = _
        rw [htr]; exact idx_tail (issue A L.sharedBase) _ _ n 1
      have hcs := read_bytes hpre ht hX ⟨Flow.load_0, hrd⟩
      rw [hcs, rebuild_scalar (by have := hpre.atom.1; omega) (hpre.atom.2 0 (by decide))] at hv
      cases hv
      exact ⟨n, cs, htr⟩
    | wait => obtain ⟨ok, h⟩ := hev; simp [waitE] at h
    | load => obtain ⟨bs, h⟩ := hev; simp [rdE] at h
    | store v => rcases hev with ⟨-, h⟩ | ⟨-, f, h⟩ <;> simp [wrE] at h
    | _ => simp [SiteEvent, initE, fenceE, arriveE, bulkE] at hev
  · obtain ⟨pc', f, bs, h, -⟩ := ht.dead h0 hget hσ
    simp at h

omit hpre in
/-- The only write of `B`. -/
theorem gB_unique {n : Nat} {cs : List (Option Byte)}
    (hX0 : X.tr 0 = issue A L.sharedBase ++ List.replicate n (waitE L.sharedBase false) ++
      [waitE L.sharedBase true, rdE L.sharedBase cs, wrE B x, exE])
    {w : EvId} {bs' : List Byte} (hw : X.Writes w { loc := gB B, size := 4 } bs') :
    w = (0, 4 + n + 2) := by
  have h0 := (writes_cases ht hX hw).1
  obtain ⟨g, j⟩ := w
  simp only at h0; subst h0
  obtain ⟨pc, hp⟩ := hw
  have hj : (X.tr 0)[j]? = some ⟨pc, .wr { loc := gB B, size := 4 } bs'⟩ := hp
  rw [hX0] at hj
  by_cases hlt : j < 4 + n
  · rw [List.getElem?_append_left (by simp [issue]; omega)] at hj
    have hm := List.mem_of_getElem? hj
    simp only [List.mem_append, List.mem_replicate] at hm
    rcases hm with hm | ⟨-, hm⟩
    · simp [issue, initE, fenceE, arriveE, bulkE] at hm
    · simp [waitE] at hm
  · rw [List.getElem?_append_right (by simp [issue]; omega)] at hj
    simp only [List.length_append, List.length_replicate] at hj
    have hpre4 : (issue A L.sharedBase).length = 4 := rfl
    rw [hpre4] at hj
    obtain ⟨k, rfl⟩ : ∃ k, j = 4 + n + k := ⟨j - (4 + n), by omega⟩
    rw [show 4 + n + k - (4 + n) = k by omega] at hj
    rcases k with _ | _ | _ | _ | k <;> simp [waitE, rdE, exE] at hj
    rfl

/-- **A complete execution leaves `x` in `B` and every other global byte unchanged.** -/
theorem result (hc : Complete L X) {m : FinalMem} (hfin : IsFinal L mem0 X m) :
    Post B x mem0 m := by
  intro l hlg
  obtain ⟨n, cs, hX0⟩ := complete_trace hpre ht hX hc
  have hat := hpre.atom
  have hw : X.Writes (0, 4 + n + 2) { loc := gB B, size := 4 } x.toBytes := by
    refine ⟨Flow.store_0, ?_⟩
    show (X.tr 0)[4 + n + 2]? = _
    rw [hX0]; exact idx_tail (issue A L.sharedBase) _ _ n 2
  split_ifs with hl
  · obtain ⟨h1, h2, h3⟩ := hl
    have hcov : Acc.Covers { loc := gB B, size := 4 } l := by
      simp only [Acc.Covers, Loc.InRange, gB]; exact ⟨hlg, h1, h2, by omega⟩
    rw [hfin.unique (w := .thread (0, 4 + n + 2)) (.inl hw) hcov fun w' a' bs' hw' hc' => by
      rcases memWrites_cases ht hX hw' with ⟨i, rfl, rfl, hwi⟩ | ⟨_, rfl, _⟩
      · exact congrArg Ref.thread (gB_unique ht hX hX0 hwi)
      · simp [Acc.Covers, Loc.InRange, buf, hlg] at hc']
    have hk : l.addr - B < 4 := by omega
    simp only [wbyte, gB]
    simp [Value.toBytes, hat.1, List.getElem?_range hk, hat.2 _ hk]
  · apply hfin.unwritten
    intro w a bs' hw' hcov
    rcases memWrites_cases ht hX hw' with ⟨i, _, rfl, _⟩ | ⟨_, rfl, _⟩
    · apply hl
      simp only [Acc.Covers, Loc.InRange, gB] at hcov
      exact ⟨hcov.2.1.symm ▸ rfl, hcov.2.2.1, hcov.2.2.2⟩
    · simp [Acc.Covers, Loc.InRange, buf, hlg] at hcov

end

end

end PTX.Kernels.TmaCopy.Proof
