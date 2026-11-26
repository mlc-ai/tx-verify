-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumBlk
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceE
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Pre103

@[expose] public section

/-! # The sink word along the trace

`InvSk l d`: the sink word of a state (`%r2422`, register 2880) is the word the trace's last
`setmaxnreg` (pc 103: `-inf`) or sink load (pc 156) left, as the events deliver it. The loop never
writes it, so a block's end carries it on (`w0_block_sk`). -/

/-! # The sink word passes through a block

The facts at the probability stores of a block (`f_ost`) carry the sink word of the block's start
(register 2880) unchanged: the loop never writes it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof
  PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

theorem w0_block_sk (x : BitVec 64) (b : Blk) : blkOst x b 2880 = b.sk := by
  unfold blkOst f_ost
  rw [lk_frame (K := w0KeepOst) (r := 2880) (by decide)
    (by simp only [pw_facts4, List.map_cons, List.map_nil]; decide) (by decide)]
  rw [w0c_fr_join 2880 (by decide), w0c_fr_vh 2880 (by decide)]
  unfold f_vote
  rw [lk_frame (K := [2880]) (r := 2880) (by decide)
    (by simp only [mld_facts1, List.map_cons, List.map_nil]; decide) (by decide)]
  rw [w0c_sc_mld 2880 (by decide), w0c_vm_car x b.m b.l b.mx b.sk b.lo b.hi b.mw 2880 (by decide)]
  simp [lookupD, f_car, List.lookup]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

structure InvSk (l : List Event) (d : D) : Prop where
  sk : d.b.sk = w0SkWord l

theorem site_pc_103 {s : Site} (h : s.pc = 103) : s = .smr := by
  cases s
  all_goals first
    | rfl
    | (exfalso; revert h; simp [Site.pc]; done)
    | (rename_i k; fin_cases k <;> (exfalso; revert h; simp [Site.pc]; done))
    | (rename_i a k; fin_cases a <;> fin_cases k <;> (exfalso; revert h; simp [Site.pc, ost2Base]))

theorem site_pc_156 {s : Site} (h : s.pc = 156) : s = .sink := by
  cases s
  all_goals first
    | rfl
    | (exfalso; revert h; simp [Site.pc]; done)
    | (rename_i k; fin_cases k <;> (exfalso; revert h; simp [Site.pc]; done))
    | (rename_i a k; fin_cases a <;> fin_cases k <;> (exfalso; revert h; simp [Site.pc, ost2Base]))

theorem w0SkWord_snoc (l : List Event) (e : Event) :
    w0SkWord (l ++ [e]) = (w0SkOf e).getD (w0SkWord l) := by
  unfold w0SkWord
  rw [List.filterMap_append]
  cases h : w0SkOf e <;> simp [h, List.filterMap]

theorem invSk_step {l : List Event} {d : D} {c' : Control.D} {e : Event} (hI : InvSk l d)
    (hpc : e.pc = d.c.site.pc) : InvSk (l ++ [e]) (dataNext L d c' e) := by
  by_cases hA : d.c.site = .arrS
  · refine ⟨?_⟩
    have h1 : e.pc ≠ 103 ∧ e.pc ≠ 156 := by rw [hpc, hA]; simp [Site.pc]
    have e1 : lookupD (wF (scX L) .arrS d.b) 2880 = blkOst (scX L) d.b 2880 := by
      unfold wF wcls
      exact lookupD_factsFrom (by decide)
    rw [w0SkWord_snoc, w0SkOf]
    simp only [h1.1, h1.2, ↓reduceIte, Option.getD_none]
    simp only [dataNext, hA]
    rw [e1, w0_block_sk, hI.sk]
  · refine ⟨?_⟩
    rw [dataNext_eq hA]
    dsimp only
    rw [w0SkWord_snoc]
    by_cases hs : d.c.site = .smr
    · have hp : e.pc = 103 := by rw [hpc, hs]; rfl
      simp [record, hs, w0SkOf, hp]
      rfl
    by_cases hk : d.c.site = .sink
    · have hp : e.pc = 156 := by rw [hpc, hk]; rfl
      have hn : e.pc ≠ 103 := by omega
      rw [w0SkOf]
      simp only [hp, ↓reduceIte]
      cases hek : e.kind with
      | nc a bs => simp [record, hk, hek]; rfl
      | _ => simp [record, hk, hek, hI.sk]
    · have h1 : e.pc ≠ 103 := fun h => hs (site_pc_103 (hpc ▸ h))
      have h2 : e.pc ≠ 156 := fun h => hk (site_pc_156 (hpc ▸ h))
      rw [w0SkOf]
      simp only [h1, h2, ↓reduceIte]
      simp only [Option.getD_none]
      have : (record d.c e d.b).sk = d.b.sk := by
        unfold record
        split <;> (try split) <;> first | rfl | (exfalso; simp_all)
      rw [this, hI.sk]

theorem invSk_pre {l : List Event} (h : ∀ f ∈ l, f.pc < 103) :
    InvSk l (code P L g w).init := by
  refine ⟨?_⟩
  have : l.filterMap w0SkOf = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro x hx
    have := h x hx
    have h1 : x.pc ≠ 103 := by omega
    have h2 : x.pc ≠ 156 := by omega
    simp [w0SkOf, h1, h2]
  show (code P L g w).init.b.sk = _
  rw [w0SkWord, this]; rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
