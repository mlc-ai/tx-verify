-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.CarryBase
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Pre103

@[expose] public section

/-! # The epilogue's reads along the trace

`InvE l d`: the peer's row-sum word (`pe`, the read at pc 1157, `%r1270`) and the accumulator words
(`o`, the last Tensor Memory load of the rescale chunks, pcs 716, 817, 918, 1019, or of the output
chunks, pcs 1201, 1361, 1519, 1676) of a state are the last such reads of the block in progress
(`w0Scan l`), as the events deliver them ("reads as"). A block restarts at the softmax-ready
arrival, which drops both. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

structure InvE (l : List Event) (d : D) : Prop where
  pe : d.b.pe = w0EpiPe (w0Scan l).2
  o : d.b.o = w0EpiO (w0Scan l).2

theorem site_pc_1157 {s : Site} (h : s.pc = 1157) : s = .eld := by
  cases s
  all_goals first
    | rfl
    | (exfalso; revert h; simp [Site.pc]; done)
    | (rename_i k; fin_cases k <;> (exfalso; revert h; simp [Site.pc]; done))
    | (rename_i a k; fin_cases a <;> fin_cases k <;> (exfalso; revert h; simp [Site.pc, ost2Base]))

theorem site_pc_oPcs {s : Site} (h : s.pc ∈ w0OPcs) :
    (∃ c, s = .rld c) ∨ ∃ c, s = .old c := by
  unfold w0OPcs at h
  cases s
  all_goals first
    | exact .inl ⟨_, rfl⟩
    | exact .inr ⟨_, rfl⟩
    | (exfalso; revert h; simp [Site.pc]; done)
    | (rename_i k; fin_cases k <;> (exfalso; revert h; simp [Site.pc]; done))
    | (rename_i a k; fin_cases a <;> fin_cases k <;> (exfalso; revert h; simp [Site.pc, ost2Base]))

theorem record_pe_rd {c : Control.D} {e : Event} {b : Blk} {a : Acc} {bs : List (Option Byte)}
    (hs : c.site = .eld) (hk : e.kind = .rd a bs) : (record c e b).pe = loadVal bs := by
  simp [record, hs, hk]

theorem record_pe_keep {c : Control.D} {e : Event} {b : Blk}
    (hs : c.site ≠ .eld ∨ ∀ a bs, e.kind ≠ .rd a bs) : (record c e b).pe = b.pe := by
  unfold record
  split <;> (try split) <;> simp_all

theorem record_o_ld {c : Control.D} {e : Event} {b : Blk} {a : Nat} {vals : List Value}
    {y : TcShape} (hs : (∃ c', c.site = .rld c') ∨ ∃ c', c.site = .old c')
    (hk : e.kind = .tc (.ld a vals y)) : (record c e b).o = vals := by
  rcases hs with ⟨c', h⟩ | ⟨c', h⟩ <;> simp [record, h, hk]

theorem record_o_keep {c : Control.D} {e : Event} {b : Blk}
    (hs : (∀ c', c.site ≠ .rld c') ∧ ∀ c', c.site ≠ .old c') : (record c e b).o = b.o := by
  obtain ⟨h1, h2⟩ := hs
  unfold record
  split <;> (try split) <;> simp_all

theorem record_o_nold {c : Control.D} {e : Event}
    {b : Blk} (hk : ∀ a vals y, e.kind ≠ .tc (.ld a vals y)) : (record c e b).o = b.o := by
  unfold record
  split <;> (try split) <;> simp_all

theorem w0Last_none_snoc {α : Type} (f : Event → Option α) (pcs : List Nat) (seg : List Event)
    (e : Event) (h : e.pc ∉ pcs ∨ f e = none) : w0Last f pcs (seg ++ [e]) = w0Last f pcs seg := by
  rw [w0Last_snoc]
  rcases h with h | h
  · simp [h]
  · simp [h]

theorem invE_step {l : List Event} {d : D} {c' : Control.D} {e : Event} (hI : InvE l d)
    (hpc : e.pc = d.c.site.pc) : InvE (l ++ [e]) (dataNext L d c' e) := by
  by_cases hA : d.c.site = .arrS
  · have hp : e.pc = w0ArrSPc := by rw [hpc, hA]; rfl
    have hsc : (w0Scan (l ++ [e])).2 = [] := by simp [w0Scan_snoc, hp]
    simp only [dataNext, hA]
    exact ⟨by dsimp only; rw [hsc]; simp [w0EpiPe, w0Last],
      by dsimp only; rw [hsc]; simp [w0EpiO, w0Last]⟩
  · have h1122 : e.pc ≠ w0ArrSPc := fun h => hA (site_pc_1122 (hpc ▸ h))
    have hsc : (w0Scan (l ++ [e])).2 = (w0Scan l).2 ++ [e] := by simp [w0Scan_snoc, h1122]
    rw [dataNext_eq hA]
    refine ⟨?_, ?_⟩
    · dsimp only
      rw [hsc]
      unfold w0EpiPe
      by_cases hs : d.c.site = .eld
      · have hp : e.pc = 1157 := by rw [hpc, hs]; rfl
        by_cases hk : ∃ a bs, e.kind = .rd a bs
        · obtain ⟨a, bs, hk⟩ := hk
          rw [record_pe_rd hs hk, w0Last_snoc]
          simp [hp, w0RdVal, hk, loadVal]
        · have hk' : ∀ a bs, e.kind ≠ .rd a bs := fun a bs h => hk ⟨a, bs, h⟩
          rw [record_pe_keep (.inr hk'), w0Last_none_snoc _ _ _ _ (.inr (by
            cases hk : e.kind <;> simp_all [w0RdVal]))]
          exact hI.pe
      · have hp : e.pc ≠ 1157 := fun h => hs (site_pc_1157 (hpc ▸ h))
        rw [record_pe_keep (.inl hs), w0Last_none_snoc _ _ _ _ (.inl (by simp [hp]))]
        exact hI.pe
    · dsimp only
      rw [hsc]
      unfold w0EpiO
      by_cases hs : (∃ c', d.c.site = .rld c') ∨ ∃ c', d.c.site = .old c'
      · have hp : e.pc ∈ w0OPcs := by
          rcases hs with ⟨c, hc⟩ | ⟨c, hc⟩ <;> rw [hpc, hc] <;> fin_cases c <;>
            simp [Site.pc, w0OPcs]
        by_cases hk : ∃ a vals y, e.kind = .tc (.ld a vals y)
        · obtain ⟨a, vals, y, hk⟩ := hk
          rw [record_o_ld hs hk, w0Last_snoc]
          simp [hp, w0TcVals, hk]
        · have hk' : ∀ a vals y, e.kind ≠ .tc (.ld a vals y) := fun a vals y h =>
            hk ⟨a, vals, y, h⟩
          rw [record_o_nold hk', w0Last_none_snoc _ _ _ _ (.inr (by
            unfold w0TcVals; split <;> simp_all))]
          exact hI.o
      · have hp : e.pc ∉ w0OPcs := fun h => hs (site_pc_oPcs (hpc ▸ h))
        rw [record_o_keep ⟨fun c h => hs (.inl ⟨c, h⟩), fun c h => hs (.inr ⟨c, h⟩)⟩,
          w0Last_none_snoc _ _ _ _ (.inl hp)]
        exact hI.o

theorem w0Last_pre {α : Type} (f : Event → Option α) (pcs : List Nat) (seg : List Event)
    (h : ∀ x ∈ seg, x.pc < 103) (hp : ∀ n ∈ pcs, 103 ≤ n) : w0Last f pcs seg = none := by
  unfold w0Last
  rw [List.getLast?_eq_none_iff, List.filterMap_eq_nil_iff]
  intro x hx
  have h1 := h x hx
  have : x.pc ∉ pcs := fun hm => by have := hp _ hm; omega
  simp [this]

theorem invE_pre {l : List Event} (h : ∀ f ∈ l, f.pc < 103) :
    InvE l (code P L g w).init := by
  have hs : (w0Scan l).2 = l := by rw [w0Scan_pre h]
  refine ⟨?_, ?_⟩
  · have hn := w0Last_pre w0RdVal [1157] l h (by simp)
    show (code P L g w).init.b.pe = _
    rw [w0EpiPe, hs, hn]; rfl
  · have hn := w0Last_pre w0TcVals w0OPcs l h (by simp [w0OPcs])
    show (code P L g w).init.b.o = _
    rw [w0EpiO, hs, hn]; rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
