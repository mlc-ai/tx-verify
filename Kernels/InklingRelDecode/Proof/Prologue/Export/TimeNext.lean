-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Time
public import Kernels.InklingRelDecode.Proof.Prologue.Measure

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow Control

private theorem sorted : allSites.Pairwise (fun a b => a.rank < b.rank) := by decide +kernel

private theorem mem (s : Site) : s ∈ allSites := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem idx_lt {a b : Site} (h : a.rank < b.rank) :
    allSites.idxOf a < allSites.idxOf b := by
  have ia : allSites.idxOf a < allSites.length := List.idxOf_lt_length_iff.mpr (mem a)
  have ib : allSites.idxOf b < allSites.length := List.idxOf_lt_length_iff.mpr (mem b)
  have ea : allSites[allSites.idxOf a] = a := List.getElem_idxOf ia
  have eb : allSites[allSites.idxOf b] = b := List.getElem_idxOf ib
  rcases Nat.lt_trichotomy (allSites.idxOf a) (allSites.idxOf b) with lt | eq | gt
  · exact lt
  · exfalso
    have : a = b := by rw [← ea, ← eb]; congr 1
    subst this
    omega
  · exfalso
    have := List.pairwise_iff_getElem.mp sorted _ _ ib ia gt
    rw [ea, eb] at this
    omega

/-- **Every step of the prologue raises the clock.** -/
public theorem time_next {Q L g d dn ev} (hn : Control.next Q L g d ev = some (some dn)) :
    time d < time dn := by
  have := idx_lt (rank_next hn)
  unfold time
  omega

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
