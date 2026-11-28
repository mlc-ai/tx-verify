-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.BiasEntry
public import Kernels.InklingRelDecode.Proof.Common.DataOrdinal
public import Kernels.InklingRelDecode.Proof.Common.EndTime
public import Kernels.InklingRelDecode.Proof.Iface.BarRows.Base

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

private def gated (p : Nat) (s : Prologue.Site) : Bool :=
  match s.block with
  | some b => decide (b.val < p)
  | none => true

private def orderOk (p : Nat) : Bool :=
  Prologue.allSites.all fun s => Prologue.allSites.all fun s' =>
    !(gated p s && gated p s' && Prologue.preloadSync s &&
      decide (Prologue.preloadPosition p s' ≤ Prologue.preloadPosition p s)) ||
    (decide (Prologue.allSites.idxOf s' ≤ Prologue.allSites.idxOf s) &&
      (Prologue.allSites.idxOf s' != Prologue.allSites.idxOf s || s' == s))

private def posOk (p : Nat) : Bool :=
  Prologue.allSites.all fun s =>
    !(gated p s && Prologue.preloadSync s) || decide (Prologue.preloadPosition p s ≤ 2 + 5 * p)

private theorem pos_all : ∀ p < 4, posOk p = true := by decide +kernel

private def syncOk : Bool :=
  Prologue.allSites.all fun s => !decide (s.pc ∈ BarRow.halfZeroSites) || Prologue.preloadSync s

private theorem sync_all : syncOk = true := by decide +kernel

private theorem order_all : ∀ p < 4, orderOk p = true := by decide +kernel

private theorem mem_all (s : Prologue.Site) : s ∈ Prologue.allSites := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem gated_of {p s} (gs : ∀ b : Fin 3, s.block = some b → b.val < p) :
    gated p s = true := by
  unfold gated
  split
  · rename_i b hb; simpa using gs b hb
  · rfl

/-- A prologue site at a half-CTA rendezvous pc is a preload rendezvous. -/
theorem sync_of_half {s : Prologue.Site} (h : s.pc ∈ BarRow.halfZeroSites) :
    Prologue.preloadSync s = true := by
  have := List.all_eq_true.mp sync_all s (mem_all s)
  simpa [h] using this

/-- The preload count of a CTA is at most three. -/
theorem preload_le_three (Q : Params) (L : Launch) (c : Nat) : Iface.preloadCount Q L c ≤ 3 :=
  Nat.min_le_left _ _

/-- **Prologue sites with no more rendezvous than a rendezvous site are no later than it**, and
equal only if they are it. -/
theorem pro_cmp {p : Nat} (hp : p ≤ 3) {d d' : Prologue.Control.D}
    (gs : ∀ b : Fin 3, d.site.block = some b → b.val < p)
    (gs' : ∀ b : Fin 3, d'.site.block = some b → b.val < p)
    (sync : Prologue.preloadSync d.site = true)
    (le : Prologue.preloadPosition p d'.site ≤ Prologue.preloadPosition p d.site) :
    Prologue.allSites.idxOf d'.site ≤ Prologue.allSites.idxOf d.site ∧
      (Prologue.allSites.idxOf d'.site = Prologue.allSites.idxOf d.site → d'.site = d.site) := by
  have ok := order_all p (by omega)
  unfold orderOk at ok
  have h1 := List.all_eq_true.mp ok d.site (mem_all _)
  have h2 := List.all_eq_true.mp h1 d'.site (mem_all _)
  simp only [gated_of gs, gated_of gs', sync, le, Bool.and_self, decide_true, Bool.not_true,
    Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at h2
  obtain ⟨a, b⟩ := h2
  refine ⟨a, fun e => ?_⟩
  rcases b with b | b
  · exact absurd e b
  · exact b

/-- **A rendezvous site of a preloaded block is before the Softmax entry.** -/
theorem pro_pos_le {p : Nat} (hp : p ≤ 3) {d : Prologue.Control.D}
    (gs : ∀ b : Fin 3, d.site.block = some b → b.val < p)
    (sync : Prologue.preloadSync d.site = true) :
    Prologue.preloadPosition p d.site ≤ 2 + 5 * p := by
  have ok := List.all_eq_true.mp (pos_all p (by omega)) d.site (mem_all _)
  simpa [gated_of gs, sync] using ok

end PTX.Kernels.InklingRelDecode.Proof
