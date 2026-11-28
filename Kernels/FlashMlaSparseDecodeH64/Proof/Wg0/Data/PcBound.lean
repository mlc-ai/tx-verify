-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.SuccPc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.CarryBase

@[expose] public section

/-! # The pcs of a block in progress stay below the machine's site

`PcBound l d`: every event of the block in progress after the trace `l` (`w0Fin`) at a pc of
warpgroup 0 (at least 103) is at a pc at most that of the machine's site. A step keeps it
(`pcBound_step`): the control machine goes forward, and the softmax-ready arrival (pc 1122)
closes the block. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- **The pcs of the block in progress** are at most the pc of the machine's site. -/
def PcBound (l : List Event) (d : D) : Prop :=
  ∀ a ∈ (w0Fin l).2, 103 ≤ a.pc → a.pc ≤ d.c.site.pc

theorem w0Fin_snoc_snd (l : List Event) (e : Event) (h : e.pc ≠ w0ArrSPc) :
    (w0Fin (l ++ [e])).2 = (w0Fin l).2 ++ [e] := by
  rw [w0Fin_snoc]
  have hne : w0ArrLPc ≠ w0ArrSPc := by unfold w0ArrLPc w0ArrSPc; decide
  by_cases h2 : e.pc = w0ArrLPc <;> simp [h, h2, hne]

theorem w0Fin_mem {l : List Event} {a : Event} (h : a ∈ (w0Fin l).2) : a ∈ l := by
  induction l using List.reverseRecOn with
  | nil => simp [w0Fin] at h
  | append_singleton l e ih =>
    by_cases h1 : e.pc = w0ArrSPc
    · rw [w0Fin_snoc] at h
      simp [h1] at h
    · rw [w0Fin_snoc_snd l e h1] at h
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ (ih h)
      · exact List.mem_append_right _ h

theorem pcBound_early {l : List Event} (d : D) (h : ∀ f ∈ l, f.pc < 103) : PcBound l d :=
  fun a ha h103 => absurd (h a (w0Fin_mem ha)) (by omega)

/-- **A step keeps the bound**: the event `ev` is at the machine's site. -/
theorem pcBound_step {l : List Event} {d : D} {c' : Control.D} {ev : Event} (hb : PcBound l d)
    (hpp : ev.pc = d.c.site.pc) (hc : Control.succ P L g (warpW L g) d.c ev = some (some c')) :
    PcBound (l ++ [ev]) (dataNext L d c' ev) := by
  intro a ha h103
  rw [dataNext_c]
  by_cases h1 : ev.pc = w0ArrSPc
  · rw [w0Fin_snoc] at ha
    simp [h1] at ha
  rw [w0Fin_snoc_snd l ev h1] at ha
  have hs : d.c.site ≠ .arrS := fun h => h1 (by rw [hpp, h]; rfl)
  have hmono := Control.succ_pc_mono hc hs
  rcases List.mem_append.mp ha with h | h
  · exact (hb a h h103).trans hmono
  · rw [List.mem_singleton.mp h, hpp]
    exact hmono

/-- **The exchange load and the epilogue's are seen**: in a state past the exchange load (pc 572,
up to the arrival) the block in progress has an event at pc 572; in a state of the epilogue past
its row-sum load (pc 1157) an event at pc 1157. -/
def PcSeen (l : List Event) (d : D) : Prop :=
  (572 < d.c.site.pc → d.c.site.pc ≤ 1122 → ∃ e ∈ (w0Fin l).2, e.pc = 572) ∧
    (1157 < d.c.site.pc → d.c.site.pc < 1840 → ∃ e ∈ (w0Fin l).2, e.pc = 1157)

theorem pcSeen_smr {l : List Event} {d : D} (h : d.c.site = .smr) : PcSeen l d := by
  refine ⟨fun h1 _ => ?_, fun h1 _ => ?_⟩ <;> rw [h] at h1 <;> simp [Site.pc] at h1

theorem pcSeen_step {l : List Event} {d : D} {c' : Control.D} {ev : Event} (hb : PcSeen l d)
    (hpp : ev.pc = d.c.site.pc) (hc : Control.succ P L g (warpW L g) d.c ev = some (some c')) :
    PcSeen (l ++ [ev]) (dataNext L d c' ev) := by
  rw [PcSeen, dataNext_c]
  by_cases h1 : ev.pc = w0ArrSPc
  · have hs : d.c.site = .arrS := site_pc_1122 (by rw [← hpp]; exact h1)
    rcases Control.succ_arrS hc hs with h | h <;> rw [h] <;>
      exact ⟨fun h2 h3 => by simp [Site.pc] at h2 h3, fun h2 h3 => by simp [Site.pc] at h2 h3⟩
  rw [w0Fin_snoc_snd l ev h1]
  have hs : d.c.site ≠ .arrS := fun h => h1 (by rw [hpp, h]; rfl)
  have hst := Control.succ_pc_step hc hs
  obtain ⟨hs1, hs2, hs3⟩ := hst
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨fun h2 h3 => ?_, fun h2 h3 => ?_⟩
  · by_cases hlt : d.c.site.pc ≤ 572
    · have : d.c.site.pc = 572 := by
        by_contra hne
        rcases hs2 (by omega) with h | h <;> omega
      exact ⟨ev, List.mem_append_right _ (by simp), by rw [hpp, this]⟩
    · obtain ⟨e, he, he'⟩ := hb1 (by omega) (by omega)
      exact ⟨e, List.mem_append_left _ he, he'⟩
  · by_cases hlt : d.c.site.pc ≤ 1157
    · have : d.c.site.pc = 1157 := by
        by_contra hne
        rcases hs3 (by omega) with h | h <;> omega
      exact ⟨ev, List.mem_append_right _ (by simp), by rw [hpp, this]⟩
    · obtain ⟨e, he, he'⟩ := hb2 (by omega) (by omega)
      exact ⟨e, List.mem_append_left _ he, he'⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
