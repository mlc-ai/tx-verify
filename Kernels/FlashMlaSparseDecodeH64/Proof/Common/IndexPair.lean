-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLive
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Time

@[expose] public section

/-! # The index state at a pair load

From a thread state behind an event at a pair load of the index warp (pcs `2403`, `2429`, `2501`,
`2517`): the index state, its element and counters, the block the counters name, and the lane's
length words (`pair_state`). The state's invariant and event come from the caller (`Follow`'s
`ev_at`, or the step's own `JF`), so the lemma needs no `Follow`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem site_pc4 {s : IxSite}
    (h : s.pc = 2403 ∨ s.pc = 2429 ∨ s.pc = 2501 ∨ s.pc = 2517) :
    s = .pre ∨ s = .pf ∨ s = .xpre ∨ s = .xpf := by
  cases s <;> simp [IxSite.pc] at h ⊢

/-- **The state behind a pair load.** -/
theorem pair_state (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .nc a bs⟩)
    (hpc : pc = 2403 ∨ pc = 2429 ∨ pc = 2501 ∨ pc = 2517) {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g k = some (some σ)) (hJ : (table P L).J g σ)
    (hi : (thread P L g).inv σ) (hev : (table P L).Ev g σ ⟨pc, .nc a bs⟩)
    (hpcσ : pc = (thread P L g).pc σ) :
    ∃ (d : Index.D) (n : Cls → Nat) (i : Nat),
      σ = (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n) ∧ warp L g = 7 ∧ d.site.pc = pc ∧
      Index.EvK P L g d ⟨pc, .nc a bs⟩ ∧ d.el < 2 ∧ Index.Ctr P L g d.site d.c i ∧
      Index.blockOf L g (fun c => ((X.tr g).take k).countP (Index.cls c)) = i ∧
      d.c.l0 = lenWA P L (g / L.block) ∧ d.c.l1 = lenWB P L (g / L.block) := by
  have hr : 2332 ≤ pc ∧ pc < 2587 := by omega
  obtain ⟨d, n, rfl, hR, ⟨hpcE, hK⟩, hw⟩ := index_state hJ hi hev hpcσ hr
  have hR := hR (state_ub hX hσ he)
  have hc : (fun c => n (.index c)) = fun c => ((X.tr g).take k).countP (Index.cls c) :=
    funext fun c => state_count hσ (.index c)
  rw [hc] at hR
  obtain ⟨i, -, -, -, hrc, hct, -⟩ := hR (ix_take_noUb hX he)
  have hS := site_pc4 (s := d.site) (by dsimp only at hpcE; rw [← hpcE]; exact hpc)
  have hA : d.site ≠ .lenA := by rcases hS with h | h | h | h <;> rw [h] <;> simp
  have hB : d.site ≠ .lenB := by rcases hS with h | h | h | h <;> rw [h] <;> simp
  obtain ⟨h0, h1⟩ := ix_words_of hA hB (ix_ok hp hX hσ d n rfl).1
  obtain ⟨-, hel, -⟩ := ix_ok hp hX hσ d n rfl
  have hw0 : Index.incW d.site = 0 := by rcases hS with h | h | h | h <;> rw [h] <;> rfl
  rw [hw0] at hrc
  refine ⟨d, n, i, rfl, hw, hpcE.symm, hK, ?_, hct, Index.blockOf_eq hrc, h0, h1⟩
  have : d.site.elems = 2 := by rcases hS with h | h | h | h <;> rw [h] <;> rfl
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
