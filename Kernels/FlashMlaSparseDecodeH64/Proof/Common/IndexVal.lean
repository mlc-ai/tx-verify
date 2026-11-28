-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.ValStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictIndexOrigin
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexPair
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.PairCore
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.PairWord
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Blocks
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLive
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLane

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow Index

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem thread_next_hsh_idx {n : Cls → Nat} {e : Event} {σ' : (thread P L g).D}
    {d' : Index.D} {n' : Cls → Nat}
    (h : (thread P L g).next (hshState P L g n) e = some (some σ'))
    (hσ' : σ' = idxState P L g d' n') : d' = ofC (ixFirst P L g) := by
  obtain ⟨h1, h2⟩ := Code.counted_next_some h
  rw [Code.glue_next_inr] at h1
  dsimp only [wg1Code, Code.roleLoop, Code.loopGlue, wg1HeadCode, Wg1.code] at h1
  simp only [Wg1.succ] at h1
  split at h1
  · rename_i md av bv cv recv ok hk
    simp only [Wg1.dispatch] at h1
    rw [hσ'] at h1
    split at h1
    · rename_i x
      split at h1
      · by_cases hg : subOk L g SubEntry.index = true
        · simp [Code.enter, Code.gatedExit, wg1Enter, Wg1.exitOf, subSel, hg] at h1
          exact h1.symm
        · simp [Code.enter, Code.gatedExit, wg1Enter, Wg1.exitOf, subSel, hg] at h1
      · split at h1
        · simp [Code.enter, Code.gatedExit, wg1Enter, Wg1.exitOf, subSel] at h1
          obtain ⟨h1, -⟩ := h1
          by_cases hg : subOk L g SubEntry.tma = true <;> simp [hg] at h1
        · split at h1
          · simp [Code.enter, Code.gatedExit, wg1Enter, Wg1.exitOf, subSel] at h1
            obtain ⟨h1, -⟩ := h1
            by_cases hg : subOk L g SubEntry.idle = true <;> simp [hg] at h1
          · simp [Code.enter, Code.gatedExit, wg1Enter, Wg1.exitOf, subSel] at h1
            obtain ⟨h1, -⟩ := h1
            by_cases hg : subOk L g SubEntry.mma = true <;> simp [hg] at h1
    · simp at h1
  · simp at h1

/-- The main cache's block count of the lane's length word is the data's. -/
theorem nMain_lane (hp : Pre P L m) {c : IxCtl} (h0 : c.l0 = lenWA P L (g / L.block)) :
    nMain c.l0 = FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g)) := by
  obtain ⟨hwa, -, -, hle, -⟩ := len_words hp (g / L.block)
  rw [rowOf_cta] at hwa hle
  rw [h0, hwa]
  exact nMain_val (by have := hp.topkAdd63Lt; omega)

/-- **A pair load's payload is the word of its position**: the lane's row at the position the
state's block, site and element name. -/
theorem ix_ldPay (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {d : Index.D} {n : Cls → Nat} {k i : Nat} {pc : Nat} {a : Acc}
    {bs : List (Option Byte)} (he : X.get (g, k) = some ⟨pc, .nc a bs⟩)
    (hσ : Frame.stateAt (thread P L) X g k = some (some (idxState P L g d n)))
    (hct : Ctr P L g d.site d.c i) (hld : isLd d.site = true) :
    rebuild 3 bs = .ok (.bits 32 (ixLdWord P L g d i)) := by
  obtain ⟨σ, hσ', hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he (fun fl h => by cases h)
  rw [hσ] at hσ'
  obtain rfl := Option.some.inj (Option.some.inj hσ')
  have hpc4 : pc = 2403 ∨ pc = 2429 ∨ pc = 2501 ∨ pc = 2517 := by
    have hp' : pc = d.site.pc := hpcσ
    obtain ⟨site, el, ac, c⟩ := d
    cases site <;> simp [isLd, IxSite.pc] at hld hp' ⊢ <;> omega
  obtain ⟨d', n', i', heq, -, hpd, hEv, hel, -, -, h0, h1⟩ :=
    pair_state hp hX he hpc4 hσ hJ hi hev hpcσ
  obtain ⟨rfl, rfl⟩ : d = d' ∧ n = n' := by
    simp only [idxState, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and]
      at heq
    exact ⟨heq.1, heq.2⟩
  have hM := nMain_lane hp h0
  obtain ⟨site, el, ac, c⟩ := d
  dsimp only at hpd hel hct h0 h1 hM ⊢
  cases site <;> simp [isLd] at hld
  · have hpc : pc = 2403 := by simpa [IxSite.pc] using hpd.symm
    obtain ⟨b, -, hb0, -, hlt, hsz, hloc⟩ := main_pair_core hp hpd hEv hel hct h0 (Or.inl hpc)
    rw [main_pair_word hp hX he (Or.inl hpc) hlt hsz hloc]
    have e : 64 * b + 2 * (tidOf L g % 32) + el = lane2 L g + el := by
      simp [lane2, hb0 hpc]
    simp only [ixLdWord, ixWdM, b32, e]
  · have hpc : pc = 2429 := by simpa [IxSite.pc] using hpd.symm
    obtain ⟨b, -, -, hb1, hlt, hsz, hloc⟩ := main_pair_core hp hpd hEv hel hct h0 (Or.inr hpc)
    rw [main_pair_word hp hX he (Or.inr hpc) hlt hsz hloc]
    have e : 64 * b + 2 * (tidOf L g % 32) + el = 64 * (i + 1) + lane2 L g + el := by
      simp [lane2, hb1 hpc]
    simp only [ixLdWord, ixWdM, b32, e]
  · have hpc : pc = 2501 := by simpa [IxSite.pc] using hpd.symm
    obtain ⟨b, -, hb0, -, hlt, hsz, hloc⟩ :=
      extra_pair_core hp hpd hEv hel hct h0 h1 (Or.inl hpc)
    rw [extra_pair_word hp hX he (Or.inl hpc) hlt hsz hloc]
    have e : 64 * b + 2 * (tidOf L g % 32) + el = lane2 L g + el := by
      simp [lane2, hb0 hpc]
    simp only [ixLdWord, ixWdX, b32, e]
  · have hpc : pc = 2517 := by simpa [IxSite.pc] using hpd.symm
    obtain ⟨b, -, -, hb1, hlt, hsz, hloc⟩ :=
      extra_pair_core hp hpd hEv hel hct h0 h1 (Or.inr hpc)
    rw [extra_pair_word hp hX he (Or.inr hpc) hlt hsz hloc]
    have hb := hb1 hpc
    rw [← hM] at hb
    have e : 64 * b + 2 * (tidOf L g % 32) + el =
        64 * (i + 1 - nMain c.l0) + lane2 L g + el := by
      simp only [lane2]; omega
    simp only [ixLdWord, ixWdX, b32, e]

/-- **The index warp's pair words** at every state of an index lane: the loops' counters are in
a block `i` of the lane's row and the pair words are the words of its positions. -/
theorem ix_val (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) :
    ∀ {k : Nat} {d : Index.D} {n : Cls → Nat},
      Frame.stateAt (thread P L) X g k = some (some (idxState P L g d n)) →
      ∃ i, Ctr P L g d.site d.c i ∧ IxV P L g d i := by
  intro k
  induction k with
  | zero =>
    intro d n h
    rw [Frame.stateAt_zero] at h
    have h1 := congrArg Prod.fst (Option.some.inj (Option.some.inj h))
    exact (enter_top_ne_index (s := (startupCode P L g).init) h1).elim
  | succ k ih =>
    intro d n h
    cases hg : (X.tr g)[k]? with
    | none =>
      have hl : (X.tr g).length ≤ k := List.getElem?_eq_none_iff.mp hg
      rw [Frame.stateAt_of_le (by omega), ← Frame.stateAt_of_le hl] at h
      exact ih h
    | some f =>
      rw [Frame.stateAt_succ hg] at h
      cases hs : Frame.stateAt (thread P L) X g k with
      | none => simp [hs] at h
      | some o =>
        rw [hs] at h
        cases o with
        | none => simp [Code.toMachine] at h
        | some σ0 =>
          rcases next_into_index h rfl with ⟨d0, n0, rfl⟩ | ⟨n0, rfl⟩
          · obtain ⟨i, hct, hV⟩ := ih hs
            obtain ⟨d3, n', hsucc, heq⟩ := thread_next_index h
            obtain ⟨rfl, -⟩ : d = d3 ∧ n = n' := by
              simp only [idxState, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq,
                true_and] at heq
              exact ⟨heq.1, heq.2⟩
            have hel := (ix_ok hp hX hs d0 n0 rfl).2.1
            refine ixv_step hp hel hct hV (fun ac bs hk hld => ?_) hsucc
            have hget : X.get (g, k) = some ⟨f.pc, .nc ac bs⟩ := by
              obtain ⟨pc', kd⟩ := f
              simp only at hk
              subst hk
              exact hg
            exact ix_ldPay hp hX hFw hget hs hct hld
          · obtain rfl := thread_next_hsh_idx h rfl
            exact ⟨0, ctr_first hp g, ixv_vac (vac_ixFirst P L g)⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
