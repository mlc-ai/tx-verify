-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Values
public import Lemmas.Kernel.Memory

@[expose] public section

/-! # The output of a complete execution

In a complete execution every thread has exited (no cluster is canceled: no cancellation request
is issued), after its whole trace (`complete_m`). The writes of global memory are the threads'
stores of their rows (`Wit.memWrites`), each byte written once: word `k` of thread `g`'s load,
`D[g][k]` (`ld_vals`). So the final memory holds `A * B` in `D` (`IsFinal.unique`), and every other
global byte its launch content (`IsFinal.unwritten`): `Post` holds (`result`). -/

namespace PTX.Kernels.TcGemm.Proof
open TcMma (byteInt s32)
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}

section
variable (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
  (hW : Wit A B D L.sharedBase X P m u)
include hpre hX hW

/-- In a complete execution every thread performed its whole trace. -/
theorem complete_m (hc : Complete L X) {g : Nat} (hg : g < 128) :
    m g = (fullE A B D L.sharedBase g (P g)).length := by
  have hT := threads_eq hpre
  obtain ⟨pc, hl⟩ : ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩ := by
    rcases hc.1 g (by omega) with ⟨-, req, ho⟩ | h
    · obtain ⟨i, s, targets, -, hi, -⟩ := hX.clc.canceled_has_issue ho
      exact (hW.no_clc hi).elim
    · exact h
  have hget : X.get (g, (X.tr g).length - 1) = some ⟨pc, .exit⟩ := by
    show (X.tr g)[(X.tr g).length - 1]? = _
    rw [← List.getLast?_eq_getElem?, hl]
  obtain ⟨-, hj, hpos⟩ := hW.exit hget
  have := hW.len g hg
  rw [hW.length g hg, u_nil hpre hX hW hg] at hj hpos
  rw [fullE_length] at this ⊢
  simp only [List.length_nil, Nat.add_zero] at hj hpos
  split_ifs at hpos this ⊢ <;> omega

/-- **A complete execution leaves `D = A * B`** and every other global byte unchanged. -/
theorem result_of (hc : Complete L X) {mf : FinalMem} (hf : IsFinal L mem0 X mf) :
    Post D a b mem0 mf := by
  have hT := threads_eq hpre
  intro l hsp
  obtain ⟨sp, cta, ad⟩ := l
  simp only at hsp; subst hsp
  -- the writes of global memory are the stores
  have wcases : ∀ w a' bs, X.MemWrites w a' bs → a'.Covers ⟨.global, cta, ad⟩ →
      ∃ g k, g < 128 ∧ k < 8 ∧ w = .thread (g, ldIdx g (P g) + 2 + k) ∧
        a' = stAcc D g k ∧ bs = stBytes (word (P g).vals k) := by
    intro w a' bs hw hcov
    rcases hW.memWrites hw with ⟨_, rfl, _⟩ | ⟨g, hg, k, hk, rfl, rfl, rfl⟩ |
      ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
    · simp [Acc.Covers, Loc.InRange, tslot] at hcov
    · exact ⟨g, k, hg, hk, rfl, rfl, rfl⟩
    · simp [Acc.Covers, Loc.InRange, sA] at hcov
    · simp [Acc.Covers, Loc.InRange, sB] at hcov
  split_ifs with hin
  · simp only at hin
    obtain ⟨rfl, h1, h2⟩ := hin
    set q := ad - D
    have hg : q / 32 < 128 := by omega
    have hk : q % 32 / 4 < 8 := by omega
    set g := q / 32
    set k := q % 32 / 4
    have hm := complete_m hpre hX hW hc hg
    have hld := ldIdx_eq (g := g) (P g)
    have hfl := fullE_length (A := A) (B := B) (D := D) (S := L.sharedBase) (g := g) (P g)
    have h14 : 14 ≤ (if g / 32 = 0 then 15 else 14) := by split_ifs <;> omega
    have hidx : ldIdx g (P g) + 2 + k < m g := by rw [hm, hfl]; omega
    have hw : X.Writes (g, ldIdx g (P g) + 2 + k) (stAcc D g k) (stBytes (word (P g).vals k)) :=
      ⟨(Site.st k).pc, by
        rw [hW.get_of_lt hg hidx, show ldIdx g (P g) + 2 + k = ldIdx g (P g) + 1 + (k + 1) by omega,
          fullAt_post]
        simp [postAt, show k + 1 < 9 by omega, stE]⟩
    have hcov : Acc.Covers (stAcc D g k) ⟨.global, 0, ad⟩ := by
      simp [Acc.Covers, Loc.InRange, stAcc]; omega
    rw [hf.unique (w := .thread _) (.inl hw) hcov (fun w' a' bs' hw' hcov' => by
      obtain ⟨g', k', hg', hk', rfl, rfl, rfl⟩ := wcases w' a' bs' hw' hcov'
      simp [Acc.Covers, Loc.InRange, stAcc] at hcov'
      have : g' = g ∧ k' = k := by omega
      obtain ⟨rfl, rfl⟩ := this
      rfl)]
    have hv := ld_vals hpre hX hW hg (by rw [hm, hfl]; omega) k hk
    have hword : word (P g).vals k = s32 (dot a b g k) := by
      simp [word, List.getD_eq_getElem?_getD, hv]
    simp only [wbyte, hword, stAcc]
    rw [stBytes_of_bytes (by simp [s32, Value.bytes])]
    have hq : ad - (D + 32 * g + 4 * k) = q % 4 := by omega
    rw [hq, Value.toBytes, List.getElem?_map,
      List.getElem?_range (by simp [s32, Value.bytes]; omega)]
    rfl
  · simp only at hin
    rw [hf.unwritten]
    intro w a' bs hw hcov
    obtain ⟨g, k, hg, hk, rfl, rfl, rfl⟩ := wcases w a' bs hw hcov
    simp [Acc.Covers, Loc.InRange, stAcc] at hcov
    exact hin ⟨by omega, by omega, by omega⟩

end

/-- **A complete execution leaves the specified output.** -/
theorem result (hpre : Pre L A B D a b mem0) (ht : ThreadFacts L A B D X)
    (hX : Consistent L kernel [] mem0 X) (hc : Complete L X) {mf : FinalMem}
    (hf : IsFinal L mem0 X mf) : Post D a b mem0 mf := by
  obtain ⟨P, m, u, hW⟩ := wit hpre ht hX
  exact result_of hpre hX hW hc hf

end

end PTX.Kernels.TcGemm.Proof
