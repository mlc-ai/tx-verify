-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Writes

@[expose] public section

/-! # No MMA read of a Tensor Memory cell is unordered with a writer of the cell -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {A : List Assumption}

/-- **ScoreDonePv**: a QK MMA writing a cell a later PV MMA of its thread reads as A is done
before that PV MMA. -/
def ScoreDonePv (L : Launch) (X : Execution) : Prop :=
  ∀ {w x : EvId} {cell : Cell}, X.MmaCell w cell → X.MmaACell x cell → w.1 = x.1 → w.2 < x.2 →
    DoneBefore L X w x

/-- **No MMA read of a Tensor Memory cell is unordered with a writer of the cell.** -/
theorem no_reads_unsafe (ht : ScoreFacts L X) (ho : OAccFacts L X) (hT : TcOrders L X) (hsp :
    ScoreDonePv L X) : ¬ ReadsUnsafe L X := by
  refine fun hn => hn (readsSafe_iff.mpr ⟨fun x w cell hrd hw => ?_,
    fun x w cell ha hw => ?_, fun x w cell hsh _ => ?_⟩)
  · obtain ⟨d, s, mask, row, col, hi, hcell⟩ := hrd
    have hx : X.MmaCell x cell := ht.mma_reads hi hcell
    rcases tmemWrite_of_no_copy ht.no_cp ht.no_shift hw with hwm | hws
    · rcases mm_order ht hx hwm with h | h | h
      · exact .inl h
      · exact .inr (.inr (h.elim (fun h => .inr (.inl h)) fun h => .inr (.inr h)))
      · exact .inr (.inl (.inl h))
    · rcases ms_order ht ho hT hx hws with h | h
      · exact .inr (.inr (h.elim (fun h => .inr (.inl h)) fun h => .inr (.inr h)))
      · exact .inr (.inl (.inr (.inl h)))
  swap
  · obtain ⟨sp, hsp, -⟩ := hsh
    exact (ht.no_shift _ _ hsp).elim
  obtain ⟨d, s, acc, mask, index, b, hi, hac⟩ := id ha
  obtain ⟨c0, hc0⟩ := ht.mma_cell hi
  obtain ⟨hgx, -, st, hst, h | h⟩ := ht.mma_cells hi
  · have hnone := ht.qk_smem hst hi hc0 (h c0 hc0).1
    simp [aCell, hnone] at hac
  obtain ⟨hO, -⟩ := h c0 hc0
  obtain ⟨-, hsc, hsome, hcells⟩ := ht.pv_polls hi hc0 hO
  obtain ⟨hPc, hcc, hhigh⟩ := hcells index cell b hac
  have hxm : IsMma X x := ⟨_, _, _, _, hi⟩
  rcases tmemWrite_of_no_copy ht.no_cp ht.no_shift hw with hwm | hws
  · obtain ⟨-, -, hlw, -⟩ := mma_region ht hwm
    obtain ⟨dw, sw, aw, mw, -, -, hwi, -⟩ := id hwm
    have hthr : w.1 = x.1 := ht.tc_one ⟨_, _, _, _, hwi⟩ (.inl hxm) (by rw [← hlw, ← hcc])
    rcases Nat.lt_trichotomy w.2 x.2 with hlt | heq | hgt
    · exact .inr (.inl (.inl (.inl (hsp hwm ha hthr hlt))))
    · exact .inl (Prod.ext hthr.symm heq.symm)
    · exact .inr (.inr (.inr (.inr (.inl
        (Pipelined.of_aRead_po hi hsome hwi hgx hthr.symm hgt)))))
  obtain ⟨a', vals', j', hs', hj', hceq⟩ := ht.storeCell hws
  obtain ⟨g, k⟩ := w
  dsimp only at hs' hj' hceq ⊢
  obtain ⟨hh, h12⟩ := ht.tc_role (.inr hs')
  by_cases h8 : Prologue.warpIndex L g < 8
  · have hP' := (ht.soft_st hh h8 hs').1 j' hj'
    rw [← hceq] at hP'
    have hst' : Prologue.warpIndex L g / 4 = st := by
      unfold InP at hP' hPc
      omega
    have hcx : x.1 / L.block = g / L.block := by rw [← hcc, hceq]; rfl
    by_cases hu : sPolls L X g st k ≤ pPolls L X x.1 st x.2
    · refine .inr (.inl (.inr (.inl (hT.p_done hh h8 hs' hxm hcx
        (by rw [hst']; exact hu) fun hhi => ?_))))
      have hc' := hhi j' hj'
      rw [← hceq, hst'] at hc'
      rw [hst', hhigh hc']
      exact hu
    · obtain ⟨pcs, hsg⟩ := id hs'
      refine .inr (.inr (.inr (.inl (hT.s_done hh h8 hxm
        hcx ?_ (len_of_get hsg)))))
      rw [hst']
      omega
  · obtain ⟨st', -, hO', -⟩ := ho.corr_st hh (by omega) h12 hs'
    have := hO' j' hj'
    rw [← hceq] at this
    unfold InO at this
    unfold InP at hPc
    omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
