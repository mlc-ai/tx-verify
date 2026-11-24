-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Safety.TcMmaWrites

@[expose] public section

/-! # The Tensor Memory read branch of `Unsafe`

Every MMA read of a Tensor Memory cell is ordered with every writer of the cell (`ReadsSafe`).

* **Accumulator reads.** An accumulating MMA reads its result cells, which it writes
  (`TcFacts.mma_reads`), so its reads are ordered as its writes (`mm_order`, `ms_order`).
* **A reads.** A PV MMA of tile `u` reads its A operand from its stage's probabilities
  (`ScoreFacts.pv_polls`; a QK MMA reads A from shared memory, `TcFacts.qk_smem`). A QK MMA
  writing such a cell is the same thread's (`ScoreFacts.tc_one`): issued after the PV MMA, it is
  the pipelined A-read/D-write pair of §9.7.18.6.2; issued before it, it is done before it
  (`ScoreDonePv`: its S-full commit is observed by the stage's softmax threads, whose P-ready
  arrival the MMA thread polls before the PV MMA). A softmax store of tile `u'` to the cell is done
  before the PV MMA when `u' ≤ u` (`TcOrders.p_done`, with the second P-ready object for the
  columns `112 …`), and comes after its completion when `u' > u`: the PV MMA precedes the S-full
  commit of tile `u + 1` (`ScoreFacts.pv_polls`), which the softmax thread observed before its
  store (`TcOrders.s_done`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX PTX.Proof TcMma

noncomputable section

variable {L : Launch} {X : Execution}

/-- **ScoreDonePv**: a QK MMA writing a cell a later PV MMA of its thread reads as A is done
before that PV MMA. -/
def ScoreDonePv (L : Launch) (X : Execution) : Prop :=
  ∀ {w x : EvId} {cell : Cell}, X.MmaCell w cell → X.MmaACell x cell → w.1 = x.1 → w.2 < x.2 →
    DoneBefore L X w x

/-- **No MMA read of a Tensor Memory cell is unordered with a writer of the cell.** -/
theorem no_reads_unsafe (ht : ScoreFacts L X) (ho : OAccFacts L X) (htc : TcFacts L X)
    (hT : TcOrders L X) (hsp : ScoreDonePv L X) : ¬ ReadsUnsafe L X := by
  refine fun hn => hn (readsSafe_iff.mpr ⟨fun x w cell hrd hw => ?_,
    fun x w cell ha hw => ?_, fun x w cell hsh _ => ?_⟩)
  · obtain ⟨d, s, mask, row, col, hi, hcell⟩ := hrd
    have hx : X.MmaCell x cell := htc.mma_reads hi hcell
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
  obtain ⟨c0, hc0⟩ := htc.mma_cell hi
  obtain ⟨hgx, -, -, st, hst, h | h⟩ := ht.mma_cells hi
  · have hnone := htc.qk_smem hst hi hc0 (h c0 hc0).1
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
  by_cases h8 : warpOf L g < 8
  · have hP' := (ht.soft_st hh h8 hs').1 j' hj'
    rw [← hceq] at hP'
    have hst' : warpOf L g / 4 = st := by
      unfold InP at hP' hPc
      omega
    have hcx : ctaOf L x.1 = leadCta (ctaOf L g) := by rw [← hcc, hceq]; rfl
    by_cases hu : sPolls L X g st k ≤ pPolls L X x.1 st x.2
    · refine .inr (.inl (.inr (.inl (hT.p_done hh h8 hs' hxm hcx
        (by rw [hst']; exact hu) fun hhi => ?_))))
      have hc' := hhi j' hj'
      rw [← hceq, hst'] at hc'
      rw [hst', hhigh hc']
      exact hu
    · obtain ⟨pcs, hsg⟩ := id hs'
      refine .inr (.inr (.inr (.inl (hT.s_done hh h8 hxm
        (by rw [hcx]; unfold leadCta; omega) ?_ (len_of_get hsg)))))
      rw [hst']
      omega
  · obtain ⟨st', -, hO', -⟩ := ho.corr_st hh (by omega) h12 hs'
    have := hO' j' hj'
    rw [← hceq] at this
    unfold InO at this
    unfold InP at hPc
    omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety
