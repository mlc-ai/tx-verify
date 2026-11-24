-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.NamedBarrierSites
public import Kernels.TmlFa4Fwd.Proof.NamedBarrierBias
public import Kernels.TmlFa4Fwd.Proof.CorrectionNamedBarrierIds
public import Kernels.TmlFa4Fwd.Proof.SoftmaxNamedBarrierIds
public import Lemmas.Protocol.NamedBarSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Proof Prologue

noncomputable section

/-- Statistics barrier `3 + w` joins softmax warp `w` to its correction warp. -/
def statsParticipants (softmaxWarp : Fin 8) : Finset Nat :=
  {softmaxWarp.val, 8 + softmaxWarp.val % 4}

/-- Each statistics rendezvous requires exactly the producer and correction warps. -/
theorem statsBarrierShape {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (w : Fin 8) :
    NamedBar.Shape l (some 64) (statsParticipants w) (3 + w.val) := by
  have hCard : (statsParticipants w).card = 2 := by fin_cases w <;> decide
  obtain ⟨n, hn⟩ := w
  refine ⟨by omega, ?_, ?_, by omega⟩
  · rw [hp.block, hCard]
    rfl
  · intro v hv
    simp only [statsParticipants, Finset.mem_insert, Finset.mem_singleton] at hv
    rw [hp.block]
    rcases hv with rfl | rfl <;> omega

private theorem barrierPcFamily {pc : Nat} (h : pc ∈ namedBarrierSites) :
    pc = 173 ∨ namedBarrierCount pc = some 416 ∨ (pc = 3583 ∨ pc = 5271) ∨
      pc ∈ Softmax.softmaxStatsSites ∨ ∃ stage : Fin 2, pc ∈ Correction.correctionStatsSites stage
    := by
  simp only [namedBarrierSites, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact .inl rfl
    | exact .inr (.inl rfl)
    | exact .inr (.inr (.inl (.inl rfl)))
    | exact .inr (.inr (.inl (.inr rfl)))
    | exact .inr (.inr (.inr (.inl (by decide))))
    | exact .inr (.inr (.inr (.inr ⟨0, by decide⟩)))
    | exact .inr (.inr (.inr (.inr ⟨1, by decide⟩)))

private theorem correctionWarpOfStats {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {e : Event} {i : EvId} (he : X.get i = some e) {stage : Fin 2}
    (hPc : e.pc ∈ Correction.correctionStatsSites stage) :
    8 ≤ warpIndex l i.1 ∧ warpIndex l i.1 < 12 := by
  have hLate : 7747 ≤ e.pc ∧ e.pc < 9205 := by
    fin_cases stage <;> simp [Correction.correctionStatsSites] at hPc <;> omega
  have hNotHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX (g := i.1) he (by omega) hNotHint
  unfold roleBodyPc at hRole
  split_ifs at hRole <;> omega

/-- All records of a statistics rendezvous come from its two decoded warps with count 64. -/
theorem statsBarrierSources {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (w : Fin 8) :
    NamedBar.Sources l X (some 64) (statsParticipants w) (3 + w.val) := by
  intro e pc count hArrive hg
  obtain ⟨mode, he⟩ := hArrive
  obtain ⟨hPc, hCount, _, _, _, hZero, hTwo⟩ := actualNamedBarrier hp hX he
  have hw := w.isLt
  rcases barrierPcFamily hPc with h | h | h | h | ⟨stage, h⟩
  · have := hZero h
    omega
  · have := hTwo (hCount.trans h)
    omega
  · rcases h with rfl | rfl
    · have hId := actualBiasBarrierId hp hX false hg he
      omega
    · have hId := actualBiasBarrierId hp hX true hg he
      omega
  · have hId := Softmax.actualSoftmaxStatsBarrierId hp hX h he
    have hWarp : warpIndex l e.1 = w.val := by omega
    have hC : namedBarrierCount pc = some 64 := by
      simp only [Softmax.softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> rfl
    refine ⟨?_, hCount.trans hC⟩
    change warpIndex l e.1 ∈ statsParticipants w
    simp [hWarp, statsParticipants]
  · have hId := Correction.actualCorrectionStatsBarrierId hp hX stage h he
    have hWarp := correctionWarpOfStats hp hX he (stage := stage) h
    have hC : namedBarrierCount pc = some 64 := by
      fin_cases stage <;> simp [Correction.correctionStatsSites] at h <;>
        rcases h with rfl | rfl | rfl <;> rfl
    refine ⟨?_, hCount.trans hC⟩
    change warpIndex l e.1 ∈ statsParticipants w
    apply Finset.mem_insert_of_mem
    apply Finset.mem_singleton.mpr
    unfold Correction.statsBarrierId at hId
    have hs := stage.isLt
    omega


/-- The count of a frozen CTA barrier is determined by its actual ID. -/
def countOfBarrierId (id : Nat) : Option Nat :=
  if id = 0 then none else if id = 2 then some 416 else if id < 11 then some 64 else some 128

theorem actualNamedBarrierCountById {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {pc id : Nat} {count : Option Nat} {mode : BarMode}
    (he : X.get i = some ⟨pc, .bar id count mode⟩) : count = countOfBarrierId id := by
  obtain ⟨hPc, hCount, _, _, hFull, hZero, hTwo⟩ := actualNamedBarrier hp hX he
  rcases barrierPcFamily hPc with h | h | h | h | ⟨stage, h⟩
  · rw [hZero h, hFull.mpr h]
    rfl
  · rw [hTwo (hCount.trans h), hCount, h]
    rfl
  · have hg := event_thread_lt hX he
    have hId : id = 11 ∨ id = 12 := by
      rcases h with rfl | rfl
      · exact actualBiasBarrierId hp hX false hg he
      · exact actualBiasBarrierId hp hX true hg he
    have hC : count = some 128 := by
      rcases h with rfl | rfl <;> exact hCount
    rw [hC]
    rcases hId with rfl | rfl <;> rfl
  · have hId := Softmax.actualSoftmaxStatsBarrierId hp hX h he
    have hRange : 3420 ≤ pc ∧ pc < 7742 := by
      simp only [Softmax.softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at h
      omega
    have hHint : pc ∉ registerHintSites := by
      simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    have hLate : 173 < (⟨pc, .bar id count mode⟩ : Event).pc := by
      change 173 < pc
      omega
    have hRole := roleBodyPcOfEvent hp hX (g := i.1) he hLate hHint
    change roleBodyPc (warpIndex l i.1) pc at hRole
    have hW : warpIndex l i.1 < 8 := by
      rcases hRole with hExit | hBody
      · omega
      · split_ifs at hBody <;> omega
    have hC : count = some 64 := by
      simp only [Softmax.softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> exact hCount
    simp [hC, countOfBarrierId, show id ≠ 0 by omega, show id ≠ 2 by omega, show id < 11 by omega]
  · have hId := Correction.actualCorrectionStatsBarrierId hp hX stage h he
    have hW := correctionWarpOfStats hp hX he (stage := stage) h
    have hs := stage.isLt
    unfold Correction.statsBarrierId at hId
    have hC : count = some 64 := by
      fin_cases stage <;> simp [Correction.correctionStatsSites] at h <;>
        rcases h with rfl | rfl | rfl <;> exact hCount
    simp [hC, countOfBarrierId, show id ≠ 0 by omega, show id ≠ 2 by omega, show id < 11 by omega]

/-- Any two arrivals on the same named barrier use the same count, including both modes. -/
theorem actualNamedBarrierCountAgrees {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i j : EvId} {pc pc' id : Nat} {count count' : Option Nat} {mode mode' : BarMode}
    (he : X.get i = some ⟨pc, .bar id count mode⟩)
    (hf : X.get j = some ⟨pc', .bar id count' mode'⟩) : count = count' :=
  (actualNamedBarrierCountById hp hX he).trans (actualNamedBarrierCountById hp hX hf).symm

end
end PTX.Kernels.TmlFa4Fwd
