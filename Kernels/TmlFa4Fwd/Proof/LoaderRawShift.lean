-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut
public import Kernels.TmlFa4Fwd.Proof.LoaderShiftPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

variable {l : Launch}

private theorem shiftCheckpoint {g lower cut budget : Nat} {s : TState} {es : List Event}
    {vs : List Visit} {F : List (Nat × Value)} (hLo : 174 ≤ lower) (hHi : cut < 401)
    (hTarget : ∃ ins, kernel.code[cut]? = some ins ∧ ins.op.isLocal = true)
    (hCode : ((kernel.code.drop lower).take (cut - lower)).all
      (fun ins => loaderPipelineCutOp lower cut 401 (F.map Prod.fst) ins.op) = true)
    (onTarget : ∀ {t ts tv}, At t cut F → Walk kernel Assumptions.all l g t ts tv →
      loaderVisitsAt 401 tv ≤ budget) (hw : Walk kernel Assumptions.all l g s es vs)
    (hp : lower ≤ s.pc ∧ s.pc ≤ cut) (hs : RingShape s) (hF : Holds s.regs F) :
    loaderVisitsAt 401 vs ≤ budget := by
  have step {t u : TState} {e : Option Event} {ts : List Event} {tv : List Visit}
      (hW : Walk kernel Assumptions.all l g u ts tv)
      (hFull : Walk kernel Assumptions.all l g t (e.toList ++ ts)
        (visit kernel l g t e :: tv))
      (hpc : lower ≤ t.pc ∧ t.pc ≤ cut) (ht : RingShape t) (hF : Holds t.regs F)
      (hStep : WStep kernel Assumptions.all l g t e u)
      (ih : (lower ≤ u.pc ∧ u.pc ≤ cut) → RingShape u → Holds u.regs F →
        loaderVisitsAt 401 tv ≤ budget) :
      loaderVisitsAt 401 (visit kernel l g t e :: tv) ≤ budget := by
    by_cases h : t.pc = cut
    · by_cases hf : t.fault = none
      · exact onTarget (pipelineAtCut h ht hF hf hTarget) hFull
      · rw [pipelineStopped hFull hf ⟨by omega, by omega⟩ (h.trans_lt hHi)]
        exact Nat.zero_le _
    have hc : t.pc < cut := by omega
    rw [visitsBeforeBranch ⟨by omega, by omega⟩ (hc.trans hHi)]
    obtain ⟨hU, hL | hR, hShape, hRegs⟩ :=
      pipelineCutStep hLo (by omega) ⟨hpc.1, hc⟩ hCode hStep ht hF
    · exact ih ⟨hU, hL⟩ hShape hRegs
    · rw [noLaterShiftBranchVisits hW hR]
      exact Nat.zero_le _
  induction hw with
  | stop => exact Nat.zero_le _
  | tau ht hw ih => exact step hw (.tau ht hw) hp hs hF (.inl ⟨rfl, ht⟩) ih
  | ev he hw ih => exact step hw (.ev he hw) hp hs hF (.inr ⟨_, rfl, he⟩) ih
  | last =>
    rw [visitsBeforeBranch ⟨by omega, by omega⟩ (hp.2.trans_lt hHi)]
    exact Nat.zero_le _

private theorem shiftSeg {g a n b : Nat} {F G : List (Nat × Value)} (hLo : 174 ≤ a)
    (hHi : a + n ≤ 1906)
    (hStraight : ((kernel.code.drop a).take (n - 1)).all
      (fun i => Epilogue.schedulerFallsThrough i.op) = true) (segment : Seg kernel [] l g n a F b G)
    :
    Seg kernel Assumptions.all l g n a F b G := by
  intro t ht
  obtain ⟨u, hr, hu⟩ := segment t ht
  exact ⟨u, (loaderLinear (regs := []) hLo hHi ht.1 (by simp) hStraight hr).1, hu⟩

private theorem shiftWiden {g : Nat} :
    Seg kernel Assumptions.all l g 1 355 [(1663, b32 16)] 356 [(7296, b64 16)] := by
  apply shiftSeg (by decide) (by decide) rfl
  intro s hs
  seg_fp hs using decide

private theorem shiftNarrow {g : Nat} :
    Seg kernel Assumptions.all l g 1 376 [(7296, b64 16)] 377 [(1798, b32 16)] := by
  apply shiftSeg (by decide) (by decide) rfl
  intro s hs
  seg_fp hs using decide

private def shiftFields (i : Nat) : List (Nat × Value) :=
  [(7171, b32 (2 ^ i)), (1059, .bits 16 (BitVec.ofNat 64 i)), (1798, b32 16)]

private theorem shiftSeed {g : Nat} :
    Seg kernel Assumptions.all l g 2 396 [(1798, b32 16)] 398 (shiftFields 1) := by
  apply shiftSeg (by decide) (by decide) (by set_option maxRecDepth 100000 in kernel_rfl)
  intro s hs
  simp only [shiftFields]
  seg_fp hs using decide

private theorem shiftIteration {g : Nat} (i : Fin 3) :
    Seg kernel Assumptions.all l g 4 398 (shiftFields (i.val + 1))
      (if i.val = 2 then 402 else 398) (shiftFields (i.val + 2)) := by
  apply shiftSeg (by decide) (by decide) (by set_option maxRecDepth 100000 in kernel_rfl)
  fin_cases i <;> intro s hs <;>
    simp only [shiftFields, show (0 : Nat) ≠ 2 by decide, ↓reduceIte] at hs ⊢ <;>
    seg_fp hs using decide

private theorem shiftFromSeed {g : Nat} :
    Seg kernel Assumptions.all l g 14 396 [(1798, b32 16)] 402 (shiftFields 4) :=
  shiftSeed.comp ((shiftIteration 0).comp ((shiftIteration 1).comp (shiftIteration 2)))

private theorem addShiftPrefix {g n pc budget : Nat} {s u : TState} {es : List Event}
    {vs : List Visit} {F : List (Nat × Value)} (hr : run kernel Assumptions.all l g n s = some u)
    (hu : At u pc F) (hw : Walk kernel Assumptions.all l g s es vs)
    (hEnd : ∀ {te tv}, At u pc F → Walk kernel Assumptions.all l g u te tv →
      loaderVisitsAt 401 tv ≤ budget) :
    loaderVisitsAt 401 vs ≤ n + budget := by
  rcases loaderLocalWalkCut hr hw with hShort | ⟨pre, tail, hTrace, hLen, hTail⟩
  · have h := loaderVisitsAt_le_length 401 vs
    omega
  rw [hTrace]
  have h := loaderVisitsAt_le_append 401 pre tail
  have hb := hEnd hu hTail
  omega

private theorem shiftPrefixCode :
    ((kernel.code.drop 174).take (355 - 174)).all
      (fun ins => loaderPipelineCutOp 174 355 401 [1663] ins.op) = true := by
  set_option maxRecDepth 100000 in decide +kernel

private theorem shiftWidenedCode :
    ((kernel.code.drop 356).take (376 - 356)).all
      (fun ins => loaderPipelineCutOp 356 376 401 [7296] ins.op) = true := by
  set_option maxRecDepth 100000 in decide +kernel

private theorem shiftNarrowedCode :
    ((kernel.code.drop 377).take (396 - 377)).all
      (fun ins => loaderPipelineCutOp 377 396 401 [1798] ins.op) = true := by
  set_option maxRecDepth 100000 in decide +kernel

private theorem shiftBoundAtSeed {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s 396 [(1798, b32 16)]) (hw : Walk kernel Assumptions.all l g s es vs) :
    loaderVisitsAt 401 vs ≤ 14 := by
  obtain ⟨u, hr, hu⟩ := shiftFromSeed s hs
  exact addShiftPrefix (budget := 0) hr hu hw (fun ht hb =>
    (noLaterShiftBranchVisits hb (by rw [ht.1]; decide)).le)

private theorem shiftBoundAtNarrow {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s 376 [(7296, b64 16)]) (hw : Walk kernel Assumptions.all l g s es vs) :
    loaderVisitsAt 401 vs ≤ 15 := by
  obtain ⟨u, hr, hu⟩ := shiftNarrow s hs
  apply addShiftPrefix (budget := 14) hr hu hw
  intro te tv ht hWalk
  exact shiftCheckpoint (F := [(1798, b32 16)]) (lower := 377) (cut := 396) (by decide) (by decide)
    ⟨_, Flow.code_396, rfl⟩ shiftNarrowedCode shiftBoundAtSeed hWalk
    (by rw [ht.1]; decide) (ringShapeOfAt ht) ht.2.2.2.2

private theorem shiftBoundAtWiden {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s 355 [(1663, b32 16)]) (hw : Walk kernel Assumptions.all l g s es vs) :
    loaderVisitsAt 401 vs ≤ 16 := by
  obtain ⟨u, hr, hu⟩ := shiftWiden s hs
  apply addShiftPrefix (budget := 15) hr hu hw
  intro te tv ht hWalk
  exact shiftCheckpoint (F := [(7296, b64 16)]) (lower := 356) (cut := 376) (by decide) (by decide)
    ⟨_, Flow.code_376, rfl⟩ shiftWidenedCode shiftBoundAtNarrow hWalk
    (by rw [ht.1]; decide) (ringShapeOfAt ht) ht.2.2.2.2

/-- The launch page-size word bounds the shift backedge on every actual loader prefix. -/
theorem loaderRawShiftBound {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s 174 [(1663, b32 16)]) (hw : Walk kernel Assumptions.all l g s es vs) :
    loaderVisitsAt 401 vs ≤ 16 :=
  shiftCheckpoint (F := [(1663, b32 16)]) (lower := 174) (cut := 355) (by decide) (by decide)
    ⟨_, Flow.code_355, rfl⟩ shiftPrefixCode shiftBoundAtWiden hw
    (by rw [hs.1]; decide) (ringShapeOfAt hs) hs.2.2.2.2

end
end PTX.Kernels.TmlFa4Fwd.Loader
