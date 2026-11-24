-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderScanVisits
public import Kernels.TmlFa4Fwd.Proof.LoaderEntry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Mma Epilogue

noncomputable section

private def loaderScan (j : Fin 2) : GroupScan :=
  if j.val = 0 then .loaderSelect else .loaderDrain

private def setupPc (j : Fin 2) : Nat := (scanSite (loaderScan j)).head - 3

private def setupFacts (j : Fin 2) (batch cta : Nat) : List (Nat × Value) :=
  let site := scanSite (loaderScan j)
  [(site.cta, b32 cta), (site.batch, b32 batch)]

private theorem scanSeed {l : Launch} {g batch cta : Nat} (j : Fin 2)
    (hCta : cta + 1 < 2 ^ 31) :
    Seg kernel Assumptions.all l g 2 (setupPc j) (setupFacts j batch cta) (setupPc j + 2)
      (groupScanFacts (loaderScan j) 0 batch cta) := by
  have hCore : Seg kernel [] l g 2 (setupPc j) (setupFacts j batch cta) (setupPc j + 2)
      (groupScanFacts (loaderScan j) 0 batch cta) := by
    fin_cases j <;> dsimp only [setupPc, setupFacts, groupScanFacts, loaderScan, scanSite] <;>
      intro t ht <;> seg_fp ht using norm_bits
  intro t ht
  obtain ⟨u, hu, hU⟩ := hCore t ht
  have hStraight : ((kernel.code.drop (setupPc j)).take 1).all
      (fun i => schedulerFallsThrough i.op) = true := by
    fin_cases j <;> set_option maxRecDepth 100000 in decide +kernel
  have hTransport := loaderLinear (regs := []) (by fin_cases j <;> decide)
    (by fin_cases j <;> decide) ht.1 (List.all_eq_true.mpr (fun _ _ => rfl)) hStraight hu
  exact ⟨u, hTransport.1, hU⟩

set_option maxRecDepth 100000 in
private theorem scanBranch {l : Launch} {g batch cta : Nat} (j : Fin 2)
    (hBatch : batch + 31 < 2 ^ 31) (hCta : cta + 1 < 2 ^ 31)
    {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s (setupPc j) (setupFacts j batch cta))
    (hw : Walk kernel Assumptions.all l g s es vs) :
    loaderVisitsAt ((scanSite (loaderScan j)).compare + 2) vs ≤ 8 * (batch + 1) + 2 := by
  let scan := loaderScan j
  let site := scanSite scan
  let branch := site.compare + 2
  have hLo : 174 ≤ setupPc j + 2 := by fin_cases j <;> decide
  have hHi : site.head ≤ 1901 := by fin_cases j <;> decide
  have hBefore : setupPc j + 2 ≤ site.head ∧ site.head < branch := by
    fin_cases j <;> decide
  have hTarget : ∃ i, kernel.code[site.head]? = some i ∧ i.op.isLocal = true := by
    fin_cases j
    · exact ⟨_, Flow.code_234, rfl⟩
    · exact ⟨_, Flow.code_1794, rfl⟩
  have hCode : ((kernel.code.drop (setupPc j + 2)).take (site.head - (setupPc j + 2))).all
      (fun i => loaderPipelineCutOp (setupPc j + 2) site.head branch
        ((groupScanFacts scan 0 batch cta).map Prod.fst) i.op) = true := by
    fin_cases j
    · change ((kernel.code.drop 233).take 1).all
        (fun i => loaderPipelineCutOp 233 234 287 [7165, 7170, 1075, 1072] i.op) = true
      set_option maxRecDepth 100000 in decide +kernel
    · change ((kernel.code.drop 1793).take 1).all
        (fun i => loaderPipelineCutOp 1793 1794 1847 [7190, 7145, 1173, 1072] i.op) = true
      set_option maxRecDepth 100000 in decide +kernel
  have hBack : loaderBackEdges.all (fun (pc, target) => !(branch < pc && target ≤ branch))
      = true := by fin_cases j <;> decide
  obtain ⟨u, hRun, hU⟩ := scanSeed j hCta s hs
  rcases loaderLocalWalkCut hRun hw with hShort | ⟨pre, tail, rfl, hN, hTail⟩
  · exact (loaderVisitsAt_le_length ..).trans (by omega)
  · have hc := loaderPrefixThroughCounter (F := groupScanFacts scan 0 batch cta)
      hLo hHi hBefore.2 hTarget hCode
      (fun hAt hW => loaderScanBranchBudget j hBatch hCta hAt hW)
      (fun hp hW => noLaterLoaderCounter hp hBack hW) hTail
      (by rw [hU.1]; exact ⟨le_rfl, hBefore.1⟩) (ringShapeOfAt hU) hU.2.2.2.2
    change loaderVisitsAt branch tail ≤ 8 * (batch + 1) at hc
    have hu := loaderVisitsAt_le_append branch pre tail
    change loaderVisitsAt branch (pre ++ tail) ≤ _
    omega

private theorem loaderDrainBatch {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g cta : Nat} : Seg kernel Assumptions.all l g 1 1744 [(1072, b32 cta)]
      1745 (setupFacts 1 p.batch cta) := by
  intro t ht
  obtain ⟨hBatch, hParam⟩ := hp.values (19, p.batch) (by simp [Params.scalarWords])
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at hParam
  rw [loaderParam19Name] at hParam
  let u := next (setReg t 7145 (b32 p.batch))
  have hRule : execLocalA [] l g t
      (kernel.code[1744]?.getD (⟨none, .exit⟩ : Instr)).op = .ok u := by
    rw [Flow.code_1744, Option.getD_some, execLocalA_nil, execLocal_mem rfl]
    simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq, hParam,
      DType.width, MemExt.extendBits_same, pure, Except.pure, truncBits_ofNat hBatch (by decide)]
    rfl
  have hRun : run kernel [] l g 1 t = some u := by
    rw [Flow.code_1744, Option.getD_some] at hRule
    simp only [run, tauStep, out, ht.1, ht.2.2.2.1, Flow.code_1744, guardHolds, pure, Except.pure,
      hRule]
    rfl
  have hTrans := loaderLinear (regs := []) (by decide) (by decide) ht.1
    (List.all_eq_true.mpr (fun _ _ => rfl)) rfl hRun
  have hPc : u.pc = 1745 := by change t.pc + 1 = 1745; rw [ht.1]
  have hC : u.regs 1072 = some (b32 cta) := ht.2.2.2.2.1
  have hB : u.regs 7145 = some (b32 p.batch) := by simp [u, next, setReg]
  exact ⟨u, hTrans.1, hPc, ht.2.1, ht.2.2.1, ht.2.2.2.1, hC, hB, trivial⟩

private theorem loaderSelectScan {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g cta : Nat} (hCta : cta + 1 < 2 ^ 31)
    {s : TState} {es : List Event} {vs : List Visit} (hs : At s 179 (setupFacts 0 p.batch cta))
    (hw : Walk kernel Assumptions.all l g s es vs) :
    loaderVisitsAt 287 vs ≤ 8 * (p.batch + 1) + 2 := by
  have hBatch : p.batch + 31 < 2 ^ 31 := by have := hp.shape.2.2.2.2.2; omega
  have hCode : ((kernel.code.drop 179).take (231 - 179)).all
      (fun i => loaderPipelineCutOp 179 231 287 [1072, 7170] i.op) = true := by
    set_option maxRecDepth 100000 in decide +kernel
  exact loaderPrefixThroughCounter (lower := 179) (cut := 231) (branch := 287)
    (F := setupFacts 0 p.batch cta)
    (by decide) (by decide) (by decide) ⟨_, Flow.code_231, rfl⟩ hCode
    (fun hAt hW => scanBranch 0 hBatch hCta hAt hW)
    (fun hPc hW => noLaterLoaderCounter hPc (by decide) hW) hw
    (by rw [hs.1]; decide) (ringShapeOfAt hs) hs.2.2.2.2

private theorem loaderDrainScan {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g cta : Nat} (hCta : cta + 1 < 2 ^ 31)
    {s : TState} {es : List Event} {vs : List Visit} (hs : At s 179 [(1072, b32 cta)])
    (hw : Walk kernel Assumptions.all l g s es vs) :
    loaderVisitsAt 1847 vs ≤ 8 * (p.batch + 1) + 3 := by
  have hBatch : p.batch + 31 < 2 ^ 31 := by have := hp.shape.2.2.2.2.2; omega
  have hEarly : ((kernel.code.drop 179).take (1744 - 179)).all
      (fun i => loaderPipelineCutOp 179 1744 1847 [1072] i.op) = true := by
    set_option maxRecDepth 100000 in decide +kernel
  have hLater : ((kernel.code.drop 1745).take (1791 - 1745)).all
      (fun i => loaderPipelineCutOp 1745 1791 1847 [1072, 7145] i.op) = true := by
    set_option maxRecDepth 100000 in decide +kernel
  have hPast {u : TState} {events : List Event} {visits : List Visit}
      (hu : 1847 < u.pc) (hw : Walk kernel Assumptions.all l g u events visits) :
      loaderVisitsAt 1847 visits = 0 := noLaterLoaderCounter hu (by decide) hw
  apply loaderPrefixThroughCounter (lower := 179) (cut := 1744) (branch := 1847)
    (F := [(1072, b32 cta)])
    (by decide) (by decide) (by decide) ⟨_, Flow.code_1744, rfl⟩ hEarly _ (@hPast)
    hw (by rw [hs.1]; decide) (ringShapeOfAt hs) hs.2.2.2.2
  intro v events visits hV hWalk
  obtain ⟨w, hw, hW⟩ := loaderDrainBatch hp v hV
  rcases loaderLocalWalkCut hw hWalk with hShort | ⟨pre, tail, rfl, hN, hTail⟩
  · exact (loaderVisitsAt_le_length ..).trans (by omega)
  · have hb := loaderPrefixThroughCounter (lower := 1745) (cut := 1791) (branch := 1847)
      (F := setupFacts 1 p.batch cta)
      (by decide) (by decide) (by decide) ⟨_, Flow.code_1791, rfl⟩ hLater
      (fun hAt hW => scanBranch 1 hBatch hCta hAt hW) (@hPast) hTail
      (by rw [hW.1]; decide) (ringShapeOfAt hW) hW.2.2.2.2
    have hu := loaderVisitsAt_le_append 1847 pre tail
    omega

/-- After the actual loader dispatch and ABI batch load, the two scheduler loops
are bounded regardless of the bytes read by their request searches. -/
theorem loaderSearchBounds {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) (warp : Fin 16) (hw : 14 ≤ warp.val) {s : TState}
    {es : List Event} {vs : List Visit} (hs : At s 174 (loaderBarrierFacts p l g warp.val))
    (hWalk : Walk kernel Assumptions.all l g s es vs) :
    loaderVisitsAt 287 vs ≤ 8 * (p.batch + 1) + 7 ∧
      loaderVisitsAt 1847 vs ≤ 8 * (p.batch + 1) + 8 := by
  have hGrid := (Nat.div_lt_iff_lt_mul (show 0 < l.block by rw [hp.block]; decide)).2 hg
  have hCta : g / l.block + 1 < 2 ^ 31 := (Nat.succ_le_of_lt hGrid).trans_lt hp.grid.2.2
  obtain ⟨u, hr, hu⟩ := loaderDispatch hp hg warp hw hs
  rcases loaderLocalWalkCut hr hWalk with hShort | ⟨pre, tail, rfl, hN, hTail⟩
  · constructor <;> exact (loaderVisitsAt_le_length ..).trans (by omega)
  · have hRegs := hu.2.2.2.2
    have h1 := loaderSelectScan hp hCta (hu.mono ⟨hRegs.2.1, hRegs.1, trivial⟩) hTail
    have h2 := loaderDrainScan hp hCta (hu.mono ⟨hRegs.2.1, trivial⟩) hTail
    have hBefore1 := loaderVisitsAt_le_append 287 pre tail
    have hBefore2 := loaderVisitsAt_le_append 1847 pre tail
    constructor <;> omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
