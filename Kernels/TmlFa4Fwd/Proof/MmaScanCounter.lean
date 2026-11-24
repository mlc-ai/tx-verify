-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaModel
public import Kernels.TmlFa4Fwd.Flow.Code.Part003
public import Kernels.TmlFa4Fwd.Flow.Code.Part004
public import Kernels.TmlFa4Fwd.Flow.Code.Part027
public import Kernels.TmlFa4Fwd.Flow.Code.Part028
public import Kernels.TmlFa4Fwd.Flow.Code.Part031
public import Kernels.TmlFa4Fwd.Flow.Code.Part042
public import Kernels.TmlFa4Fwd.Flow.Code.Part044
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part049
public import Kernels.TmlFa4Fwd.Flow.Code.Part050
public import Kernels.TmlFa4Fwd.Flow.Code.Part119
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part122
public import Kernels.TmlFa4Fwd.Flow.Code.Part142
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

inductive GroupScan where
  | select
  | drain
  | epilogueSelect
  | epilogueDrain
  | softmaxSelect
  | softmaxDrain
  | correctionSelect
  | correctionDrain
  | loaderSelect
  | loaderDrain

structure ScanSite where
  head : Nat
  compare : Nat
  base : Nat
  batch : Nat
  sentinel : Nat
  advanced : Nat
  stopPred : Nat
  work : Nat
  carry : Nat
  testPred : Nat
  cta : Nat

def scanSite : GroupScan → ScanSite
  | .select => ⟨1988, 2039, 7199, 7203, 1182, 1183, 347, 7200, 7194, 360, 1072⟩
  | .drain => ⟨2696, 2747, 7215, 7149, 1196, 1197, 420, 7216, 7210, 433, 1072⟩
  | .epilogueSelect => ⟨2824, 2875, 7223, 7228, 1203, 1204, 278, 7224, 7218, 291, 1072⟩
  | .epilogueDrain => ⟨3032, 3083, 7235, 7147, 1210, 1211, 317, 7236, 7230, 330, 1072⟩
  | .softmaxSelect => ⟨3158, 3209, 7243, 7247, 1217, 1218, 451, 7244, 7238, 464, 1072⟩
  | .softmaxDrain => ⟨7666, 7717, 7265, 7151, 1607, 1608, 663, 7266, 7260, 676, 1606⟩
  | .correctionSelect => ⟨7810, 7861, 7273, 7277, 1619, 1620, 695, 7274, 7268, 708, 1618⟩
  | .correctionDrain => ⟨9133, 9184, 7285, 7153, 1658, 1659, 754, 7286, 7280, 767, 1618⟩
  | .loaderSelect => ⟨234, 285, 7165, 7170, 1075, 1076, 74, 7166, 7160, 87, 1072⟩
  | .loaderDrain => ⟨1794, 1845, 7190, 7145, 1173, 1174, 241, 7191, 7185, 254, 1072⟩

variable {l : Launch}

theorem scanRoleOut {g : Nat} {t : TState} (hLo : 1904 ≤ t.pc) (hHi : t.pc < 3101) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  by_cases hm : t.pc < 2768
  · exact out_eq_core hLo hm
  · exact Epilogue.epilogue_out_all_eq_nil (.inl ⟨by omega, by omega⟩)

private def coreScanInstruction (pair : Instr × Nat) : Bool :=
  Assumptions.coreOp pair.1.op && !Assumptions.swExp2Sites.contains pair.2 &&
    !Assumptions.tcLdDataflowSites.contains pair.2 && !Assumptions.delayedTmemSites.contains pair.2

private theorem nonMmaScanCore {g : Nat} {t : TState} (scan : GroupScan)
    (hScan : scan = .softmaxSelect ∨ scan = .softmaxDrain ∨
      scan = .correctionSelect ∨ scan = .correctionDrain ∨
      scan = .loaderSelect ∨ scan = .loaderDrain) (hLo : (scanSite scan).head - 3 ≤ t.pc)
    (hHi : t.pc < (scanSite scan).compare + 3) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  let lo := (scanSite scan).head - 3
  let hi := (scanSite scan).compare + 3
  have hAll : (((kernel.code.drop lo).take (hi - lo)).zipIdx lo).all coreScanInstruction =
      true := by
    rcases hScan with rfl | rfl | rfl | rfl | rfl | rfl <;>
      set_option maxRecDepth 100000 in kernel_rfl
  have hBound : hi ≤ kernel.code.length := by
    rcases hScan with rfl | rfl | rfl | rfl | rfl | rfl <;>
      set_option maxRecDepth 100000 in decide +kernel
  have hPc : t.pc < kernel.code.length := hHi.trans_le hBound
  let ins := kernel.code[t.pc]
  have hCode : kernel.code[t.pc]? = some ins := List.getElem?_eq_getElem hPc
  have hMem : (ins, t.pc) ∈ ((kernel.code.drop lo).take (hi - lo)).zipIdx lo := by
    apply List.mem_of_getElem? (i := t.pc - lo)
    have hLo' : lo ≤ t.pc := hLo
    have hHi' : t.pc < hi := hHi
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hLo', hCode]
    rfl
  have hc := List.all_eq_true.mp hAll _ hMem
  simp only [coreScanInstruction, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hc
  exact Assumptions.out_all_eq_nil hc.1.1.2 hc.1.2 hc.2 hCode hc.1.1.1

/-- Each frozen group-search slice uses the core local and event rules. -/
theorem groupScanOut (scan : GroupScan) {l : Launch} {g : Nat} {t : TState}
    (hLo : (scanSite scan).head - 3 ≤ t.pc) (hHi : t.pc < (scanSite scan).compare + 3) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  cases scan
  case softmaxSelect => exact nonMmaScanCore .softmaxSelect (.inl rfl) hLo hHi
  case softmaxDrain => exact nonMmaScanCore .softmaxDrain (.inr (.inl rfl)) hLo hHi
  case correctionSelect => exact nonMmaScanCore .correctionSelect (.inr (.inr (.inl rfl))) hLo hHi
  case correctionDrain =>
    exact nonMmaScanCore .correctionDrain (.inr (.inr (.inr (.inl rfl)))) hLo hHi
  case loaderSelect =>
    exact nonMmaScanCore .loaderSelect (.inr (.inr (.inr (.inr (.inl rfl))))) hLo hHi
  case loaderDrain =>
    exact nonMmaScanCore .loaderDrain (.inr (.inr (.inr (.inr (.inr rfl))))) hLo hHi
  all_goals
    simp only [scanSite] at hLo hHi
    exact scanRoleOut (by omega) (by omega)

/-- Transport a local segment inside a frozen group-search slice. -/
theorem groupScanLocalRun (scan : GroupScan) {l : Launch} {g pc n : Nat} {t u : TState}
    (hlo : (scanSite scan).head - 3 ≤ pc) (hhi : pc + n ≤ (scanSite scan).compare + 3)
    (hpc : t.pc = pc)
    (hStraight : ((kernel.code.drop pc).take (n - 1)).all
      (fun i => Epilogue.schedulerFallsThrough i.op) = true)
    (hRun : run kernel [] l g n t = some u) : run kernel Assumptions.all l g n t = some u :=
  Epilogue.schedulerLocalTransport (lo := pc) (len := n) hStraight
    (fun hLo hHi => groupScanOut scan (by omega) (by omega)) hRun hpc.ge (by omega)

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

private theorem advanceScanSegment {g old batch sentinel : Nat} (scan : GroupScan)
    (hAdvance : old + 31 < 2 ^ 31) (hBatch : batch < 2 ^ 31) :
    let site := scanSite scan
    Seg kernel [] l g 4 site.head
      [(site.base, b32 old), (site.batch, b32 batch), (site.sentinel, b32 sentinel)]
      (site.head + 4)
      [(site.advanced, b32 (old + 31)), (site.stopPred, .pred (decide (batch ≤ old + 31))),
      (site.base, b32 (min (old + 31) batch)), (site.work, b32 sentinel)] := by
  have hOld32 : old < 2 ^ 32 := by omega
  have hNext32 : old + 31 < 2 ^ 32 := by omega
  have hBatch32 : batch < 2 ^ 32 := by omega
  have hLit : truncBits 32 (BitVec.ofInt 64 31) = BitVec.ofNat 64 31 := rfl
  cases scan <;> dsimp only [scanSite] <;> intro t ht <;>
    seg_fp ht using
      simp only [b32, hLit, ← BitVec.ofNat_add, truncBits_ofNat hOld32 (by decide),
        truncBits_ofNat hNext32 (by decide), truncBits_ofNat hBatch32 (by decide), compare,
        Option.getD_some, signedWord hAdvance, signedWord hBatch, Int.ofNat_le, ge_iff_le]
      all_goals
        by_cases h : old + 31 < batch
        · simp [Nat.min_eq_left (Nat.le_of_lt h)]
          omega
        · simp [Nat.min_eq_right (Nat.le_of_not_lt h)]
          omega

private theorem advanceScanBranch (scan : GroupScan) :
    let site := scanSite scan
    kernel.code[site.head + 4]? = some ⟨some (site.stopPred, false), .bra site.compare false⟩ := by
  cases scan
  · exact Flow.code_1992
  · exact Flow.code_2700
  · exact Flow.code_2828
  · exact Flow.code_3036
  · exact Flow.code_3162
  · exact Flow.code_7670
  · exact Flow.code_7814
  · exact Flow.code_9137
  · exact Flow.code_238
  · exact Flow.code_1798

private theorem exhaustedSegment {g cta : Nat} (scan : GroupScan) (hCta : cta + 1 < 2 ^ 31) :
    let site := scanSite scan
    Seg kernel [] l g 2 site.compare [(site.work, b32 (cta + 1)), (site.cta, b32 cta)]
      (site.compare + 2) [(site.testPred, .pred false), (site.carry, b32 (cta + 1))] := by
  have hC32 : cta < 2 ^ 32 := by omega
  have hS32 : cta + 1 < 2 ^ 32 := by omega
  have hC31 : cta < 2 ^ 31 := by omega
  cases scan <;> dsimp only [scanSite] <;> intro s hs <;>
    seg_fp hs using
      simp only [compare, Option.getD_some, truncBits_ofNat hC32 (by decide),
        truncBits_ofNat hS32 (by decide), signedWord hC31, signedWord hCta, Int.ofNat_le,
        decide_eq_false (show ¬cta + 1 ≤ cta by omega)]

private theorem scanBackedge (scan : GroupScan) :
    let site := scanSite scan
    kernel.code[site.compare + 2]? = some ⟨some (site.testPred, false), .bra site.head false⟩ := by
  cases scan
  · exact Flow.code_2041
  · exact Flow.code_2749
  · exact Flow.code_2877
  · exact Flow.code_3085
  · exact Flow.code_3211
  · exact Flow.code_7719
  · exact Flow.code_7863
  · exact Flow.code_9186
  · exact Flow.code_287
  · exact Flow.code_1847

/-- The exhausted search saves CTA+1 as the terminal bound and cannot take the decoded backedge. -/
theorem exhaustedGroupScan {g cta : Nat} (scan : GroupScan) (hCta : cta + 1 < 2 ^ 31) {s : TState} :
    let site := scanSite scan
    At s site.compare [(site.work, b32 (cta + 1)), (site.cta, b32 cta)] →
    ∃ u, run kernel Assumptions.all l g 3 s = some u ∧
      At u (site.compare + 3) [(site.carry, b32 (cta + 1))] := by
  dsimp only
  intro hs
  let site := scanSite scan
  obtain ⟨v, hv, hV⟩ := exhaustedSegment (l := l) (g := g) scan hCta s hs
  have hStraight : ((kernel.code.drop site.compare).take 1).all
      (fun i => Epilogue.schedulerFallsThrough i.op) = true := by
    cases scan <;> set_option maxRecDepth 100000 in kernel_rfl
  have hRun₁ := groupScanLocalRun scan (by cases scan <;> decide) (by cases scan <;> decide)
    hs.1 hStraight hv
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    (scanBackedge scan) false hV hV.2.2.2.2.1 (by simp)
  have hRun₂ := groupScanLocalRun scan (by cases scan <;> decide) (by cases scan <;> decide)
    hV.1 rfl hu
  have hPc : u.pc = site.compare + 3 := by
    simpa only [Bool.false_eq_true, ↓reduceIte, Nat.add_assoc] using hU.1
  exact ⟨u, run_comp hRun₁ hRun₂, hPc, hU.2.1, hU.2.2.1, hU.2.2.2.1, hU.2.2.2.2.2⟩

/-- The register facts retained between group-search iterations. -/
def groupScanFacts (scan : GroupScan) (first batch cta : Nat) : List (Nat × Value) :=
  let site := scanSite scan
  [(site.base, b32 first), (site.batch, b32 batch),
   (site.sentinel, b32 (cta + 1)), (site.cta, b32 cta)]

/-- The group advance retains the selected ABI registers and computed group bounds. -/
theorem advanceGroupScanPreserving {g first batch cta : Nat} (scan : GroupScan)
    (hAdvance : first + 31 < 2 ^ 31) (hBatch : batch < 2 ^ 31) {s : TState} {F : List (Nat × Value)}
    (hw : ((kernel.code.drop (scanSite scan).head).take 5).all
      (fun i => (F.map Prod.fst).all fun r => !(writesRegs i.op).contains r) = true)
    (hs : At s (scanSite scan).head (groupScanFacts scan first batch cta ++ F)) :
    let site := scanSite scan
    ∃ u, run kernel Assumptions.all l g 5 s = some u ∧
      At u (if batch ≤ first + 31 then site.compare else site.head + 5)
        ((site.advanced, b32 (first + 31)) ::
          (site.work, b32 (cta + 1)) :: groupScanFacts scan (min (first + 31) batch) batch cta ++
          F) := by
  dsimp only
  let site := scanSite scan
  let frame := [(site.batch, b32 batch), (site.sentinel, b32 (cta + 1)), (site.cta, b32 cta)]
  have hsplit := hs.2.2.2.2
  rw [holds_append] at hsplit
  have hInitial := hsplit.1
  have hs' : At s site.head
      [(site.base, b32 first), (site.batch, b32 batch), (site.sentinel, b32 (cta + 1))] :=
    hs.mono ⟨hInitial.1, hInitial.2.1, hInitial.2.2.1, trivial⟩
  obtain ⟨v, hv, hV⟩ := advanceScanSegment (l := l) (g := g) (sentinel := cta + 1)
    scan hAdvance hBatch s hs'
  have hStraight : ((kernel.code.drop site.head).take 3).all
      (fun i => Epilogue.schedulerFallsThrough i.op) = true := by
    cases scan <;> set_option maxRecDepth 100000 in kernel_rfl
  have hWrites : ((kernel.code.drop site.head).take 4).all
      (fun i => (frame.map Prod.fst).all fun r => !(writesRegs i.op).contains r) = true := by
    cases scan <;> set_option maxRecDepth 100000 in kernel_rfl
  have hRegs : Holds v.regs frame := by
    apply Epilogue.holdsSchedulerFrame (regs := frame.map Prod.fst) hInitial.2
    · intro r hr
      apply Epilogue.schedulerLocalFrame hWrites hStraight hv
      · exact hs.1.ge
      · rw [hs.1]
      · exact hr
    · exact fun _ hp => List.mem_map_of_mem hp
  let pick := decide (batch ≤ first + 31)
  have hGuard : At v (site.head + 4)
      ((site.stopPred, .pred pick) :: (site.advanced, b32 (first + 31)) ::
        (site.work, b32 (cta + 1)) ::
        groupScanFacts scan (min (first + 31) batch) batch cta) :=
    hV.mono ⟨hV.2.2.2.2.2.1, hV.2.2.2.2.1, hV.2.2.2.2.2.2.2.1,
      hV.2.2.2.2.2.2.1, hRegs⟩
  have hRun₁ := groupScanLocalRun scan (by cases scan <;> decide) (by cases scan <;> decide)
    hs.1 hStraight hv
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    (advanceScanBranch scan) pick hGuard hGuard.2.2.2.2.1 (by simp)
  have hRun₂ := groupScanLocalRun scan (by cases scan <;> decide) (by cases scan <;> decide)
    hGuard.1 rfl hu
  have hStraightAll : ((kernel.code.drop site.head).take (5 - 1)).all
      (fun i => Epilogue.schedulerFallsThrough i.op) = true := by
    cases scan <;> set_option maxRecDepth 100000 in kernel_rfl
  have hFrame : Holds u.regs F := Epilogue.holdsSchedulerFrame hsplit.2
    (fun _ hr => Epilogue.schedulerLocalFrame hw hStraightAll (run_comp hv hu)
      hs.1.ge (by rw [hs.1]) hr)
    (fun _ hp => List.mem_map_of_mem hp)
  refine ⟨u, run_comp hRun₁ hRun₂, ?_, hU.2.1, hU.2.2.1, hU.2.2.2.1, ?_⟩
  · simpa only [pick, decide_eq_true_eq, Nat.add_assoc] using hU.1
  · rw [List.cons_append, List.cons_append, holds_cons, holds_cons, holds_append]
    exact ⟨hU.2.2.2.2.2.1, hU.2.2.2.2.2.2.1, hU.2.2.2.2.2.2.2, hFrame⟩

/-- The actual group advance retains the batch width, CTA id and terminal sentinel. -/
theorem advanceGroupScanFramed {g first batch cta : Nat} (scan : GroupScan)
    (hAdvance : first + 31 < 2 ^ 31) (hBatch : batch < 2 ^ 31) {s : TState}
    (hs : At s (scanSite scan).head (groupScanFacts scan first batch cta)) :
    let site := scanSite scan
    ∃ u, run kernel Assumptions.all l g 5 s = some u ∧
      At u (if batch ≤ first + 31 then site.compare else site.head + 5)
        ((site.work, b32 (cta + 1)) :: groupScanFacts scan (min (first + 31) batch) batch cta) := by
  obtain ⟨u, hu, hU⟩ := advanceGroupScanPreserving (F := []) (l := l) (g := g)
    scan hAdvance hBatch (by cases scan <;> set_option maxRecDepth 100000 in kernel_rfl) hs
  rw [List.append_nil] at hU
  exact ⟨u, hu, hU.mono hU.2.2.2.2.2⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
