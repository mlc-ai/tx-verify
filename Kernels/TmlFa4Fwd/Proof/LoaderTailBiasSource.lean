-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderTailBiasEntry
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasEntry
import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasSource
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingBiasWarp
import Kernels.TmlFa4Fwd.Flow.Code.Part021

import Kernels.TmlFa4Fwd.Proof.SoftmaxRecurringBiasGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue Prologue

private theorem tailShift {l : Launch} {g counter : Nat} (hCounter : counter ≤ 9) :
    Seg kernel [] l g 1 1369 [(7181,b32 counter)] 1370 [(1143,b32 (128*counter))] := by
  intro s hs
  seg_fp hs using
    (nf_simp [Nat.shiftLeft_eq]
     all_goals omega)

set_option maxRecDepth 10000 in
private theorem tailIssueRegisters {l : Launch} {g row head counter address : Nat}
    (half : Fin 2) (hCounter : counter ≤ 9)
    {s : TState} {es : List Event} {vs : List Visit} {spec : TensorCopy.Spec}
    (hs : At s 1355 [(7181,b32 counter),(1062,b32 14),(2535,b32 l.sharedBase),
      (1087,b32 row),(7169,b32 head)])
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hSeen : (⟨(inputSite (tailBiasInputSite half)).pc,.tensorIssue address spec⟩ : Event) ∈ es) :
    let site := inputSite (tailBiasInputSite half)
    ∃ t u, EStep kernel Assumptions.all l g t ⟨site.pc,.tensorIssue address spec⟩ (some u) ∧
      t.regs site.colReg = some (b32 (residualBiasColumn half counter)) ∧
      t.regs site.rowReg = some (b32 row) ∧ t.regs 7169 = some (b32 head) := by
  dsimp only
  let site := inputSite (tailBiasInputSite half)
  let event : Event := ⟨site.pc,.tensorIssue address spec⟩
  let stop := site.pc+1
  let first := [(7181,b32 counter),(1062,b32 14),(2535,b32 l.sharedBase),
    (1087,b32 row),(7169,b32 head)]
  let core := [(1087,b32 row),(7169,b32 head)]
  let F := (1143,b32 (128*counter))::core
  let col := if half = 0 then 1373 else 1380
  let G := (site.colReg,b32 (residualBiasColumn half counter))::core
  have hBounds : 1370 ≤ col ∧ col+1 ≤ site.pc ∧ stop ≤ 1901 := by
    change 1370 ≤ (if half = 0 then 1373 else 1380) ∧
      (if half = 0 then 1373 else 1380)+1 ≤ (inputSite (tailBiasInputSite half)).pc ∧
      (inputSite (tailBiasInputSite half)).pc+1 ≤ 1901
    fin_cases half <;> decide
  have hTail (bound : Nat) : ((kernel.code.drop stop).take (1901-stop)).all
      (fun i => loaderPipelineCutOp stop 1901 bound [2535,1062] i.op) = true := by
    fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hRole : Holds s.regs [(2535,b32 l.sharedBase),(1062,b32 (14+(0:Fin 2).val))] :=
    ⟨hs.2.2.2.2.2.2.1,hs.2.2.2.2.2.1,trivial⟩
  have hInside := Thread.Loader.loaderEventInClosedSlice 0 (by omega) hBounds.2.2
    hTail hw (by rw [hs.1]; decide) (ringShapeOfAt hs) hRole hSeen (Nat.lt_succ_self _)
  have hCont : ¬ Ends event := by simp [event,Ends]
  have hAudit : ((kernel.code.drop 1355).take (1369-1355)).all
      (fun i => loaderPipelineCutOp 1355 1369 (stop-1) (first.map Prod.fst) i.op) = true := by
    fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨a,tail,visits,hA,hWalk,hSaw⟩ := biasLocalCut hs (by decide : 174 ≤ 1355)
    (by decide) (by decide) (by omega) hAudit ⟨_,Flow.code_1369,rfl⟩ hw hInside
    (by change 1369 ≤ site.pc; omega) hCont
  obtain ⟨b,hb,hB⟩ := (tailShift (l := l) (g := g) hCounter).apply
    (hA.mono ⟨hA.2.2.2.2.1,trivial⟩)
  obtain ⟨hbA,hbFrame⟩ := loaderLinear (regs := core.map Prod.fst) (by decide) (by decide) hA.1
    (by set_option maxRecDepth 100000 in kernel_rfl) (by simp) hb
  have hB' : At b 1370 F := hB.mono ⟨hB.2.2.2.2.1,
    holdsSchedulerFrame ⟨hA.2.2.2.2.2.2.2.1,hA.2.2.2.2.2.2.2.2.1,trivial⟩ hbFrame
      (fun _ hm => List.mem_map_of_mem hm)⟩
  obtain ⟨post,hPost,hPostMem⟩ := biasSeenAfterLocal hWalk hSaw (run_rtg hbA)
  have hPhaseAudit : ((kernel.code.drop 1370).take (col-1370)).all
      (fun i => loaderPipelineCutOp 1370 col (stop-1) (F.map Prod.fst) i.op) = true := by
    fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hColCode : ∃ i,kernel.code[col]? = some i ∧ i.op.isLocal = true := by
    fin_cases half
    · exact ⟨_,Flow.code_1373,rfl⟩
    · exact ⟨_,Flow.code_1380,rfl⟩
  obtain ⟨c,rest,seen,hC,hNext,hMem⟩ := biasLocalCut hB' (by decide : 174 ≤ 1370)
    ⟨by decide,hBounds.1⟩ (by omega) (by omega) hPhaseAudit hColCode hPost hPostMem
    (by change col ≤ site.pc; omega) hCont
  obtain ⟨d,hd,hD⟩ := (residualBiasColumnSegment (l := l) (g := g) half hCounter).apply
    (hC.mono ⟨hC.2.2.2.2.1,trivial⟩)
  have hKeep : ((kernel.code.drop col).take 1).all
      (fun i => (core.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true := by
    fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨hdA,hdFrame⟩ := loaderLinear (regs := core.map Prod.fst) (by omega) (by omega) hC.1
    hKeep (by simp) hd
  have hD' : At d (col+1) G := hD.mono ⟨hD.2.2.2.2.1,
    holdsSchedulerFrame hC.2.2.2.2.2 hdFrame (fun _ hm => List.mem_map_of_mem hm)⟩
  obtain ⟨after,hAfter,hLast⟩ := biasSeenAfterLocal hNext hMem (run_rtg hdA)
  have hCode : ((kernel.code.drop (col+1)).take (stop-(col+1))).all
      (fun i => loaderPipelineCutOp (col+1) stop (stop-1) (G.map Prod.fst) i.op) = true := by
    fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨t,u,_,hRegs,hStep⟩ := loaderEventWithRegisters (by omega) (by omega) hBounds.2.2
    hCode hAfter (hD'.1.symm ▸ le_rfl) (ringShapeOfAt hD') hD'.2.2.2.2 hLast hCont
  have hRowReg : site.rowReg = 1087 := by fin_cases half <;> rfl
  exact ⟨t,u,hStep,hRegs.1,hRowReg.symm ▸ hRegs.2.1,hRegs.2.2.1⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    (hCuQ : DrainCuQProtected p X) (half : Fin 2) {g j : Nat} {spec : TensorCopy.Spec}
    (hBox : Thread.Loader.BiasSubbox p l X (g,j) 0 half spec)
    (he : X.get (g,j) =
      some ⟨(inputSite (tailBiasInputSite half)).pc,.tensorIssue p.biasMapAddress spec⟩)
include hp hX hFrame hCuQ half hBox he

/-- A realized Bias tail input uses the selected packed row, head and the clipped warm count. -/
theorem tailBiasInputOrigin :
    ∃ batch < p.batch,
      tilePrefix p batch*p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧
      let co := assignedCoordinates p batch (g/l.block)
      (⟨spec.outer,spec.origin⟩ : (n : Nat) × (Fin (n+1) → Int)) =
        ⟨2,inputCoordinate (residualBiasColumn half (min (Mma.trips p batch co.1-1) 9))
          (p.qOffset batch+256*co.1) co.2⟩ := by
  obtain ⟨batch,hb,hLo,hHi,pos,hPos,s,ending,hs,hRun⟩ :=
    tailBiasEntryOfIssue hp hX hFrame hCuQ half hBox he
  let co := assignedCoordinates p batch (g/l.block)
  let row := p.qOffset batch+256*co.1
  let counter := min (Mma.trips p batch co.1-1) 9
  have hCount : counter ≤ 9 := Nat.min_le_right _ _
  have hMem : (⟨(inputSite (tailBiasInputSite half)).pc,
      .tensorIssue p.biasMapAddress spec⟩ : Event) ∈ (X.tr g).drop pos := by
    apply List.mem_of_getElem? (i := j-pos)
    rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
    exact he
  obtain ⟨visits,hWalk⟩ := Mma.walkFromRun hRun
  obtain ⟨t,u,hStep,hCol,hRow,hHeadReg⟩ := tailIssueRegisters half hCount hs hWalk hMem
  obtain ⟨hTile,hHead⟩ := assignedCoordinates_valid hp hLo hHi
  have hPacked : row < p.totalQ := hp.packedRow_lt hb hTile
  have hFit := hp.shape.2.2.2.2.2
  have hOuter : spec.outer = 2 := congrArg Sigma.fst hBox.2.2.2.1
  have hColBound : residualBiasColumn half counter < 2^31 := by
    have hHalf := half.isLt
    unfold residualBiasColumn
    omega
  exact ⟨batch,hb,hLo,hHi,inputOriginOfRegisters (row := row) (tailBiasInputSite half) hStep hOuter
    hCol hRow hHeadReg hColBound (by omega) (hHead.trans hp.heads_signed)⟩

/-- The optional tail half reads the last in-range Bias block for the low stage. -/
theorem tailBiasFinalOrigin :
    ∃ batch < p.batch,
      tilePrefix p batch*p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧
      let co := assignedCoordinates p batch (g/l.block)
      10 < Mma.trips p batch co.1 ∧ warmBiasResidualBit p batch co.1 = 1 ∧
      (⟨spec.outer,spec.origin⟩ : (n : Nat) × (Fin (n+1) → Int)) =
        ⟨2,inputCoordinate (residualBiasColumn half 9) (p.qOffset batch+256*co.1) co.2⟩ := by
  obtain ⟨batch,hb,hLo,hHi,hOrigin⟩ := tailBiasInputOrigin hp hX hFrame hCuQ half hBox he
  obtain ⟨other,ho,hOtherLo,hOtherHi,hTrips,hResidue⟩ := tailBiasIssueTrips hp hX hCuQ half hBox he
  have hActive : g/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  obtain ⟨owner,_,hOwner⟩ := tileBatch_existsUnique p hActive
  have heq := (hOwner other ⟨ho,hOtherLo,hOtherHi⟩).trans (hOwner batch ⟨hb,hLo,hHi⟩).symm
  subst other
  have hMin : min (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1) 9 = 9 :=
    Nat.min_eq_right (by omega)
  simp only [hMin] at hOrigin
  exact ⟨batch,hb,hLo,hHi,hTrips,Softmax.warmBiasResidualBit_eq_one p _ _ hResidue,hOrigin⟩

end PTX.Kernels.TmlFa4Fwd.Loader
