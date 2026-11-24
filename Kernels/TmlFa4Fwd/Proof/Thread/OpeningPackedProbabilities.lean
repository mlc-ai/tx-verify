-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningMaskCursor
import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstNumeric
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningAffineLaunchScores
public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitProbabilityOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption Epilogue

noncomputable section

def openingPackedWeight (scale reference : ℝ) (score : Nat → Option ℝ) (col : Nat) : ℝ :=
  (affineScore scale (-reference) (score col)).elim 0 (fun x => (2 : ℝ)^x)

private theorem openingExponent (scale reference : ℝ) (score : Nat → Option ℝ) (col : Nat) :
    ex2E true (scoreValue (affineScore scale (-reference) (score col))) =
      .ok (.float .f32 (openingPackedWeight scale reference score col)) := by
  unfold openingPackedWeight
  cases hs : affineScore scale (-reference) (score col) with
  | none => exact hardwareExponentNegInf
  | some x =>
    have hx : valFloat .f32 (.float .f32 x) = .ok x := by simp [valFloat,pure,Except.pure]
    exact ex2E_fin hx

/-- The first round's masked logits, including the physical padding lanes. -/
def OpeningAffineLane.maskedScores {p : Params} {l : Launch} {X : Execution}
    {g batch wait : Nat} {stage : Fin 2} (lane : OpeningAffineLane p l X g batch stage wait) :
    Nat → Option ℝ :=
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let row := 128*(2*tile+stage.val)+(g%l.block)%128
  let blocks := Mma.trips p batch tile
  let raw := firstBiasLogit (abiFloat p.invScaleBits)
    (firstBiasRegisterValue (openingBiasColumns p l g batch stage)) (firstQkRegisterValue lane.dot)
  firstMaskedValue p batch row blocks raw

/-- The first round's weights use a finite shift even if the lane masks all columns. -/
def OpeningAffineLane.probabilityWeights {p : Params} {l : Launch} {X : Execution}
    {g batch wait : Nat} {stage : Fin 2} (lane : OpeningAffineLane p l X g batch stage wait) :
    Nat → ℝ :=
  let scale := abiFloat p.scaleLog2Bits
  let reference := scale*(scoreMax lane.maskedScores (List.range 128)).getD 0
  openingPackedWeight scale reference lane.maskedScores

private theorem scoreMax_agreesOn {first second : Nat → Option ℝ} {columns : List Nat}
    (hSame : ∀ col ∈ columns, first col = second col) :
    scoreMax first columns = scoreMax second columns := by
  induction columns with
  | nil => rfl
  | cons col rest ih =>
    change maxScore (first col) (scoreMax first rest) = maxScore (second col) (scoreMax second rest)
    rw [hSame col (by simp), ih (fun k hk => hSame k (List.mem_cons_of_mem _ hk))]

/-- For a live row the first hardware probability agrees with the specification's
reference-shifted weight, with the masked columns giving zero. -/
theorem OpeningAffineLane.probabilityWeightOfLaunch {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch wait : Nat} {stage : Fin 2}
    (lane : OpeningAffineLane p l X g batch stage wait)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (col : Fin 128) :
    let coords := assignedCoordinates p batch (g/l.block)
    let row := 128*(2*coords.1+stage.val)+(g%l.block)%128
    let blocks := Mma.trips p batch coords.1
    row < p.qLength batch →
    lane.probabilityWeights col.val = shiftedWeight p batch coords.2 row
      (visitKey blocks 0 col.val) (firstReference p batch coords.2 row blocks) := by
  let coords := assignedCoordinates p batch (g/l.block)
  let row := 128*(2*coords.1+stage.val)+(g%l.block)%128
  let blocks := Mma.trips p batch coords.1
  let logits := fun c => maskedLogit p batch coords.2 row (visitKey blocks 0 c)
  let reference := firstReference p batch coords.2 row blocks
  change row < p.qLength batch → lane.probabilityWeights col.val =
    shiftedWeight p batch coords.2 row (visitKey blocks 0 col.val) reference
  intro hRow
  have hLogits (c : Fin 128) : lane.maskedScores c.val = logits c.val :=
    lane.maskedLogitOfLaunch hp hX hFrame hb hLo hHi c hRow
  have hMax : scoreMax lane.maskedScores (List.range 128) = scoreMax logits (List.range 128) :=
    scoreMax_agreesOn (fun c hc => hLogits ⟨c,List.mem_range.mp hc⟩)
  have hExp := openingExponent (abiFloat p.scaleLog2Bits) reference lane.maskedScores col.val
  rw [hLogits col] at hExp
  have hRef := hardwareShiftedWeight hp batch coords.2 row (visitKey blocks 0 col.val) reference
  change ex2E true (scoreValue (affineScore (abiFloat p.scaleLog2Bits) (-reference) (logits col))) =
    _ at hRef
  have hWeight := Value.float.inj (Except.ok.inj (hExp.symm.trans hRef))
  unfold OpeningAffineLane.probabilityWeights
  rw [hMax]
  exact hWeight.2

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) {g batch wait : Nat}
    {stage : Fin 2} (lane : OpeningAffineLane p l X g batch stage wait) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
include hp lane hb hLo hHi

/-- The observed opening lane reaches its publication with four quarters of finite BF16
probabilities, even if its actual trace continues with an unfinished lane state. -/
theorem OpeningAffineLane.packsOfPrefix (hMore : lane.entry.pos+1 < (X.tr g).length) :
    ∃ u : TState, At u 4818 [] ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (lane.entry.pos+1))
        lane.entry.arrival.loaded.opening.ending ∧
      (∀ q : Fin 4, ∀ i < 8, u.regs (firstPackedReg q+i) =
        some (probabilityDoubleWord (fun col => lane.probabilityWeights (32*q.val+col)) i)) ∧
      u.regs 3217 = some (b32 (l.sharedBase+8*stage.val)) ∧
      ∀ q : Fin 4, u.regs (probabilityReg .first q) =
        some (b32 (probabilityAddress l g stage q)) := by
  let entry := lane.entry
  let warp := entry.arrival.loaded.opening.warp
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let base := 2*tile+stage.val
  let blocks := Mma.trips p batch tile
  let row := 128*base+(g%l.block)%128
  let raw := firstBiasLogit (abiFloat p.invScaleBits)
    (firstBiasRegisterValue (openingBiasColumns p l g batch stage)) (firstQkRegisterValue lane.dot)
  let columns := firstMaskedValue p batch row blocks raw
  let scale := abiFloat p.scaleLog2Bits
  let reference := scale*(scoreMax columns (List.range 128)).getD 0
  let weights := openingPackedWeight scale reference columns
  obtain ⟨u,hu,hAddr,hRaw,hScale,hBar,hReach⟩ := lane.maskCursor hp
  have hNonempty (j : Nat) (hj : j < (X.tr g).length) : (X.tr g).drop j ≠ [] := by
    intro hEmpty
    have hZero := congrArg List.length hEmpty
    simp only [List.length_drop,List.length_nil] at hZero
    omega
  have hLive := hNonempty entry.pos (by dsimp [entry]; omega)
  have hTail := entry.continuation.after_local_nonempty hReach hLive
  have hMeta := hp.lengths batch hb
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  have hBound := (Mma.trips_bounds hp hb hTile).2.1
  have hBlocks : 128*(blocks-1) ≤ p.kLength batch := by
    change blocks ≤ (p.kLength batch+127)/128 at hBound
    omega
  have hTid : g%l.block < 2^32 := by
    rw [hp.block]
    have := Nat.mod_lt g (by decide : 0 < 512)
    omega
  have hRow : row < p.qLength batch+256 := by
    have hStage := stage.isLt
    have hLane := Nat.mod_lt (g%l.block) (by decide : 0 < 128)
    dsimp only [row,base]
    omega
  obtain ⟨v,hv,hVRun,hScores,hFrame⟩ :=
    firstCausalMaskInPrefix p batch (g%l.block) base blocks raw hTid hMeta.2.1 hMeta.2.2
      hRow hBlocks hu hRaw hTail hLive
  have hKeeps (r : Nat) (hr : r ∈ [7132,5127,3217,3223,3224,3225,3226]) : v.regs r = u.regs r := by
    have hSetup : List.all [7132,5127,3217,3223,3224,3225,3226]
        (fun reg => !firstMaskSetupWrites.contains reg) = true := by decide +kernel
    refine hFrame r (by simpa using List.all_eq_true.mp hSetup r hr) (fun group => ?_)
    have hGroup := group.isLt
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    unfold firstMaskGroupWrites maskScratch maskPred
    omega
  obtain ⟨s,hs,_,hSRun,hScaled,hOffset,hRead,hSource,_,hShift⟩ :=
    firstShiftInputInPrefix hp warp columns hv hScores
      ((hKeeps 7132 (by decide)).trans hScale) ((hKeeps 5127 (by decide)).trans hBar) hVRun hMore
  have hShifted : At s (shiftStart 0) [] := hs
  have hMore' := hNonempty (entry.pos+1) hMore
  obtain ⟨w,hw,hPacks,_,hPKeep,hFinal⟩ :=
    firstShiftedPacksInPrefix hp reference columns weights (openingExponent scale reference columns)
      (firstShiftValues s) (firstShiftLogits columns) hShifted hRead hSource
      (fun _ _ => ⟨rfl,rfl⟩) hScaled hOffset hSRun hMore'
  have hBaseValue : u.regs 3217 = some (b32 (l.sharedBase+8*stage.val)) :=
    holds_mem hAddr (by simp [firstAddressFacts])
  have hSignalBase : w.regs 3217 = some (b32 (l.sharedBase+8*stage.val)) :=
    (hPKeep 3217 (by decide +kernel) (by decide) (by decide) (by decide)).trans
      ((hShift _ (by decide +kernel)).trans ((hKeeps _ (by decide)).trans hBaseValue))
  refine ⟨w,hw,hFinal,hPacks,hSignalBase,fun q => ?_⟩
  have hReg (q : Fin 4) : probabilityReg .first q ∈ [7132,5127,3217,3223,3224,3225,3226] := by
    fin_cases q <;> decide
  have hShiftKeep (q : Fin 4) : (probabilityReg .first q) ∉
      rWrites (firstMaxItems.map MaxItem.item) ++ [622,3685,1230,3686,8024,8025,8026] := by
    fin_cases q <;> decide +kernel
  have hReadAddr (q : Fin 4) : (probabilityReg .first q,b32 (probabilityAddress l g stage q)) ∈
      firstAddressFacts l g stage := by fin_cases q <;> simp [probabilityReg,firstAddressFacts]
  exact (hPKeep _ (by fin_cases q <;> decide +kernel) (by fin_cases q <;> decide)
      (by fin_cases q <;> decide) (by fin_cases q <;> decide)).trans
    ((hShift _ (hShiftKeep q)).trans
      ((hKeeps _ (hReg q)).trans (holds_mem hAddr (hReadAddr q))))

/-- The observed first visit writes BF16 words to its two probability packets
before the lane's exit. The words come from the mask and exponent replay. -/
theorem OpeningAffineLane.firstStoresOfPrefix (hMore : lane.entry.pos+7 < (X.tr g).length) :
    ∀ q : Fin 4, X.get (g,lane.entry.pos+1+probabilityTraceIndex q) =
      some (firstStoreEvent l g stage q (fun col => lane.probabilityWeights (32*q.val+col))) := by
  let pos := lane.entry.pos+1
  obtain ⟨t,ht,hRun,hPacked,hBase,hAddr⟩ :=
    lane.packsOfPrefix hp hb hLo hHi (by omega)
  let values (q : Fin 4) (col : Nat) := lane.probabilityWeights (32*q.val+col)
  have hEarly : pos+3 < (X.tr g).length := by dsimp [pos]; omega
  obtain ⟨u,_,h0,h1,h2,hU,hFrame,hTail⟩ :=
    firstThreeStoresInPrefix hp stage values ht hPacked hAddr hRun hEarly
  have hPack (word : Nat) (hWord : word < 8) :
      u.regs (firstPackedReg 3+word) = some (probabilityDoubleWord (values 3) word) := by
    rw [hFrame _ (.inr (by unfold firstPackedReg; omega))]
    exact hPacked 3 word hWord
  have hLast : (pos+4)+2 < (X.tr g).length := by dsimp [pos]; omega
  obtain ⟨_,_,_,h3,_,_,_⟩ :=
    firstLastStoreInPrefix hp stage (values 3) hU ((hFrame 3217 (by decide)).trans hBase)
      hPack ((hFrame (probabilityReg .first 3) (by decide)).trans (hAddr 3)) hTail hLast
  intro q
  fin_cases q
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- Each of the three initial P stores is already a BF16 pair sequence as soon
as that particular store is present in the actual prefix. -/
theorem OpeningAffineLane.firstEarlyStoreOfPrefix (q : Fin 3)
    (hRecorded : lane.entry.pos+1+(q.val+1) < (X.tr g).length) :
    X.get (g,lane.entry.pos+1+(q.val+1)) =
      some (firstStoreEvent l g stage ⟨q.val,q.isLt.trans (by decide)⟩
        (fun col => lane.probabilityWeights (32*q.val+col))) := by
  let pos := lane.entry.pos+1
  have hBound : pos+(q.val+1) < (X.tr g).length := hRecorded
  obtain ⟨t,ht,hRun,hPacked,_,hAddr⟩ :=
    lane.packsOfPrefix hp hb hLo hHi (by dsimp only [pos] at hBound; omega)
  let values (quarter : Fin 4) (col : Nat) := lane.probabilityWeights (32*quarter.val+col)
  fin_cases q
  · obtain ⟨_,_,hStore,_,_,_⟩ :=
      packedQuarterStoreInPrefix hp stage 0 (values 0) ht (hPacked 0) (hAddr 0)
        hRun (show pos+1 < (X.tr g).length from hBound)
    exact hStore
  · have hFirst : pos+1 < (X.tr g).length := by
      have h := show pos+2 < (X.tr g).length from hBound
      omega
    obtain ⟨u,_,_,hU,hKeep,hTail⟩ :=
      packedQuarterStoreInPrefix hp stage 0 (values 0) ht (hPacked 0) (hAddr 0) hRun hFirst
    have hPack (word : Nat) (hWord : word < 8) :
        u.regs (firstPackedReg 1+word) = some (probabilityDoubleWord (values 1) word) := by
      have hSafe : firstUnpackBase 0+16 ≤ firstPackedReg 1+word := by
        change 3895 ≤ 8162+word
        omega
      exact (hKeep _ (.inr hSafe)).trans (hPacked 1 word hWord)
    have hAddress := (hKeep (probabilityReg .first 1) (.inl (by decide))).trans (hAddr 1)
    obtain ⟨_,_,hStore,_,_,_⟩ :=
      packedQuarterStoreInPrefix hp stage 1 (values 1) hU hPack hAddress hTail
        (show pos+2 < (X.tr g).length from hBound)
    exact hStore
  · obtain ⟨_,_,_,_,hStore,_,_,_⟩ :=
      firstThreeStoresInPrefix hp stage values ht hPacked hAddr hRun hBound
    exact hStore

end
end PTX.Kernels.TmlFa4Fwd.Softmax
