-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedScoreTrace
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstScoreValues
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLaterBiasVectorTrace

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption

/-- The unpacked BF16 register of each logical column in a repeated Bias round. -/
def laterBiasColumnReg (col : Nat) : Nat := 921+8*(col/8)-col%8

private def laterBiasRegValue (bias : Nat → Option ℝ) (reg : Nat) : Option ℝ :=
  bias (8*((reg-914)/8)+(7-(reg-914)%8))

private theorem laterBiasRegValue_inverse (bias : Nat → Option ℝ) (col : Nat) :
    laterBiasRegValue bias (laterBiasColumnReg col) = bias col := by
  unfold laterBiasRegValue laterBiasColumnReg
  apply congrArg bias
  have hSub : 921+8*(col/8)-col%8-914 = 8*(col/8)+(7-col%8) := by omega
  rw [hSub]
  omega

private theorem laterBiasRegistersOfWords {t : TState} (bias : Nat → Option ℝ)
    (hUnpacked : ∀ i : Fin 16, BiasUnpacked true i t (fun k =>
      biasLoadWord (bias (8*i.val+2*k)) (bias (8*i.val+2*k+1)))) :
    ∀ col < 128, t.regs (laterBiasColumnReg col) = some (biasValue (bias col)) := by
  intro col hCol
  let i : Fin 16 := ⟨col/8,by omega⟩
  let word := col%8/2
  obtain ⟨hLo,hHi⟩ := hUnpacked i word (by dsimp [word]; omega)
  rw [splitBiasLoadWord] at hLo hHi
  by_cases hEven : col%2 = 0
  · have hIndex : 8*i.val+2*word = col := by dsimp [i,word]; omega
    have hReg : (biasUnpackRegs true i word).1 = laterBiasColumnReg col := by
      simp only [biasUnpackRegs,biasUnpackTop,ite_true,laterBiasColumnReg,i,word]
      omega
    simpa only [hReg,hIndex] using hLo
  · have hIndex : 8*i.val+2*word+1 = col := by dsimp [i,word]; omega
    have hReg : (biasUnpackRegs true i word).2 = laterBiasColumnReg col := by
      simp only [biasUnpackRegs,biasUnpackTop,ite_true,laterBiasColumnReg,i,word]
      omega
    simpa only [hReg,hIndex] using hHi

private def laterBiasItemInOrder (item : BiasAffineItem) : Bool :=
  let pair := item.qk-7367
  (7367 ≤ item.qk) && (pair < 64) &&
    (item.biasLow == laterBiasColumnReg (2*pair)) &&
    (item.biasHigh == laterBiasColumnReg (2*pair+1))

private theorem laterBiasItemsInOrder : (biasBodyItems true).all laterBiasItemInOrder = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem laterBiasOrdered (i : BiasAffineItem) (hi : i ∈ biasBodyItems true) :
      7367 ≤ i.qk ∧ i.qk-7367 < 64 ∧ i.biasLow = laterBiasColumnReg (2*(i.qk-7367)) ∧
        i.biasHigh = laterBiasColumnReg (2*(i.qk-7367)+1) := by
  have hh := List.all_eq_true.mp laterBiasItemsInOrder i hi
  simp only [laterBiasItemInOrder,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hh
  exact ⟨hh.1.1.1,hh.1.1.2,hh.1.2,hh.2⟩

/-- The decoded repeated Bias body produces canonical score pairs for any physical
row, including padding, from the finite score words and BF16 Bias operands. -/
theorem laterBiasBodyOfCanonicalInputs {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} {t : TState}
    (bias : Nat → Option ℝ) (dot : Nat → ℝ) (ht : At t (biasBodyStart true) [])
    (hScale : readERealPair l g t (.reg 7896) =
      some (.ok ((abiFloat p.invScaleBits : EReal),(abiFloat p.invScaleBits : EReal))))
    (hUnpacked : ∀ i : Fin 16, BiasUnpacked true i t (fun k =>
      biasLoadWord (bias (8*i.val+2*k)) (bias (8*i.val+2*k+1))))
    (hDots : ∀ pair < 64,
      readERealPair l g t (.reg (7367+pair)) =
        some (.ok ((dot (2*pair) : EReal),(dot (2*pair+1) : EReal)))) :
    ∃ u, At u (biasBodyStart true+4*biasBodyPairs true) [] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (∀ r ∉ (biasBodyItems true).flatMap BiasAffineItem.writes, u.regs r = t.regs r) ∧
      ∀ i ∈ biasBodyItems true,
        u.regs i.result = some (.pair
          (scoreValue (affineScore (abiFloat p.invScaleBits) (dot (2*(i.qk-7367)))
            (bias (2*(i.qk-7367)))))
          (scoreValue (affineScore (abiFloat p.invScaleBits) (dot (2*(i.qk-7367)+1))
            (bias (2*(i.qk-7367)+1))))) := by
  let biasReg := laterBiasRegValue bias
  let qk := fun reg => (dot (2*(reg-7367)),dot (2*(reg-7367)+1))
  have hBias := laterBiasRegistersOfWords bias hUnpacked
  have hInput (i : BiasAffineItem) (hi : i ∈ biasBodyItems true) :
      t.regs i.biasLow = some (biasValue (biasReg i.biasLow)) ∧
      t.regs i.biasHigh = some (biasValue (biasReg i.biasHigh)) ∧
      readERealPair l g t (.reg i.qk) =
        some (.ok (((qk i.qk).1 : EReal),((qk i.qk).2 : EReal))) := by
    obtain ⟨hBase,hCount,hLo,hHi⟩ := laterBiasOrdered i hi
    refine ⟨?_,?_,?_⟩
    · rw [hLo]
      change _ = some (biasValue (laterBiasRegValue bias (laterBiasColumnReg (2*(i.qk-7367)))))
      rw [laterBiasRegValue_inverse]
      exact hBias _ (by omega)
    · rw [hHi]
      change _ = some (biasValue (laterBiasRegValue bias (laterBiasColumnReg (2*(i.qk-7367)+1))))
      rw [laterBiasRegValue_inverse]
      exact hBias _ (by omega)
    · have h := hDots (i.qk-7367) hCount
      rwa [Nat.add_sub_of_le hBase] at h
  obtain ⟨u,hAt,hLocal,hFrame,hValue⟩ := biasBodyRun true (scalePositive hp).2
    biasReg qk ht hScale hInput
  refine ⟨u,hAt,run_rtg hLocal,hFrame,fun i hi => ?_⟩
  obtain ⟨_,_,hLo,hHi⟩ := laterBiasOrdered i hi
  have h := hValue i hi
  rw [hLo,hHi] at h
  dsimp only [qk,biasReg] at h
  rwa [laterBiasRegValue_inverse,laterBiasRegValue_inverse] at h

/-- A valid repeated visit inside the biased extent lies in the launch Bias columns. -/
theorem laterVisitBiasColumnInRange (p : Params) (batch tile : Nat) (stage : Fin 2)
    {lane visit col : Nat} (hLane : lane < 128) (hCol : col < 128)
    (hVisit : 0 < visit) (hTrips : visit < Mma.trips p batch tile)
    (hBiased : visit < Mma.trips p batch tile-stageGeometryBlocks p batch tile stage+10) :
    let row := 256*tile+128*stage.val+lane
    let column := p.biasColumn batch row (visitKey (Mma.trips p batch tile) visit col)
    0 ≤ column ∧ column < 1280 := by
  let trips := Mma.trips p batch tile
  let geom := stageGeometryBlocks p batch tile stage
  let row := 256*tile+128*stage.val+lane
  have hGeometry : geom ≤ trips ∧ trips ≤ geom+1 := by
    fin_cases stage <;> dsimp [geom,trips,stageGeometryBlocks,Mma.trips] <;> omega
  change visit < trips at hTrips
  change visit < trips-geom+10 at hBiased
  change 0 ≤ p.biasColumn batch row (128*(trips-1-visit)+col) ∧
    p.biasColumn batch row (128*(trips-1-visit)+col) < 1280
  rw [p.biasColumn_of_block]
  change 0 ≤ 128*(10+((trips-1-visit : Nat) : Int)-(biasStageBlocks p batch row : Int))+col ∧
    128*(10+((trips-1-visit : Nat) : Int)-(biasStageBlocks p batch row : Int))+col < 1280
  have hRowBlocks : biasStageBlocks p batch row = geom :=
    biasLaneStageBlocks p batch tile stage hLane
  rw [hRowBlocks]
  change 0 ≤ 128*(10+((trips-1-visit : Nat) : Int)-(geom : Int))+col ∧
    128*(10+((trips-1-visit : Nat) : Int)-(geom : Int))+col < 1280
  omega

/-- The actual affine sequence combines the repeated Bias vector words and the
corresponding observed QK pairs into the masked logical logits for this visit. -/
theorem laterBiasBodyOfLogicalDots {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (stage : Fin 2) {g batch tile lane head visit : Nat} {t : TState}
    (hb : batch < p.batch) (hh : head < p.heads)
    (hLane : lane < 128) (hRow : 256*tile+128*stage.val+lane < p.qLength batch)
    (hVisit : 0 < visit) (hTrips : visit < Mma.trips p batch tile)
    (hBiased : visit < Mma.trips p batch tile-stageGeometryBlocks p batch tile stage+10)
    (ht : At t (biasBodyStart true) [])
    (hScale : readERealPair l g t (.reg 7896) =
      some (.ok ((abiFloat p.invScaleBits : EReal),(abiFloat p.invScaleBits : EReal))))
    (hUnpacked : ∀ i, BiasUnpacked true i t
      (laterBiasWord p batch tile (256*tile+128*stage.val+lane) head visit i))
    (dot : Nat → ℝ)
    (hLiveDot : ∀ col < 128, let row := 256*tile+128*stage.val+lane
      let key := visitKey (Mma.trips p batch tile) visit col
      key < p.keyCount batch row → dot col = queryKeyDot p batch head row key)
    (hDots : ∀ pair < 64,
      readERealPair l g t (.reg (7367+pair)) =
        some (.ok ((dot (2*pair) : EReal),(dot (2*pair+1) : EReal)))) :
    let row := 256*tile+128*stage.val+lane
    let logit := fun col => maskedLogit p batch head row
      (visitKey (Mma.trips p batch tile) visit col)
    ∃ u, At u (biasBodyStart true+4*biasBodyPairs true) [] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (∀ r ∉ (biasBodyItems true).flatMap BiasAffineItem.writes, u.regs r = t.regs r) ∧
      ∀ i ∈ biasBodyItems true,
        u.regs i.result = some (.pair
          (scoreValue (logit (2*(i.qk-7367))))
          (scoreValue (logit (2*(i.qk-7367)+1)))) := by
  let row := 256*tile+128*stage.val+lane
  let key := fun col => visitKey (Mma.trips p batch tile) visit col
  let bias := visitBiasElement p batch tile row head visit
  obtain ⟨u,hAt,hLocal,hFrame,hValue⟩ :=
    laterBiasBodyOfCanonicalInputs hp bias dot ht hScale hUnpacked hDots
  refine ⟨u,hAt,hLocal,hFrame,?_⟩
  intro i hi
  have hCount := (laterBiasOrdered i hi).2.1
  have hLogit (col : Nat) (hc : col < 128) :
      affineScore (abiFloat p.invScaleBits) (dot col) (bias col) =
        maskedLogit p batch head row (key col) := by
    obtain ⟨hColumn,hBound⟩ :=
      laterVisitBiasColumnInRange p batch tile stage hLane hc hVisit hTrips hBiased
    have hPacked := hp.packedRow_lt hb hRow
    have hBacked : p.qOffset batch+row < p.totalQ+128 := by omega
    unfold bias visitBiasElement biasBoxValue
    rw [ite_eq_left hBacked]
    by_cases hLive : key col < p.keyCount batch row
    · rw [hLiveDot col hc hLive]
      exact biasedLogit_eq hp hb hRow hh hColumn hBound
    · have hMask := hp.biasMask batch hb row hRow head hh (key col) hColumn hBound
      cases hbValue : p.bias
          (p.qOffset batch+row) head (p.biasColumn batch row (key col)).toNat with
      | none => simp [affineScore,maskedLogit,hLive]
      | some value =>
        rw [hbValue] at hMask
        exact (hLive (of_decide_eq_true hMask.symm)).elim
  have h := hValue i hi
  rwa [hLogit _ (by omega),hLogit _ (by omega)] at h

section
variable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (stage : Fin 2)
    {g batch tile lane head visit : Nat} {t : TState} {events : List Event} (hb : batch < p.batch)
    (hh : head < p.heads) (hLane : lane < 128)
    (hRow : 256*tile+128*stage.val+lane < p.qLength batch) (hVisit : 0 < visit)
    (hTrips : visit < Mma.trips p batch tile)
    (hBiased : visit < Mma.trips p batch tile-stageGeometryBlocks p batch tile stage+10)
    (ht : At t (biasBodyStart true) [])
    (hScale : readERealPair l g t (.reg 7896) =
      some (.ok ((abiFloat p.invScaleBits : EReal),(abiFloat p.invScaleBits : EReal))))
    (hUnpacked : ∀ i, BiasUnpacked true i t
      (laterBiasWord p batch tile (256*tile+128*stage.val+lane) head visit i))
include hp stage hb hh hLane hRow hVisit hTrips hBiased ht hScale hUnpacked

end

/-- The observed QK words and their packed registers supply the data for the biased
affine computation, including rows supplied by K zero fill. -/
theorem laterBiasBodyLocalFromObservedWords {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (stage : Fin 2) {g batch tile head visit : Nat} {t : TState}
    (hb : batch < p.batch) (hh : head < p.heads)
    (hRow : 256*tile+128*stage.val+(g%l.block)%128 < p.qLength batch)
    (hVisit : 0 < visit) (hTrips : visit < Mma.trips p batch tile)
    (hBiased : visit < Mma.trips p batch tile-stageGeometryBlocks p batch tile stage+10)
    (ht : At t (biasBodyStart true) [])
    (hScale : readERealPair l g t (.reg 7896) =
      some (.ok ((abiFloat p.invScaleBits : EReal),(abiFloat p.invScaleBits : EReal))))
    (hUnpacked : ∀ i, BiasUnpacked true i t
      (laterBiasWord p batch tile (256*tile+128*stage.val+(g%l.block)%128) head visit i))
    (values : Fin 4 → List Value)
    (hPacked : ∀ (quarter : Fin 4) (pair : Fin 16),
      t.regs (repeatedScorePairReg .biased quarter pair.val) =
        some (joinValue ((values quarter).getD (2*pair.val) (b32 0))
          ((values quarter).getD (2*pair.val+1) (b32 0))))
    (hWords : ∀ (quarter : Fin 4) (word : Fin 32),
      (values quarter)[word.val]? = some (.float .f32 (firstScoreDot p l g batch head
        (p.qOffset batch+256*tile+128*stage.val)
        (128*(Mma.trips p batch tile-1-visit)) quarter word))) :
    let row := 256*tile+128*stage.val+(g%l.block)%128
    let logit := fun col => maskedLogit p batch head row
      (visitKey (Mma.trips p batch tile) visit col)
    ∃ u, At u (biasBodyStart true+4*biasBodyPairs true) [] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (∀ r ∉ (biasBodyItems true).flatMap BiasAffineItem.writes, u.regs r = t.regs r) ∧
      ∀ i ∈ biasBodyItems true,
        u.regs i.result = some (.pair
          (scoreValue (logit (2*(i.qk-7367))))
          (scoreValue (logit (2*(i.qk-7367)+1)))) := by
  let row := 256*tile+128*stage.val+(g%l.block)%128
  let key := visitKey (Mma.trips p batch tile) visit
  let dot := fun col => ∑ d ∈ Finset.range 128,
    Mma.qkQuery p (p.qOffset batch+row) head d * Mma.qkKey p batch head (key col) d
  have hLive (col : Nat) (_ : col < 128) (hc : key col < p.keyCount batch row) :
      dot col = queryKeyDot p batch head row (key col) := by
    have hQ : p.qOffset batch+row < p.totalQ := hp.packedRow_lt hb hRow
    have hK := hc.trans_le (Nat.min_le_left ..)
    simp only [dot,queryKeyDot,Mma.qkQuery,Mma.qkKey,ite_eq_left hQ,ite_eq_left hK]
  apply laterBiasBodyOfLogicalDots hp stage hb hh (Nat.mod_lt _ (by decide)) hRow
    hVisit hTrips hBiased ht hScale hUnpacked dot hLive _
  intro i hi
  let quarter : Fin 4 := ⟨i/16,by omega⟩
  let pair : Fin 16 := ⟨i%16,Nat.mod_lt _ (by decide)⟩
  have hReg : repeatedScorePairReg .biased quarter pair.val = 7367+i := by
    change 7367+16*(i/16)+i%16 = _
    omega
  have hColumn₀ : 32*quarter.val+2*pair.val = 2*i := by
    dsimp [quarter,pair]
    omega
  have hColumn₁ : 32*quarter.val+(2*pair.val+1) = 2*i+1 := by omega
  have hWord (w : Fin 32) : (values quarter)[w.val]? =
      some (.float .f32 (dot (32*quarter.val+w.val))) := by
    simpa only [dot,key,firstScoreDot,firstScoreColumn,scoreRow_eq_tid,visitKey,row,Nat.add_assoc]
      using hWords quarter w
  have h := repeatedPackedScoreValues (l := l) (g := g) .biased quarter pair _ hWord
    (hPacked quarter pair)
  dsimp only at h
  rwa [hReg,hColumn₀,hColumn₁] at h

end PTX.Kernels.TmlFa4Fwd.Softmax
