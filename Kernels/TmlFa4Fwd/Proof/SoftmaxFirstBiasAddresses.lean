-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitGeometry
public import Kernels.TmlFa4Fwd.Proof.SoftmaxTileCoordinates
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasAddressArithmetic
import Kernels.TmlFa4Fwd.Flow.Code.Part051
import Kernels.TmlFa4Fwd.Flow.Code.Part052
import Lemmas.Flow.Swizzle
import Lemmas.Flow.Footprint
import Lemmas.Flow.SegChain
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Proof.MmaQkKeyLayout
import Kernels.TmlFa4Fwd.Proof.StatsBarrierSetup
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Epilogue

private def firstBiasVector (i : Fin 14) : Fin 16 :=
  ⟨if i.val < 7 then 15 - i.val else 14 - i.val, by split <;> omega⟩

private def firstBiasDisplacement (i : Fin 14) : Nat :=
  let col := (firstBiasVector i).val
  166912 + 16384 * (col / 8) + 16 * (col % 8)

private theorem firstBiasAddressQuad {l : Launch} {g base : Nat} (i : Fin 14)
    (hBound : base + 183408 < 4294967296) :
    Seg kernel [] l g 4 (3309 + 4 * i.val)
      [(2790, b32 base)]
      (3309 + 4 * (i.val + 1))
      [(2794 + 4 * i.val, b32 (kvSwizzle (base + firstBiasDisplacement i)))] := by
  have hMask (n : Nat) : (n &&& 112) < 4294967296 :=
    Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  fin_cases i <;> intro t ht
  all_goals
    simp only [firstBiasDisplacement, firstBiasVector, Fin.val_mk,
      Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul,
      Nat.reduceAdd, kvSwizzle, Nat.shiftRight_eq_div_pow, Nat.reducePow] at ht ⊢
    seg_fp ht using
      nf_simp [nf_xor]
      simp (disch := omega) only [Nat.mod_eq_of_lt (hMask _), Nat.mod_eq_of_lt]
      rw [Nat.xor_comm]

private def firstBiasPriorRegs (i : Fin 14) : List Nat :=
  2790 :: (List.range i.val).map (fun j => 2794 + 4 * j)

set_option maxRecDepth 100000 in
private theorem firstBiasQuadStable (i : Fin 14) :
    ((kernel.code.drop (3309 + 4 * i.val)).take 4).all
      (fun ins => (firstBiasPriorRegs i).all (fun r => !(writesRegs ins.op).contains r)) =
      true := by
  fin_cases i <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem firstBiasQuadStraight (i : Fin 14) :
    ((kernel.code.drop (3309 + 4 * i.val)).take 3).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
  fin_cases i <;> kernel_rfl

private theorem firstBiasBodyPrefix {l : Launch} {g base : Nat} {t : TState}
    (ht : At t 3309 [(2790, b32 base)]) (hb : base + 183408 < 4294967296)
    (n : Nat) (hn : n ≤ 14) :
    ∃ u, run kernel [] l g (4 * n) t = some u ∧ At u (3309 + 4 * n) [(2790, b32 base)] ∧
      ∀ i : Fin 14, i.val < n → u.regs (2794 + 4 * i.val) =
        some (b32 (kvSwizzle (base + firstBiasDisplacement i))) := by
  induction n with
  | zero => exact ⟨t, rfl, ht, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  | succ n ih =>
    let i : Fin 14 := ⟨n, by omega⟩
    obtain ⟨v, hV, hv, hPrev⟩ := ih (by omega)
    obtain ⟨u, hU, hu⟩ := (firstBiasAddressQuad (l := l) (g := g) i hb).apply hv
    have hFrame {r : Nat} (hr : r ∈ firstBiasPriorRegs i) : u.regs r = v.regs r :=
      schedulerLocalFrame (firstBiasQuadStable i) (firstBiasQuadStraight i) hU
        hv.1.ge (by rw [hv.1]) hr
    have hu' : At u (3309 + 4 * (n + 1)) [(2790, b32 base)] :=
      hu.mono ⟨(hFrame (r := 2790) (by simp [firstBiasPriorRegs])).trans hv.2.2.2.2.1, trivial⟩
    refine ⟨u, by rw [Nat.mul_succ]; exact run_comp hV hU, hu', ?_⟩
    intro j hj
    by_cases hEq : j = i
    · subst j
      exact hu.2.2.2.2.1
    · have hLt : j.val < n := by
        have hNe : j.val ≠ n := fun h => hEq (Fin.ext h)
        omega
      have hMem : 2794 + 4 * j.val ∈ firstBiasPriorRegs i :=
        List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_range.mpr hLt))
      exact (hFrame hMem).trans (hPrev j hLt)

set_option maxRecDepth 100000 in
private theorem firstBiasPreludeCore : ((kernel.code.drop 3274).take (3367 - 3274)).all
    (fun i => Assumptions.coreOp i.op) = true := by kernel_rfl

private theorem firstBiasPreludeOut {l : Launch} {g : Nat} {s : TState}
    (hLo : 3274 ≤ s.pc) (hHi : s.pc < 3367) :
    out kernel Assumptions.all l g s = out kernel [] l g s := by
  cases hCode : kernel.code[s.pc]? with
  | none => simp only [out, hCode]
  | some ins =>
    have hMem : ins ∈ (kernel.code.drop 3274).take (3367 - 3274) := by
      apply List.mem_of_getElem? (i := s.pc - 3274)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo, hCode]
    apply Assumptions.out_all_eq_nil _ _ _ hCode (List.all_eq_true.mp firstBiasPreludeCore _ hMem)
    all_goals
      simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
        Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega

private theorem firstBiasLinear {l : Launch} {g pc n : Nat} {t u : TState}
    {regs : List Nat} (hLo : 3274 ≤ pc) (hHi : pc + n ≤ 3367) (hPc : t.pc = pc)
    (hStable : ((kernel.code.drop pc).take n).all
      (fun ins => regs.all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hStraight : ((kernel.code.drop pc).take (n - 1)).all
      (fun ins => schedulerFallsThrough ins.op) = true)
    (hRun : run kernel [] l g n t = some u) :
    run kernel Assumptions.all l g n t = some u ∧ ∀ r ∈ regs, u.regs r = t.regs r :=
  ⟨schedulerLocalTransport hStraight
      (fun lo hi => firstBiasPreludeOut (by omega) (by omega)) hRun (by omega) (by omega),
    fun _ hr => schedulerLocalFrame hStable hStraight hRun (by omega) (by omega) hr⟩

private def firstBiasRawRow (l : Launch) (g : Nat) (stage : Fin 2) : Nat :=
  l.sharedBase + 128 * ((g % l.block) % 128) + 32768 * stage.val

private def firstBiasZeroAddress (l : Launch) (g : Nat) (stage : Fin 2) : Nat :=
  kvSwizzle (firstBiasRawRow l g 0 + 166912) + 32768 * stage.val

private theorem firstBiasRowMask (tid : Nat) :
    (tid * 128) &&& 16256 = 128 * (tid % 128) := by
  rw [show tid * 128 = tid <<< 7 by simp [Nat.shiftLeft_eq],
    show (16256 : Nat) = 127 <<< 7 by decide, ← Nat.shiftLeft_and_distrib,
    show (127 : Nat) = 2 ^ 7 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  simp [Nat.shiftLeft_eq, Nat.mul_comm]

private def firstBiasRawFacts (l : Launch) (g : Nat) (stage : Fin 2) : List (Nat × Value) :=
  [(2790, b32 (firstBiasRawRow l g stage)), (2784, b32 (firstBiasZeroAddress l g stage)),
    (2788, b32 (scoreAddress l g stage 0)), (2789, b32 (scoreAddress l g stage 2)),
    (2775, b32 (g % l.block))]

variable {p : Params} {l : Launch} {m : Mem0}

private theorem firstBiasRawRowSegment (hp : Pre p l m) (g : Nat) (stage : Fin 2) :
    Seg kernel [] l g 16 3293 [(2535, b32 l.sharedBase), (481, .pred (stage.val = 1))]
      3309 (firstBiasRawFacts l g stage) := by
  have hTid : (l.tidOf g).get .x = g % l.block :=
    Option.some.inj (sregValue_oneDim hp.cluster.2.2 g).1
  have hT : g % l.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hB := hp.shared.2.1
  have hRow := Nat.mod_lt (g % l.block) (by decide : 0 < 128)
  have hLane := tmem_warp_encoding_lt l g (col := 0) (by decide)
  have hMask (n : Nat) : n &&& 112 < 4294967296 :=
    Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hSwizzle :
      kvSwizzle (l.sharedBase + 128 * (g % l.block % 128) + 166912) < 262144 := by
    unfold kvSwizzle
    exact Nat.xor_lt_two_pow (n := 18) (by omega)
      (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))
  simp only [kvSwizzle, Nat.shiftRight_eq_div_pow, Nat.reducePow] at hSwizzle
  have hLaneField : (g % l.block * 65536) &&& 6291456 = 65536 * laneBase l g := by
    simpa only [Nat.shiftLeft_eq, Nat.reducePow] using tmem_lane_field_mask l g
  have hOr0 : (128 : Nat) ||| (65536 * laneBase l g) = 65536 * laneBase l g + 128 := by
    rw [Nat.or_comm, PTX.Proof.lor_eq_add (k := 16) (by omega) (by decide)]
  have hOr2zero : (65536 * laneBase l g) ||| 64 = 65536 * laneBase l g + 64 :=
    PTX.Proof.lor_eq_add (k := 7) (by omega) (by decide)
  have hOr2one : (65536 * laneBase l g + 128) ||| 64 = 65536 * laneBase l g + 192 := by
    rw [PTX.Proof.lor_eq_add (k := 7) (by omega) (by decide)]
  fin_cases stage <;> intro t ht
  all_goals
    simp [firstBiasRawFacts, firstBiasRawRow, firstBiasZeroAddress, scoreAddress, scoreColumn,
      kvSwizzle, Nat.shiftRight_eq_div_pow] at ht ⊢
    seg_fp ht using
      nf_simp [hTid, nf_xor]
      simp (disch := omega) only [Nat.mod_eq_of_lt (hMask _), Nat.mod_eq_of_lt, firstBiasRowMask,
        hLaneField, Nat.zero_or, hOr0, hOr2zero, hOr2one, Nat.xor_comm, Nat.add_zero]

private theorem firstBiasAddressValue (hp : Pre p l m) (g : Nat) (stage : Fin 2) (i : Fin 16) :
    kvSwizzle (firstBiasRawRow l g stage +
      (166912 + 16384 * (i.val / 8) + 16 * (i.val % 8))) = biasVectorAddress l g stage i := by
  let base := biasBoxStart l stage (i.val / 8)
  let row := (g % l.block) % 128
  let col := i.val % 8
  have hBase : base % 128 = 0 := by
    have h := hp.shared.1
    dsimp [base, biasBoxStart]
    omega
  have hRaw : firstBiasRawRow l g stage +
      (166912 + 16384 * (i.val / 8) + 16 * (i.val % 8)) = base + 128 * row + 16 * col := by
    simp only [firstBiasRawRow, base, biasBoxStart, row, col]
    omega
  rw [hRaw]
  unfold kvSwizzle
  rw [Nat.xor_comm]
  exact biasSwizzleWord (row := row) hBase (Nat.mod_lt i.val (by decide))

private theorem firstBiasBodyValue (hp : Pre p l m) (g : Nat) (stage : Fin 2) (i : Fin 14) :
    kvSwizzle (firstBiasRawRow l g stage + firstBiasDisplacement i) =
      biasVectorBase l g stage false (firstBiasVector i) := by
  have hOff : (biasReadSite false (firstBiasVector i)).offset = 0 := by
    fin_cases i <;> decide
  rw [biasVectorBase, hOff, Nat.sub_zero]
  exact firstBiasAddressValue hp g stage (firstBiasVector i)

set_option maxRecDepth 100000 in
private theorem firstBiasZeroValue (hp : Pre p l m) (g : Nat) (stage : Fin 2) (i : Fin 16)
    (hi : i = 0 ∨ i = 8) :
    firstBiasZeroAddress l g stage = biasVectorBase l g stage false i := by
  let raw := firstBiasRawRow l g 0 + 166912
  have hStep : firstBiasRawRow l g stage + 166912 = raw + 1024 * (32 * stage.val) := by
    simp [firstBiasRawRow, raw]
    omega
  have hZero : firstBiasZeroAddress l g stage = kvSwizzle (firstBiasRawRow l g stage + 166912) := by
    rw [hStep, Mma.kvSwizzle_add_period]
    simp only [firstBiasZeroAddress, raw]
    omega
  rcases hi with rfl | rfl
  · rw [hZero, biasVectorBase, show (biasReadSite false 0).offset = 0 from rfl, Nat.sub_zero]
    exact firstBiasAddressValue hp g stage 0
  · have hUpper := firstBiasAddressValue hp g stage 8
    change kvSwizzle (firstBiasRawRow l g stage + 166912 + 1024 * 16) = _ at hUpper
    rw [Mma.kvSwizzle_add_period, ← hZero] at hUpper
    unfold biasVectorBase
    change _ = biasVectorAddress l g stage 8 - 16384
    omega

private theorem firstBiasLanePredicate {l : Launch} {g : Nat} (hTid : g % l.block < 512) :
    Seg kernel [] l g 2 3365 [(2775, b32 (g % l.block))]
      3367 [(482, .pred (laneOf l g ≠ 0))] := by
  intro t ht
  have hSmall : g % l.block % 32 < 2 ^ 64 := by omega
  seg_fp ht using
    nf_simp [laneOf]
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    change decide (((BitVec.ofNat 64 (g % l.block % 32)).toNat : Int) ≠ 0) =
      decide (g % l.block % 32 ≠ 0)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hSmall]
    exact decide_eq_decide.mpr Int.natCast_ne_zero

/-- Active softmax address inputs at the beginning of the stage-specific setup. -/
def firstBiasAddressInput (p : Params) (l : Launch) (warp : Fin 8) (batch tile : Nat) :
    List (Nat × Value) :=
  [(1062, b32 warp.val), (2535, b32 l.sharedBase), (5127, b32 (3 + warp.val)),
    (7247, b32 batch), (7246, b32 tile), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase)]

private def firstBiasStageFacts (p : Params) (l : Launch) (g : Nat) (warp : Fin 8)
    (batch tile : Nat) (stage : Fin 2) : List (Nat × Value) :=
  [(481, .pred (stage.val = 1)), (2772, b32 stage.val),
    (2774, b32 (l.sharedBase + 8 * stage.val)),
    (2769, b32 (waitLoc l g stage 1).addr), (2771, b32 (waitLoc l g stage 2).addr)] ++
    firstBiasAddressInput p l warp batch tile

private theorem firstBiasStageTest (p : Params) (l : Launch) (g : Nat)
    (warp : Fin 8) (batch tile : Nat) :
    Seg kernel [] l g 1 3286 (firstBiasAddressInput p l warp batch tile)
      3287 ((481, .pred ((stageOf warp).val = 1)) ::
        firstBiasAddressInput p l warp batch tile) := by
  fin_cases warp <;> intro t ht <;>
    simp only [firstBiasAddressInput, stageOf, Fin.val_mk, Nat.reduceDiv] at ht ⊢ <;>
    seg_fp ht using decide +kernel

private theorem firstBiasStageAddressCore (hp : Pre p l m) (g : Nat) (warp : Fin 8)
    (batch tile : Nat) (stage : Fin 2) :
    Seg kernel [] l g 6 3287
      ((481, .pred (stage.val = 1)) :: firstBiasAddressInput p l warp batch tile)
      3293 (firstBiasStageFacts p l g warp batch tile stage) := by
  have hBound := hp.shared.2.1
  fin_cases stage <;> intro t ht <;>
    simp [firstBiasAddressInput, firstBiasStageFacts, waitLoc, waitSite] at ht ⊢ <;>
    seg_fp ht using norm_bits

private theorem firstBiasStageSegment (hp : Pre p l m) (g : Nat) (warp : Fin 8) (batch tile : Nat) :
    Seg kernel [] l g 7 3286 (firstBiasAddressInput p l warp batch tile)
      3293 (firstBiasStageFacts p l g warp batch tile (stageOf warp)) :=
  (firstBiasStageTest p l g warp batch tile).comp
    (firstBiasStageAddressCore hp g warp batch tile (stageOf warp))

private theorem firstBiasVectorIndex (i : Fin 16) (hi : ¬ (i = 0 ∨ i = 8)) :
    ∃ j : Fin 14, firstBiasVector j = i := by
  have hlo : i.val ≠ 0 := fun h => hi (.inl (Fin.ext h))
  have hhi : i.val ≠ 8 := fun h => hi (.inr (Fin.ext h))
  have hb := i.isLt
  by_cases h : i.val < 8
  · let j : Fin 14 := ⟨14 - i.val, by omega⟩
    refine ⟨j, Fin.ext ?_⟩
    have hJ : ¬ j.val < 7 := by dsimp [j]; omega
    simp only [firstBiasVector, Fin.val_mk, ite_eq_right hJ, j]
    omega
  · let j : Fin 14 := ⟨15 - i.val, by omega⟩
    refine ⟨j, Fin.ext ?_⟩
    have hJ : j.val < 7 := by dsimp [j]; omega
    simp only [firstBiasVector, Fin.val_mk, ite_eq_left hJ, j]
    omega

/-- The real stage setup computes every first Bias vector base and both QK addresses,
and retains them along the path to the first request length load. -/
theorem firstBiasAddressSegment (hp : Pre p l m) (g : Nat) (warp : Fin 8) (batch tile : Nat) :
    Seg kernel Assumptions.all l g 81 3286 (firstBiasAddressInput p l warp batch tile)
      3367 (firstGeometryAddressInput p l g batch tile (stageOf warp) ++
        singleVisitGeometryCarry l g warp) := by
  intro t ht
  let stage := stageOf warp
  let R := firstBiasRawRow l g stage
  let F := firstBiasStageFacts p l g warp batch tile stage
  let G := firstBiasRawFacts l g stage ++ F
  let D := (List.finRange 14).map (fun i => 2794 + 4 * i.val)
  have hTid : g % l.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hBound := hp.shared.2.1
  have hStage := stage.isLt
  have hRow := Nat.mod_lt (g % l.block) (by decide : 0 < 128)
  have hRawBound : R + 183408 < 4294967296 := by dsimp [R, firstBiasRawRow]; omega
  obtain ⟨v, hV, hv⟩ := (firstBiasStageSegment hp g warp batch tile).apply ht
  have hv' : At v 3293 [(2535, b32 l.sharedBase), (481, .pred (stage.val = 1))] := by
    apply hv.mono
    exact ⟨holds_mem hv.2.2.2.2 (by simp [firstBiasStageFacts, firstBiasAddressInput]),
      hv.2.2.2.2.1, trivial⟩
  obtain ⟨w, hW, hw⟩ := (firstBiasRawRowSegment hp g stage).apply hv'
  have hKeepW (r : Nat) (hr : r ∈ F.map Prod.fst) : w.regs r = v.regs r :=
    schedulerLocalFrame (lo := 3293) (len := 16)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hW hv.1.ge (by rw [hv.1]) hr
  have hFrameW : Holds w.regs G := (holds_append ..).mpr ⟨hw.2.2.2.2,
    holdsSchedulerFrame hv.2.2.2.2 hKeepW (fun _ hx => List.mem_map_of_mem hx)⟩
  obtain ⟨y, hY, hy, hWords⟩ := firstBiasBodyPrefix
    (l := l) (g := g) (hw.mono ⟨hw.2.2.2.2.1, trivial⟩) hRawBound 14 (by decide)
  have hKeepY (r : Nat) (hr : r ∈ G.map Prod.fst) : y.regs r = w.regs r :=
    schedulerLocalFrame (lo := 3309) (len := 56)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hY hw.1.ge (by rw [hw.1]) hr
  have hFrameY := holdsSchedulerFrame hFrameW hKeepY (fun _ hx => List.mem_map_of_mem hx)
  have hy' : At y 3365 [(2775, b32 (g % l.block))] :=
    hy.mono ⟨holds_mem hFrameY (by simp [G, firstBiasRawFacts]), trivial⟩
  obtain ⟨u, hU, hu⟩ := (firstBiasLanePredicate (l := l) (g := g) hTid).apply hy'
  have hLast (r : Nat) (hr : r ∈ G.map Prod.fst ++ D) : u.regs r = y.regs r :=
    schedulerLocalFrame (lo := 3365) (len := 2)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hU hy.1.ge (by rw [hy.1]) hr
  have hFrameU := holdsSchedulerFrame hFrameY hLast (fun _ hx =>
    List.mem_append_left _ (List.mem_map_of_mem hx))
  have hBases (i : Fin 16) :
      u.regs (biasReadSite false i).base = some (b32 (biasVectorBase l g stage false i)) := by
    by_cases hi : i = 0 ∨ i = 8
    · rw [← firstBiasZeroValue hp g stage i hi]
      have hReg : (biasReadSite false i).base = 2784 := by rcases hi with rfl | rfl <;> rfl
      rw [hReg]
      exact holds_mem hFrameU (by simp [G, firstBiasRawFacts])
    · obtain ⟨j, rfl⟩ := firstBiasVectorIndex i hi
      rw [← firstBiasBodyValue hp g stage j]
      have hReg : (biasReadSite false (firstBiasVector j)).base = 2794 + 4 * j.val := by
        fin_cases j <;> rfl
      rw [hReg, hLast _ (List.mem_append_right _
        (List.mem_map_of_mem (List.mem_finRange j) : 2794 + 4 * j.val ∈ D))]
      exact hWords j j.isLt
  have hBasesFrame : Holds u.regs ((List.finRange 16).map
      (fun i => ((biasReadSite false i).base, b32 (biasVectorBase l g stage false i)))) := by
    generalize List.finRange 16 = is
    induction is with
    | nil => trivial
    | cons i is ih => exact ⟨hBases i, ih⟩
  have hFull : run kernel [] l g 81 t = some u :=
    run_comp (run_comp (run_comp hV hW) hY) hU
  have hLinear := firstBiasLinear (regs := []) (by decide) (by decide) ht.1
    (List.all_eq_true.mpr (fun _ _ => rfl))
    (by set_option maxRecDepth 100000 in kernel_rfl) hFull
  refine ⟨u, hLinear.1, hu.mono ?_⟩
  simp only [firstGeometryAddressInput, geometryAddressInputs, firstGeometrySync,
    singleVisitGeometryCarry, biasFenceFacts, biasStageReg, biasKeep, Bool.false_eq_true, ite_false,
    holds_append, holds_cons, holds_nil]
  repeat' first | exact hBasesFrame | exact hu.2.2.2.2.1 | apply And.intro
  all_goals first
    | trivial
    | exact holds_mem hFrameU (by
        simp [G, F, firstBiasRawFacts, firstBiasStageFacts, firstBiasAddressInput, stage])

/-- The shared bases for the first sixteen Bias vectors in one softmax lane. -/
def firstBiasBases (l : Launch) (g : Nat) (warp : Fin 8) : List (Nat × Value) :=
  (List.finRange 16).map
    (fun i => ((biasReadSite false i).base, b32 (biasVectorBase l g (stageOf warp) false i)))

private theorem firstBiasStageOnly (l : Launch) (g : Nat) (warp : Fin 8) :
    Seg kernel [] l g 1 3286 [(1062, b32 warp.val), (2535, b32 l.sharedBase)]
      3287 [(481, .pred ((stageOf warp).val = 1)), (2535, b32 l.sharedBase)] := by
  intro t ht
  seg_fp ht using (fin_cases warp <;> rfl)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem firstBiasBarrierAddressLocals (l : Launch) (g : Nat) (stage : Fin 2) :
    Seg kernel [] l g 6 3287 [(481, .pred (stage.val = 1)), (2535, b32 l.sharedBase)]
      3293 [(2535, b32 l.sharedBase), (481, .pred (stage.val = 1))] := by
  fin_cases stage <;> intro t ht <;> seg_fp ht using rfl

/-- The score tile's first and third addresses are prepared by the first bias setup. -/
theorem firstScoreBaseSetup (hp : Pre p l m) (g : Nat) (warp : Fin 8) :
    Seg kernel Assumptions.all l g 23 3286 [(1062, b32 warp.val), (2535, b32 l.sharedBase)]
      3309 [(2788,b32 (scoreAddress l g (stageOf warp) 0)),
        (2789,b32 (scoreAddress l g (stageOf warp) 2))] := by
  intro t ht
  let stage := stageOf warp
  obtain ⟨u, hU, hu⟩ := ((firstBiasStageOnly l g warp).comp
    (firstBiasBarrierAddressLocals l g stage)).apply ht
  obtain ⟨v, hV, hv⟩ := (firstBiasRawRowSegment hp g stage).apply hu
  have hFull : run kernel [] l g 23 t = some v := run_comp hU hV
  have hLinear := firstBiasLinear (regs := []) (by decide) (by decide) ht.1
    (List.all_eq_true.mpr (fun _ _ => rfl)) (by decide +kernel) hFull
  exact ⟨v,hLinear.1,hv.mono ⟨hv.2.2.2.2.2.2.1,hv.2.2.2.2.2.2.2.1,trivial⟩⟩

/-- Replay the first Bias vector address setup using only the warp and shared base.
The address calculation holds for every actual first-round read, regardless of metadata values. -/
theorem firstBiasAddressBases (hp : Pre p l m) (g : Nat) (warp : Fin 8) :
    Seg kernel Assumptions.all l g 79 3286 [(1062, b32 warp.val), (2535, b32 l.sharedBase)]
      3365 (firstBiasBases l g warp) := by
  let stage := stageOf warp
  let base := firstBiasRawRow l g stage
  have hShared := hp.shared.2.1
  have hRow := Nat.mod_lt (g % l.block) (show 0 < 128 by decide)
  have hStage := stage.isLt
  have hBound : base + 183408 < 4294967296 := by dsimp [base, firstBiasRawRow]; omega
  intro t ht
  obtain ⟨u, hU, hu⟩ := ((firstBiasStageOnly l g warp).comp
    (firstBiasBarrierAddressLocals l g stage)).apply ht
  obtain ⟨v, hV, hv⟩ := (firstBiasRawRowSegment hp g stage).apply hu
  obtain ⟨w, hW, hw, hWords⟩ := firstBiasBodyPrefix
    (l := l) (g := g) (hv.mono ⟨hv.2.2.2.2.1, trivial⟩) hBound 14 (by decide)
  have hZeroReg : w.regs 2784 = some (b32 (firstBiasZeroAddress l g stage)) := by
    rw [schedulerLocalFrame (lo := 3309) (len := 56) (regs := [2784])
      (by decide +kernel) (by decide +kernel) hW hv.1.ge (by rw [hv.1]) (by simp)]
    exact hv.2.2.2.2.2.1
  have hBases (i : Fin 16) :
      w.regs (biasReadSite false i).base = some (b32 (biasVectorBase l g stage false i)) := by
    by_cases hFirst : i = 0 ∨ i = 8
    · rw [← firstBiasZeroValue hp g stage i hFirst]
      rcases hFirst with rfl | rfl <;> exact hZeroReg
    · obtain ⟨j, rfl⟩ := firstBiasVectorIndex i hFirst
      rw [← firstBiasBodyValue hp g stage j]
      have hReg := (by decide : ∀ j : Fin 14,
        (biasReadSite false (firstBiasVector j)).base = 2794 + 4 * j.val) j
      rw [hReg]
      exact hWords j j.isLt
  have hHolds : Holds w.regs (firstBiasBases l g warp) := by
    unfold firstBiasBases
    induction List.finRange 16 with
    | nil => trivial
    | cons i rest ih => exact ⟨hBases i, ih⟩
  have hFull : run kernel [] l g 79 t = some w := run_comp (run_comp hU hV) hW
  have hLinear := firstBiasLinear (regs := []) (by decide) (by decide) ht.1
    (List.all_eq_true.mpr (fun _ _ => rfl)) (by decide +kernel) hFull
  exact ⟨w, hLinear.1, hw.mono hHolds⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem firstBiasBarTail (p : Params) (l : Launch) (g : Nat) (warp : Fin 8)
    (batch : Nat) :
    Seg kernel [] l g 3 3283 ((5127, b32 (3 + warp.val)) :: firstActiveTileFacts p l g warp batch)
      3286 (firstBiasAddressInput p l warp batch
        (assignedCoordinates p batch (g / l.block)).1) := by
  intro t ht
  simp only [firstActiveTileFacts, dispatchInput, firstBiasAddressInput,
    List.cons_append, List.nil_append] at ht ⊢
  seg_fp ht using rfl

private theorem firstBiasBarSegment (p : Params) (l : Launch) (g : Nat) (warp : Fin 8)
    (batch : Nat) :
    Seg kernel [] l g 12 3274 (firstActiveTileFacts p l g warp batch) 3286
      (firstBiasAddressInput p l warp batch (assignedCoordinates p batch (g / l.block)).1) := by
  intro t ht
  let F := firstActiveTileFacts p l g warp batch
  have hWarp : (1062, b32 warp.val) ∈ F := by simp [F, firstActiveTileFacts, dispatchInput]
  obtain ⟨v, hV, hv⟩ := (softmaxStatsBarrierCore l g warp).apply
    (ht.mono ⟨holds_mem ht.2.2.2.2 hWarp, trivial⟩)
  have hKeep (r : Nat) (hr : r ∈ F.map Prod.fst) : v.regs r = t.regs r :=
    schedulerLocalFrame (lo := 3274) (len := 9)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hV ht.1.ge (by rw [ht.1]) hr
  have hv' : At v 3283 ((5127, b32 (3 + warp.val)) :: F) :=
    hv.mono ⟨hv.2.2.2.2.1,
      holdsSchedulerFrame ht.2.2.2.2 hKeep (fun _ hx => List.mem_map_of_mem hx)⟩
  obtain ⟨u, hU, hu⟩ := (firstBiasBarTail p l g warp batch).apply hv'
  exact ⟨u, run_comp hV hU, hu⟩

/-- The selected softmax lane reaches its first metadata load with the exact Bias and QK
address registers and the lane predicates required by the first round. -/
theorem firstActiveBiasAddresses (hp : Pre p l m) (g : Nat) (warp : Fin 8) (batch : Nat) :
    Seg kernel Assumptions.all l g 93 3274 (firstActiveTileFacts p l g warp batch) 3367
      (firstGeometryAddressInput p l g batch (assignedCoordinates p batch (g / l.block)).1
        (stageOf warp) ++ singleVisitGeometryCarry l g warp) := by
  have hBar : Seg kernel Assumptions.all l g 12 3274 (firstActiveTileFacts p l g warp batch) 3286
      (firstBiasAddressInput p l warp batch (assignedCoordinates p batch (g / l.block)).1) := by
    intro t ht
    obtain ⟨u, hu, hU⟩ := (firstBiasBarSegment p l g warp batch).apply ht
    have hLinear := firstBiasLinear (regs := []) (by decide) (by decide) ht.1
      (List.all_eq_true.mpr (fun _ _ => rfl))
      (by set_option maxRecDepth 100000 in kernel_rfl) hu
    exact ⟨u, hLinear.1, hU⟩
  exact hBar.comp (firstBiasAddressSegment hp g warp batch
    (assignedCoordinates p batch (g / l.block)).1)

/-- The active lane's metadata reads and correction acknowledgement reach the first QK wait
with the concrete Bias addresses and first-visit geometry on that lane's actual trace. -/
theorem firstActiveSingleVisitGeometry {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (warp : Fin 8) {g j batch : Nat}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 = 1) {t : TState}
    (ht : At t 3274 (firstActiveTileFacts p l g warp batch))
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let tile := (assignedCoordinates p batch (g / l.block)).1
    ∃ fails u, FirstGeometryReads p X g j batch ∧
      At u 3425 (singleVisitRoundFacts p l g warp batch tile
        (1 - stageGeometryBlocks p batch tile (stageOf warp) + 10)
        (p.kLength batch - p.qLength batch + 256 * tile)) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + 3 + fails + 1)) none := by
  obtain ⟨v, hV, hv⟩ := (firstActiveBiasAddresses hp g warp batch).apply ht
  exact singleVisitGeometryReady hp hX warp hb (assignedCoordinates_valid hp hLo hHi).1
    hTrip hv writes (hr.after_local (run_rtg hV))

end PTX.Kernels.TmlFa4Fwd.Softmax
