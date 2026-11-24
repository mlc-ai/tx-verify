-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasLayout
public import Kernels.TmlFa4Fwd.Proof.SoftmaxStartup
public import Kernels.TmlFa4Fwd.Proof.PagedKvGeometry
import Kernels.TmlFa4Fwd.Flow.Code.Part078
public import Kernels.TmlFa4Fwd.Proof.SoftmaxUnbiasedProbabilityAddress
import Kernels.TmlFa4Fwd.Flow.Code.Part079
import Kernels.TmlFa4Fwd.Flow.Code.Part081
public import Lemmas.Flow.SegChain
import Lemmas.Flow.Swizzle
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Kernels.TmlFa4Fwd.Assumptions.Transparency

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax

open PTX PTX.Proof PTX.Flow

def repeatedBiasRowBase (l : Launch) (g : Nat) : Nat :=
  l.sharedBase + 128 * ((g % l.block) % 128)

def repeatedBiasStageOffset (w : Fin 8) : Nat := 32768 * (stageOf w).val

private theorem rowMask (tid : Nat) : (tid <<< 7) &&& 16256 = 128 * (tid % 128) := by
  rw [show (16256 : Nat) = 127 <<< 7 by decide, ← Nat.shiftLeft_and_distrib,
    show (127 : Nat) = 2 ^ 7 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq]
  omega

private theorem maskedTidRow (tid : Nat) :
    ((tid * 128) % 4294967296 &&& 16256) = 128 * (tid % 128) := by
  have h : (tid * 128 &&& 16256) % 2 ^ 32 =
      (tid * 128) % 2 ^ 32 &&& 16256 % 2 ^ 32 := Nat.and_mod_two_pow
  have hMask : 16256 % 2 ^ 32 = 16256 := by decide
  rw [hMask] at h
  have hLt := Nat.and_lt_two_pow (tid * 128) (by decide : 16256 < 2 ^ 32)
  rw [Nat.mod_eq_of_lt hLt] at h
  change (tid * 128) % 2 ^ 32 &&& 16256 = _
  rw [← h, show tid * 128 = tid <<< 7 by rw [Nat.shiftLeft_eq], rowMask]

private theorem repeatedStage (l : Launch) (g : Nat) (w : Fin 8) :
    Seg kernel Assumptions.all l g 1 5032
      [(1062, b32 w.val), (2535, b32 l.sharedBase)] 5033
      [(631, .pred (decide (3 < w.val))), (2535, b32 l.sharedBase)] := by
  intro t ht
  seg_fp ht using
    (fin_cases w <;> rfl)

private theorem repeatedTid {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Bool) :
    Seg kernel Assumptions.all l g 8 5033
      [(631, .pred stage), (2535, b32 l.sharedBase)] 5041
      [(631, .pred stage), (2535, b32 l.sharedBase), (3967, b32 (g % l.block))] := by
  have hTid := Nat.mod_lt g (show 0 < l.block by rw [hp.block]; decide)
  have ht32 : g % l.block < 2 ^ 32 := by rw [hp.block] at hTid ⊢; omega
  have hTidRaw : (l.tidOf g).get .x = g % l.block :=
    Option.some.inj ((sregValue_oneDim hp.cluster.2.2 g).1)
  cases stage <;> intro t ht <;> seg_fp ht using
    (nf_simp [hTidRaw]
     all_goals omega)

/-- A biased replay recomputes all four score word addresses from the physical warp. -/
theorem biasedScoreAddressSegment {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (w : Fin 8) :
    Seg kernel Assumptions.all l g 9 5032
      [(1062,b32 w.val),(2535,b32 l.sharedBase)] 5041
      (roundScoreFacts l g (stageOf w) .biased) := by
  let stage := stageOf w
  have hStage : decide (3 < w.val) = decide (stage.val = 1) := by
    fin_cases w <;> rfl
  have hBlock : g % l.block < 512 := hp.block ▸ Nat.mod_lt g (by rw [hp.block]; decide)
  have hSmall : g % l.block < 4294967296 := by omega
  have hShift : (g % l.block) * 65536 < 4294967296 := by omega
  have hTid : (l.tidOf g).get .x = g % l.block :=
    Option.some.inj ((sregValue_oneDim hp.cluster.2.2 g).1)
  have hMask : ((g % l.block % 4294967296) * 65536 % 4294967296) &&& 6291456 =
      65536 * laneBase l g := by
    rw [Nat.mod_eq_of_lt hSmall,Nat.mod_eq_of_lt hShift]
    have h := tmem_lane_field_mask l g
    rwa [Nat.shiftLeft_eq] at h
  have hField : 65536 * laneBase l g < 2^32 := by
    simpa only [Nat.add_zero,Nat.reducePow] using tmem_warp_encoding_lt l g (col := 0) (by decide)
  have hThread (stage : Fin 2) : Seg kernel Assumptions.all l g 2 5033
      [(631,.pred (decide (stage.val = 1))),(2535,b32 l.sharedBase)] 5035
      [(3967,b32 (g % l.block)),(3966,b32 (scoreColumn stage))] := by
    fin_cases stage <;> intro t ht <;> seg_fp ht using
      (nf_simp [hTid,scoreColumn]; all_goals omega)
  have hLane (stage : Fin 2) : Seg kernel Assumptions.all l g 2 5035
      [(3967,b32 (g % l.block)),(3966,b32 (scoreColumn stage))] 5037
      [(3969,b32 (65536 * laneBase l g)),(3966,b32 (scoreColumn stage))] := by
    intro t ht
    seg_fp ht using norm_bits [hMask,Nat.mod_eq_of_lt hField]
  have hCore (stage : Fin 2) : Seg kernel Assumptions.all l g 4 5037
      [(3969,b32 (65536 * laneBase l g)),(3966,b32 (scoreColumn stage))] 5041
      (roundScoreFacts l g stage .biased) := by
    fin_cases stage <;> intro s hs <;>
      simp only [roundScoreFacts,List.ofFn_succ,List.ofFn_zero,scoreReg,scoreAddress,
        scoreColumn] at hs ⊢ <;>
      seg_fp hs using
        first
        | exact scoreBaseAddressBits l g 0 (by decide)
        | exact probabilityAddressBits l g 0 32 (by decide) (by decide)
        | exact probabilityAddressBits l g 0 64 (by decide) (by decide)
        | exact probabilityAddressBits l g 0 96 (by decide) (by decide)
        | exact scoreBaseAddressBits l g 128 (by decide)
        | exact probabilityAddressBits l g 128 32 (by decide) (by decide)
        | exact probabilityAddressBits l g 128 64 (by decide) (by decide)
        | exact probabilityAddressBits l g 128 96 (by decide) (by decide)
  intro t ht
  obtain ⟨u,hu,huAt⟩ := (repeatedStage l g w).apply ht
  rw [hStage] at huAt
  obtain ⟨v,hv,hvAt⟩ := (((hThread stage).comp (hLane stage)).comp (hCore stage)).apply huAt
  exact ⟨v,run_comp hu hv,hvAt⟩

private theorem repeatedRow {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Bool) :
    Seg kernel Assumptions.all l g 5 5041
      [(631, .pred stage), (2535, b32 l.sharedBase), (3967, b32 (g % l.block))] 5046
      [(3976, b32 (repeatedBiasRowBase l g)), (3977, b32 (if stage then 32768 else 0)),
        (3978, b32 (repeatedBiasRowBase l g + if stage then 32768 else 0)),
        (631, .pred stage)] := by
  let tid := g % l.block
  have hTid := Nat.mod_lt g (show 0 < l.block by rw [hp.block]; decide)
  have ht32 : tid < 2 ^ 32 := by dsimp [tid]; rw [hp.block] at hTid ⊢; omega
  have ht64 : tid < 2 ^ 64 := by omega
  have hShared := hp.shared.2.1
  have hRow : tid % 128 < 128 := Nat.mod_lt _ (by decide)
  have hBase : l.sharedBase < 2 ^ 32 := by omega
  have hAddr : l.sharedBase + 128 * (tid % 128) < 2 ^ 32 := by omega
  have hSum : l.sharedBase + 128 * (tid % 128) + 32768 < 2 ^ 32 := by omega
  change Seg kernel Assumptions.all l g 5 5041
    [(631, .pred stage), (2535, b32 l.sharedBase), (3967, b32 tid)] 5046
    [(3976, b32 (l.sharedBase + 128 * (tid % 128))), (3977, b32 (if stage then 32768 else 0)),
      (3978, b32 (l.sharedBase + 128 * (tid % 128) + if stage then 32768 else 0)),
      (631, .pred stage)]
  cases stage <;> intro t ht <;> seg_fp ht using
    (nf_simp [Nat.mod_eq_of_lt ht32, Nat.mod_eq_of_lt ht64, Nat.mod_eq_of_lt hBase,
        Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hSum, maskedTidRow]
     all_goals try omega)

/-- The repeated Bias setup computes the unswizzled row base and the physical stage increment. -/
theorem repeatedBiasRowSetupFramed {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (w : Fin 8) :
    Seg kernel Assumptions.all l g 14 5032
      [(1062, b32 w.val), (2535, b32 l.sharedBase)] 5046
      [(3976, b32 (repeatedBiasRowBase l g)), (3977, b32 (repeatedBiasStageOffset w)),
        (3978, b32 (repeatedBiasRowBase l g + repeatedBiasStageOffset w)),
        (631,.pred ((stageOf w).val = 1))] := by
  have hStage : (if decide (3 < w.val) then 32768 else 0) = repeatedBiasStageOffset w := by
    fin_cases w <;> rfl
  have hPred : decide (3 < w.val) = decide ((stageOf w).val = 1) := by
    fin_cases w <;> rfl
  rw [← hStage,← hPred]
  exact (repeatedStage l g w).comp
    ((repeatedTid hp g (decide (3 < w.val))).comp (repeatedRow hp g (decide (3 < w.val))))

/-- The fourteen independent address calculations other than the two vectors that
share the final address register. The order is the frozen instruction order. -/
def repeatedBiasVector (i : Fin 14) : Fin 16 :=
  ⟨if i.val < 7 then 15 - i.val else 14 - i.val, by split <;> omega⟩

/-- Displacement from the biased row base for an independently addressed vector. -/
def repeatedVectorDisplacement (i : Fin 14) : Nat :=
  let col := (repeatedBiasVector i).val
  166912 + 16384 * (col / 8) + 16 * (col % 8)

private def repeatedVectorCoreSpec (l : Launch) (g base : Nat) (i : Fin 14) : Prop :=
  Seg kernel [] l g 4 (5046 + 4 * i.val) [(3978, b32 base)] (5046 + 4 * (i.val + 1))
    [(3982 + 4 * i.val, b32 (kvSwizzle (base + repeatedVectorDisplacement i))), (3978, b32 base)]

local macro "prove_repeat_quad " j:term : tactic =>
  `(tactic| (
    unfold repeatedVectorCoreSpec
    have hMask (n : Nat) : (n &&& 112) < 4294967296 :=
      Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    fin_cases $j:term <;> intro t ht
    all_goals
      simp only [repeatedVectorDisplacement, repeatedBiasVector, Fin.val_mk,
        Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul,
        Nat.reduceAdd, kvSwizzle, Nat.shiftRight_eq_div_pow, Nat.reducePow] at ht ⊢
      seg_fp ht using
        nf_simp [nf_xor]
        all_goals try (simp (disch := omega) only [Nat.mod_eq_of_lt (hMask _), Nat.mod_eq_of_lt])
        all_goals rw [Nat.xor_comm]))

private theorem repeatedVectorCoreLower {l : Launch} {g base : Nat} (j : Fin 7)
    (hBound : base + 183408 < 4294967296) :
    repeatedVectorCoreSpec l g base ⟨j.val, by have := j.isLt; omega⟩ := by
  prove_repeat_quad j

private theorem repeatedVectorCoreUpper {l : Launch} {g base : Nat} (j : Fin 7)
    (hBound : base + 183408 < 4294967296) :
    repeatedVectorCoreSpec l g base ⟨7 + j.val, by have := j.isLt; omega⟩ := by
  prove_repeat_quad j

private theorem repeatedVectorCore {l : Launch} {g base : Nat} (i : Fin 14)
    (hBound : base + 183408 < 4294967296) : repeatedVectorCoreSpec l g base i := by
  by_cases hi : i.val < 7
  · exact repeatedVectorCoreLower ⟨i.val, hi⟩ hBound
  · let j : Fin 7 := ⟨i.val - 7, by have := i.isLt; omega⟩
    have hEq : (⟨7 + j.val, by have := j.isLt; omega⟩ : Fin 14) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    exact hEq ▸ repeatedVectorCoreUpper j hBound

private theorem repeatQuadOut {l : Launch} {g : Nat} {t : TState}
    (hLo : 5046 ≤ t.pc) (hHi : t.pc < 5102) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  have hAll : ((kernel.code.drop 5046).take 56).all (fun ins => Assumptions.coreOp ins.op) =
      true := by decide +kernel
  cases hc : kernel.code[t.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    have hMem : ins ∈ (kernel.code.drop 5046).take 56 := by
      apply List.mem_of_getElem? (i := t.pc - 5046)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo, hc]
    apply Assumptions.out_all_eq_nil _ _ _ hc (List.all_eq_true.mp hAll _ hMem)
    all_goals
      simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
        Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega

private theorem repeatedVectorStraight (i : Fin 14) :
    ((kernel.code.drop (5046 + 4 * i.val)).take 3).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op) = true := by
  have hAll : (List.finRange 14).all (fun j =>
      ((kernel.code.drop (5046 + 4 * j.val)).take 3).all
        (fun ins => Epilogue.schedulerFallsThrough ins.op)) = true := by decide +kernel
  exact List.all_eq_true.mp hAll i (List.mem_finRange _)

variable {p : Params} {l : Launch} {m : Mem0}

/-- A straight-line four-instruction group computes the swizzled base for its own vector. -/
theorem repeatedBiasOtherVectorSetup (hp : Pre p l m) (g : Nat) (w : Fin 8) (i : Fin 14) :
    Seg kernel Assumptions.all l g 4 (5046 + 4 * i.val)
      [(3978, b32 (repeatedBiasRowBase l g + repeatedBiasStageOffset w))]
      (5050 + 4 * i.val)
      [(3982 + 4 * i.val, b32 (kvSwizzle
        (repeatedBiasRowBase l g + repeatedBiasStageOffset w + repeatedVectorDisplacement i))),
        (3978, b32 (repeatedBiasRowBase l g + repeatedBiasStageOffset w))] := by
  let base := repeatedBiasRowBase l g + repeatedBiasStageOffset w
  have hBound : base + 183408 < 4294967296 := by
    have hShared := hp.shared.2.1
    have hRow := Nat.mod_lt (g % l.block) (show 0 < 128 by decide)
    have hStage := (stageOf w).isLt
    dsimp [base, repeatedBiasRowBase, repeatedBiasStageOffset]
    omega
  intro t ht
  have hCore := repeatedVectorCore (l := l) (g := g) i hBound
  unfold repeatedVectorCoreSpec at hCore
  obtain ⟨u, hRun, hAt⟩ := hCore.apply ht
  have hIndex := i.isLt
  have hStraight := Epilogue.schedulerLocalTransport (lo := 5046 + 4 * i.val) (len := 4)
    (repeatedVectorStraight i)
    (fun hlo hhi => repeatQuadOut (by omega) (by omega)) hRun
    (by rw [ht.1]) (by rw [ht.1])
  rw [show 5046 + 4 * (i.val + 1) = 5050 + 4 * i.val by omega] at hAt
  exact ⟨u, hStraight, hAt⟩

private theorem repeatedBiasFirstVectorSetupCore (hp : Pre p l m) (g : Nat) (w : Fin 8) :
    Seg kernel [] l g 5 5184
      [(3976, b32 (repeatedBiasRowBase l g)), (3977, b32 (repeatedBiasStageOffset w))] 5189
      [(4170, b32 (kvSwizzle (repeatedBiasRowBase l g + 166912) +
        repeatedBiasStageOffset w))] := by
  let row := repeatedBiasRowBase l g
  let off := repeatedBiasStageOffset w
  let raw := row + 166912
  have hShared := hp.shared.2.1
  have hRow : row ≤ l.sharedBase + 16256 := by
    have hm := Nat.mod_lt ((g % l.block)) (show 0 < 128 by decide)
    dsimp [row, repeatedBiasRowBase]
    omega
  have hOff : off ≤ 32768 := by
    have hStage := (stageOf w).isLt
    dsimp [off, repeatedBiasStageOffset]
    omega
  have hRaw : raw < 2 ^ 18 := by dsimp [raw]; omega
  have hMask (x : Nat) : x &&& 112 < 128 := Nat.and_lt_two_pow x (by decide : 112 < 2 ^ 7)
  have hSwizzle : kvSwizzle raw < 2 ^ 18 :=
    Nat.xor_lt_two_pow hRaw (by have := hMask (raw >>> 3); omega)
  have mod32 (x : Nat) (h : x < 2 ^ 32) : x % 4294967296 = x := Nat.mod_eq_of_lt h
  have mod64 (x : Nat) (h : x < 2 ^ 64) : x % 18446744073709551616 = x := Nat.mod_eq_of_lt h
  have narrow (x : Nat) (h : x < 2 ^ 32) : x % 4294967296 = x ∧
      x % 18446744073709551616 = x := ⟨mod32 x h, mod64 x (by omega)⟩
  have hAddr := narrow row (by omega)
  have hOffset := narrow off (by omega)
  have hFull := narrow raw (by omega)
  have hShift := narrow (raw / 8) (by omega)
  have hAnd := narrow (raw / 8 &&& 112) (by have := hMask (raw / 8); omega)
  have hWord := narrow (kvSwizzle raw) (by omega)
  have hTotal := narrow (kvSwizzle raw + off) (by omega)
  have hXor : raw / 8 &&& 112 ^^^ raw = kvSwizzle raw := by
    simp only [kvSwizzle, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.xor_comm]
  change Seg kernel [] l g 5 5184
    [(3976, b32 row), (3977, b32 off)] 5189 [(4170, b32 (kvSwizzle raw + off))]
  intro t ht
  seg_fp ht using
    (nf_simp [nf_xor, hAddr.1, hAddr.2, hOffset.1, hOffset.2, ← show raw = row + 166912 from rfl,
       hFull.1, hFull.2, hShift.1, hShift.2, hAnd.1, hAnd.2, hXor, hWord.1, hWord.2,
       hTotal.1, hTotal.2])

private theorem firstVectorCoreOut {l : Launch} {g : Nat} {t : TState}
    (hLo : 5184 ≤ t.pc) (hHi : t.pc < 5189) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  have hPc : t.pc = 5184 ∨ t.pc = 5185 ∨ t.pc = 5186 ∨ t.pc = 5187 ∨ t.pc = 5188 := by omega
  rcases hPc with h | h | h | h | h
  all_goals
    first
    | exact Assumptions.out_all_eq_nil (by rw [h]; decide) (by rw [h]; decide)
        (by rw [h]; decide) (h.symm ▸ Flow.code_5184) rfl
    | exact Assumptions.out_all_eq_nil (by rw [h]; decide) (by rw [h]; decide)
        (by rw [h]; decide) (h.symm ▸ Flow.code_5185) rfl
    | exact Assumptions.out_all_eq_nil (by rw [h]; decide) (by rw [h]; decide)
        (by rw [h]; decide) (h.symm ▸ Flow.code_5186) rfl
    | exact Assumptions.out_all_eq_nil (by rw [h]; decide) (by rw [h]; decide)
        (by rw [h]; decide) (h.symm ▸ Flow.code_5187) rfl
    | exact Assumptions.out_all_eq_nil (by rw [h]; decide) (by rw [h]; decide)
        (by rw [h]; decide) (h.symm ▸ Flow.code_5188) rfl

/-- The final repeated Bias address setup carries every register outside its five temporaries. -/
theorem repeatedBiasFirstVectorSetupFramed (hp : Pre p l m) (g : Nat) (w : Fin 8) {t : TState}
    (ht : At t 5184 [(3976,b32 (repeatedBiasRowBase l g)),(3977,b32 (repeatedBiasStageOffset w))]) :
    ∃ u, run kernel Assumptions.all l g 5 t = some u ∧
      At u 5189 [(4170,b32 (kvSwizzle (repeatedBiasRowBase l g+166912)+
        repeatedBiasStageOffset w))] ∧
      ∀ r ∉ [4166,4167,4168,4169,4170], u.regs r = t.regs r := by
  obtain ⟨u,hCore,hAt⟩ := (repeatedBiasFirstVectorSetupCore hp g w).apply ht
  have hStraight : ((kernel.code.drop 5184).take 4).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hRun := Epilogue.schedulerLocalTransport (lo := 5184) (len := 5) hStraight
    (fun hLo hHi => firstVectorCoreOut hLo hHi) hCore (by rw [ht.1]) (by rw [ht.1])
  refine ⟨u,hRun,hAt,?_⟩
  intro r hR
  have hCriteria : ((kernel.code.drop 5184).take 5).all
      (fun ins => [r].all (fun reg => !(writesRegs ins.op).contains reg)) = true := by
    have hAll : ((kernel.code.drop 5184).take 5).all
        (fun ins => (writesRegs ins.op).all ([4166,4167,4168,4169,4170] : List Nat).contains) =
        true := by set_option maxRecDepth 100000 in kernel_rfl
    apply List.all_eq_true.mpr
    intro ins hMem
    simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.not_eq_true',List.contains_eq_mem]
    apply decide_eq_false
    intro h
    exact hR (by simpa only [List.contains_eq_mem,decide_eq_true_eq] using
      List.all_eq_true.mp (List.all_eq_true.mp hAll ins hMem) r h)
  exact Epilogue.schedulerLocalFrame hCriteria hStraight hCore
    (by rw [ht.1]) (by rw [ht.1]) (by simp)

/-- The setup shared by vectors zero and eight applies the absolute-address Bias swizzle
and the physical stage increment. Vector eight adds its half-box offset in the load. -/
theorem repeatedBiasFirstVectorSetup (hp : Pre p l m) (g : Nat) (w : Fin 8) :
    Seg kernel Assumptions.all l g 5 5184
      [(3976, b32 (repeatedBiasRowBase l g)), (3977, b32 (repeatedBiasStageOffset w))] 5189
      [(4170, b32 (kvSwizzle (repeatedBiasRowBase l g + 166912) +
        repeatedBiasStageOffset w))] := by
  intro t ht
  obtain ⟨u,hu,hAt,_⟩ := repeatedBiasFirstVectorSetupFramed hp g w ht
  exact ⟨u,hu,hAt⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
