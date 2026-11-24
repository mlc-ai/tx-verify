-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPacketSites
public import Kernels.TmlFa4Fwd.Proof.LoaderRingTail

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The four warm/steady copy packet sites have explicit stage-register operands. -/
def recurringPacketSite (i : Fin 4) : Fin 6 := ⟨i.val + 2, by have := i.isLt; omega⟩

def recurringEvenSeed : Fin 4 → Nat
  | 0 => 1009
  | 1 => 1245
  | 2 => 1474
  | 3 => 1638

def recurringOddSeed : Fin 4 → Nat
  | 0 => 1019
  | 1 => 1253
  | 2 => 1484
  | 3 => 1646

def recurringDstBases : Fin 4 → Nat × Nat
  | 0 => (1992, 1988)
  | 1 => (2076, 2072)
  | 2 => (1153, 1152)
  | 3 => (1153, 1152)

def recurringStageInputs : Fin 4 → Nat × Nat
  | 0 => (7179, 2002)
  | 1 => (1139, 2081)
  | 2 => (7179, 2160)
  | 3 => (1170, 2202)

def recurringEvenFacts (l : Launch) (i : Fin 4) (stage lane : Nat) : List (Nat × Value) :=
  [(packetDstReg (recurringPacketSite i) 0, b32 (kvCopyAddress l.sharedBase stage lane 0 false)),
   ((recurringStageInputs i).2, b32 (32768 * stage))]

private theorem stageAddr (l : Launch) (stage lane k : Nat) :
    kvCopyAddress l.sharedBase 0 lane k false + 32768 * stage =
      kvCopyAddress l.sharedBase stage lane k false := by
  simp [kvCopyAddress]
  omega

private theorem recurringEvenCore {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g stage lane : Nat} (i : Fin 4) (hStage : stage < 3) :
    Seg kernel [] l g 2 (recurringEvenSeed i)
      [((recurringStageInputs i).1, b32 stage),
       ((recurringDstBases i).1, b32 (kvCopyAddress l.sharedBase 0 lane 0 false))]
      (recurringEvenSeed i + 2) (recurringEvenFacts l i stage lane) := by
  have hBase := hp.shared.2.1
  have h32 : stage < 4294967296 := by omega
  have h64 : stage < 18446744073709551616 := by omega
  have hShift32 : 32768 * stage < 4294967296 := by omega
  have hShift64 : 32768 * stage < 18446744073709551616 := by omega
  have hZero0 := kvCopyAddress_range (base := l.sharedBase) (stage := 0) (lane := lane)
    (group := 0) (byte := 0) (upper := false) hp.shared.1 (by decide) (by decide) (by decide)
  have hZero : kvCopyAddress l.sharedBase 0 lane 0 false < 4294967296 := by omega
  have hZero64 : kvCopyAddress l.sharedBase 0 lane 0 false < 18446744073709551616 := by omega
  have hRange := kvCopyAddress_range (base := l.sharedBase) (stage := stage) (lane := lane)
    (group := 0) (byte := 0) (upper := false) hp.shared.1 hStage (by decide) (by decide)
  have hSum : kvCopyAddress l.sharedBase 0 lane 0 false + 32768 * stage < 4294967296 := by
    rw [stageAddr]
    omega
  have hSum64 : kvCopyAddress l.sharedBase 0 lane 0 false + 32768 * stage <
      18446744073709551616 := by omega
  fin_cases i <;> intro s hs <;>
    simp only [recurringEvenSeed, recurringStageInputs, recurringDstBases, recurringEvenFacts,
      recurringPacketSite, packetDstReg] at hs ⊢ <;>
    seg_fp hs using
      norm_bits [Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt hShift32,
        Nat.mod_eq_of_lt hShift64, Nat.mod_eq_of_lt hZero, Nat.mod_eq_of_lt hZero64,
        Nat.mod_eq_of_lt hSum, Nat.mod_eq_of_lt hSum64, Nat.mul_comm stage 32768, stageAddr]

/-- Before the first even vector pair, the PTX shifts the live stage word and adds
that stage's offset to the computed even base. -/
theorem recurringEvenSeedRun {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g stage lane : Nat} (i : Fin 4) (hStage : stage < 3) :
    Seg kernel Assumptions.all l g 2 (recurringEvenSeed i)
      [((recurringStageInputs i).1, b32 stage),
       ((recurringDstBases i).1, b32 (kvCopyAddress l.sharedBase 0 lane 0 false))]
      (recurringEvenSeed i + 2) (recurringEvenFacts l i stage lane) := by
  intro s hs
  obtain ⟨u, hu, hU⟩ := recurringEvenCore hp i hStage s hs
  have hLo : 174 ≤ recurringEvenSeed i := by fin_cases i <;> decide
  have hHi : recurringEvenSeed i + 2 ≤ 1906 := by fin_cases i <;> decide
  have hSeq : ((kernel.code.drop (recurringEvenSeed i)).take 1).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op) = true := by
    fin_cases i <;> (set_option maxRecDepth 100000 in kernel_rfl)
  exact ⟨u, (loaderLinear (regs := []) hLo hHi hs.1 (by simp) hSeq hu).1, hU⟩

/-- The odd vector base uses the same stage offset and the other swizzled plane. -/
theorem recurringOddSeedRun {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g stage lane : Nat} (i : Fin 4) (hStage : stage < 3) :
    Seg kernel Assumptions.all l g 1 (recurringOddSeed i)
      [((recurringDstBases i).2, b32 (kvCopyAddress l.sharedBase 0 lane 1 false)),
       ((recurringStageInputs i).2, b32 (32768 * stage))]
      (recurringOddSeed i + 1)
      [(packetDstReg (recurringPacketSite i) 1,
        b32 (kvCopyAddress l.sharedBase stage lane 1 false))] := by
  have hBase := hp.shared.2.1
  have hShift32 : 32768 * stage < 4294967296 := by omega
  have hShift64 : 32768 * stage < 18446744073709551616 := by omega
  have hZero0 := kvCopyAddress_range (base := l.sharedBase) (stage := 0) (lane := lane)
    (group := 1) (byte := 0) (upper := false) hp.shared.1 (by decide) (by decide) (by decide)
  have hZero : kvCopyAddress l.sharedBase 0 lane 1 false < 4294967296 := by omega
  have hZero64 : kvCopyAddress l.sharedBase 0 lane 1 false < 18446744073709551616 := by omega
  have hRange := kvCopyAddress_range (base := l.sharedBase) (stage := stage) (lane := lane)
    (group := 1) (byte := 0) (upper := false) hp.shared.1 hStage (by decide) (by decide)
  have hSum : kvCopyAddress l.sharedBase 0 lane 1 false + 32768 * stage < 4294967296 := by
    rw [stageAddr]
    omega
  have hSum64 : kvCopyAddress l.sharedBase 0 lane 1 false + 32768 * stage <
      18446744073709551616 := by omega
  have hCore : Seg kernel [] l g 1 (recurringOddSeed i)
      [((recurringDstBases i).2, b32 (kvCopyAddress l.sharedBase 0 lane 1 false)),
       ((recurringStageInputs i).2, b32 (32768 * stage))]
      (recurringOddSeed i + 1)
      [(packetDstReg (recurringPacketSite i) 1,
        b32 (kvCopyAddress l.sharedBase stage lane 1 false))] := by
    fin_cases i <;> intro s hs <;>
      simp only [recurringOddSeed, recurringStageInputs, recurringDstBases,
        recurringPacketSite, packetDstReg] at hs ⊢ <;>
      seg_fp hs using
        norm_bits [Nat.mod_eq_of_lt hShift32, Nat.mod_eq_of_lt hShift64, Nat.mod_eq_of_lt hZero,
          Nat.mod_eq_of_lt hZero64, Nat.mod_eq_of_lt hSum, Nat.mod_eq_of_lt hSum64, stageAddr]
  intro s hs
  obtain ⟨u, hu, hU⟩ := hCore s hs
  have hLo : 174 ≤ recurringOddSeed i := by fin_cases i <;> decide
  have hHi : recurringOddSeed i + 1 ≤ 1906 := by fin_cases i <;> decide
  exact ⟨u, (loaderLinear (regs := []) hLo hHi hs.1 (by simp) rfl hu).1, hU⟩

/-- The local transition after the warm or steady K arrival. -/
def recurringVTransitionPc : Fin 2 → Nat
  | 0 => 1138
  | 1 => 1603

def recurringVTransitionRegs : Fin 2 → Nat × Nat
  | 0 => (1139, 2064)
  | 1 => (1170, 2141)

def recurringVTransitionFacts (i : Fin 2) (stage : Fin 3) (phase : Bool) : List (Nat × Value) :=
  [((recurringVTransitionRegs i).1, b32 ((stage.val + 1) % 3)),
   ((recurringVTransitionRegs i).2, loaderPhaseWord (loaderNextPhase stage phase))]

/-- Each recurring K/V pair increments the stage before V and toggles parity on wrap. -/
theorem recurringVTransitionRun {l : Launch} {g : Nat}
    (i : Fin 2) (stage : Fin 3) (phase : Bool) :
    Seg kernel Assumptions.all l g 5 (recurringVTransitionPc i)
      [(7179, b32 stage.val), (7180, loaderPhaseWord phase)]
      (recurringVTransitionPc i + 5) (recurringVTransitionFacts i stage phase) := by
  have hCore : Seg kernel [] l g 5 (recurringVTransitionPc i)
      [(7179, b32 stage.val), (7180, loaderPhaseWord phase)]
      (recurringVTransitionPc i + 5) (recurringVTransitionFacts i stage phase) := by
    fin_cases i <;> fin_cases stage <;> cases phase <;> intro s hs <;>
      simp only [recurringVTransitionPc, recurringVTransitionFacts, recurringVTransitionRegs,
        loaderPhaseWord, loaderNextPhase] at hs ⊢ <;>
      seg_fp hs using decide
  have hLo : 174 ≤ recurringVTransitionPc i := by fin_cases i <;> decide
  have hHi : recurringVTransitionPc i + 5 ≤ 1906 := by fin_cases i <;> decide
  have hSeq : ((kernel.code.drop (recurringVTransitionPc i)).take 4).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op) = true := by
    fin_cases i <;> (set_option maxRecDepth 100000 in kernel_rfl)
  intro s hs
  obtain ⟨u, hu, hU⟩ := hCore s hs
  exact ⟨u, (loaderLinear (regs := []) hLo hHi hs.1 (by simp) hSeq hu).1, hU⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
