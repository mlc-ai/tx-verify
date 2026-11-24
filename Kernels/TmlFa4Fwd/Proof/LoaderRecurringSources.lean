-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringDestinations
public import Kernels.TmlFa4Fwd.Proof.LoaderCopyGeometry
public import Kernels.TmlFa4Fwd.Proof.LoaderWalkCheckpoint

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The point where a recurring window packs the shuffled page pointer. -/
def recurringSourceStart : Fin 4 → Nat
  | 0 => 1006
  | 1 => 1241
  | 2 => 1472
  | 3 => 1635

def recurringSourceWords : Fin 4 → Nat × Nat
  | 0 => (2000, 2001)
  | 1 => (2079, 2080)
  | 2 => (2158, 2159)
  | 3 => (2200, 2201)

def recurringSourceInputs (i : Fin 4) (base tid : Nat) : List (Nat × Value) :=
  [((recurringSourceWords i).1, b32 (base % 2 ^ 32)),
   ((recurringSourceWords i).2, b32 (base / 2 ^ 32))] ++
  match i with
  | 0 => [(1119, b32 (8 * (tid % 8)))]
  | 1 => [(2066, b32 (16 * tid))]
  | 2 => [(7781, b64 (16 * (tid % 8)))]
  | 3 => [(1147, b32 (8 * (tid % 8)))]

def recurringSourceAddress (base tid : Nat) : Nat :=
  (base + 16 * (tid % 8)) % 2 ^ 64

def recurringSourceFacts (i : Fin 4) (base tid : Nat) : List (Nat × Value) :=
  [(packetSrcReg (recurringPacketSite i) 0, b64 (recurringSourceAddress base tid))]

private theorem pagePointerJoin {base : Nat} (hBase : base < 2 ^ 64) :
    (base % 4294967296 ||| base / 4294967296 * 4294967296 % 18446744073709551616) = base := by
  have hLo : base % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hShift : base / 4294967296 * 4294967296 < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hShift, Nat.or_comm, Nat.mul_comm]
  change 2 ^ 32 * (base / 2 ^ 32) ||| base % 2 ^ 32 = base
  rw [← Nat.two_pow_add_eq_or_of_lt hLo]
  omega

private theorem columnMask16 (tid : Nat) : (16 * tid &&& 112) = 16 * (tid % 8) := by
  have h := congrArg (fun n => n <<< 4) (Nat.and_two_pow_sub_one_eq_mod tid 3)
  change (tid &&& 7) <<< 4 = (tid % 8) <<< 4 at h
  rw [Nat.shiftLeft_and_distrib] at h
  simpa only [Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMul, Nat.mul_comm _ 16] using h

private theorem recurringSourceCore {l : Launch} {g base tid : Nat}
    (hBase : base < 2 ^ 64) (hTid : tid < 512) (i : Fin 4) :
    Seg kernel [] l g (recurringEvenSeed i - recurringSourceStart i)
      (recurringSourceStart i) (recurringSourceInputs i base tid)
      (recurringEvenSeed i) (recurringSourceFacts i base tid) := by
  have hLo : base % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  have hHi : base / 4294967296 < 4294967296 := by omega
  have hOffset1 : 8 * (tid % 8) < 4294967296 := by omega
  have hOffset2 : 16 * (tid % 8) < 4294967296 := by omega
  have hOffset3 : 16 * tid < 4294967296 := by omega
  have hOffset4 : (8 * (tid % 8)) * 2 = 16 * (tid % 8) := by omega
  have hOff64 : 16 * (tid % 8) < 18446744073709551616 := by omega
  have hTid64 : 16 * tid < 18446744073709551616 := by omega
  fin_cases i <;> intro s hs <;>
    simp only [recurringSourceStart, recurringEvenSeed, recurringSourceInputs, recurringSourceWords,
      recurringSourceFacts, recurringSourceAddress, recurringPacketSite, packetSrcReg,
      List.cons_append, List.nil_append] at hs ⊢ <;>
    seg_fp hs using
      norm_bits [pagePointerJoin hBase, Nat.mod_eq_of_lt hOffset1, Nat.mod_eq_of_lt hOffset2,
        Nat.mod_eq_of_lt hOffset3, Nat.mod_eq_of_lt hOff64, Nat.mod_eq_of_lt hTid64,
        hOffset4, columnMask16]

/-- The first recurring source vector adds the issuing lane's BF16 byte offset
to the page pointer broadcast by the two shuffles. -/
theorem recurringSourceRun {l : Launch} {g base tid : Nat}
    (hBase : base < 2 ^ 64) (hTid : tid < 512) (i : Fin 4) :
    Seg kernel Assumptions.all l g (recurringEvenSeed i - recurringSourceStart i)
      (recurringSourceStart i) (recurringSourceInputs i base tid)
      (recurringEvenSeed i) (recurringSourceFacts i base tid) := by
  intro s hs
  obtain ⟨u, hu, hU⟩ := recurringSourceCore hBase hTid i s hs
  have hL : 174 ≤ recurringSourceStart i := by fin_cases i <;> decide
  have hH : recurringSourceStart i + (recurringEvenSeed i - recurringSourceStart i) ≤ 1906 := by
    fin_cases i <;> decide
  have hSeq : ((kernel.code.drop (recurringSourceStart i)).take
      (recurringEvenSeed i - recurringSourceStart i - 1)).all
        (fun ins => Epilogue.schedulerFallsThrough ins.op) = true := by
    fin_cases i <;> (set_option maxRecDepth 100000 in kernel_rfl)
  exact ⟨u, (loaderLinear (regs := []) hL hH hs.1 (by simp) hSeq hu).1, hU⟩

private theorem recurringSourceFrame (i : Fin 4) :
    let site := recurringPacketSite i
    let lo := recurringEvenSeed i
    let stop := copyCommitPc site
    ((kernel.code.drop lo).take (stop - lo)).all
      (fun ins => loaderPipelineCutOp lo stop (stop - 1) [packetSrcReg site 0] ins.op) = true := by
  fin_cases i <;> (set_option maxRecDepth 100000 in decide +kernel)

/-- An observed first pair in any recurring K/V packet uses the source produced
from its two page-pointer words, with the lane column and the selected BF16 plane. -/
theorem recurringFirstCopySource {l : Launch} {g base tid : Nat}
    (hBase : base < 2 ^ 64) (hTid : tid < 512) (i : Fin 4) (upper : Bool)
    {s : TState} {es : List Event} {vs : List Visit} {sp : AsyncCopy.Spec}
    (hs : At s (recurringSourceStart i) (recurringSourceInputs i base tid))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hSeen : ⟨packetPlanePc (recurringPacketSite i) 0 upper, .copy sp⟩ ∈
      loaderSliceEvents (recurringSourceStart i) (copyCommitPc (recurringPacketSite i)) vs) :
    sp.src.loc = globalLoc ((base + 16 * (tid % 8) + packetSrcOff upper) % 2 ^ 64) := by
  let site := recurringPacketSite i
  let event : Event := ⟨packetPlanePc site 0 upper, .copy sp⟩
  obtain ⟨t, hr, ht⟩ := recurringSourceRun hBase hTid i s hs
  obtain ⟨tail, htWalk, _, htSaw⟩ := loaderEventAfterLocal hr hw hSeen
  obtain ⟨a, b, hp, hField, hStep⟩ := loaderCopyWithRegisters
    (scopeLower := recurringSourceStart i) (lower := recurringEvenSeed i)
    (stop := copyCommitPc site) (F := recurringSourceFacts i base tid)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (recurringSourceFrame i) htWalk ht.1.ge (ringShapeOfAt ht) ht.2.2.2.2 htSaw rfl
  have hEvent : event = ⟨a.pc, .copy sp⟩ := by rw [hp]
  change EStep kernel Assumptions.all l g a event (some b) at hStep
  rw [hEvent] at hStep
  have hAddr : recurringSourceAddress base tid < 2 ^ 64 := Nat.mod_lt _ (by decide)
  simpa [recurringSourceAddress, Nat.mod_add_mod] using
    packetCopySource site 0 upper hp hField.1 hAddr hStep

end
end PTX.Kernels.TmlFa4Fwd.Loader
