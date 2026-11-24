-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringDestinations
public import Kernels.TmlFa4Fwd.Proof.LoaderDrainPoll
public import Kernels.TmlFa4Fwd.Proof.PrologueInit
public import Kernels.TmlFa4Fwd.Flow.Code.Part015
public import Kernels.TmlFa4Fwd.Flow.Code.Part018
public import Kernels.TmlFa4Fwd.Flow.Code.Part022

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The address calculation and empty-stage acquire before each recurring packet. -/
def recurringEmptyWait : Fin 4 → DrainWaitSite
  | 0 => ⟨960, 9612, 1976, 7180⟩
  | 1 => ⟨1206, 9615, 2063, 2064⟩
  | 2 => ⟨1430, 9617, 2138, 7180⟩
  | 3 => ⟨1611, 9618, 2140, 2141⟩

theorem recurringEmptyWaitCode (i : Fin 4) : LoaderWaitCode (recurringEmptyWait i) := by
  fin_cases i
  · exact ⟨Flow.code_960, Flow.code_961, Flow.code_962⟩
  · exact ⟨Flow.code_1206, Flow.code_1207, Flow.code_1208⟩
  · exact ⟨Flow.code_1430, Flow.code_1431, Flow.code_1432⟩
  · exact ⟨Flow.code_1611, Flow.code_1612, Flow.code_1613⟩

def readySlot (stage : Fin 3) : Fin 34 := ⟨4 + stage, by omega⟩

def emptySlot (stage : Fin 3) : Fin 34 := ⟨7 + stage, by omega⟩

theorem readySlot_address (l : Launch) (cta : Nat) (stage : Fin 3) :
    Prologue.initObject l cta (readySlot stage) =
      ⟨.shared, cta, l.sharedBase + 8 * stage + 32⟩ := by
  fin_cases stage <;> rfl

theorem emptySlot_address (l : Launch) (cta : Nat) (stage : Fin 3) :
    Prologue.initObject l cta (emptySlot stage) =
      ⟨.shared, cta, l.sharedBase + 8 * stage + 56⟩ := by
  fin_cases stage <;> rfl

def recurringBarrierInput (l : Launch) (i : Fin 4) (stage : Fin 3) (phase : Nat) :
    List (Nat × Value) :=
  [((recurringStageInputs i).1, b32 stage), (2535, b32 l.sharedBase),
   ((recurringEmptyWait i).phase, b32 phase)]

def recurringBarrierFacts (l : Launch) (i : Fin 4) (stage : Fin 3) (phase : Nat) :
    List (Nat × Value) :=
  [((recurringEmptyWait i).base, b32 (l.sharedBase + 8 * stage + 56)),
   ((recurringEmptyWait i).phase, b32 phase),
   ((copyArrivalAddress (recurringPacketSite i)).1, b32 (l.sharedBase + 8 * stage))]

/-- The packet's address operands, with an optional fact for its incoming phase register. -/
def recurringBarrierInputWith (l : Launch) (i : Fin 4) (stage : Fin 3)
    (phase : Option Value) : List (Nat × Value) :=
  [((recurringStageInputs i).1, b32 stage), (2535, b32 l.sharedBase)] ++
    phase.toList.map (fun word => ((recurringEmptyWait i).phase, word))

/-- The paired address registers immediately before polling, with the optional phase fact. -/
def recurringBarrierFactsWith (l : Launch) (i : Fin 4) (stage : Fin 3)
    (phase : Option Value) : List (Nat × Value) :=
  [((recurringEmptyWait i).base, b32 (l.sharedBase + 8 * stage + 56)),
   ((copyArrivalAddress (recurringPacketSite i)).1, b32 (l.sharedBase + 8 * stage))] ++
    phase.toList.map (fun word => ((recurringEmptyWait i).phase, word))

/-- Three local steps calculate the ready and empty operands and preserve the incoming
phase register when its value is recorded in the frame. -/
theorem recurringBarrierPrepWith {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (i : Fin 4) (stage : Fin 3) (phase : Option Value) :
    Seg kernel Assumptions.all l g 3 ((recurringEmptyWait i).pc - 3)
      (recurringBarrierInputWith l i stage phase) (recurringEmptyWait i).pc
      (recurringBarrierFactsWith l i stage phase) := by
  have hBase := hp.shared.2.1
  have hStage := stage.isLt
  let k := stage.val
  change k < 3 at hStage
  have h32 : k < 4294967296 := by omega
  have h64 : k < 18446744073709551616 := by omega
  have hShift32 : 8 * k < 4294967296 := by omega
  have hShift64 : 8 * k < 18446744073709551616 := by omega
  have hBase32 : l.sharedBase < 4294967296 := by omega
  have hBase64 : l.sharedBase < 18446744073709551616 := by omega
  have hAddr32 : l.sharedBase + 8 * k < 4294967296 := by omega
  have hAddr64 : l.sharedBase + 8 * k < 18446744073709551616 := by omega
  have hPoll32 : l.sharedBase + 8 * k + 56 < 4294967296 := by omega
  have hPoll64 : l.sharedBase + 8 * k + 56 < 18446744073709551616 := by omega
  have hCore : Seg kernel [] l g 3 ((recurringEmptyWait i).pc - 3)
      (recurringBarrierInputWith l i stage phase) (recurringEmptyWait i).pc
      (recurringBarrierFactsWith l i stage phase) := by
    fin_cases i <;> cases phase <;> intro s hs <;>
      simp only [recurringBarrierInputWith, recurringBarrierFactsWith, Option.toList, List.map,
        List.append_nil, List.cons_append, List.nil_append, recurringEmptyWait,
        recurringStageInputs, recurringPacketSite, copyArrivalAddress] at hs ⊢ <;>
      seg_fp hs using
        norm_bits [show (stage : Nat) = k from rfl, Nat.mod_eq_of_lt h32,
          Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt hShift32, Nat.mod_eq_of_lt hShift64,
          Nat.mod_eq_of_lt hBase32, Nat.mod_eq_of_lt hBase64,
          Nat.mod_eq_of_lt hAddr32, Nat.mod_eq_of_lt hAddr64,
          Nat.mod_eq_of_lt hPoll32, Nat.mod_eq_of_lt hPoll64, Nat.mul_comm k 8]
  intro s hs
  obtain ⟨t, ht, hAt⟩ := hCore s hs
  have hLo : 174 ≤ (recurringEmptyWait i).pc - 3 := by fin_cases i <;> decide
  have hHi : (recurringEmptyWait i).pc - 3 + 3 ≤ 1906 := by fin_cases i <;> decide
  have hSeq : ((kernel.code.drop ((recurringEmptyWait i).pc - 3)).take 2).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op) = true := by
    fin_cases i <;> (set_option maxRecDepth 100000 in kernel_rfl)
  exact ⟨t, (loaderLinear (regs := []) hLo hHi hs.1 (by simp) hSeq ht).1, hAt⟩

/-- Three real local steps calculate the paired ready and empty mbarrier addresses
from the same live stage word, retaining the empty poll's incoming parity. -/
theorem recurringBarrierPrep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (i : Fin 4) (stage : Fin 3) (phase : Nat) :
    Seg kernel Assumptions.all l g 3 ((recurringEmptyWait i).pc - 3)
      (recurringBarrierInput l i stage phase) (recurringEmptyWait i).pc
      (recurringBarrierFacts l i stage phase) := by
  intro s hs
  obtain ⟨u, hu, ht⟩ := recurringBarrierPrepWith hp i stage (some (b32 phase)) s hs
  refine ⟨u, hu, ht.mono ?_⟩
  exact ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.2.1, ht.2.2.2.2.2.1, trivial⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
