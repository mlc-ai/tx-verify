-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderReadyOrdinals
public import Kernels.TmlFa4Fwd.Proof.MmaGeometry
public import Lemmas.Flow.Polls

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue

noncomputable section

/-- The stage selected by the global K/V use cursor, shared with the MMA role. -/
def kvUseStage (use : Nat) : Fin 3 := ⟨Mma.kvSlot use, Nat.mod_lt use (by decide)⟩

/-- The empty predicate starts with the opposite parity of the ready predicate. -/
def kvEmptyPhase (use : Nat) : Bool := Mma.kvParity use == 0

theorem kvUseStage_val (use : Nat) : (kvUseStage use).val = use % 3 := rfl

/-- Advancing the use cursor preserves both decoded loader ring registers. -/
theorem loaderRingWordsOfUse (use : Nat) :
    loaderNextRingFacts (kvUseStage use) (kvEmptyPhase use) =
      [(7179, b32 (kvUseStage (use + 1)).val),
       (7180, loaderPhaseWord (kvEmptyPhase (use + 1)))] := by
  have hStage : (use % 3 + 1) % 3 = (use + 1) % 3 := by omega
  have hWrap : use % 3 < 3 := Nat.mod_lt _ (by decide)
  have hParity : use / 3 % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases hw : use % 3 = 2
  · have hDiv : (use + 1) / 3 = use / 3 + 1 := by omega
    have hSlot : (use + 1) % 3 = 0 := by omega
    interval_cases hPar : use / 3 % 2
    · have hn : (use / 3 + 1) % 2 = 1 := by omega
      simp [loaderNextRingFacts, loaderNextPhase, kvUseStage_val, kvEmptyPhase,
        Mma.kvParity, hw, hPar, hDiv, hn, hSlot]
    · have hn : (use / 3 + 1) % 2 = 0 := by omega
      simp [loaderNextRingFacts, loaderNextPhase, kvUseStage_val, kvEmptyPhase,
        Mma.kvParity, hw, hPar, hDiv, hn, hSlot]
  · have hDiv : (use + 1) / 3 = use / 3 := by omega
    have hNotWrap : (use % 3 == 2) = false := by simpa using hw
    simp [loaderNextRingFacts, loaderNextPhase, kvUseStage_val, kvEmptyPhase,
      Mma.kvParity, hNotWrap, hDiv, hStage]

private theorem countCyclicPrefix (stage : Nat) (hStage : stage < 3) (count : Nat) :
    (List.range count).countP (fun use => decide (use % 3 = stage)) =
      (count + 2 - stage) / 3 := by
  induction count with
  | zero => simp; omega
  | succ count ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil, Nat.zero_add]
    by_cases hc : count % 3 = stage
    · rw [ite_eq_left (decide_eq_true hc)]
      omega
    · rw [ite_eq_right (by simpa)]
      omega

/-- The ready target subsequence forgets nonarrival events without changing slot order. -/
def readyTarget (e : Event) : Option Loc :=
  match e.kind with
  | .asyncArrive loc true => some loc
  | _ => none

def readyUseTarget (l : Launch) (cta use : Nat) : Loc :=
  initObject l cta (readySlot (kvUseStage use))

private theorem readyUseTarget_eq (l : Launch) (cta a b : Nat) :
    readyUseTarget l cta a = readyUseTarget l cta b ↔ a % 3 = b % 3 := by
  rw [readyUseTarget, readyUseTarget, readySlot_address, readySlot_address]
  simp only [Loc.mk.injEq, true_and, kvUseStage_val]
  omega

/-- Once an actual producer trace follows the cyclic K/V cursor, its per-slot
arrival ordinal is the quotient of that use by the ring width. -/
theorem readyOrdinalOfUse {l : Launch} {X : Execution} {cta use : Nat} {i : EvId}
    (hPrefix : ((X.tr i.1).take i.2).filterMap readyTarget =
      (List.range use).map (readyUseTarget l cta)) :
    readyOrdinal X (readyUseTarget l cta use) i = use / 3 := by
  let loc := readyUseTarget l cta use
  have hPred : namesReady loc =
      (fun e => ((readyTarget e).map (fun q => decide (q = loc))).getD false) := by
    funext e
    obtain ⟨_, kind⟩ := e
    cases kind <;> try rfl
    case asyncArrive target noinc => cases noinc <;> rfl
  unfold readyOrdinal
  change (((X.tr i.1).take i.2).countP (namesReady loc)) = _
  rw [hPred, ← List.countP_filterMap, hPrefix, List.countP_map]
  simp only [Function.comp_def, loc, readyUseTarget_eq]
  rw [countCyclicPrefix (use % 3) (Nat.mod_lt _ (by decide))]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
