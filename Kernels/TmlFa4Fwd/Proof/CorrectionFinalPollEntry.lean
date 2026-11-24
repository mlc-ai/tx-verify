-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalizePoll
public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalStats
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part137

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

def finalPollPrepReg (stage : Fin 2) : Nat := if stage.val = 0 then 6496 else 6499

def finalPollPrepWord (l : Launch) (stage : Fin 2) : Value :=
  b32 (if stage.val = 0 then 0 else l.sharedBase + 152)

private theorem finalPollPrepCore {l : Launch} {g : Nat} {t : TState} {ins : Instr}
    (stage : Fin 2) (ht : t.pc = reciprocalPc stage + 3)
    (hc : kernel.code[reciprocalPc stage + 3]? = some ins)
    (hCore : Assumptions.coreOp ins.op = true) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  apply Assumptions.out_all_eq_nil _ _ _ (ht.symm ▸ hc) hCore
  all_goals rw [ht]; fin_cases stage <;> decide

/-- Initialize the first phase word or compute the second done barrier's address at the
actual decoded instruction preceding the acquire spins. -/
theorem finalPollPrep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {F : List (Nat × Value)} (stage : Fin 2)
    (ht : At t (reciprocalPc stage + 3) F)
    (hShared : t.regs 2535 = some (b32 l.sharedBase))
    (hFresh : ∀ rv ∈ F, rv.1 ≠ finalPollPrepReg stage) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (finalizePollPc stage false)
        ((finalPollPrepReg stage, finalPollPrepWord l stage) :: F) := by
  let u := next (setReg t (finalPollPrepReg stage) (finalPollPrepWord l stage))
  have hCore : run kernel [] l g 1 t = some u := by
    fin_cases stage
    · apply run_local Flow.code_8472 rfl ht
      rw [execLocalA_nil, execLocal_move rfl]
      rfl
    · apply run_local Flow.code_8768 rfl ht
      rw [execLocalA_nil, execLocal_int rfl]
      have hBound := hp.shared.2.1
      simp only [execInt, DType.width, readValue, readBits,
        readReg, hShared, pure, Except.pure, bind, Except.bind, b32,
        truncBits_ofNat (show l.sharedBase < 2 ^ 32 by omega) (by decide)]
      have hImm : truncBits 32 (BitVec.ofInt 64 152) = BitVec.ofNat 64 152 := rfl
      rw [hImm]
      rw [← BitVec.ofNat_add, truncBits_ofNat (show l.sharedBase + 152 < 2 ^ 32 by omega)
        (by decide)]
      rfl
  have hOut : out kernel Assumptions.all l g t = out kernel [] l g t := by
    fin_cases stage
    · exact finalPollPrepCore 0 ht.1 Flow.code_8472 rfl
    · exact finalPollPrepCore 1 ht.1 Flow.code_8768 rfl
  have hRun : run kernel Assumptions.all l g 1 t = some u := by
    simpa only [run, tauStep, hOut] using hCore
  have hPC : reciprocalPc stage + 3 + 1 = finalizePollPc stage false := by
    fin_cases stage <;> decide
  exact ⟨u, run_rtg hRun, hPC ▸ ht.set hFresh⟩

/-- Locate both successful waits and the precise first x8 read on the correction trace. -/
theorem observeFinalPollEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g pos : Nat} {t : TState} {F : List (Nat × Value)}
    (stage : Fin 2) (reciprocal : ℝ) (ht : At t (finalizePollPc stage false) F)
    (hFresh : ∀ pair ∈ F, (∀ free, pair.1 ≠ finalizePollPred stage free) ∧
      pair.1 ≠ finalizeReciprocalPair stage)
    (hBase : ∀ free, (finalizePollBase stage free, b32 (finalizePollLoc l g stage free).addr) ∈ F)
    (hPhase : ∀ free, (finalizePollPhase free, b32 free.toNat) ∈ F)
    (hRecip : (reciprocalReg stage, fl reciprocal) ∈ F)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ n k u, X.get (g, pos + n) =
        some ⟨finalizePollPc stage false,
          .wait (finalizePollLoc l g stage false) 0 true true .cta⟩ ∧
      X.get (g, pos + n + 1 + k) =
        some ⟨finalizePollPc stage true, .wait (finalizePollLoc l g stage true) 1 true true .cta⟩ ∧
      At u (finalizeLoadPc stage 0)
        ((finalizeReciprocalPair stage, .pair (fl reciprocal) (fl reciprocal)) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + n + 1 + k + 1)) none := by
  obtain ⟨n, k, u, rest, hEvents, hu, hU⟩ := finalizePollAndPack hp stage reciprocal
    ht hFresh hBase hPhase hRecip hr
  let event (free ok : Bool) : Event :=
    ⟨finalizePollPc stage free, .wait (finalizePollLoc l g stage free) free.toNat ok true .cta⟩
  change (X.tr g).drop pos = List.replicate n (event false false) ++
    (event false true :: List.replicate k (event true false) ++ (event true true :: rest))
    at hEvents
  have h1 : X.get (g, pos + n) = some (event false true) := by
    change (X.tr g)[pos + n]? = _
    rw [← List.getElem?_drop, hEvents]
    simp
  have h2 : X.get (g, pos + n + 1 + k) = some (event true true) := by
    change (X.tr g)[pos + n + 1 + k]? = _
    rw [show pos + n + 1 + k = pos + (n + 1 + k) by omega, ← List.getElem?_drop, hEvents,
      List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate, show n + 1 + k - n = k + 1 by omega]
    simp
  let waits := List.replicate n (event false false) ++ [event false true] ++
    List.replicate k (event true false) ++ [event true true]
  have hLen : waits.length = n + 1 + k + 1 := by simp [waits]; omega
  have hPref : (X.tr g).drop pos = waits ++ rest := by
    rw [hEvents]
    simp [waits, List.append_assoc]
  have hRest : (X.tr g).drop (pos + n + 1 + k + 1) = rest := by
    rw [show pos + n + 1 + k + 1 = pos + waits.length by rw [hLen]; omega,
      ← List.drop_drop, hPref, List.drop_append_length]
  exact ⟨n, k, u, h1, h2, hu, hRest.symm ▸ hU⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
