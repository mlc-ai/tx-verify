-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseNumerics
public import Kernels.TmlFa4Fwd.Proof.ResultGeometry
import Kernels.TmlFa4Fwd.Flow.Code.Part141

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

def lseGuardPc (stage : Fin 2) : Nat := 9072 + 9 * stage.val

def lseTailPred (stage : Fin 2) : Nat := 741 + 2 * stage.val

private theorem lseGuardCode (stage : Fin 2) :
    kernel.code[lseGuardPc stage]? =
      some ⟨some (lseTailPred stage, false), .bra (lseGuardPc stage + 2) false⟩ := by
  fin_cases stage
  · exact Flow.code_9072
  · exact Flow.code_9081

private theorem lseStoreCode (stage : Fin 2) :
    kernel.code[lseGuardPc stage + 1]? =
      some ⟨none, .mem {
        kind := .store, space := some .global, sem := .weak, elem := .int .b 32
        addr := ⟨.reg 7491 64, (512 * stage.val : Nat)⟩
        srcs := [.reg (lseOutReg stage)] }⟩ := by
  fin_cases stage
  · exact Flow.code_9073
  · exact Flow.code_9082

private theorem segmentFree {t : TState} (hp : 9072 ≤ t.pc) : t.pc ∉ Assumptions.swExp2Sites := by
  simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- The tail branch of each LSE stage skips its store when its computed row is outside the
request. The input predicate is the result of the corresponding signed comparison. -/
theorem lseBranchLocal {p : Params} {l : Launch} {g tile batch : Nat}
    {t : TState} {F : List (Nat × Value)} (stage : Fin 2) (ht : At t (lseGuardPc stage) F)
    (hTest : t.regs (lseTailPred stage) = some
      (.pred (p.qLength batch ≤ Epilogue.stageRow tile stage + rowOf l g)))
    : ∃ u, At u (if Epilogue.stageRow tile stage + rowOf l g < p.qLength batch then
        lseGuardPc stage + 1 else lseGuardPc stage + 2) F ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  let tail := p.qLength batch ≤ Epilogue.stageRow tile stage + rowOf l g
  obtain ⟨u, huRun, hu⟩ := run_bra (A := []) (lseGuardCode stage) (decide tail) ht hTest (by simp)
  have hPc : 9072 ≤ t.pc := by rw [ht.1]; unfold lseGuardPc; omega
  have huAll : run kernel Assumptions.all l g 1 t = some u := by
    simpa only [run, Assumptions.tauStep_all_eq_nil (segmentFree hPc)
      (ht.1.symm ▸ lseGuardCode stage) rfl] using huRun
  refine ⟨u, ?_, run_rtg huAll⟩
  by_cases hRow : Epilogue.stageRow tile stage + rowOf l g < p.qLength batch
  · have ht' : ¬ tail := Nat.not_le_of_gt hRow
    simpa only [ht', decide_false, Bool.false_eq_true, ↓reduceIte, hRow] using hu
  · have ht' : tail := Nat.le_of_not_gt hRow
    simpa only [ht', decide_true, ↓reduceIte, hRow] using hu

/-- A live LSE store's decoded template uses the packed global row address. -/
theorem lseStoreTemplate {p : Params} {l : Launch} {m : Mem0}
    {g tile batch head : Nat} {t : TState} {F : List (Nat × Value)}
    (hp : Pre p l m) (stage : Fin 2) (hBatch : batch < p.batch) (hHead : head < p.heads)
    (hRow : Epilogue.stageRow tile stage + rowOf l g < p.qLength batch)
    (value : Value) (hBytes : value.bytes = 4)
    (ht : At t (lseGuardPc stage + 1) F)
    (hReg : t.regs (lseOutReg stage) = some value)
    (hAddress : t.regs 7491 = some (b64
      (p.lseLoc (p.qOffset batch + Epilogue.stageRow tile 0 + rowOf l g) head).addr))
    : out kernel Assumptions.all l g t = .ev (.write
      { loc := p.lseLoc (p.qOffset batch + Epilogue.stageRow tile stage + rowOf l g) head,
        size := 4 } value.toBytes (next t)) := by
  let q := p.qOffset batch + Epilogue.stageRow tile stage + rowOf l g
  let base := (p.lseLoc (p.qOffset batch + Epilogue.stageRow tile 0 + rowOf l g) head).addr
  let a : Acc := { loc := p.lseLoc q head, size := 4 }
  have hPacked : q < p.totalQ := by
    dsimp only [q]
    rw [Nat.add_assoc]
    exact hp.packedRow_lt hBatch hRow
  have hRegion := lseByte_in (p := p) hPacked hHead (k := 0) (by decide)
  have hRange := hp.ranges p.lseRegion (by simp)
  have hAddr : a.loc.addr < 2 ^ 64 := by
    have hz := hRegion.2.2.2
    change a.loc.addr + 0 < p.lseRegion.base + p.lseRegion.bytes at hz
    omega
  have hCalc : base + 512 * stage.val = a.loc.addr := by
    simp only [base, a, q, Params.lseLoc, globalLoc, Epilogue.stageRow]
    omega
  have hBase : base < 2 ^ 64 := by omega
  have hAlign : a.loc.addr % 4 = 0 := by
    have hLse := hp.alignment.2.2.2.2.2.2.2.2.2.2.2
    change (p.lseBase + 4 * (head * p.lseStride + q)) % 4 = 0
    omega
  have hEff : effAddr l g t .global 7491 (512 * stage.val : Nat) = .ok a.loc := by
    have hRead : t.regs 7491 = some (b64 base) := hAddress
    have hBase' := truncBits_ofNat hBase (by decide : 64 ≤ 64)
    simp only [effAddr, readBits, readReg, hRead, b64, hBase', bind, Except.bind,
      pure, Except.pure, BitVec.ofInt_natCast, ← BitVec.ofNat_add, hCalc]
    rw [toNat_ofNat_lt hAddr]
    rfl
  have hPc : 9072 ≤ t.pc := by rw [ht.1]; unfold lseGuardPc; omega
  have hModel : out kernel Assumptions.all l g t = out kernel [] l g t := by
    apply Assumptions.out_all_eq_nil (segmentFree hPc) _ _ (ht.1.symm ▸ lseStoreCode stage) rfl
    all_goals rw [ht.1]; fin_cases stage <;> decide
  have hElem : elemAcc a.loc (32 / 8) 1 0 = .ok a := by
    rw [elemAcc_ok (by decide) (by simpa only [Nat.mul_one] using hAlign)]
    simp only [a, Params.lseLoc, globalLoc, Loc.at, Nat.mul_zero, Nat.add_zero]
  let srcs : List Opnd := [.reg (lseOutReg stage)]
  rw [hModel, out_event ht.2.2.2.1 (ht.1.symm ▸ lseStoreCode stage) rfl rfl]
  change Out.ev (storeTmpl l g t .global 32 7491 (512 * stage.val : Nat) srcs) = _
  have hAfter : afterStore t srcs = next t := by
    unfold afterStore
    change (if t.sub + 1 < 1 then _ else _) = _
    rw [ite_eq_right (by omega), next, ← ht.2.1]
  have hLen : srcs.length = 1 := rfl
  have hSrc : srcs[0]? = some (.reg (lseOutReg stage)) := rfl
  simp only [storeTmpl, hEff, bind, Except.bind, hLen, ht.2.1, hElem, hSrc, readValue,
    readReg, hReg, pure, Except.pure, storeValue_of_bytes (show value.bytes = 32 / 8 from hBytes),
    hAfter]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Correction
