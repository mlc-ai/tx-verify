-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionTmemLoads
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part126
import Kernels.TmlFa4Fwd.Flow.Code.Part127
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part129
import Kernels.TmlFa4Fwd.Flow.Code.Part130
import Kernels.TmlFa4Fwd.Flow.Code.Part131

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof

noncomputable section

def rescaleStorePc (stage : Fin 2) (chunk : Fin 8) : Nat :=
  8038 + 219 * stage.val + 26 * chunk.val

/-- Unpacking visits descending pairs; the store restores the ascending column order. -/
def rescaleValueReg (stage : Fin 2) (chunk : Fin 8) (word : Fin 16) : Nat :=
  5996 + 258 * stage.val + 32 * chunk.val + 2 * (7 - word.val / 2) + word.val % 2

private def rescaleOperands (stage : Fin 2) (chunk : Fin 8) : List Opnd :=
  List.ofFn fun word => .reg (rescaleValueReg stage chunk word)

private theorem rescaleStoreCode (stage : Fin 2) (chunk : Fin 8) :
    kernel.code[rescaleStorePc stage chunk]? =
      some ⟨none, .tcSt (rescaleAddressReg stage chunk) (rescaleOperands stage chunk) .s32x32b⟩ :=
  by
    fin_cases stage <;> fin_cases chunk
    · exact Flow.code_8038
    · exact Flow.code_8064
    · exact Flow.code_8090
    · exact Flow.code_8116
    · exact Flow.code_8142
    · exact Flow.code_8168
    · exact Flow.code_8194
    · exact Flow.code_8220
    · exact Flow.code_8257
    · exact Flow.code_8283
    · exact Flow.code_8309
    · exact Flow.code_8335
    · exact Flow.code_8361
    · exact Flow.code_8387
    · exact Flow.code_8413
    · exact Flow.code_8439

theorem rescaleStoreOpcode (stage : Fin 2) (chunk : Fin 8) :
    ∃ ops, kernel.code[rescaleStorePc stage chunk]? =
      some ⟨none, .tcSt (rescaleAddressReg stage chunk) ops .s32x32b⟩ :=
  ⟨_,rescaleStoreCode stage chunk⟩

theorem rescaleStoreHook (stage : Fin 2) (chunk : Fin 8) :
    Assumptions.all.any (·.tcStWaitLd (rescaleStorePc stage chunk)) = false := by
  rw [Assumptions.all_tcStWaitLd]
  have hlo : 8038 ≤ rescaleStorePc stage chunk := by unfold rescaleStorePc; omega
  have hNot : rescaleStorePc stage chunk ∉ Assumptions.delayedTmemSites := by
    simp only [Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  simp [hNot]

variable {p : Params} {l : Launch} {m : Mem0}

/-- The decoded rescale store issues the sixteen computed products. -/
theorem rescaleStoreOut {g : Nat} {t : TState} {F : List (Nat × Value)} (hp : Pre p l m)
    (stage : Fin 2) (chunk : Fin 8) (value : Fin 16 → Value)
    (ht : At t (rescaleStorePc stage chunk) F)
    (hAddr : t.regs (rescaleAddressReg stage chunk) =
      some (b32 (outputAddress l g stage (16 * chunk.val))))
    (hReg : ∀ j, t.regs (rescaleValueReg stage chunk j) = some (value j))
    (hBytes : ∀ j, (value j).bytes = 4) : out kernel Assumptions.all l g t = .ev (.tc
      (.st (outputAddress l g stage (16*chunk.val)) (List.ofFn value) .s32x32b) (next t)) := by
  let column := outputColumn stage + 16 * chunk.val
  let address := outputAddress l g stage (16 * chunk.val)
  let ss := rescaleOperands stage chunk
  let vals := List.ofFn value
  have hColumn : column < 512 := by
    have hb := outputColumn_range stage
    have hc := chunk.isLt
    dsimp [column]
    omega
  have hLimit : address < 2 ^ 32 := tmem_warp_encoding_lt l g hColumn
  have hAddressOk : tcDataAddressOk l g .s32x32b address = true :=
    tcDataAddressOk_warp32 l g hColumn
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLen : ss.length = 16 := List.length_ofFn
  have hCount : TcShape.countOk .s32x32b ss.length = true := hLen.symm ▸ (by decide)
  have hRead (j : Fin 16) :
      readValue l g t 32 (.reg (rescaleValueReg stage chunk j)) = .ok (value j) := by
    simp [readValue, readReg, hReg j, pure, Except.pure]
  have hMap : ss.mapM (readValue l g t 32) = .ok vals := by
    let indices : List (Fin 16) := List.ofFn id
    let op := fun j : Fin 16 => Opnd.reg (rescaleValueReg stage chunk j)
    have hSs : ss = indices.map op := (List.map_ofFn (f := id) (g := op)).symm
    have hVals : vals = indices.map value := (List.map_ofFn (f := id) (g := value)).symm
    rw [hSs, hVals, List.mapM_map]
    have hFn : (readValue l g t 32 ∘ op) = fun j => (pure (value j) : Exec Value) := funext hRead
    rw [hFn, List.mapM_pure]
    rfl
  have hAll : vals.all (·.bytes = 4) = true := by
    rw [List.all_eq_true]
    intro v hv
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
    exact decide_eq_true (hBytes j)
  have hn : Next kernel Assumptions.all l g t t (.tc (.st address vals .s32x32b) (next t)) := by
    refine ⟨.refl, ?_⟩
    rw [out_event ht.2.2.2.1 (ht.1.symm ▸ rescaleStoreCode stage chunk) rfl rfl]
    rw [eventTmpl_tcSt_noWait (ht.1.symm ▸ rescaleStoreHook stage chunk)]
    change Out.ev (tcTmpl l g t (.tcSt (rescaleAddressReg stage chunk) ss .s32x32b)) = _
    have hReadAddr : readBits l g t 32 (.reg (rescaleAddressReg stage chunk)) =
        .ok (BitVec.ofNat 64 address) := readBits_b32 hAddr hLimit
    have hAddressNat : (BitVec.ofNat 64 address).toNat = address :=
      toNat_ofNat_lt (by omega)
    simp only [tcTmpl, hBlock, hCount, hReadAddr, hAddressNat, hAddressOk, hMap, hAll,
      ofExec, bind, Except.bind, pure, Except.pure, ↓reduceIte]
  exact hn.2

/-- Read the next rescale store at an observed prefix position. -/
theorem observeRescaleStoreInPrefix {X : Execution} {g pos : Nat} {t : TState}
    {ending : Option TState} {F : List (Nat × Value)} (hp : Pre p l m) (stage : Fin 2)
    (chunk : Fin 8) (value : Fin 16 → Value) (ht : At t (rescaleStorePc stage chunk) F)
    (hAddr : t.regs (rescaleAddressReg stage chunk) =
      some (b32 (outputAddress l g stage (16 * chunk.val))))
    (hReg : ∀ j, t.regs (rescaleValueReg stage chunk j) = some (value j))
    (hBytes : ∀ j, (value j).bytes = 4)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (hSeen : (X.tr g).drop pos ≠ []) :
    X.get (g, pos) = some ⟨rescaleStorePc stage chunk,
      .tc (.st (outputAddress l g stage (16 * chunk.val)) (List.ofFn value) .s32x32b)⟩ ∧
    At (next t) (rescaleStorePc stage chunk + 1) F ∧
    Run kernel Assumptions.all l g (next t) ((X.tr g).drop (pos + 1)) ending := by
  let hn := Next.mk (.refl (a := t)) (rescaleStoreOut hp stage chunk value ht hAddr hReg hBytes)
  obtain ⟨_, _, he, hFire, hTail⟩ := hn.continuing_at_nonempty (by
    rintro _ ⟨_, hBad⟩
    cases hBad) hr hSeen
  obtain ⟨rfl, hu⟩ := hFire
  obtain rfl := Option.some.inj hu
  exact ⟨ht.1 ▸ he, ht.next, hTail⟩

private theorem finishWaitCode (stage : Fin 2) :
    kernel.code[rescaleStorePc stage 7 + 1]? = some ⟨none, .tcWaitSt⟩ := by
  fin_cases stage
  · exact Flow.code_8221
  · exact Flow.code_8440

/-- After the last rescale store, the actual wait event completes that lane's pending stores. -/
theorem observeRescaleWait {X : Execution} {g pos : Nat} {t : TState} {F : List (Nat × Value)}
    (hp : Pre p l m) (stage : Fin 2) (ht : At t (rescaleStorePc stage 7 + 1) F)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    X.get (g, pos) = some ⟨rescaleStorePc stage 7 + 1, .tc .waitSt⟩ ∧
    At (next t) (rescaleStorePc stage 7 + 2) F ∧
    Run kernel Assumptions.all l g (next t) ((X.tr g).drop (pos + 1)) none := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hn : Next kernel Assumptions.all l g t t (.tc .waitSt (next t)) := by
    refine ⟨.refl, ?_⟩
    rw [out_event ht.2.2.2.1 (ht.1.symm ▸ finishWaitCode stage) rfl rfl]
    change Out.ev (tcTmpl l g t .tcWaitSt) = _
    simp [tcTmpl, hBlock, ofExec, pure, Except.pure]
  obtain ⟨_, _, he, hFire, hTail⟩ := hn.continuing_at (by
    rintro _ ⟨_, hBad⟩
    cases hBad) hr
  obtain ⟨rfl, hu⟩ := hFire
  obtain rfl := Option.some.inj hu
  exact ⟨ht.1 ▸ he, ht.next, hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
