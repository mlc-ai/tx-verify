-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.FirstStores
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.BiasStores
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.PlainStores
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Flow.Code.Part101
import Kernels.TmlFa4Fwd.Flow.Code.Part102
import Kernels.TmlFa4Fwd.Flow.Code.Part115
import Kernels.TmlFa4Fwd.Flow.Code.Part116
public import Lemmas.Tcgen05.TcDataCell
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemCol
import Lemmas.Flow.ElemAccess
import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000

def storeReg : Rd → Nat → Nat
  | .first => firstStoreReg
  | .bias => biasStoreReg
  | .plain => plainStoreReg

def operands (r : Rd) (q : Fin 4) :=
  (List.range 16).map fun j => Opnd.reg (storeReg r (16*q.val+j))

private theorem decoded_store (r : Rd) (q : Fin 4) :
    ∃ ta, kernel.code[(Site.pst r q).pc]? =
      some { guard := none, op := .tcSt ta (operands r q) .s32x32b } := by
  cases r with
  | first =>
    match q with
    | 0 => exact ⟨_, Flow.code_4826⟩
    | 1 => exact ⟨_, Flow.code_4835⟩
    | 2 => exact ⟨_, Flow.code_4844⟩
    | 3 => exact ⟨_, Flow.code_4856⟩
  | bias =>
    match q with
    | 0 => exact ⟨_, Flow.code_6508⟩
    | 1 => exact ⟨_, Flow.code_6517⟩
    | 2 => exact ⟨_, Flow.code_6526⟩
    | 3 => exact ⟨_, Flow.code_6541⟩
  | plain =>
    match q with
    | 0 => exact ⟨_, Flow.code_7416⟩
    | 1 => exact ⟨_, Flow.code_7425⟩
    | 2 => exact ⟨_, Flow.code_7434⟩
    | 3 => exact ⟨_, Flow.code_7446⟩

private theorem live (r : Rd) (q : Fin 4) :
    (List.range 16).all (fun j => (liveD (Site.pst r q).pc).contains
      (storeReg r (16*q.val+j))) = true := by
  cases r <;> fin_cases q <;> kernel_rfl

theorem store_reg {p L m} (hp : Pre p L m) (g v r q k acc) {i : Nat} (hi : i < 64) :
    Values.Bf16Pair (valueOfD p L g ⟨.pst r q, v, k, acc⟩ (storeReg r i))
      (P p L g v r (2*i)) (P p L g v r (2*i+1)) := by
  cases r
  · exact first_store hp g v q k acc i hi
  · exact bias_store hp g v q k acc i hi
  · exact plain_store hp g v q k acc i hi

/-- Data-machine version of SoftStores and the PStored numeric equality, for a single firing. -/
theorem store_fired {p L m} (hp : Pre p L m) (g v r q k acc) {t e o a vals}
    (hat : (codeD p L g).AtD ⟨.pst r q,v,k,acc⟩ t)
    (hf : Fires (Site.pst r q).pc ((codeD p L g).tmpl (some ⟨.pst r q,v,k,acc⟩) t) e o)
    (hk : e.kind = .tc (.st a vals .s32x32b)) :
    vals.length = 16 ∧ ∀ j (hj : j < vals.length),
      Values.Bf16Pair vals[j] (P p L g v r (2*(16*q.val+j))) (P p L g v r (2*(16*q.val+j)+1)) := by
  obtain ⟨ta,ht⟩ := decoded_store r q
  change Fires _ (match kernel.code[(Site.pst r q).pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op | none => .ub .pcOutOfRange) e o at hf
  rw [ht] at hf
  have len := fires_tcSt_len (fun _ h => by cases h) hf hk
  simp only [operands, List.length_map, List.length_range] at len
  refine ⟨len, fun j hj => ?_⟩
  have h16 : j < 16 := hj.trans_le len.le
  have src : (operands r q)[j]? = some (.reg (storeReg r (16*q.val+j))) := by
    simp [operands, h16]
  have hm := List.contains_iff_mem.mp ((List.all_eq_true.mp (live r q)) j (List.mem_range.mpr h16))
  obtain ⟨_, _, _, _, hregs⟩ := hat
  have hv := fires_tcSt_vals (fun _ h => by cases h) hf hk src
    (regs_of_factsFrom hregs hm)
  rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hv
  rw [hv]
  exact store_reg hp g v r q k acc (by have := q.isLt; omega)

/-- The same two columns in the tensor-memory coordinates used by PStored. -/
theorem stored_cell {p L m} (hp : Pre p L m) (g v r q k acc) {t e o a vals}
    (hw : Prologue.warpIndex L g < 8)
    (hat : (codeD p L g).AtD ⟨.pst r q,v,k,acc⟩ t)
    (hf : Fires (Site.pst r q).pc ((codeD p L g).tmpl (some ⟨.pst r q,v,k,acc⟩) t) e o)
    (hk : e.kind = .tc (.st a vals .s32x32b)) (j : Nat) (hj : j < vals.length) :
    let i := (tcDataCell32 L g a j).column - (128 * (Prologue.warpIndex L g / 4) + 64)
    Values.Bf16Pair vals[j] (P p L g v r (2*i)) (P p L g v r (2*i+1)) := by
  have h := (store_fired hp g v r q k acc hat hf hk).2 j hj
  obtain ⟨ta,ht⟩ := decoded_store r q
  change Fires _ (match kernel.code[(Site.pst r q).pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op | none => .ub .pcOutOfRange) e o at hf
  rw [ht] at hf
  have hc := (pst_col (atD_mono hat) ht hf hk).2.1
  rw [colS_eq hw] at hc
  have eq : (tcDataCell32 L g a j).column - (128 * (Prologue.warpIndex L g / 4) + 64) =
      16*q.val+j := by
    change a % 65536 + j - (128 * (g % L.block / 32 / 4) + 64) = _
    omega
  dsimp only
  rw [eq]
  exact h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
