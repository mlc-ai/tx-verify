-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Base
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
public import Lemmas.Flow.MaskedPack
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The unpack of a bias word

After the last element of a bias load the code unpacks each of its four words into two `bf16`
halves (`mov.b32 {lo, hi}, w`). A word the machine accepted (`biasOk`) unpacks into its recorded
halves (lane L's `exec_unpack_masked`), each written as the conditional value `hv16`: the payload
when the half is one, else the masked pattern. The piece `seg_unpack` is one such step; the
segment tactics do not unpack a word that is not given by its parts. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {g : Nat}

theorem maskedValue_hv16 (o : Option ℝ) :
    maskedValue .bf16 0xFF80 o = hv16 o.isSome (o.getD 0) := by
  cases o <;> rfl

/-- No assumption of the kernel names the unpack of a word into two halves. -/
theorem noUnpack_all : NoUnpack Assumptions.all := by
  intro lo hi src L g t a ha
  simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `freshKeys` on keys only. -/
def freshK : List Nat → List Nat → Bool
  | [], _ => true
  | d :: rest, ks => ks.elem d = false && freshK rest (d :: ks)

theorem freshKeys_eq : ∀ (dv F : List (Nat × Value)),
    freshKeys dv F = freshK (dv.map Prod.fst) (F.map Prod.fst)
  | [], _ => rfl
  | (d, v) :: rest, F => by
    simp only [freshKeys, freshK, List.map_cons]
    rw [freshKeys_eq rest ((d, v) :: F)]
    rfl

theorem keys_dropReg (r : Nat) (F : List (Nat × Value)) :
    (Code.dropReg r F).map Prod.fst = (F.map Prod.fst).filter fun x => x != r := by
  unfold Code.dropReg
  induction F with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.filter_cons, List.map_cons]
    split <;> simp_all

theorem keys_factsFrom (live : List Nat) (val : Nat → Value) :
    (factsFrom live val).map Prod.fst = live := by
  simp [factsFrom, List.map_map, Function.comp_def]

/-- Prove `freshKeys dv F = true` from the keys alone (the values may be free variables). -/
macro "fresh_keys" : tactic => `(tactic| (
  rw [PTX.Kernels.TmlFa4Fwd.Proof.Softmax.freshKeys_eq]
  simp only [List.map_cons, List.map_nil, PTX.Kernels.TmlFa4Fwd.Proof.Softmax.keys_dropReg,
    PTX.Kernels.TmlFa4Fwd.Proof.Softmax.keys_factsFrom,
    PTX.Kernels.TmlFa4Fwd.Proof.Softmax.livePc]
  decide +kernel))

/-- **The unpack of an accepted bias word** at `pc` from register `src`, as a piece: the high
half and the low half are written as their recorded values, every other fact is kept. -/
theorem seg_unpack {pc lo hi src : Nat} {F : List (Nat × Value)} {x : Value}
    (hc : kernel.code[pc]? =
      some ⟨none, .move ⟨.unpack, .int .b 32, [some lo, some hi], [.reg src]⟩⟩)
    (hS : Assumption.SegFreePc Assumptions.all pc)
    (hx : (src, x) ∈ F) (hok : biasOk x = true)
    (hk : freshKeys [(lo, hv16 (maskedPair .bf16 x).1.isSome ((maskedPair .bf16 x).1.getD 0)),
      (hi, hv16 (maskedPair .bf16 x).2.isSome ((maskedPair .bf16 x).2.getD 0))] F = true) :
    ∃ n, Seg kernel Assumptions.all L g n pc F (pc + 1)
      ((hi, hv16 (maskedPair .bf16 x).2.isSome ((maskedPair .bf16 x).2.getD 0)) ::
       (lo, hv16 (maskedPair .bf16 x).1.isSome ((maskedPair .bf16 x).1.getD 0)) :: F) := by
  have h := Seg.writes (K := kernel) (A := Assumptions.all) (L := L) (g := g) (F := F)
    (dv := [(lo, hv16 (maskedPair .bf16 x).1.isSome ((maskedPair .bf16 x).1.getD 0)),
      (hi, hv16 (maskedPair .bf16 x).2.isSome ((maskedPair .bf16 x).2.getD 0))]) hc rfl ?_ hk
  · simpa using h
  · intro R cf hR
    have hr : R src = some x := holds_mem hR hx
    rw [exec_unpack_masked (t := ⟨pc, R, cf, 0, [], none⟩) noUnpack_all hr hok hS]
    simp only [maskedValue_hv16, setRegsL]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
