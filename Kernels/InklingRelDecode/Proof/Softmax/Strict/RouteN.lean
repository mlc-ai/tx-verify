-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Route
import Kernels.InklingRelDecode.Proof.Softmax.Strict.Vals
import Kernels.InklingRelDecode.Proof.Softmax.Steps.Pointers
import Kernels.InklingRelDecode.Proof.Softmax.Steps.Header
import Kernels.InklingRelDecode.Flow.Code
@[expose] public section
/-! # The loop's route to the first bias load: pcs 1051 to 1124 -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g : Nat}

/-- The closers of the pointer table of the loop's loads. -/
macro "late_nxp" : tactic => `(tactic|
  (simp only [Control.valueOf, Control.scalarValue, Nat.reduceEqDiff, ↓reduceIte,
      Nat.reduceLeDiff, and_self, and_false, Bool.false_eq_true]
   first | exact Control.ptr_add _ _ | exact Control.ptr_mad _ _))

set_option hygiene false in
/-- A step of the gate of the next block (pcs 1051 to 1058), run exactly. -/
macro "nx_gate " n:ident a:num b:num " using " tac:tacticSeq : command => `(
theorem $n {j : Nat} {v : Control.Carry} (m : Value) (ok : e.Ok) (hj : j ≤ e.limit) :
    Seg kernel Assumptions.all L g ($b - $a) $a (RF e L g m j v $a) $b (RF e L g m j v $b) := by
  have hb : e.split + j * e.splits + e.splits < 2 ^ 31 :=
    Control.next_block_bound (d := ⟨.arrive, j, v⟩) ok hj
  have h1 := ok.bias
  have h2 := ok.blockWord
  have h3 := Control.limit_bound ok
  have hs : Lib.sx e.blocks < 2 ^ 64 := by
    unfold Lib.sx
    have := Nat.mod_lt e.blocks (by decide : 0 < 2 ^ 32)
    omega
  have hn' : (e.split + j * e.splits + e.splits) % 2 ^ 32 = e.split + j * e.splits + e.splits :=
    Nat.mod_eq_of_lt (by omega)
  intro t ht
  simp only [RF, List.cons_append, List.nil_append] at ht ⊢
  seg_fp ht using $tac)

/-- The closer of a sum of bit vectors: the equality of the numbers. -/
macro "bv_add" : tactic => `(tactic|
  ((try congr 1); apply BitVec.eq_of_toNat_eq
   simp only [truncBits, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
   omega))

nx_gate nx_1051 1051 1052 using
  simp only [Control.valueOf, Control.scalarValue, Control.u32, b32, Nat.reduceEqDiff, ↓reduceIte]
  bv_add
nx_gate nx_1052 1052 1053 using
  simp only [Control.valueOf, Control.scalarValue, Value.pred.injEq, Nat.reduceEqDiff,
    ↓reduceIte, hn']
  exact Control.cmp_ge_s32 _ _ hb h1
nx_gate nx_1053 1053 1054 using
  simp only [Control.valueOf, Control.scalarValue, b64, Nat.reduceEqDiff, ↓reduceIte]
  bv_add
nx_gate nx_1054 1054 1055 using
  simp only [Control.valueOf, Control.scalarValue, Value.pred.injEq, Nat.reduceEqDiff,
    ↓reduceIte, Nat.mod_eq_of_lt hs]
  exact Control.cmp_lt_s64 _ _ (by omega) h2
nx_gate nx_1055 1055 1057 using
  simp [Control.valueOf, Control.scalarValue, Control.nextEnabled, Bool.and_assoc]
nx_gate nx_1057 1057 1058 using
  simp only [Control.valueOf, Control.scalarValue, Control.u32, b32, Nat.reduceEqDiff, ↓reduceIte]
  bv_add
nx_gate nx_1058 1058 1059 using late_nxp

set_option hygiene false in
/-- A chunk of the pointer table of the loop's loads: the adds from `a` to `b`, run exactly. -/
macro "nx_chunk " n:ident a:num b:num : command => `(
theorem $n {j : Nat} {v : Control.Carry} (m : Value) :
    Seg kernel Assumptions.all L g ($b - $a) $a (RF e L g m j v $a) $b (RF e L g m j v $b) := by
  intro t ht
  simp only [RF, List.cons_append, List.nil_append] at ht ⊢
  seg_fp ht using late_nxp)

nx_chunk nx_1059 1059 1066
nx_chunk nx_1066 1066 1073
nx_chunk nx_1073 1073 1080
nx_chunk nx_1080 1080 1087
nx_chunk nx_1087 1087 1094
nx_chunk nx_1094 1094 1101
nx_chunk nx_1101 1101 1108
nx_chunk nx_1108 1108 1115
nx_chunk nx_1115 1115 1122
nx_chunk nx_1122 1122 1124

/-- The whole stretch from the branch to the first load, run exactly. -/
theorem nx_seg {j : Nat} {v : Control.Carry} (m : Value) (ok : e.Ok) (hj : j ≤ e.limit) :
    Seg kernel Assumptions.all L g (1124 - 1051) 1051 (RF e L g m j v 1051) 1124
      (RF e L g m j v 1124) :=
  ((nx_1051 m ok hj).comp ((nx_1052 m ok hj).comp ((nx_1053 m ok hj).comp ((nx_1054 m ok hj).comp
    ((nx_1055 m ok hj).comp ((nx_1057 m ok hj).comp ((nx_1058 m ok hj).comp ((nx_1059 m).comp
    ((nx_1066 m).comp ((nx_1073 m).comp ((nx_1080 m).comp ((nx_1087 m).comp ((nx_1094 m).comp
    ((nx_1101 m).comp ((nx_1108 m).comp ((nx_1115 m).comp (nx_1122 m))))))))))))))))).of_len
    (by omega)

/-- **The route to the first load**: the span from the fall-through of the test to pc 1124. -/
theorem route_nxt {j : Nat} {v : Control.Carry} (m : Value) (ok : e.Ok) (hj : j ≤ e.limit) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1051
      (RF e L g m j v 1051) 1124 (RF e L g m j v 1124) :=
  SegQ.tauAll _ (segQF_of_seg_typed lateQt (Ft := []) (n := 1124 - 1051) (nx_seg m ok hj) rfl
    (by decide +kernel) (by decide +kernel) (AbsSound.mono (absF5_sound (fp3_of (L := L) (g := g)
    (a := 1051) (b := 1124) (by decide +kernel))) (by decide +kernel) (by decide +kernel))
    trivial (by decide +kernel))
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
