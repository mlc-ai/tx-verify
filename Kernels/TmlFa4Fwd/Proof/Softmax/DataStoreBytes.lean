-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Open
import Kernels.TmlFa4Fwd.Proof.Softmax.BiasSumStart
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBT
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBTKA
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBTKB
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBK8
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsP1
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsP1Control
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPB
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainE1b
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainPUnpack
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainRs
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # The stored values have four bytes

The value of every register a P store, a statistics store or a final store writes has four bytes:
the P parts' halves by the kinds of the exponent stretches' terms (`expo1_ok`, `tailA_ok`,
`tailB_ok`, `expoP4_ok`), the second to fourth store's halves as the splits of packed words. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The registers the store unpacks write. -/
abbrev halfRegs (S : List (Nat × Nat × Nat)) : List Nat := S.flatMap fun (lo, hi, _) => [lo, hi]

private theorem half_bytes {S : List (Nat × Nat × Nat)} {E W : Nat → Value}
    (hv : ∀ lo hi w, (lo, hi, w) ∈ S →
      W lo = (splitValue 64 (E w)).1 ∧ W hi = (splitValue 64 (E w)).2)
    (hk : ∀ lo hi w, (lo, hi, w) ∈ S → (Kd.pr .w4).Has (E w)) {r : Nat} (hr : r ∈ halfRegs S) :
    (W r).bytes = 4 := by
  obtain ⟨⟨lo, hi, w⟩, hm, h⟩ := List.mem_flatMap.mp hr
  have hw := hk lo hi w hm
  have hs := hv lo hi w hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · rw [hs.1]; exact (SK.clean hw.2.1).1
  · rw [hs.2]; exact (SK.clean hw.2.2).1

/-- The first P store's halves of a first round. -/
abbrev storeRegs1 : List Nat := List.range' 3879 16
/-- The first P store's halves of a bias round. -/
abbrev storeRegsB : List Nat := List.range' 5048 16
/-- The first P store's halves of a plain round. -/
abbrev storeRegsP : List Nat := List.range' 5733 16

theorem bytes_p1 (hp : Pre p L m) {d : D} (hd : valuesData p L g d = p1Data p L g d.v) {r : Nat}
    (hr : r ∈ storeRegs1 ++ halfRegs unpackSpec1) : (valueOfD p L g d r).bytes = 4 := by
  rcases List.mem_append.mp hr with h | h
  · rw [valueOfD_p1 hd (by
      have hk : storeRegs1.all (((expoE p L g d.v).map Prod.fst).contains ·) = true := by
        unfold expoE; kernel_rfl
      exact List.contains_iff_mem.mp (List.all_eq_true.mp hk r h))]
    exact (clean_of_isS ((expo1_ok (g := g) hp d.v).2.2.2 r h) rfl).1
  · refine half_bytes (fun _ _ _ hm => valueOfD_p1h hd hm) (fun _ _ w hm => ?_) h
    have hk : unpackSpec1.all (fun q => wordRegs1.contains q.2.2) = true := by decide
    exact (expo1_ok (g := g) hp d.v).2.1 w
      (List.contains_iff_mem.mp (List.all_eq_true.mp hk _ hm))

theorem bytes_pB (hp : Pre p L m) {d : D} (hd : valuesData p L g d = pBData p L g d.v) {r : Nat}
    (hr : r ∈ storeRegsB ++ halfRegs unpackSpecB) : (valueOfD p L g d r).bytes = 4 := by
  rcases List.mem_append.mp hr with h | h
  · rw [valueOfD_pB hd (by
      have hk : storeRegsB.all (((tailB p L g d.v).map Prod.fst).contains ·) = true := by
        unfold tailB; kernel_rfl
      exact List.contains_iff_mem.mp (List.all_eq_true.mp hk r h))]
    unfold tailB vTailB
    cases Epilogue.scmp .lt .u d.v.bt (r301 p L g d.v)
    · have hk : storeRegsB.all (fun r => isS (kOf tAb4 r)) = true := by decide +kernel
      exact (clean_of_isS ((tailA_ok (g := g) hp d.v).2.2.2 r) (List.all_eq_true.mp hk r h)).1
    · have hk : storeRegsB.all (fun r => isS (kOf tBb4 r)) = true := by decide +kernel
      rw [expoBTA1_eq_B]
      exact (clean_of_isS ((tailB_ok d.v (bb8_kinds hp d.v)).2.2.2 r)
        (List.all_eq_true.mp hk r h)).1
  · have hk : unpackSpecB.all (fun q => wordRegsB.contains q.2.2) = true := by decide
    refine half_bytes (fun _ _ _ hm => valueOfD_pBh hd hm) (fun _ _ w hm => ?_) h
    have hw := List.contains_iff_mem.mp (List.all_eq_true.mp hk _ hm)
    rw [← valueOfD_pBw hd hm]
    exact pB_words hp hd (rs := [w]) (by simpa using hw) (w, _) (List.mem_singleton.mpr rfl)

theorem bytes_pP (hp : Pre p L m) {d : D} (hd : valuesData p L g d = pPData p d.v) {r : Nat}
    (hr : r ∈ storeRegsP ++ halfRegs unpackSpecP) : (valueOfD p L g d r).bytes = 4 := by
  rcases List.mem_append.mp hr with h | h
  · rw [valueOfD_pP hd (by
      have hk : storeRegsP.all (((expoPE p d.v).map Prod.fst).contains ·) = true := by
        unfold expoPE; kernel_rfl
      exact List.contains_iff_mem.mp (List.all_eq_true.mp hk r h))]
    have hk : storeRegsP.all (fun r => isS (kOf r4L3 r)) = true := by kernel_rfl
    exact (clean_of_isS ((expoP4_ok hp d.v).2 r) (List.all_eq_true.mp hk r h)).1
  · refine half_bytes (fun _ _ _ hm => valueOfD_pPh hd hm) (fun _ _ w hm => ?_) h
    have hk : unpackSpecP.all (fun q => wordRegsP.contains q.2.2) = true := by decide
    exact pP_wordK hp d.v w (List.contains_iff_mem.mp (List.all_eq_true.mp hk _ hm))

/-! ### The statistics -/

theorem bytes_statB (v : V) (k : Fin 4) (acc : List Value) :
    (valueOfD p L g ⟨.stat false, v, k, acc⟩ 1362).bytes = 4 :=
  (show SK.fl.Has (valueOfD p L g ⟨.stat false, v, k, acc⟩ 1362) from by
    rw [show valueOfD p L g ⟨.stat false, v, k, acc⟩ 1362 = lookupD (valuesBiasM p v) 1362 by
      kernel_rfl]
    exact facB_fl v).1.1

theorem bytes_statP (v : V) (k : Fin 4) (acc : List Value) :
    (valueOfD p L g ⟨.stat true, v, k, acc⟩ 1492).bytes = 4 := by
  have e : valueOfD p L g ⟨.stat true, v, k, acc⟩ 1492 = facP p v := by
    have h1 : (valuesPlainP p v).lookup 1492 = some (facP p v) := by
      unfold valuesPlainP facP
      cases v.mf <;> rfl
    have h0 : (valuesPairs .plain v 64).lookup 1492 = none := by kernel_rfl
    simp only [valueOfD, valuesData, valuesData0, List.lookup_append, h0, h1, Option.none_or,
      Option.getD_some]
  rw [e]
  exact (facP_fl p v).1.1

theorem bytes_fin (v : V) (k : Fin 4) (acc : List Value) (j : Fin 2) :
    (valueOfD p L g ⟨.fin j, v, k, acc⟩ 7257).bytes = 4 ∧
      (valueOfD p L g ⟨.fin j, v, k, acc⟩ 7256).bytes = 4 := by
  refine ⟨rfl, ?_⟩
  show (mxVal v).bytes = 4
  unfold mxVal
  cases v.mf <;> rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
