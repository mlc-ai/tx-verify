-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.DerivedJump
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The derived constants hold at the stop after the runs -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

theorem holds_factsFrom_app {R : Nat → Option Value} {a b : List Nat} {v : Nat → Value}
    (h1 : Holds R (factsFrom a v)) (h2 : Holds R (factsFrom b v)) :
    Holds R (factsFrom (a ++ b) v) := by
  simpa [factsFrom, List.map_append, holds_append] using And.intro h1 h2

/-- The result of a jump of the table. -/
abbrev Jump (e : Entry) (L : Launch) (g : Nat) (t : TState) : Prop :=
  (∃ w, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t w ∧ t ≠ w ∧
    TabGood kernel ivsD tk (fun _ => false) (derV e L g) (derV e L g) w) ∨
    Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) t

theorem jmp_en {t : TState} (ht : t.pc = 576) (hf : t.fault = none) (hT : TabD e L g t) :
    Jump e L g t :=
  jump_tab (ins := (kernel.code.drop 576).take 21) (Hk := [482, 525])
    (Gen.en_run L g (lookupD (G0 e L g))) rfl (by decide +kernel) (by decide +kernel)
    (fun i hi => smSegFree (by simp only [intPc, decide_eq_true_eq]; omega)) (by decide)
    (by decide +kernel)
    (fun R h => ⟨to0 (live := [462, 481]) (holds_factsFrom_mono h (by decide)) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
      holds_factsFrom_mono h (by decide)⟩)
    (fun R hG hH => holds_factsFrom_mono (holds_factsFrom_app (a := kEn) (b := [482, 525])
      (up1 hG rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hH)
      (by decide))
    ht hf hT

theorem jmp_dv {t : TState} (ht : t.pc = 599) (hf : t.fault = none) (hT : TabD e L g t) :
    Jump e L g t :=
  jump_tab (ins := (kernel.code.drop 599).take 3) (Hk := [1, 2, 496, 798, 482])
    (Gen.dv_run L g (lookupD (G1 e L g))) rfl (by decide +kernel) (by decide +kernel)
    (fun i hi => segFreeLt (by omega)) (by decide) (by decide +kernel)
    (fun R h => ⟨to1 (live := [525]) (holds_factsFrom_mono h (by decide)) (by decide)
      (by decide) (by decide) (by decide) (by decide), holds_factsFrom_mono h (by decide)⟩)
    (fun R hG hH => holds_factsFrom_mono (holds_factsFrom_app (a := kDv)
      (b := [1, 2, 496, 798, 482])
      (up2 hG rfl (by decide) (by decide) (by decide) (by decide) (by decide)) hH) (by decide))
    ht hf hT

theorem jmp_e8 {t : TState} (ht : t.pc = 609) (hf : t.fault = none) (hT : TabD e L g t) :
    Jump e L g t :=
  jump_tab (ins := (kernel.code.drop 609).take 1) (Hk := [798, 1, 2, 496, 482, 498, 805])
    (Gen.e8_run L g (lookupD (G2 e L g))) rfl (by decide +kernel) (by decide +kernel)
    (fun i hi => smSegFree (by simp only [intPc, decide_eq_true_eq]; omega)) (by decide)
    (by decide +kernel)
    (fun R h => ⟨to2 (live := [798]) (holds_factsFrom_mono h (by decide)) (by decide)
      (by decide) (by decide) (by decide), holds_factsFrom_mono h (by decide)⟩)
    (fun R hG hH => holds_factsFrom_mono (holds_factsFrom_app (a := kE8)
      (b := [798, 1, 2, 496, 482, 498, 805])
      (up3 hG rfl (by decide) (by decide) (by decide) (by decide)) hH) (by decide))
    ht hf hT

theorem jmp_ng {t : TState} (ht : t.pc = 807) (hf : t.fault = none) (hT : TabD e L g t) :
    Jump e L g t :=
  jump_tab (ins := (kernel.code.drop 807).take 1) (Hk := [1956, 1, 2, 496, 798, 482, 805])
    (Gen.ng_run L g (lookupD (G3 e L g))) rfl (by decide +kernel) (by decide +kernel)
    (fun i hi => segFreeLt (by omega)) (by decide) (by decide +kernel)
    (fun R h => ⟨to3 (live := [498]) (holds_factsFrom_mono h (by decide)) (by decide)
      (by decide) (by decide), holds_factsFrom_mono h (by decide)⟩)
    (fun R hG hH => holds_factsFrom_mono (holds_factsFrom_app (a := kNg)
      (b := [1956, 1, 2, 496, 798, 482, 805])
      (up4 hG rfl (by decide) (by decide) (by decide)) hH) (by decide))
    ht hf hT

theorem jmp_ie {t : TState} (ht : t.pc = 814) (hf : t.fault = none) (hT : TabD e L g t) :
    Jump e L g t :=
  jump_tab (ins := (kernel.code.drop 814).take 2) (Hk := [1956, 1, 2, 805, 499])
    (Gen.ie_run L g (lookupD (G4 e L g))) rfl (by decide +kernel) (by decide +kernel)
    (fun i hi => smSegFree (by simp only [intPc, decide_eq_true_eq]; omega)) (by decide)
    (by decide +kernel)
    (fun R h => ⟨to4 (live := [482, 496, 798]) (holds_factsFrom_mono h (by decide))
      (by decide) (by decide), holds_factsFrom_mono h (by decide)⟩)
    (fun R hG hH => holds_factsFrom_mono (holds_factsFrom_app (a := kIe)
      (b := [1956, 1, 2, 805, 499]) (up5 hG rfl (by decide) (by decide)) hH) (by decide))
    ht hf hT

theorem jmp_io {t : TState} (ht : t.pc = 848) (hf : t.fault = none) (hT : TabD e L g t) :
    Jump e L g t :=
  jump_tab (ins := (kernel.code.drop 848).take 95) (Hk := [1, 2, 1956, 499])
    (Gen.io_run L g (lookupD (G5 e L g))) rfl (by decide +kernel) (by decide +kernel)
    (fun i hi => smSegFree (by simp only [intPc, decide_eq_true_eq]; omega)) (by decide)
    (by decide +kernel)
    (fun R h => ⟨to5 (live := [805, 810, 811]) (holds_factsFrom_mono h (by decide)) (by decide),
      holds_factsFrom_mono h (by decide)⟩)
    (fun R hG hH => holds_factsFrom_mono (holds_factsFrom_app (a := kIo) (b := [1, 2, 1956, 499])
      (up6 hG rfl (by decide)) hH) (by decide))
    ht hf hT

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
