-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Proof.SoftmaxNumerics
public import Lemmas.Flow.Local
import Tactics.KernelRfl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

def biasConvertOp (dst src : Nat) : Op :=
  .cvt {dst := .float .f32, src := .float .bf16, d := dst, srcs := [.reg src]}

def probabilityConvertOp (dst a b : Nat) : Op :=
  .cvt {
    dst := .packed (.float .bf16) 2
    src := .float .f32
    rnd := some .rn
    d := dst
    srcs := [.reg a, .reg b] }

set_option maxRecDepth 10000 in
private theorem widenSitesCheck :
    Assumptions.biasWidenSites.all (fun pc => !Assumptions.swExp2Sites.contains pc) = true := by
  kernel_rfl

set_option maxRecDepth 10000 in
private theorem packSitesCheck :
    Assumptions.probPackSites.all (fun pc => !Assumptions.swExp2Sites.contains pc) = true := by
  kernel_rfl

private theorem noSwStep {l : Launch} {g : Nat} {t : TState}
    (h : t.pc ∉ Assumptions.swExp2Sites) : Assumptions.swExp2.segmentRule l g t = none := by
  simp [Assumptions.swExp2, h]

private theorem numericNoSegment {l : Launch} {g : Nat} {t : TState}
    (h : t.pc ∉ Assumptions.swExp2Sites) :
    (Assumptions.numeric.findSome? fun a => a.segmentRule l g t) = none := by
  have hI : Assumptions.idealArith.segmentRule l g t = none := rfl
  have hA : Assumptions.approx.segmentRule l g t = none := rfl
  have hL : Assumptions.lg2.segmentRule l g t = none := rfl
  have hB : Assumptions.bf16Convert.segmentRule l g t = none := rfl
  simp only [Assumptions.numeric, List.findSome?_cons, List.findSome?_nil, hI, hA, hL, hB,
    noSwStep h]

/-- For each finite BF16 bias value, the decoded widening step puts its exact F32 value in
the destination register under the kernel's numerical profile. -/
theorem biasConvertRun {l : Launch} {g pc dst src : Nat} {t : TState} {x : ℝ}
    {F : List (Nat × Value)} (ht : At t pc F)
    (hCode : kernel.code[pc]? = some ⟨none, biasConvertOp dst src⟩)
    (hSite : pc ∈ Assumptions.biasWidenSites)
    (hSrc : readFinite t .bf16 (.reg src) = some (.ok x)) :
    run kernel Assumptions.all l g 1 t = some (next (setReg t dst (.float .f32 x))) := by
  have hMember : t.pc ∈ Assumptions.biasWidenSites := ht.1.symm ▸ hSite
  have hOff : t.pc ∉ Assumptions.swExp2Sites := by
    simpa using List.all_eq_true.mp widenSitesCheck t.pc hMember
  have hNS := numericNoSegment (l := l) (g := g) hOff
  rw [Assumptions.run_all_eq_numeric]
  apply run_local hCode rfl ht
  have hArith : Assumptions.idealArith.localRule l g t (biasConvertOp dst src) = none := rfl
  have hApprox : Assumptions.approx.localRule l g t (biasConvertOp dst src) = none := rfl
  have hLog : Assumptions.lg2.localRule l g t (biasConvertOp dst src) = none := rfl
  have hWiden : Assumptions.bf16Convert.localRule l g t (biasConvertOp dst src) =
      some (.ok (next (setReg t dst (.float .f32 x)))) := by
    change (if !Assumptions.biasWidenSites.contains t.pc then none
      else bindRead (readFinite t .bf16 (.reg src))
        fun y => some (.ok (next (setReg t dst (.float .f32 y))))) = _
    simp [hMember, hSrc, bindRead]
  rw [execLocalA, hNS]
  simp only [Assumptions.numeric, execLocalRule, List.findSome?_cons, hArith, hApprox, hLog, hWiden]

/-- The actual packed-probability conversion packs the second finite probability into the
low half and the first into the high half before the TMEM operand reads those bytes. -/
theorem probabilityConvertRun {l : Launch} {g pc dst a b : Nat} {t : TState} {x y : ℝ}
    {F : List (Nat × Value)} (ht : At t pc F)
    (hCode : kernel.code[pc]? = some ⟨none, probabilityConvertOp dst a b⟩)
    (hSite : pc ∈ Assumptions.probPackSites)
    (ha : readFinite t .f32 (.reg a) = some (.ok x))
    (hb : readFinite t .f32 (.reg b) = some (.ok y)) :
    run kernel Assumptions.all l g 1 t =
      some (next (setReg t dst (.pair (.float .bf16 y) (.float .bf16 x)))) := by
  have hMember : t.pc ∈ Assumptions.probPackSites := ht.1.symm ▸ hSite
  have hOff : t.pc ∉ Assumptions.swExp2Sites := by
    simpa using List.all_eq_true.mp packSitesCheck t.pc hMember
  have hNS := numericNoSegment (l := l) (g := g) hOff
  rw [Assumptions.run_all_eq_numeric]
  apply run_local hCode rfl ht
  have hArith : Assumptions.idealArith.localRule l g t (probabilityConvertOp dst a b) = none := rfl
  have hApprox : Assumptions.approx.localRule l g t (probabilityConvertOp dst a b) = none := rfl
  have hLog : Assumptions.lg2.localRule l g t (probabilityConvertOp dst a b) = none := rfl
  have hPack : Assumptions.bf16Convert.localRule l g t (probabilityConvertOp dst a b) =
      some (.ok (next (setReg t dst (.pair (.float .bf16 y) (.float .bf16 x))))) := by
    change (if !Assumptions.probPackSites.contains t.pc then none
      else bindRead (readFinite t .f32 (.reg a)) fun x =>
        bindRead (readFinite t .f32 (.reg b)) fun y =>
          some (.ok (next (setReg t dst (.pair (.float .bf16 y) (.float .bf16 x)))))) = _
    simp [hMember, ha, hb, bindRead]
  rw [execLocalA, hNS]
  simp only [Assumptions.numeric, execLocalRule, List.findSome?_cons, hArith, hApprox, hLog, hPack]

end
end PTX.Kernels.TmlFa4Fwd.Softmax
