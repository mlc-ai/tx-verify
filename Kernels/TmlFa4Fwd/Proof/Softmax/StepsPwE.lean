-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # The end of the first round: the loop entry

From pc 5006 (after the row sum) into the bias rounds, the plain rounds or the final stores. The
walk is cut at pc 5022 (`pwA`), where the facts state `%p628` as the test on `r169` and `r299`,
`%r299` and `%r300` in closed form and the control registers by name; the branch at pc 5024 then
reads `%p628` as a literal (`Seg.pred_ex`), and the plain entry's test at pc 6656 reads the walked
`min32 (r169 …) (r299 …)`, which the hypothesis states with `r431` unfolded. Each walk runs once
per kind of the round's maximum (`-∞` or a real), since the successor's table states the maximum
by its kind. The bias-round exits and the step are in `StepsPwE2.lean`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (i32 sub32 addi scmpi add32 shrs shru sel scmp andi)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (neg32)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- `%r300` (pcs 5009 to 5019): the plain rounds' bound before its clamp at 0 (`r301`). -/
def r300 (p : Params) (L : Launch) (g : Nat) (v : V) : BitVec 64 :=
  let x := addi (r165 p L g v) (-256)
  let s := add32 x (shru (shrs x 31) 25)
  add32 (shrs s 7) (sel (scmpi .lt .s x 0 && scmp .ne .b x (andi s (-128))) (i32 (-1)) (i32 0))

/-- The facts at pc 5022, with the maximum's value `M` and the row sum `x`. -/
def pwMid (p : Params) (L : Launch) (g : Nat) (v : V) (M : Value) (x : ℝ) :
    List (Nat × Value) :=
  (630, .pred (scmpi .lt .s (sub32 (r169 p L g v) (r299 p L g v)) 1)) ::
    (1359, .bits 32 (r299 p L g v)) :: (1360, .bits 32 (r300 p L g v)) ::
    (7257, .float .f32 x) :: (7256, M) :: (1230, negS p) ::
    (441, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 441) ::
    (1062, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 1062) ::
    (1069, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 1069) ::
    (1215, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 1215) ::
    (1226, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 1226) ::
    (1229, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 1229) ::
    (2390, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 2390) ::
    (2535, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 2535) ::
    (5127, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 5127) ::
    (6495, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 6495) ::
    (6497, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 6497) ::
    (7132, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 7132) ::
    (7500, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 7500) ::
    (7501, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 7501) ::
    (7502, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 7502) ::
    (7503, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 7503) ::
    (7506, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 7506) ::
    (7896, valueOf p L g ⟨.pwend .first, v, 0, []⟩ 7896) :: []

/-- **To pc 5022.** -/
theorem pwA (hp : Pre p L m) (v : V) (x : ℝ) (M : Value) :
    ∃ n, Seg kernel Assumptions.all L g n 5006
      ((7257, .float .f32 x) :: (7256, M) :: (1230, negS p) ::
        factsFrom (ctlLive 5006) (valueOf p L g ⟨.pwend .first, v, 0, []⟩)) 5022
      (pwMid p L g v M x) := by
  have hparams := params hp
  unfold pwMid
  seg_sym using (soft_seg)

theorem pwFinN (hp : Pre p L m) (v : V) (x : ℝ)
    (_h1 : scmpi .lt .s (sub32 (r169 p L g v) (r299 p L g v)) 1 = true)
    (h2 : scmpi .lt .s (r431 p L g v) 1 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 5022 ((630, .pred true) :: pwMid p L g v (ninf32) x) 7614
      (factsD p L g (D.mk' (.fin 0) { v with
          ppar := i32 1, spar := i32 1, mf := false, mr := 0, rs := x })) := by
  have hparams := params hp
  simp only [r431] at h2
  unfold pwMid
  seg_sym using (soft_seg)

theorem pwFinR (hp : Pre p L m) (v : V) (x : ℝ) (r : ℝ)
    (_h1 : scmpi .lt .s (sub32 (r169 p L g v) (r299 p L g v)) 1 = true)
    (h2 : scmpi .lt .s (r431 p L g v) 1 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 5022 ((630, .pred true) ::
      pwMid p L g v (.float .f32 r) x) 7614
      (factsD p L g (D.mk' (.fin 0) { v with
          ppar := i32 1, spar := i32 1, mf := true, mr := r, rs := x })) := by
  have hparams := params hp
  simp only [r431] at h2
  unfold pwMid
  seg_sym using (soft_seg)

theorem pwPlN (hp : Pre p L m) (v : V) (x : ℝ)
    (_h1 : scmpi .lt .s (sub32 (r169 p L g v) (r299 p L g v)) 1 = true)
    (h2 : ¬ scmpi .lt .s (r431 p L g v) 1 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 5022 ((630, .pred true) :: pwMid p L g v (ninf32) x) 6676
      (factsD p L g (D.mk' (.ws .plain) { v with
          ppar := i32 1, spar := i32 1, mf := false, mr := 0, rs := x,
          pl := neg32 (r431 p L g v) })) := by
  have hparams := params hp
  simp only [r431] at h2
  unfold pwMid
  seg_sym using (soft_seg)

theorem pwPlR (hp : Pre p L m) (v : V) (x : ℝ) (r : ℝ)
    (_h1 : scmpi .lt .s (sub32 (r169 p L g v) (r299 p L g v)) 1 = true)
    (h2 : ¬ scmpi .lt .s (r431 p L g v) 1 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 5022 ((630, .pred true) ::
      pwMid p L g v (.float .f32 r) x) 6676
      (factsD p L g (D.mk' (.ws .plain) { v with
          ppar := i32 1, spar := i32 1, mf := true, mr := r, rs := x,
          pl := neg32 (r431 p L g v) })) := by
  have hparams := params hp
  simp only [r431] at h2
  unfold pwMid
  seg_sym using (soft_seg)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
