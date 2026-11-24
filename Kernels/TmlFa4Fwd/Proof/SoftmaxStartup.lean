-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
public import Kernels.TmlFa4Fwd.Flow.Code.Part029
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.SegChain
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Prologue

noncomputable section

/-- The same softmax body serves both groups of four warps. -/
def stageOf (warp : Fin 8) : Fin 2 := ⟨warp.val / 4, by have := warp.isLt; omega⟩

/-- The shared-base broadcast and ABI pointers used by the softmax scheduler. -/
def dispatchInput (p : Params) (l : Launch) (warp : Fin 8) : List (Nat × Value) :=
  [(1062, b32 warp.val), (2535, b32 l.sharedBase),
   (7502, b64 p.cuQBase), (7503, b64 p.usedKBase), (7506, b64 p.cuQBase)]

def dispatchOutput (p : Params) (l : Launch) (g : Nat) (warp : Fin 8) :
    List (Nat × Value) :=
  (1072, b32 (g / l.block)) :: dispatchInput p l warp

private theorem ctaWord {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) :
    truncBits 32 (BitVec.ofNat 64 ((l.ctaidOf (g / l.block)).get .x)) =
      BitVec.ofNat 64 (g / l.block) := by
  have hcta : (l.ctaidOf (g / l.block)).get .x = g / l.block :=
    Option.some.inj (sregValue_oneDim hp.cluster.2.2 g).2.2.1
  have hblock : 0 < l.block := by rw [hp.block]; decide
  have hgrid : g / l.block < l.grid :=
    (Nat.div_lt_iff_lt_mul hblock).2 (show g < l.grid * l.block from hg)
  have hCta32 : g / l.block < 2 ^ 32 := by have := hp.grid.2.2; omega
  rw [hcta, truncBits_ofNat hCta32 (by decide)]

/-- Every warp in either softmax group reaches the same role-specific ABI load. -/
theorem dispatchRun {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (hg : g < l.threads) (warp : Fin 8) :
    Seg kernel Assumptions.all l g 11 174 (dispatchInput p l warp) 3101
      (dispatchOutput p l g warp) := by
  have hcta := ctaWord hp hg
  fin_cases warp <;> intro t ht <;>
    simp only [dispatchInput, dispatchOutput] at ht ⊢ <;>
    seg_fp ht using simp only [b32, hcta]

set_option maxRecDepth 10000 in
private theorem param19Name :
    param 19 = "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_\
      object_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf16\
      gmemalign16o1i64div8_0_param_19" := by
  have h : toString (19 : Nat) = "19" := by
    rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
    simp only [show (19 / 10 : Nat) = 1 by decide, show (19 % 10 : Nat) = 9 by decide,
      Nat.repr_of_lt (n := 1) (by decide), Nat.repr_of_lt (n := 9) (by decide),
      Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_nine.mpr rfl]
    rfl
  unfold param
  rw [h]
  rfl

/-- The scalar batch bound is loaded from launch parameter 19 before the register hint. -/
theorem batchRun {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (warp : Fin 8) :
    Seg kernel Assumptions.all l g 1 3101 (dispatchOutput p l g warp) 3102
      ((7247, b32 p.batch) :: dispatchOutput p l g warp) := by
  obtain ⟨hb, hParam⟩ := hp.values (19, p.batch) (by simp [Params.scalarWords])
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at hParam
  rw [param19Name] at hParam
  intro t ht
  have hCore : run kernel [] l g 1 t = some (next (setReg t 7247 (b32 p.batch))) := by
    apply run_local Flow.code_3101 rfl ht
    rw [execLocalA_nil, execLocal_mem rfl]
    simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq,
      DType.width, MemExt.extendBits_same, pure, Except.pure]
    rw [hParam]
    change Except.ok (next (setReg t 7247 (.bits 32 (truncBits 32 (BitVec.ofNat 64 p.batch))))) = _
    rw [truncBits_ofNat (show p.batch < 2 ^ 32 from hb) (by decide)]
    rfl
  have hModel : out kernel Assumptions.all l g t = out kernel [] l g t := by
    apply Assumptions.out_all_eq_nil _ _ _ (by rw [ht.1]; exact Flow.code_3101) rfl
    all_goals rw [ht.1]; decide
  refine ⟨_, by simpa only [run, tauStep, hModel] using hCore, ht.set ?_⟩
  simp [dispatchOutput, dispatchInput]

/-- The first softmax instruction that issues an event raises the register limit. -/
theorem firstHint {l : Launch} {g : Nat} {t : TState} {F : List (Nat × Value)}
    (ht : At t 3102 F) :
    out kernel Assumptions.all l g t = .ev (.setMaxReg true 184 (next t)) := by
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_3102) rfl rfl]
  rfl

/-- Both softmax groups synchronize on the 416-thread register handoff after the hint. -/
theorem entryBarrier {l : Launch} {g : Nat} {t : TState} {F : List (Nat × Value)}
    (hb : l.block = 512) (ht : At t 3103 F) :
    out kernel Assumptions.all l g t = .ev (.bar 2 (next t) (some 416) .sync) := by
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_3103) rfl rfl]
  change Out.ev (barTmpl l g t (.imm 2) (some (.imm 416)) .sync) = _
  simp [barTmpl, readBits, pure, Except.pure, hb,
    show (truncBits 32 2#64).toNat = 2 by decide,
    show (truncBits 32 416#64).toNat = 416 by decide]

end
end PTX.Kernels.TmlFa4Fwd.Softmax
