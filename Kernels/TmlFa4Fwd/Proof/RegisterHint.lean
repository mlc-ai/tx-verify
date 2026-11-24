-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

/-- The direction and count used by the two softmax warpgroups, the correction warpgroup,
and the warpgroup containing MMA, output and both loaders. -/
def registerHintOf (warp : Nat) : Bool × Nat :=
  if warp < 8 then (true, 184) else if warp < 12 then (false, 64) else (false, 80)

/-- The five role entry instructions that request a warpgroup register limit. -/
def registerHintPc (warp : Fin 16) : Nat := dispatchParamPc warp + 1

private def batchDst (warp : Nat) : Nat :=
  if 14 ≤ warp then 7170 else
  if warp = 13 then 7228 else if warp = 12 then 7203 else if warp < 8 then 7247 else 7277

private def batchAccess (d : Nat) : MemAccess :=
  { kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
    addr := ⟨.param (param 19) false, 0⟩, dsts := [some d] }

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

private theorem batchAtDispatch (warp : Fin 16) :
    kernel.code[dispatchParamPc warp]? = some ⟨none, .mem (batchAccess (batchDst warp.val))⟩ := by
  unfold dispatchParamPc batchDst batchAccess
  rw [param19Name]
  split_ifs
  · exact Flow.code_178
  · exact Flow.code_2768
  · exact Flow.code_1906
  · exact Flow.code_3101
  · exact Flow.code_7745

private theorem hintAtDispatch (warp : Fin 16) :
    kernel.code[registerHintPc warp]? = some
      ⟨none, .setMaxReg (registerHintOf warp.val).1 (registerHintOf warp.val).2⟩ := by
  unfold registerHintPc dispatchParamPc
  split_ifs with h14 hout hmma hSoft
  · simp only [registerHintOf, ite_eq_right (show ¬ warp.val < 8 by omega),
      ite_eq_right (show ¬ warp.val < 12 by omega)]
    exact Flow.code_179
  · simp only [registerHintOf, ite_eq_right (show ¬ warp.val < 8 by omega),
      ite_eq_right (show ¬ warp.val < 12 by omega)]
    exact Flow.code_2769
  · simp only [registerHintOf, ite_eq_right (show ¬ warp.val < 8 by omega),
      ite_eq_right (show ¬ warp.val < 12 by omega)]
    exact Flow.code_1907
  · simp only [registerHintOf, ite_eq_left hSoft]
    exact Flow.code_3102
  · simp only [registerHintOf, ite_eq_right hSoft,
      ite_eq_left (show warp.val < 12 by omega)]
    exact Flow.code_7746

private theorem batchUnhooked (warp : Fin 16) :
    dispatchParamPc warp ∉ Assumptions.swExp2Sites ∧
      dispatchParamPc warp ∉ Assumptions.tcLdDataflowSites ∧
      dispatchParamPc warp ∉ Assumptions.delayedTmemSites := by
  fin_cases warp <;> decide

private theorem hintUnhooked (warp : Fin 16) :
    registerHintPc warp ∉ Assumptions.swExp2Sites ∧
      registerHintPc warp ∉ Assumptions.tcLdDataflowSites ∧
      registerHintPc warp ∉ Assumptions.delayedTmemSites := by
  fin_cases warp <;> decide

private theorem batchRun {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (g : Nat) (warp : Fin 16) {t : TState}
    (ht : At t (dispatchParamPc warp)
      [(1062, b32 warp.val), (1072, b32 (g / l.block)), (2535, b32 l.sharedBase)]) :
    run kernel Assumptions.all l g 1 t =
      some (next (setReg t (batchDst warp.val) (b32 p.batch))) := by
  obtain ⟨hb, hParam⟩ := hp.values (19, p.batch) (by simp [Params.scalarWords])
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at hParam
  have hCore : run kernel [] l g 1 t =
      some (next (setReg t (batchDst warp.val) (b32 p.batch))) := by
    apply run_local (batchAtDispatch warp) rfl ht
    rw [execLocalA_nil, execLocal_mem rfl]
    simp only [batchAccess, execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil,
      id_eq, DType.width, MemExt.extendBits_same, pure, Except.pure, hParam,
      truncBits_ofNat (show p.batch < 2 ^ 32 from hb) (by decide)]
    rfl
  have hOff := batchUnhooked warp
  have hModel : out kernel Assumptions.all l g t = out kernel [] l g t :=
    Assumptions.out_all_eq_nil (ht.1.symm ▸ hOff.1) (ht.1.symm ▸ hOff.2.1)
      (ht.1.symm ▸ hOff.2.2) (ht.1.symm ▸ batchAtDispatch warp) rfl
  simpa only [run, tauStep, hModel] using hCore

/-- The first register request is prepared using only the local startup registers and ABI. -/
theorem firstRegisterHintNext {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} (hg : g < l.threads) (warp : Fin 16) {t : TState}
    (ht : At t 174 [(1062, b32 warp.val), (2535, b32 l.sharedBase)]) :
    ∃ u, At u (registerHintPc warp) [(1062, b32 warp.val), (2535, b32 l.sharedBase)] ∧
      Next kernel Assumptions.all l g t u
        (.setMaxReg (registerHintOf warp.val).1 (registerHintOf warp.val).2 (next u)) := by
  obtain ⟨s, hs, hS⟩ := dispatchRunFromCommon hp warp hg ht
  let u := next (setReg s (batchDst warp.val) (b32 p.batch))
  have hU : At u (registerHintPc warp)
      [(1062, b32 warp.val), (2535, b32 l.sharedBase)] := by
    have hFresh : ∀ f ∈ [(1062, b32 warp.val), (1072, b32 (g / l.block)),
        (2535, b32 l.sharedBase)], f.1 ≠ batchDst warp.val := by
      fin_cases warp <;> simp [batchDst]
    have hAt := hS.set (v := b32 p.batch) hFresh
    exact hAt.mono ⟨hAt.2.2.2.2.2.1, hAt.2.2.2.2.2.2.2.1, trivial⟩
  have hOff := hintUnhooked warp
  have hc : kernel.code[u.pc]? = some
      ⟨none, .setMaxReg (registerHintOf warp.val).1 (registerHintOf warp.val).2⟩ :=
    hU.1.symm ▸ hintAtDispatch warp
  have hv : SetMaxNReg.validCount (registerHintOf warp.val).2 = true := by
    fin_cases warp <;> decide
  have hout : out kernel [] l g u =
      .ev (.setMaxReg (registerHintOf warp.val).1 (registerHintOf warp.val).2 (next u)) := by
    rw [out, hU.2.2.2.1, hc]
    change Out.ev (SetMaxNReg.tmpl u (registerHintOf warp.val).1 (registerHintOf warp.val).2) = _
    simp [SetMaxNReg.tmpl, hv]
  have hn : Next kernel Assumptions.all l g t u
      (.setMaxReg (registerHintOf warp.val).1 (registerHintOf warp.val).2 (next u)) :=
    ⟨run_rtg (run_comp hs (batchRun hp g warp hS)),
      (Assumptions.out_all_eq_nil (hU.1.symm ▸ hOff.1) (hU.1.symm ▸ hOff.2.1)
        (hU.1.symm ▸ hOff.2.2) hc rfl).trans hout⟩
  exact ⟨u, hU, hn⟩

/-- Every actual post-barrier prefix with a recorded event issues the role's decoded
register hint at its first event position. -/
theorem firstRegisterHintFromCommon {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g pos : Nat} (hg : g < l.threads) (warp : Fin 16)
    {t : TState} {o : Option TState}
    (ht : At t 174 [(1062, b32 warp.val), (2535, b32 l.sharedBase)])
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o)
    (hNonempty : (X.tr g).drop pos ≠ []) :
    ∃ u inst, X.get (g, pos) = some
        ⟨registerHintPc warp, .setMaxReg (registerHintOf warp.val).1 (registerHintOf warp.val).2
          inst⟩ ∧
      At u (registerHintPc warp + 1) [(1062, b32 warp.val), (2535, b32 l.sharedBase)] ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) o := by
  obtain ⟨u, hU, hn⟩ := firstRegisterHintNext hp hg warp ht
  obtain ⟨_, v, he, ⟨inst, rfl, hv⟩, hTail⟩ := hn.continuing_at_nonempty (by
    rintro _ ⟨_, _, h⟩
    cases h) hr hNonempty
  obtain rfl := Option.some.inj hv
  exact ⟨next u, inst, hU.1 ▸ he, hU.next, hTail⟩

end
end PTX.Kernels.TmlFa4Fwd
