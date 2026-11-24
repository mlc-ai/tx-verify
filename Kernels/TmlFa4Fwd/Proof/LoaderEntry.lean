-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderTransparency
public import Kernels.TmlFa4Fwd.Proof.PrologueRoles
public import Kernels.TmlFa4Fwd.Proof2.Startup.Abi
public import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section
set_option maxRecDepth 2000

/-- Registers kept from the common CTA barrier through loader dispatch. -/
def loaderBarrierFacts (p : Params) (l : Launch) (g warp : Nat) : List (Nat × Value) :=
  [(1062, b32 warp), (2535, b32 l.sharedBase)] ++ abiFacts p l ++
    [(1061, b32 (g % l.block))]

/-- The loader's ABI and its role-specific batch length and CTA index. -/
def loaderEntryFacts (p : Params) (l : Launch) (g warp : Nat) : List (Nat × Value) :=
  [(7170, b32 p.batch), (1072, b32 (g / l.block))] ++ loaderBarrierFacts p l g warp

theorem loaderLinear {l : Launch} {g lo n : Nat} {t u : TState} {regs : List Nat}
    (hLo : 174 ≤ lo) (hHi : lo + n ≤ 1906) (hpc : t.pc = lo)
    (hCode : ((kernel.code.drop lo).take n).all
      (fun i => regs.all (fun r => !(writesRegs i.op).contains r)) = true)
    (hStraight : ((kernel.code.drop lo).take (n - 1)).all
      (fun i => schedulerFallsThrough i.op) = true)
    (hRun : run kernel [] l g n t = some u) :
    run kernel Assumptions.all l g n t = some u ∧ ∀ r ∈ regs, u.regs r = t.regs r :=
  ⟨schedulerLocalTransport hStraight (fun hlo hhi => loaderOutCore (by omega) (by omega))
    hRun (by omega) (by omega),
    fun _ h => schedulerLocalFrame hCode hStraight hRun (by omega) (by omega) h⟩

theorem loaderParam19Name : param 19 =
    "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_object_at__tenso\
    r000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf16gmemalign16o1i64div8_\
    0_param_19" := by
  have hDec : toString (19 : Nat) = "19" := by
    rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
    simp only [show (19 / 10 : Nat) = 1 by decide, show (19 % 10 : Nat) = 9 by decide,
      Nat.repr_of_lt (n := 1) (by decide), Nat.repr_of_lt (n := 9) (by decide),
      Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_nine.mpr rfl]
    rfl
  unfold param
  rw [hDec]
  rfl

private theorem loaderBatchParam {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} (hpc : t.pc = 178) (hf : t.fault = none) :
    run kernel Assumptions.all l g 1 t = some (next (setReg t 7170 (b32 p.batch))) := by
  obtain ⟨hBatch, hParam⟩ := hp.values (19, p.batch) (by simp [Params.scalarWords])
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at hParam
  rw [loaderParam19Name] at hParam
  have hRule : execLocalA [] l g t (kernel.code[178]?.getD (⟨none, .exit⟩ : Instr)).op =
      .ok (next (setReg t 7170 (b32 p.batch))) := by
    rw [Flow.code_178, Option.getD_some, execLocalA_nil, execLocal_mem rfl]
    simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq, hParam,
      DType.width, MemExt.extendBits_same, pure, Except.pure, truncBits_ofNat hBatch (by decide)]
    rfl
  have hRun : run kernel [] l g 1 t = some (next (setReg t 7170 (b32 p.batch))) := by
    rw [Flow.code_178, Option.getD_some] at hRule
    simp only [run, tauStep, out, hpc, hf, Flow.code_178, guardHolds, pure, Except.pure,
      hRule]
    rfl
  exact (loaderLinear (regs := []) (by decide) (by decide) hpc (by
    set_option maxRecDepth 100000 in kernel_rfl) rfl hRun).1

/-- The four decoded dispatch instructions and the batch parameter load lead to the first
loader event, with the common ABI registers unchanged. -/
theorem loaderDispatch {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) (warp : Fin 16) (hw : 14 ≤ warp.val) {t : TState}
    (ht : At t 174 (loaderBarrierFacts p l g warp.val)) :
    ∃ u, run kernel Assumptions.all l g 5 t = some u ∧ At u 179
      (loaderEntryFacts p l g warp.val) := by
  have hAt : At t 174 [(1062, b32 warp.val), (2535, b32 l.sharedBase)] :=
    ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, trivial⟩
  obtain ⟨v, hv, hvAt⟩ := dispatchRoles hp warp g hg t hAt
  rw [dispatchSteps, ite_eq_left hw] at hv
  rw [dispatchParamPc, ite_eq_left hw] at hvAt
  let regs := (loaderBarrierFacts p l g warp.val).map Prod.fst
  obtain ⟨hvA, hFrame⟩ := loaderLinear (regs := regs) (by decide) (by decide) ht.1 (by
    change ((kernel.code.drop 174).take 4).all (fun i =>
      ([1062, 2535, 1, 7492, 7493, 7494, 7495, 1663, 1664, 7496, 7497, 7498, 7499,
        7500, 7501, 7502, 7503, 7504, 7505, 7291, 7290, 7289, 7506, 7292, 7293, 7294, 7295,
        1665, 1061] : List Nat).all (fun r => !(writesRegs i.op).contains r)) = true
    set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hKeep := holdsSchedulerFrame ht.2.2.2.2 hFrame (fun _ h => List.mem_map_of_mem h)
  have hBefore : At v 178 ((1072, b32 (g / l.block)) :: loaderBarrierFacts p l g warp.val) :=
    hvAt.mono ⟨hvAt.2.2.2.2.2.1, hKeep⟩
  have hFresh : ∀ x ∈ ((1072, b32 (g / l.block)) :: loaderBarrierFacts p l g warp.val),
      x.1 ≠ 7170 := by
    intro x hx heq
    have hm := List.mem_map_of_mem (f := Prod.fst) hx
    rw [heq] at hm
    exact (of_decide_eq_true rfl : ¬ 7170 ∈
      [1072, 1062, 2535, 1, 7492, 7493, 7494, 7495, 1663, 1664, 7496, 7497, 7498, 7499,
        7500, 7501, 7502, 7503, 7504, 7505, 7291, 7290, 7289, 7506, 7292, 7293, 7294, 7295,
        1665, 1061]) hm
  exact ⟨_, run_comp hvA (loaderBatchParam hp hvAt.1 hvAt.2.2.2.1),
    hBefore.set (v := b32 p.batch) hFresh⟩

/-- The first loader register request follows the common CTA barrier. -/
theorem loaderHintNext {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) (warp : Fin 16) (hw : 14 ≤ warp.val)
    {t : TState} (ht : At t 174 (loaderBarrierFacts p l g warp.val)) :
    ∃ s, At s 179 (loaderEntryFacts p l g warp.val) ∧
      Next kernel Assumptions.all l g t s (.setMaxReg false 80 (next s)) := by
  obtain ⟨s, hs, hAt⟩ := loaderDispatch hp hg warp hw ht
  have hCore : out kernel [] l g s = .ev (.setMaxReg false 80 (next s)) := by
    unfold out
    rw [hAt.1, hAt.2.2.2.1, Flow.code_179]
    rfl
  exact ⟨s,hAt,run_rtg hs,
    (loaderOutCore (by rw [hAt.1]; decide) (by rw [hAt.1]; decide)).trans hCore⟩

/-- A nonempty loader prefix from the common CTA barrier performs the register hint at
PC 179 and continues with the fully decoded ABI state. -/
theorem loaderHintObservedPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m)
    {g i : Nat} (hg : g < l.threads) (warp : Fin 16) (hw : 14 ≤ warp.val)
    {t : TState} {o : Option TState}
    (ht : At t 174 (loaderBarrierFacts p l g warp.val))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) o)
    (hNonempty : (X.tr g).drop i ≠ []) :
    ∃ inst u, X.get (g, i) = some ⟨179, .setMaxReg false 80 inst⟩ ∧
      At u 180 (loaderEntryFacts p l g warp.val) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1)) o := by
  obtain ⟨s,hAt,hNext⟩ := loaderHintNext hp hg warp hw ht
  obtain ⟨e, u, he, ⟨inst, rfl, hu⟩, hTail⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨_, _, hBad⟩
    cases hBad) hRun hNonempty
  obtain rfl := Option.some.inj hu
  exact ⟨inst, next s, by simpa only [hAt.1] using he, hAt.next, hTail⟩


/-- A terminated loader trace continues past the register hint with the decoded ABI state. -/
theorem loaderHintObserved {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g i : Nat} (hg : g < l.threads) (warp : Fin 16) (hw : 14 ≤ warp.val) {t : TState}
    (ht : At t 174 (loaderBarrierFacts p l g warp.val))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    ∃ inst u, X.get (g, i) = some ⟨179, .setMaxReg false 80 inst⟩ ∧
      At u 180 (loaderEntryFacts p l g warp.val) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1)) none :=
  loaderHintObservedPrefix hp hg warp hw ht hRun (fun h => by rw [h] at hRun; cases hRun)

end
end PTX.Kernels.TmlFa4Fwd.Loader
