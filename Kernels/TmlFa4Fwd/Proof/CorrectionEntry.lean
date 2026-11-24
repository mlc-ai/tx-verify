-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Kernels.TmlFa4Fwd.Flow.Code.Part002
import Kernels.TmlFa4Fwd.Proof.RegisterHint

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Prologue

noncomputable section

/-- The 128 correction threads use their position within the four correction warps as a row. -/
def rowOf (l : Launch) (g : Nat) : Nat := (g % l.block) % 128

def creditLoc (l : Launch) (g : Nat) (stage : Fin 2) : Loc :=
  ⟨.shared, g / l.block, l.sharedBase + (96 + 8 * stage.val)⟩

def entryFacts (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(7277, b32 p.batch), (1072, b32 (g / l.block))] ++ nonzeroBarrierFacts p l g

def creditFacts (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(5868, b32 1), (1614, b32 (l.sharedBase + 96)), (1613, b32 (rowOf l g)),
    (1612, b32 (g % l.block))] ++ entryFacts p l g

def afterCreditFacts (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  (1615, b32 (l.sharedBase + 104)) :: creditFacts p l g

private theorem entryModel {l : Launch} {g : Nat} {t : TState} {pc : Nat} {ins : Instr}
    (hpc : t.pc = pc) (hLo : 7745 ≤ pc) (hHi : pc ≤ 7754)
    (hc : kernel.code[pc]? = some ins) (hi : Assumptions.coreOp ins.op = true) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  apply Assumptions.out_all_eq_nil _ _ _ (hpc.symm ▸ hc) hi
  all_goals
    rw [hpc]
    simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites, Assumptions.delayedTmemSites,
      List.mem_cons, List.not_mem_nil, or_false]
    omega

private theorem kernelName : kernel.name =
    "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_object_at__tenso\
    r000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf16gmemalign16o1i64div8_\
    0" := rfl

private theorem decimal19 : toString (19 : Nat) = "19" := by
  rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
  simp only [show (19 / 10 : Nat) = 1 by decide, show (19 % 10 : Nat) = 9 by decide,
    Nat.repr_of_lt (n := 1) (by decide), Nat.repr_of_lt (n := 9) (by decide),
    Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_nine.mpr rfl]
  rfl

variable {p : Params} {l : Launch} {m : Mem0}

set_option maxRecDepth 2000 in
/-- Read the batch parameter on the actual Correction entry path. -/
theorem entryBatch {g : Nat} {t : TState} (hp : Pre p l m)
    (ht : At t 7745 ((1072, b32 (g / l.block)) :: nonzeroBarrierFacts p l g)) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧ At u 7746 (entryFacts p l g) := by
  let u := next (setReg t 7277 (b32 p.batch))
  obtain ⟨hBound, hParam⟩ := hp.values (19, p.batch) (by simp [Params.scalarWords])
  have hName : param 19 =
      "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttention\
      ForwardSm100_object_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_\
      tensorptrbf16gmemalign16o1i64div8_0_param_19" := by
    unfold param
    rw [kernelName, decimal19]
    rfl
  have hCore : run kernel [] l g 1 t = some u := by
    apply run_local Flow.code_7745 rfl ht
    rw [execLocalA_nil, execLocal_mem rfl]
    change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at hParam
    rw [hName] at hParam
    simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq,
      DType.width, MemExt.extendBits_same, pure, Except.pure]
    rw [hParam]
    change Except.ok (next (setReg t 7277 (.bits 32 (truncBits 32 (BitVec.ofNat 64 p.batch))))) = _
    rw [truncBits_ofNat hBound (by decide)]
    rfl
  have hModel := entryModel (l := l) (g := g) ht.1 (by decide) (by decide) Flow.code_7745 rfl
  refine ⟨u, by simpa only [run, tauStep, hModel] using hCore, ht.set ?_⟩
  intro pair hPair
  have hpKey := List.mem_map_of_mem (f := Prod.fst) hPair
  change pair.1 ∈ [1072, 1062, 2535, 1063, 1064, 1065, 1066, 1067, 1068, 6495, 2390, 1069,
    1070, 6497, 1071, 1, 7492, 7493, 7494, 7495, 1663, 1664, 7496, 7497, 7498, 7499, 7500,
    7501, 7502, 7503, 7504, 7505, 7291, 7290, 7289, 7506, 7292, 7293, 7294, 7295, 1665] at hpKey
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpKey
  omega

/-- Decode the correction lane’s register relinquish request. -/
theorem entryHint {l : Launch} {g : Nat} {t : TState}
    (hp : t.pc = 7746) (hf : t.fault = none) :
    out kernel Assumptions.all l g t = .ev (.setMaxReg false 64 (next t)) := by
  rw [entryModel hp (by decide) (by decide) Flow.code_7746 rfl]
  unfold out
  rw [hp, hf, Flow.code_7746]
  rfl

/-- Decode the correction lane’s initial 416-thread rendezvous. -/
theorem entryBar {l : Launch} {g : Nat} {t : TState}
    (hp : t.pc = 7747) (hf : t.fault = none) (hb : l.block = 512) :
    out kernel Assumptions.all l g t = .ev (.bar 2 (next t) (some 416) .sync) := by
  rw [entryModel hp (by decide) (by decide) Flow.code_7747 rfl]
  unfold out
  rw [hp, hf, Flow.code_7747]
  change Out.ev (barTmpl l g t (.imm 2) (some (.imm 416))) = _
  simp [barTmpl, readBits, pure, Except.pure, hb, truncBits]

/-- An observed named barrier in the correction role passes the allocation entry,
or is the allocation entry itself. -/
theorem correctionEntryRendezvous {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j site id : Nat} {count : Option Nat}
    {mode : BarMode} (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12)
    (he : X.get (g,j) = some ⟨site, .bar id count mode⟩) (hSite : 173 < site) :
    ∃ t o inst, 6 ≤ j ∧ t.pc = 7748 ∧
      X.get (g,3) = some ⟨172, .fenceMbarInit⟩ ∧
      X.get (g,4) = some ⟨173, .bar 0 none .sync⟩ ∧
      X.get (g,5) = some ⟨7746, .setMaxReg false 64 inst⟩ ∧
      X.get (g,6) = some ⟨7747, .bar 2 (some 416) .sync⟩ ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 7) o := by
  have hg := event_thread_lt hX he
  have hLength : j < (X.tr g).length := len_of_get he
  have hMore (n : Nat) (hn : n ≤ j) : (X.tr g).drop n ≠ [] :=
    fun h => Nat.not_le_of_lt hLength ((List.drop_eq_nil_iff.mp h).trans hn)
  obtain ⟨s, o, hFive, hs, _, hr, hf, hCommon⟩ :=
    nonzeroCommonPrefixOfDemand hp hX hg (show 0 < warpIndex l g by omega) he (.inl hSite)
  let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
  have hAt : At s 174 [(1062, b32 warp.val), (2535, b32 l.sharedBase)] :=
    hs.mono ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1, trivial⟩
  obtain ⟨t, inst, hHint, ht, hSuffix⟩ :=
    firstRegisterHintFromCommon hp hg warp hAt hr (hMore 5 hFive)
  have hSite' : registerHintPc warp = 7746 := by
    unfold registerHintPc dispatchParamPc
    split_ifs <;> dsimp [warp] at * <;> omega
  have hForm : registerHintOf warp.val = (false,64) := by
    simp [registerHintOf, warp, Nat.not_lt_of_ge hLo, hHi]
  rw [hSite', hForm] at hHint
  rw [hSite'] at ht
  have hSix : 6 ≤ j := by
    by_contra! hj
    obtain rfl : j = 5 := by omega
    rw [he] at hHint
    cases hHint
  have hNext : Next kernel Assumptions.all l g t t (.bar 2 (next t) (some 416) .sync) :=
    ⟨.refl, entryBar ht.1 ht.2.2.2.1 hp.block⟩
  obtain ⟨_, _, hBar, ⟨rfl, hAfter⟩, hTail⟩ :=
    hNext.continuing_at_nonempty (by rintro _ ⟨_, h⟩; cases h) hSuffix (hMore 6 hSix)
  obtain rfl := Option.some.inj hAfter
  rw [ht.1] at hBar
  refine ⟨next t, o, inst, hSix, ?_, hf, hCommon, hHint, hBar, hTail⟩
  change t.pc + 1 = 7748
  rw [ht.1]

/-- Decode either initial statistics credit from the prepared state. -/
theorem creditTemplate {g : Nat} {t : TState} (hp : Pre p l m) (stage : Fin 2)
    (hpc : t.pc = 7752 + 2 * stage.val) (hf : t.fault = none)
    (hShared : t.regs 2535 = some (b32 l.sharedBase)) (hOne : t.regs 5868 = some (b32 1)) :
    out kernel Assumptions.all l g t =
      .ev (.arrive (creditLoc l g stage) 0
        (next (mbarStateDest t (some (8985 + stage.val)))) 1 true .cta) := by
  let off := 96 + 8 * stage.val
  have hLim := hp.shared.2.1
  have hAlign := hp.shared.1
  have hStage := stage.isLt
  have hAddr : l.sharedBase + off < 2 ^ 32 := by dsimp [off]; omega
  have hBase : l.sharedBase < 2 ^ 32 := by dsimp [off] at hAddr; omega
  have hEight : (l.sharedBase + off) % 8 = 0 := by dsimp [off]; omega
  have hSum : (truncBits 32 (truncBits 32 (BitVec.ofNat 64 l.sharedBase) +
      BitVec.ofNat 64 off)).toNat = l.sharedBase + off := by
    rw [truncBits_ofNat hBase (by decide), ← BitVec.ofNat_add, truncBits_ofNat hAddr (by decide),
      toNat_ofNat_lt (show l.sharedBase + off < 2 ^ 64 by omega)]
  have hLoc : mbarLoc l g t 2535 (off : Int) = .ok (creditLoc l g stage) := by
    simp only [mbarLoc, effAddr, sharedEffAddr, readReg, hShared, b32, readBits, bind, Except.bind,
      pure, Except.pure, BitVec.ofInt_natCast, hSum, hEight, creditLoc, ↓reduceIte]
    rfl
  have hCount : readBits l g t 32 (.reg 5868) = .ok (1 : BitVec 64) := by
    simp [readBits, readReg, hOne, b32, truncBits, bind, Except.bind, pure, Except.pure]
  fin_cases stage
  · have hpc' : t.pc = 7752 := hpc
    rw [entryModel hpc' (by decide) (by decide) Flow.code_7752 rfl]
    unfold out
    rw [hpc', hf, Flow.code_7752]
    change Out.ev (tmaTmpl l g t (.mbarArrive 2535 96 (.imm 0) (.reg 5868)
      false true .cta (some 8985))) = _
    simp only [tmaTmpl, show mbarLoc l g t 2535 96 = _ from hLoc, hCount, Bool.false_eq_true,
      ↓reduceIte, bind, Except.bind, pure, Except.pure, ofExec]
    rfl
  · have hpc' : t.pc = 7754 := hpc
    rw [entryModel hpc' (by decide) (by decide) Flow.code_7754 rfl]
    unfold out
    rw [hpc', hf, Flow.code_7754]
    change Out.ev (tmaTmpl l g t (.mbarArrive 2535 104 (.imm 0) (.reg 5868)
      false true .cta (some 8986))) = _
    simp only [tmaTmpl, show mbarLoc l g t 2535 104 = _ from hLoc, hCount, Bool.false_eq_true,
      ↓reduceIte, bind, Except.bind, pure, Except.pure, ofExec]
    rfl

private theorem entryFactsFresh {p : Params} {l : Launch} {g : Nat} {r : Nat}
    (hr : r ∈ [1612, 1613, 1614, 5868, 1615, 8985, 8986]) :
    ∀ pair ∈ entryFacts p l g, pair.1 ≠ r := by
  intro pair hp
  have hKey := List.mem_map_of_mem (f := Prod.fst) hp
  change pair.1 ∈ [7277, 1072, 1062, 2535, 1063, 1064, 1065, 1066, 1067, 1068, 6495, 2390,
    1069, 1070, 6497, 1071, 1, 7492, 7493, 7494, 7495, 1663, 1664, 7496, 7497, 7498,
    7499, 7500, 7501, 7502, 7503, 7504, 7505, 7291, 7290, 7289, 7506, 7292, 7293, 7294,
    7295, 1665] at hKey
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hKey
  omega

/-- The statistics registers can be written without changing the first credit frame. -/
theorem creditFactsFresh {p : Params} {l : Launch} {g : Nat} {r : Nat}
    (hr : r ∈ [1615, 8985, 8986]) : ∀ pair ∈ creditFacts p l g, pair.1 ≠ r := by
  intro pair hm
  have hr' : r ∈ [1612, 1613, 1614, 5868, 1615, 8985, 8986] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    omega
  simp only [creditFacts, List.cons_append, List.nil_append, List.mem_cons] at hm
  rcases hm with rfl | rfl | rfl | rfl | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; omega
  · exact entryFactsFresh hr' pair h

private theorem liftEntryStep {l : Launch} {g pc : Nat} {t u : TState} {ins : Instr}
    (hp : t.pc = pc) (hlo : 7745 ≤ pc) (hhi : pc ≤ 7754)
    (hc : kernel.code[pc]? = some ins) (hi : Assumptions.coreOp ins.op = true)
    (hr : run kernel [] l g 1 t = some u) :
    run kernel Assumptions.all l g 1 t = some u := by
  simpa only [run, tauStep, entryModel hp hlo hhi hc hi] using hr

/-- Prepare the first statistics credit and preserve the role ABI frame. -/
theorem prepareCredits {g : Nat} {t : TState} (hp : Pre p l m) (ht : At t 7748 (entryFacts p l g)) :
    ∃ u, run kernel Assumptions.all l g 4 t = some u ∧ At u 7752 (creditFacts p l g) := by
  let tid := g % l.block
  let t₁ := next (setReg t 1612 (b32 tid))
  let t₂ := next (setReg t₁ 1613 (b32 (rowOf l g)))
  let t₃ := next (setReg t₂ 1614 (b32 (l.sharedBase + 96)))
  let t₄ := next (setReg t₃ 5868 (b32 1))
  have hTid : tid < 2 ^ 32 := by
    have hlt := Nat.mod_lt g (by rw [hp.block]; decide : 0 < l.block)
    dsimp [tid]
    rw [hp.block] at hlt ⊢
    omega
  have ha₁ : At t₁ 7749 ((1612, b32 tid) :: entryFacts p l g) :=
    ht.set (entryFactsFresh (by decide))
  have ha₂ : At t₂ 7750 ((1613, b32 (rowOf l g)) :: (1612, b32 tid) :: entryFacts p l g) :=
    ha₁.set (by
      intro pair hm
      rcases List.mem_cons.mp hm with rfl | hm
      · dsimp only; decide
      · exact entryFactsFresh (by decide) pair hm)
  have ha₃ : At t₃ 7751 ((1614, b32 (l.sharedBase + 96)) :: (1613, b32 (rowOf l g)) ::
      (1612, b32 tid) :: entryFacts p l g) :=
    ha₂.set (by
      intro pair hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | rfl | hm
      · dsimp only; decide
      · dsimp only; decide
      · exact entryFactsFresh (by decide) pair hm)
  have ha₄ : At t₄ 7752 (creditFacts p l g) :=
    ha₃.set (by
      intro pair hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | rfl | rfl | hm
      · dsimp only; decide
      · dsimp only; decide
      · dsimp only; decide
      · exact entryFactsFresh (by decide) pair hm)
  have hs₁ : run kernel [] l g 1 t = some t₁ := by
    apply run_local Flow.code_7748 rfl ht
    rw [execLocalA_nil, execLocal_move rfl]
    have hReg := (sregValue_oneDim hp.cluster.2.2 g).1
    simp [execMove, readValue, readBits, SReg.width, hReg, DType.width, Value.bytes, t₁, b32, tid,
      bind, Except.bind, pure, Except.pure, truncBits_ofNat hTid (by decide)]
  have hs₂ : run kernel [] l g 1 t₁ = some t₂ := by
    apply run_local Flow.code_7749 rfl ha₁
    rw [execLocalA_nil, execLocal_int rfl]
    have hReg : t₁.regs 1612 = some (b32 tid) := rfl
    have hAnd : BitVec.ofNat 64 tid &&& 127 = BitVec.ofNat 64 (rowOf l g) := by
      apply BitVec.eq_of_toNat_eq
      have hTid64 : tid < 2 ^ 64 := by omega
      have hRow := Nat.mod_lt tid (by decide : 0 < 128)
      rw [BitVec.toNat_and, toNat_ofNat_lt hTid64, show (127 : BitVec 64).toNat = 127 by rfl,
        toNat_ofNat_lt (by unfold rowOf; change tid % 128 < 2 ^ 64; omega)]
      exact Nat.and_two_pow_sub_one_eq_mod tid 7
    simp only [execInt, DType.width, readBits, readReg, hReg, b32, bind, Except.bind,
      pure, Except.pure, truncBits_ofNat hTid (by decide)]
    change Except.ok (next (setReg t₁ 1613 (.bits 32
      (BitVec.ofNat 64 tid &&& 127)))) = .ok t₂
    rw [hAnd]
    rfl
  have hs₃ : run kernel [] l g 1 t₂ = some t₃ := by
    have hShared := holds_mem ha₂.2.2.2.2
      (by simp [entryFacts, nonzeroBarrierFacts] :
        (2535, b32 l.sharedBase) ∈ (1613, b32 (rowOf l g)) ::
          (1612, b32 tid) :: entryFacts p l g)
    have hBound : l.sharedBase + 96 < 2 ^ 32 := by have := hp.shared.2.1; omega
    have hs := evalSharedAdd (g := g) ha₂.1 ha₂.2.2.2.1 hShared hBound Flow.code_7750
    simp [run, hs, t₃]
  have hs₄ : run kernel [] l g 1 t₃ = some t₄ := by
    apply run_local Flow.code_7751 rfl ha₃
    rfl
  exact ⟨t₄, run_comp (run_comp (run_comp
    (liftEntryStep ht.1 (by decide) (by decide) Flow.code_7748 rfl hs₁)
    (liftEntryStep ha₁.1 (by decide) (by decide) Flow.code_7749 rfl hs₂))
    (liftEntryStep ha₂.1 (by decide) (by decide) Flow.code_7750 rfl hs₃))
    (liftEntryStep ha₃.1 (by decide) (by decide) Flow.code_7751 rfl hs₄), ha₄⟩

/-- Prepare the second statistics credit after the first one arrived. -/
theorem prepareSecondCredit {g : Nat} {t : TState} (hp : Pre p l m)
    (ht : At t 7753 (creditFacts p l g)) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧ At u 7754 (afterCreditFacts p l g) := by
  let u := next (setReg t 1615 (b32 (l.sharedBase + 104)))
  have hBase := holds_lookup ht.2.2.2.2
    (show (creditFacts p l g).lookup 2535 = some (b32 l.sharedBase) from rfl)
  have hBound : l.sharedBase + 104 < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hStep := evalSharedAdd (g := g) ht.1 ht.2.2.2.1 hBase hBound Flow.code_7753
  have hCore : run kernel [] l g 1 t = some u := by simp [run, hStep, u]
  exact ⟨u, liftEntryStep ht.1 (by decide) (by decide) Flow.code_7753 rfl hCore,
    ht.set (creditFactsFresh (by decide))⟩

private theorem observeCredit {X : Execution} (hp : Pre p l m) {g pos : Nat} {before t : TState}
    {o : Option TState} {F : List (Nat × Value)} (stage : Fin 2)
    (ht : At t (7752 + 2 * stage.val) F) (hShared : (2535, b32 l.sharedBase) ∈ F)
    (hOne : (5868, b32 1) ∈ F) (hFresh : ∀ pair ∈ F, pair.1 ≠ 8985 + stage.val)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before t)
    (hRun : Run kernel Assumptions.all l g before ((X.tr g).drop pos) o)
    (hSuffix : (X.tr g).drop pos ≠ []) :
    ∃ u, X.get (g, pos) = some ⟨7752 + 2 * stage.val, .arrive (creditLoc l g stage) 0 1
          true .cta⟩ ∧
      At u (7752 + 2 * stage.val + 1) F ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) o := by
  let u := next (mbarStateDest t (some (8985 + stage.val)))
  have hNext : Next kernel Assumptions.all l g before t
      (.arrive (creditLoc l g stage) 0 u 1 true .cta) :=
    ⟨hLocal, creditTemplate hp stage ht.1 ht.2.2.2.1
      (holds_mem ht.2.2.2.2 hShared) (holds_mem ht.2.2.2.2 hOne)⟩
  obtain ⟨e, v, he, hFire, hTail⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨_, h⟩; cases h) hRun hSuffix
  obtain ⟨rfl, hv⟩ := hFire
  obtain rfl := Option.some.inj hv
  rw [ht.1] at he
  exact ⟨u, he, ⟨congrArg (· + 1) ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1,
    holds_update ht.2.2.2.2 hFresh⟩, hTail⟩

/-- The actual correction trace makes its register request, joins the 416-thread rendezvous,
and releases both initial stage credits before its first scheduler instruction. -/
theorem correctionEntry {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X) {g : Nat}
    (hg : g < l.threads) (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12) :
    ∃ t inst, At t 7755 (afterCreditFacts p l g) ∧
      X.get (g, 5) = some ⟨7746, .setMaxReg false 64 inst⟩ ∧
      X.get (g, 6) = some ⟨7747, .bar 2 (some 416) .sync⟩ ∧
      X.get (g, 7) = some ⟨7752, .arrive (creditLoc l g 0) 0 1 true .cta⟩ ∧
      X.get (g, 8) = some ⟨7754, .arrive (creditLoc l g 1) 0 1 true .cta⟩ ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 9) none := by
  obtain ⟨t, ht, hRun⟩ := nonzeroRoleEntry hp hX hComplete hg (by omega)
  have hPc : dispatchParamPc ⟨warpIndex l g, warpIndex_lt hp g⟩ = 7745 := by
    simp only [dispatchParamPc]
    split_ifs <;> omega
  rw [hPc] at ht
  obtain ⟨u, hLocal, hu⟩ := entryBatch hp ht
  have hHint : Next kernel Assumptions.all l g t u (.setMaxReg false 64 (next u)) :=
    ⟨run_rtg hLocal, entryHint hu.1 hu.2.2.2.1⟩
  obtain ⟨e, v, he, hFire, hTail⟩ := hHint.continuing_at (pos := 5) (by
    rintro e ⟨_, _, h⟩; cases h) hRun
  obtain ⟨inst, rfl, hv⟩ := hFire
  obtain rfl := Option.some.inj hv
  rw [hu.1] at he
  have hvPc : (next u).pc = 7747 := congrArg (· + 1) hu.1
  have hBar : Next kernel Assumptions.all l g (next u) (next u)
      (.bar 2 (next (next u)) (some 416) .sync) :=
    ⟨.refl, entryBar hvPc hu.2.2.2.1 hp.block⟩
  obtain ⟨event, w, hGet, hFire, hRun⟩ := hBar.continuing_at (pos := 6) (by
    rintro e ⟨_, h⟩; cases h) hTail
  obtain ⟨rfl, hw⟩ := hFire
  obtain rfl := Option.some.inj hw
  rw [hvPc] at hGet
  have hStart : At (next (next u)) 7748 (entryFacts p l g) :=
    ⟨congrArg (· + 1) hvPc, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2⟩
  obtain ⟨s, hs, hS⟩ := prepareCredits hp hStart
  obtain ⟨s', hGet₀, hs', hRun₀⟩ := observeCredit hp (pos := 7) 0 hS
    (by simp [creditFacts, entryFacts, nonzeroBarrierFacts]) (by simp [creditFacts])
    (creditFactsFresh (by decide)) (run_rtg hs) hRun (by intro h; rw [h] at hRun; cases hRun)
  obtain ⟨q, hq, hQ⟩ := prepareSecondCredit hp hs'
  obtain ⟨q', hGet₁, hq', hRun₁⟩ := observeCredit hp (pos := 8) 1 hQ
    (by simp [afterCreditFacts, creditFacts, entryFacts, nonzeroBarrierFacts])
    (by simp [afterCreditFacts, creditFacts])
    (by
      intro pair hm
      rcases List.mem_cons.mp hm with rfl | hm
      · dsimp only; decide
      · exact creditFactsFresh (by decide) pair hm)
    (run_rtg hq) hRun₀ (by intro h; rw [h] at hRun₀; cases hRun₀)
  exact ⟨q', inst, hq', he, hGet, hGet₀, hGet₁, hRun₁⟩

private theorem correctionCommonBeforeEvent {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {target : Event} (hg : g < l.threads)
    (hW : 0 < warpIndex l g) (hTarget : X.get (g, j) = some target)
    (hDemand : 7754 < target.pc ∨ target.kind = .exit ∨ 3 ≤ j ∧ Execution.isShfl target = true) :
    5 ≤ j ∧ X.get (g, 3) = some ⟨172, .fenceMbarInit⟩ ∧
      X.get (g, 4) = some ⟨173, .bar 0 none .sync⟩ := by
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hTarget).1
  have hDiff {pos : Nat} {e : Event} (hPc : e.pc ≤ 7754) (hKind : e.kind ≠ .exit)
      (hShfl : pos < 3 ∨ Execution.isShfl e = false) (hEq : pos = j) : e ≠ target := by
    rintro rfl
    rcases hDemand with hl | he | ⟨hj, hs⟩
    · omega
    · exact hKind he
    · rcases hShfl with hEarly | hNo
      · omega
      · exact Bool.noConfusion (hNo.symm.trans hs)
  have advanceIndex {pos : Nat} {e : Event} (he : X.get (g, pos) = some e) (hJ : pos ≤ j)
      (hPc : e.pc ≤ 7754) (hKind : e.kind ≠ .exit)
      (hShfl : pos < 3 ∨ Execution.isShfl e = false) : pos + 1 ≤ j := by
    by_cases hEq : pos = j
    · exact by
        subst j
        exact (hDiff hPc hKind hShfl rfl (Option.some.inj (he.symm.trans hTarget))).elim
    · omega
  have h₀ : 0 < (X.tr g).length := by omega
  let e₀ := (X.tr g)[0]
  have he₀ : X.get (g, 0) = some e₀ := List.getElem?_eq_getElem h₀
  have hj₁ : 1 ≤ j := by
    have he := firstSharedValue hp hX g hg he₀
    exact advanceIndex he₀ (Nat.zero_le j) (by rw [he]; exact (by decide : 25 ≤ 7754))
      (by rw [he]; intro h; cases h) (.inl (by decide))
  have h₁ : 1 < (X.tr g).length := by omega
  let e₁ := (X.tr g)[1]
  have he₁ : X.get (g, 1) = some e₁ := List.getElem?_eq_getElem h₁
  have hj₂ : 2 ≤ j := by
    have he := secondWarpValue hp hX g hg he₁
    exact advanceIndex he₁ hj₁ (by rw [he]; exact (by decide : 34 ≤ 7754))
      (by rw [he]; intro h; cases h) (.inl (by decide))
  have h₂ : 2 < (X.tr g).length := by omega
  let e₂ := (X.tr g)[2]
  have he₂ : X.get (g, 2) = some e₂ := List.getElem?_eq_getElem h₂
  have hj₃ : 3 ≤ j := by
    have he := thirdWarpValue hp hX g hg he₂
    exact advanceIndex he₂ hj₂ (by rw [he]; exact (by decide : 35 ≤ 7754))
      (by rw [he]; intro h; cases h) (.inl (by decide))
  have hPrefix : X.tr g = e₀ :: e₁ :: e₂ :: (X.tr g).drop 3 := by
    have h0 := List.drop_eq_getElem_cons h₀
    have h1 := List.drop_eq_getElem_cons h₁
    have h2 := List.drop_eq_getElem_cons h₂
    rw [h2] at h1
    rw [h1] at h0
    exact h0
  obtain ⟨t, o, ht, hf, hBase, hWarp, _, _, _, hRun⟩ := broadcastPrefix hp hX g hg hPrefix
  have nonempty {pos : Nat} (hpos : pos ≤ j) : (X.tr g).drop pos ≠ [] :=
    fun h => (Nat.not_lt_of_ge ((List.drop_eq_nil_iff.mp h).trans hpos)) hLen
  obtain ⟨u, hLocal, hu, huf, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hFrame⟩ :=
    nonzeroWarpWith (A := Assumptions.all) hp g (warpIndex l g) t
      (by omega) (warpIndex_lt hp g) ht hf hWarp hBase
  have hFenceBase : out kernel [] l g u = .ev (.fenceMbarInit (next u)) := by
    unfold out
    rw [hu, huf, Flow.code_172]
    rfl
  have hFence : Next kernel Assumptions.all l g t u (.fenceMbarInit (next u)) :=
    ⟨run_rtg hLocal, startupOut (.inl (by rw [hu]; decide)) hFenceBase⟩
  obtain ⟨e₃, u', he₃, hf₃, hRun₃⟩ := hFence.continuing_at_nonempty (by
    rintro e ⟨_, hBad⟩
    cases hBad) hRun (nonempty hj₃)
  obtain ⟨rfl, hEq⟩ := hf₃
  have hj₄ : 4 ≤ j := advanceIndex he₃ hj₃
    (by change u.pc ≤ 7754; rw [hu]; decide) (by intro h; cases h) (.inr rfl)
  obtain rfl := Option.some.inj hEq
  have hu' : (next u).pc = 173 := by change u.pc + 1 = 173; rw [hu]
  have hBarBase : out kernel [] l g (next u) = .ev (.bar 0 (next (next u)) none .sync) := by
    unfold out
    have hClean : (next u).fault = none := huf
    rw [hu', hClean, Flow.code_173]
    rfl
  have hBar : Next kernel Assumptions.all l g (next u) (next u)
      (.bar 0 (next (next u)) none .sync) :=
    ⟨.refl, startupOut (.inl (by rw [hu']; decide)) hBarBase⟩
  obtain ⟨e₄, u'', he₄, hf₄, hRun₄⟩ := hBar.continuing_at_nonempty (pos := 4) (by
    rintro e ⟨_, hBad⟩
    cases hBad) hRun₃ (nonempty hj₄)
  obtain ⟨rfl, hEq⟩ := hf₄
  have hj₅ : 5 ≤ j := advanceIndex he₄ hj₄
    (by change (next u).pc ≤ 7754; rw [hu']; decide) (by intro h; cases h) (.inr rfl)
  exact ⟨hj₅, by simpa only [hu] using he₃, by simpa only [hu'] using he₄⟩


/-- Any observed later event, exit, or fourth shuffle on a correction lane requires the
ordinary events in the role's actual entry first. -/
theorem correctionEntryBeforeEvent {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {target : Event} (hg : g < l.threads)
    (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12) (hTarget : X.get (g, j) = some target)
    (hDemand : 7754 < target.pc ∨ target.kind = .exit ∨ 3 ≤ j ∧ Execution.isShfl target = true) :
    ∃ t o inst, At t 7755 (afterCreditFacts p l g) ∧
      X.get (g, 3) = some ⟨172, .fenceMbarInit⟩ ∧
      X.get (g, 4) = some ⟨173, .bar 0 none .sync⟩ ∧
      X.get (g, 5) = some ⟨7746, .setMaxReg false 64 inst⟩ ∧
      X.get (g, 6) = some ⟨7747, .bar 2 (some 416) .sync⟩ ∧
      X.get (g, 7) = some ⟨7752, .arrive (creditLoc l g 0) 0 1 true .cta⟩ ∧
      X.get (g, 8) = some ⟨7754, .arrive (creditLoc l g 1) 0 1 true .cta⟩ ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 9) o ∧ 9 ≤ j := by
  obtain ⟨h5, hFence, hBar0⟩ := correctionCommonBeforeEvent hp hX hg (by omega) hTarget hDemand
  have hLength : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hTarget).1
  have nonempty {n : Nat} (hN : n ≤ j) : (X.tr g).drop n ≠ [] := by
    intro hn
    exact Nat.not_le_of_lt hLength ((List.drop_eq_nil_iff.mp hn).trans hN)
  have later {n : Nat} {event : Event} (hn : n ≤ j) (he : X.get (g, n) = some event)
      (hc : event.pc ≤ 7754) (hx : event.kind ≠ .exit)
      (hs : Execution.isShfl event = false) : n + 1 ≤ j := by
    by_cases hEq : n = j
    · subst j
      obtain rfl := Option.some.inj (he.symm.trans hTarget)
      rcases hDemand with h | h | ⟨_, h⟩
      · omega
      · exact (hx h).elim
      · exact Bool.noConfusion (hs.symm.trans h)
    · omega
  obtain ⟨t, o, ht, hRun⟩ := nonzeroRoleEntryPrefix hp hX hg (by omega) (by omega)
  have hPc : dispatchParamPc ⟨warpIndex l g, warpIndex_lt hp g⟩ = 7745 := by
    simp only [dispatchParamPc]
    split_ifs <;> omega
  rw [hPc] at ht
  obtain ⟨u, hLocal, hu⟩ := entryBatch hp ht
  have hHint : Next kernel Assumptions.all l g t u (.setMaxReg false 64 (next u)) :=
    ⟨run_rtg hLocal, entryHint hu.1 hu.2.2.2.1⟩
  obtain ⟨e, v, he, hFire, hTail⟩ := hHint.continuing_at_nonempty (pos := 5) (by
    rintro e ⟨_, _, h⟩; cases h) hRun (nonempty h5)
  obtain ⟨inst, rfl, hv⟩ := hFire
  obtain rfl := Option.some.inj hv
  rw [hu.1] at he
  have h6 := later h5 he (by change 7746 ≤ 7754; decide) (by intro he; cases he) rfl
  have hvPc : (next u).pc = 7747 := congrArg (· + 1) hu.1
  have hBar : Next kernel Assumptions.all l g (next u) (next u)
      (.bar 2 (next (next u)) (some 416) .sync) :=
    ⟨.refl, entryBar hvPc hu.2.2.2.1 hp.block⟩
  obtain ⟨event, w, hGet, hFire, hRun⟩ := hBar.continuing_at_nonempty (pos := 6) (by
    rintro e ⟨_, h⟩; cases h) hTail (nonempty h6)
  obtain ⟨rfl, hw⟩ := hFire
  obtain rfl := Option.some.inj hw
  rw [hvPc] at hGet
  have h7 := later h6 hGet (by change 7747 ≤ 7754; decide) (by intro he; cases he) rfl
  have hStart : At (next (next u)) 7748 (entryFacts p l g) :=
    ⟨congrArg (· + 1) hvPc, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2⟩
  obtain ⟨s, hs, hS⟩ := prepareCredits hp hStart
  obtain ⟨s', hGet₀, hs', hRun₀⟩ := observeCredit hp (pos := 7) 0 hS
    (by simp [creditFacts, entryFacts, nonzeroBarrierFacts]) (by simp [creditFacts])
    (creditFactsFresh (by decide)) (run_rtg hs) hRun (nonempty h7)
  have h8 := later h7 hGet₀ (by change 7752 ≤ 7754; decide) (by intro he; cases he) rfl
  obtain ⟨q, hq, hQ⟩ := prepareSecondCredit hp hs'
  obtain ⟨q', hGet₁, hq', hRun₁⟩ := observeCredit hp (pos := 8) 1 hQ
    (by simp [afterCreditFacts, creditFacts, entryFacts, nonzeroBarrierFacts])
    (by simp [afterCreditFacts, creditFacts])
    (by
      intro pair hm
      rcases List.mem_cons.mp hm with rfl | hm
      · dsimp only; decide
      · exact creditFactsFresh (by decide) pair hm)
    (run_rtg hq) hRun₀ (nonempty h8)
  have h9 := later h8 hGet₁ (by change 7754 ≤ 7754; decide) (by intro he; cases he) rfl
  exact ⟨q', o, inst, hq', hFence, hBar0, he, hGet, hGet₀, hGet₁, hRun₁, h9⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
