-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxTmem
public import Kernels.TmlFa4Fwd.Flow.Code.Part075
public import Kernels.TmlFa4Fwd.Flow.Code.Part101
public import Kernels.TmlFa4Fwd.Flow.Code.Part102
public import Kernels.TmlFa4Fwd.Flow.Code.Part115
public import Kernels.TmlFa4Fwd.Flow.Code.Part116

public import Lemmas.Flow.TraceReach

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

def probabilityPc (round : Round) (quarter : Fin 4) : Nat :=
  match round with
  | .first => (#v[4826, 4835, 4844, 4856] : Vector Nat 4)[quarter]
  | .biased => (#v[6508, 6517, 6526, 6541] : Vector Nat 4)[quarter]
  | .unbiased => (#v[7416, 7425, 7434, 7446] : Vector Nat 4)[quarter]

def probabilityReg (round : Round) (quarter : Fin 4) : Nat :=
  match round with
  | .first => (#v[3223, 3226, 3225, 3224] : Vector Nat 4)[quarter]
  | .biased => (#v[4821, 4824, 4823, 4822] : Vector Nat 4)[quarter]
  | .unbiased => (#v[5183, 5185, 5181, 5184] : Vector Nat 4)[quarter]

theorem probabilityCode (round : Round) (quarter : Fin 4) :
    ∃ ss : List Opnd, ss.length = 16 ∧
      kernel.code[probabilityPc round quarter]? =
        some ⟨none, .tcSt (probabilityReg round quarter) ss .s32x32b⟩ := by
  cases round <;> fin_cases quarter
  · exact ⟨_, rfl, Flow.code_4826⟩
  · exact ⟨_, rfl, Flow.code_4835⟩
  · exact ⟨_, rfl, Flow.code_4844⟩
  · exact ⟨_, rfl, Flow.code_4856⟩
  · exact ⟨_, rfl, Flow.code_6508⟩
  · exact ⟨_, rfl, Flow.code_6517⟩
  · exact ⟨_, rfl, Flow.code_6526⟩
  · exact ⟨_, rfl, Flow.code_6541⟩
  · exact ⟨_, rfl, Flow.code_7416⟩
  · exact ⟨_, rfl, Flow.code_7425⟩
  · exact ⟨_, rfl, Flow.code_7434⟩
  · exact ⟨_, rfl, Flow.code_7446⟩

def delayedProbability (round : Round) (quarter : Fin 4) : Bool :=
  round != .unbiased && quarter == 0

theorem probabilityWaitHook (round : Round) (quarter : Fin 4) :
    Assumptions.all.any (·.tcStWaitLd (probabilityPc round quarter)) =
      delayedProbability round quarter := by
  rw [Assumptions.all_tcStWaitLd]
  cases round <;> fin_cases quarter <;> rfl

def probabilityAddress (l : Launch) (g : Nat) (stage : Fin 2) (quarter : Fin 4) : Nat :=
  2 ^ 16 * laneBase l g + (probabilityColumn stage + 16 * quarter.val)

private theorem probabilityBound (stage : Fin 2) (quarter : Fin 4) :
    probabilityColumn stage + 16 * quarter.val < 512 := by
  have := scoreColumn_range stage
  have := quarter.isLt
  unfold probabilityColumn
  omega

private theorem probabilityCore {l : Launch} {g : Nat} {t : TState} {a : Nat} {ss : List Opnd}
    {vals : List Value} (stage : Fin 2) (quarter : Fin 4) (hBlock : l.block % 32 = 0)
    (hAddr : t.regs a = some (b32 (probabilityAddress l g stage quarter))) (hLen : ss.length = 16)
    (hVals : ss.mapM (readValue l g t 32) = .ok vals) (hBytes : vals.all (·.bytes = 4) = true) :
    tcTmpl l g t (.tcSt a ss .s32x32b) =
      .tc (.st (probabilityAddress l g stage quarter) vals .s32x32b) (next t) := by
  have hAddr32 : probabilityAddress l g stage quarter < 2 ^ 32 :=
    tmem_warp_encoding_lt l g (probabilityBound stage quarter)
  have hAddr64 : probabilityAddress l g stage quarter < 2 ^ 64 := by omega
  have hOk : tcDataAddressOk l g .s32x32b (probabilityAddress l g stage quarter) = true :=
    tcDataAddressOk_warp32 l g (probabilityBound stage quarter)
  have hCount : TcShape.countOk .s32x32b ss.length = true := by rw [hLen]; decide
  simp [tcTmpl, ofExec, hBlock, hCount, readBits_b32 hAddr hAddr32, toNat_ofNat_lt hAddr64,
    hOk, hVals, hBytes, bind, Except.bind, pure, Except.pure]

private theorem takeTc {l : Launch} {g i : Nat} {X : Execution} {t u : TState} {kind : TcKind}
    (ho : out kernel Assumptions.all l g t = .ev (.tc kind u))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    X.get (g, i) = some ⟨t.pc, .tc kind⟩ ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1)) none := by
  have hn : Next kernel Assumptions.all l g t t (.tc kind u) := ⟨.refl, ho⟩
  obtain ⟨e, v, hGet, ⟨rfl, hV⟩, hRest⟩ := hn.continuing_at (by
    rintro _ ⟨_, hBad⟩
    cases hBad) hr
  obtain rfl := Option.some.inj hV
  exact ⟨hGet, hRest⟩

private theorem takeTcInPrefix {l : Launch} {g i : Nat} {X : Execution}
    {t u : TState} {kind : TcKind} {ending : Option TState}
    (ho : out kernel Assumptions.all l g t = .ev (.tc kind u))
    (hi : i < (X.tr g).length)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending) :
    X.get (g, i) = some ⟨t.pc, .tc kind⟩ ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1)) ending := by
  rw [List.drop_eq_getElem_cons hi] at hr
  have hn : Next kernel Assumptions.all l g t t (.tc kind u) := ⟨.refl, ho⟩
  obtain ⟨v,⟨hGet,hV⟩,hRest⟩ := hn.continuing_event (by
    rintro ⟨_, hBad⟩
    cases hBad) hr
  obtain rfl := Option.some.inj hV
  exact ⟨by
    change (X.tr g)[i]? = _
    rw [List.getElem?_eq_getElem hi,hGet],hRest⟩

/-- A recorded event is the singleton slice beginning at its index. -/
theorem probabilityEventSingleton {X : Execution} {g j : Nat} {e : Event}
    (he : X.get (g,j) = some e) : ((X.tr g).drop j).take 1 = [e] := by
  rw [List.take_one,List.head?_drop]
  change (X.get (g,j)).toList = [e]
  rw [he]
  rfl

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (round : Round)
    (quarter : Fin 4) (stage : Fin 2) {g i : Nat} {t : TState} {ss : List Opnd} {vals : List Value}
    {ending : Option TState} (hpc : t.pc = probabilityPc round quarter) (hf : t.fault = none)
    (hs : t.sub = 0)
    (hc : kernel.code[probabilityPc round quarter]? =
      some ⟨none, .tcSt (probabilityReg round quarter) ss .s32x32b⟩)
    (hAddr : t.regs (probabilityReg round quarter) =
      some (b32 (probabilityAddress l g stage quarter)))
    (hVals : ss.mapM (readValue l g t 32) = .ok vals) (hBytes : vals.all (·.bytes = 4) = true)
include hp round quarter stage hpc hf hs hc hAddr hVals hBytes

/-- The actual packed probability store. At the first P store of a biased round, the earlier
score loads finish through the modeled same-PC wait before the store issues. -/
theorem probabilityTraceWithPath (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hPresent : ending = none ∨
      (if delayedProbability round quarter then i+1 else i) < (X.tr g).length) :
    let j := if delayedProbability round quarter then i + 1 else i
    (delayedProbability round quarter = true → X.get (g, i) = some ⟨t.pc, .tc .waitLd⟩) ∧
      X.get (g, j) = some ⟨t.pc, .tc (.st (probabilityAddress l g stage quarter) vals .s32x32b)⟩ ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (j + 1)) ending ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop i).take (j+1-i)) (next t) := by
  have stepRecorded {index : Nat} {a b : TState} {kind : TcKind}
      (hOut : out kernel Assumptions.all l g a = .ev (.tc kind b))
      (hAvail : ending = none ∨ index < (X.tr g).length)
      (hr : Run kernel Assumptions.all l g a ((X.tr g).drop index) ending) :
      X.get (g,index) = some ⟨a.pc,.tc kind⟩ ∧
      Run kernel Assumptions.all l g b ((X.tr g).drop (index+1)) ending ∧
      TraceReach kernel Assumptions.all l g a (((X.tr g).drop index).take 1) b := by
    have hNext := hAvail.elim (fun e => e ▸ takeTc hOut (e ▸ hr))
      (fun hi => takeTcInPrefix hOut hi hr)
    refine ⟨hNext.1,hNext.2,?_⟩
    rw [probabilityEventSingleton hNext.1]
    exact .event ⟨_,hOut,rfl,rfl⟩ (.refl _)
  obtain ⟨src, hLen, hCode⟩ := probabilityCode round quarter
  rw [hc] at hCode
  cases hCode
  rw [← hpc] at hc
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hHook : Assumptions.all.any (·.tcStWaitLd t.pc) = delayedProbability round quarter := by
    rw [hpc, probabilityWaitHook]
  have hCore := probabilityCore stage quarter hBlock hAddr hLen hVals hBytes
  cases hDelayed : delayedProbability round quarter with
  | false =>
    simp only [hDelayed,Bool.false_eq_true,ite_false] at hPresent
    simp only [Bool.false_eq_true,ite_false]
    have ho : out kernel Assumptions.all l g t =
        .ev (.tc (.st (probabilityAddress l g stage quarter) vals .s32x32b) (next t)) := by
      rw [out_event hf hc rfl rfl, eventTmpl_tcSt_noWait (hHook.trans hDelayed), hCore]
    refine ⟨False.elim,?_⟩
    simpa only [Nat.add_sub_cancel_left] using stepRecorded ho hPresent hRun
  | true =>
    simp only [hDelayed,ite_true] at hPresent
    simp only [ite_true]
    let u := {t with sub := 1}
    have hWait : out kernel Assumptions.all l g t = .ev (.tc .waitLd u) := by
      rw [out_event hf hc rfl rfl, eventTmpl_tcSt_wait (hHook.trans hDelayed) hs hBlock]
    obtain ⟨hWaitEvent,hRest,hWaitPath⟩ := stepRecorded hWait
      (hPresent.imp_right (fun hi => by omega)) hRun
    have hReset : {u with sub := 0} = t := by cases t; simp_all [u]
    have hStore : out kernel Assumptions.all l g u =
        .ev (.tc (.st (probabilityAddress l g stage quarter) vals .s32x32b) (next t)) := by
      have hu : Assumptions.all.any (·.tcStWaitLd u.pc) = true := hHook.trans hDelayed
      rw [out_event (t := u) hf hc rfl rfl, eventTmpl_tcSt_afterWait hu Nat.one_ne_zero,
        hReset, hCore]
    obtain ⟨he,hAfter,hStorePath⟩ := stepRecorded hStore hPresent hRest
    refine ⟨(fun _ => hWaitEvent),he,hAfter,?_⟩
    rw [show i+1+1-i = 1+1 by omega,List.take_add,List.drop_drop]
    exact hWaitPath.append hStorePath


omit hp round quarter stage hpc hf hs hc hAddr hVals hBytes in
/-- The actual packed probability store. At the first P store of a biased round, the earlier
score loads finish through the modeled same-PC wait before the store issues. -/
theorem probabilityTrace {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (round : Round) (quarter : Fin 4) (stage : Fin 2)
    {g i : Nat} {t : TState} {ss : List Opnd} {vals : List Value}
    (hpc : t.pc = probabilityPc round quarter) (hf : t.fault = none) (hs : t.sub = 0)
    (hc : kernel.code[probabilityPc round quarter]? =
      some ⟨none, .tcSt (probabilityReg round quarter) ss .s32x32b⟩)
    (hAddr : t.regs (probabilityReg round quarter) =
      some (b32 (probabilityAddress l g stage quarter)))
    (hVals : ss.mapM (readValue l g t 32) = .ok vals) (hBytes : vals.all (·.bytes = 4) = true)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    let j := if delayedProbability round quarter then i + 1 else i
    (delayedProbability round quarter = true → X.get (g, i) = some ⟨t.pc, .tc .waitLd⟩) ∧
      X.get (g, j) = some ⟨t.pc, .tc (.st (probabilityAddress l g stage quarter) vals .s32x32b)⟩ ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (j + 1)) none := by
  obtain ⟨hWait,hStore,hTail,_⟩ := probabilityTraceWithPath hp round quarter stage
    hpc hf hs hc hAddr hVals hBytes hRun (.inl rfl)
  exact ⟨hWait,hStore,hTail⟩

/-- The actual packed probability store. At the first P store of a biased round, the earlier
score loads finish through the modeled same-PC wait before the store issues. -/
theorem probabilityTraceInPrefix (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hi : (if delayedProbability round quarter then i+1 else i) < (X.tr g).length) :
    let j := if delayedProbability round quarter then i + 1 else i
    (delayedProbability round quarter = true → X.get (g, i) = some ⟨t.pc, .tc .waitLd⟩) ∧
      X.get (g, j) = some ⟨t.pc, .tc (.st (probabilityAddress l g stage quarter) vals .s32x32b)⟩ ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (j + 1)) ending := by
  obtain ⟨hWait,hStore,hTail,_⟩ := probabilityTraceWithPath hp round quarter stage
    hpc hf hs hc hAddr hVals hBytes hRun (.inr hi)
  exact ⟨hWait,hStore,hTail⟩
end

def probabilityWaitPc (round : Round) (final : Bool) : Nat :=
  match round, final with
  | .first, false => 4845
  | .first, true => 4857
  | .biased, false => 6527
  | .biased, true => 6542
  | .unbiased, false => 7435
  | .unbiased, true => 7447

private theorem probabilityWaitCode (round : Round) (final : Bool) :
    kernel.code[probabilityWaitPc round final]? = some ⟨none, .tcWaitSt⟩ := by
  cases round <;> cases final
  · exact Flow.code_4845
  · exact Flow.code_4857
  · exact Flow.code_6527
  · exact Flow.code_6542
  · exact Flow.code_7435
  · exact Flow.code_7447

variable {p : Params} {l : Launch}

/-- Decoded probability store with the delayed load wait already reflected in its substate. -/
theorem probabilityStoreTemplate {m : Mem0} (hp : Pre p l m) (round : Round) (quarter : Fin 4)
    (stage : Fin 2) {g : Nat} {t : TState} {ss : List Opnd} {vals : List Value}
    (hpc : t.pc = probabilityPc round quarter) (hf : t.fault = none)
    (hSub : t.sub = if delayedProbability round quarter then 1 else 0)
    (hc : kernel.code[probabilityPc round quarter]? =
      some ⟨none,.tcSt (probabilityReg round quarter) ss .s32x32b⟩)
    (hAddr : t.regs (probabilityReg round quarter) =
      some (b32 (probabilityAddress l g stage quarter)))
    (hVals : ss.mapM (readValue l g t 32) = .ok vals) (hBytes : vals.all (·.bytes = 4) = true) :
    out kernel Assumptions.all l g t =
    .ev (.tc (.st (probabilityAddress l g stage quarter) vals .s32x32b)
      (next {t with sub := 0})) := by
  obtain ⟨src,hLen,hCode⟩ := probabilityCode round quarter
  rw [hc] at hCode
  cases hCode
  rw [← hpc] at hc
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hHook : Assumptions.all.any (·.tcStWaitLd t.pc) = delayedProbability round quarter := by
    rw [hpc,probabilityWaitHook]
  cases hDelayed : delayedProbability round quarter with
  | false =>
    have hCore := probabilityCore stage quarter hBlock hAddr hLen hVals hBytes
    have hs : t.sub = 0 := by simpa [hDelayed] using hSub
    have hZero : {t with sub := 0} = t := by cases t; simp_all
    rw [hZero,out_event hf hc rfl rfl,eventTmpl_tcSt_noWait (hHook.trans hDelayed),hCore]
  | true =>
    let u := {t with sub := 0}
    have hCore : tcTmpl l g u (.tcSt (probabilityReg round quarter) ss .s32x32b) =
        .tc (.st (probabilityAddress l g stage quarter) vals .s32x32b) (next u) :=
      probabilityCore stage quarter hBlock hAddr hLen hVals hBytes
    have hs : t.sub ≠ 0 := by simp [hDelayed] at hSub; omega
    rw [out_event hf hc rfl rfl,eventTmpl_tcSt_afterWait (hHook.trans hDelayed) hs,hCore]

/-- The final probability wait returns the actual lane with the program counter advanced. -/
theorem probabilityWaitTemplate {m : Mem0} (hp : Pre p l m) (round : Round) (final : Bool) {g : Nat}
    {t : TState} (hpc : t.pc = probabilityWaitPc round final) (hf : t.fault = none) :
    out kernel Assumptions.all l g t = .ev (.tc .waitSt (next t)) := by
  have hc := probabilityWaitCode round final
  rw [← hpc] at hc
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  rw [out_event hf hc rfl rfl]
  simp [eventTmpl,tcTmpl,ofExec,hBlock,pure,Except.pure]

/-- Each P publication follows the matching actual TMEM store wait. -/
theorem probabilityWaitTrace {m : Mem0} {X : Execution} (hp : Pre p l m) (round : Round)
    (final : Bool) {g i : Nat} {t : TState} (hpc : t.pc = probabilityWaitPc round final)
    (hf : t.fault = none) (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    X.get (g, i) = some ⟨probabilityWaitPc round final, .tc .waitSt⟩ ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (i + 1)) none := by
  simpa only [hpc] using takeTc (probabilityWaitTemplate hp round final hpc hf) hRun

theorem probabilityWaitInPrefix {m : Mem0} {X : Execution} (hp : Pre p l m) (round : Round)
    (final : Bool) {g i : Nat} {t : TState} {ending : Option TState}
    (hpc : t.pc = probabilityWaitPc round final) (hf : t.fault = none)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending) (hi : i < (X.tr g).length) :
    X.get (g, i) = some ⟨probabilityWaitPc round final, .tc .waitSt⟩ ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (i + 1)) ending := by
  have hc := probabilityWaitCode round final
  rw [← hpc] at hc
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have ho : out kernel Assumptions.all l g t = .ev (.tc .waitSt (next t)) := by
    rw [out_event hf hc rfl rfl]
    simp [eventTmpl, tcTmpl, ofExec, hBlock, pure, Except.pure]
  simpa only [hpc] using takeTcInPrefix ho hi hRun

end
end PTX.Kernels.TmlFa4Fwd.Softmax
