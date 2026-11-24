-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
public import Kernels.TmlFa4Fwd.Proof.TmemGeometry
public import Kernels.TmlFa4Fwd.Flow.Code.Part053
public import Kernels.TmlFa4Fwd.Flow.Code.Part054
public import Kernels.TmlFa4Fwd.Flow.Code.Part079
public import Kernels.TmlFa4Fwd.Flow.Code.Part080
public import Kernels.TmlFa4Fwd.Flow.Code.Part104
public import Kernels.TmlFa4Fwd.Flow.Code.Part105
public import Lemmas.Flow.TcTmpl
public import Mathlib.Tactic.FinCases

import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.EventFrame

noncomputable section

inductive Round
  | first | biased | unbiased
  deriving DecidableEq

/-- One quarter of the score tile is read into 32 consecutive output registers. -/
def scorePc (round : Round) (quarter : Fin 4) : Nat :=
  match round with
  | .first => (#v[3428, 3446, 3463, 3481] : Vector Nat 4)[quarter]
  | .biased => (#v[5112, 5129, 5146, 5163] : Vector Nat 4)[quarter]
  | .unbiased => (#v[6679, 6696, 6713, 6730] : Vector Nat 4)[quarter]

def scoreReg (round : Round) (quarter : Fin 4) : Nat :=
  match round with
  | .first => #v[2788, 2913, 2789, 2978][quarter]
  | .biased => #v[3970, 3972, 3973, 3971][quarter]
  | .unbiased => #v[5180, 5182, 5183, 5181][quarter]

theorem scoreCode (round : Round) (quarter : Fin 4) :
    ∃ ds : List Nat, ds.length = 32 ∧
      kernel.code[scorePc round quarter]? =
        some ⟨none, .tcLd ds (scoreReg round quarter) .s32x32b none⟩ := by
  cases round <;> fin_cases quarter
  · exact ⟨_, rfl, Flow.code_3428⟩
  · exact ⟨_, rfl, Flow.code_3446⟩
  · exact ⟨_, rfl, Flow.code_3463⟩
  · exact ⟨_, rfl, Flow.code_3481⟩
  · exact ⟨_, rfl, Flow.code_5112⟩
  · exact ⟨_, rfl, Flow.code_5129⟩
  · exact ⟨_, rfl, Flow.code_5146⟩
  · exact ⟨_, rfl, Flow.code_5163⟩
  · exact ⟨_, rfl, Flow.code_6679⟩
  · exact ⟨_, rfl, Flow.code_6696⟩
  · exact ⟨_, rfl, Flow.code_6713⟩
  · exact ⟨_, rfl, Flow.code_6730⟩

set_option maxRecDepth 10000 in
/-- The 32-word score load is followed by a same-PC implicit wait only in the unbiased loop. -/
theorem scoreWaitHook (round : Round) (quarter : Fin 4) :
    Assumptions.all.any (·.tcLdWait (scorePc round quarter)) = decide (round = .unbiased) := by
  rw [Assumptions.all_tcLdWait]
  cases round <;> fin_cases quarter <;> kernel_rfl

def scoreAddress (l : Launch) (g : Nat) (stage : Fin 2) (quarter : Fin 4) : Nat :=
  2 ^ 16 * laneBase l g + (scoreColumn stage + 32 * quarter.val)

private theorem scoreColumnBound (stage : Fin 2) (quarter : Fin 4) :
    scoreColumn stage + 32 * quarter.val < 512 := by
  have := scoreColumn_range stage
  have := quarter.isLt
  omega

/-- In the actual model, each S load returns 32 score words. The state keeps the original
source PC and a pending wait in the unbiased loop. -/
private theorem scoreLoadTemplateDecoded {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (round : Round) (quarter : Fin 4) (g : Nat) (stage : Fin 2) (t : TState)
    (hpc : t.pc = scorePc round quarter) (hf : t.fault = none) (hs : t.sub = 0)
    (hr : t.regs (scoreReg round quarter) = some (b32 (scoreAddress l g stage quarter))) :
    ∃ ds : List Nat, ds.length = 32 ∧
      kernel.code[scorePc round quarter]? =
        some ⟨none,.tcLd ds (scoreReg round quarter) .s32x32b none⟩ ∧
      out kernel Assumptions.all l g t =
        .ev (.tcLd (scoreAddress l g stage quarter) 32 .s32x32b fun vals =>
          if round = .unbiased then {setRegs (next t) ds vals with pc := t.pc, sub := 1}
          else setRegs (next t) ds vals) := by
  obtain ⟨ds,hLen,hDecoded⟩ := scoreCode round quarter
  have hc := hpc.symm ▸ hDecoded
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hCore := tc_ld_supported (L := l) (g := g) (ds := ds) (sh := .s32x32b)
    (by intro s h; cases h) hBlock hr (tmem_warp_encoding_lt l g (scoreColumnBound stage quarter))
    (by rw [hLen]; decide) (tcDataAddressOk_warp32 l g (scoreColumnBound stage quarter))
  refine ⟨ds,hLen,hDecoded,?_⟩
  rw [out_event hf hc rfl rfl]
  change Out.ev (tcLdTmpl Assumptions.all l g t
    (.tcLd ds (scoreReg round quarter) .s32x32b none)) = _
  have hHook := congrArg (fun q => Assumptions.all.any (·.tcLdWait q)) hpc
  rw [scoreWaitHook] at hHook
  by_cases h : round = .unbiased
  · simp only [tcLdTmpl, hHook, hs, decide_eq_true h, ↓reduceIte, hCore, Tmpl.thenWaitLd, hLen,
      ite_eq_left h]
  · simp only [tcLdTmpl, hHook, decide_eq_false h, Bool.false_eq_true, ↓reduceIte, hCore, hLen,
      ite_eq_right h]

/-- In the actual model, each S load returns 32 score words. The state keeps the original
source PC and a pending wait in the unbiased loop. -/
theorem scoreLoadTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (round : Round) (quarter : Fin 4) (g : Nat) (stage : Fin 2) (t : TState)
    (hpc : t.pc = scorePc round quarter) (hf : t.fault = none) (hs : t.sub = 0)
    (hr : t.regs (scoreReg round quarter) = some (b32 (scoreAddress l g stage quarter))) :
    ∃ ds : List Nat, ds.length = 32 ∧
      out kernel Assumptions.all l g t =
        .ev (.tcLd (scoreAddress l g stage quarter) 32 .s32x32b fun vals =>
          if round = .unbiased then {setRegs (next t) ds vals with pc := t.pc, sub := 1}
          else setRegs (next t) ds vals) := by
  obtain ⟨ds,hLen,_,hOut⟩ := scoreLoadTemplateDecoded hp round quarter g stage t hpc hf hs hr
  exact ⟨ds,hLen,hOut⟩

private theorem setRegsControl (t : TState) (ds : List Nat) (vals : List Value) :
    (setRegs t ds vals).fault = t.fault ∧ (setRegs t ds vals).sub = t.sub := by
  induction ds generalizing t vals with
  | nil => exact ⟨rfl, rfl⟩
  | cons d ds ih =>
    cases vals with
    | nil => exact ⟨rfl, rfl⟩
    | cons v vals => exact ih (setReg t d v) vals

private theorem resetPending {t : TState} {pc : Nat} (hp : t.pc = pc) (hs : t.sub = 0) :
    {t with pc := pc, sub := 0} = t := by
  cases t
  simp_all

/-- The actual load records its decoded word registers through the optional implicit wait. -/
theorem scoreLoadTraceDecodedInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (round : Round) (quarter : Fin 4) (stage : Fin 2)
    {g i : Nat} {t : TState} {ending : Option TState}
    (hpc : t.pc = scorePc round quarter) (hf : t.fault = none) (hs : t.sub = 0)
    (hr : t.regs (scoreReg round quarter) = some (b32 (scoreAddress l g stage quarter)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hPresent : ending = none ∨ i + (if round = .unbiased then 1 else 0) < (X.tr g).length) :
    ∃ ds vals, ds.length = 32 ∧ vals.length = 32 ∧
      kernel.code[scorePc round quarter]? =
        some ⟨none,.tcLd ds (scoreReg round quarter) .s32x32b none⟩ ∧
      X.get (g, i) = some
        ⟨scorePc round quarter, .tc (.ld (scoreAddress l g stage quarter) vals .s32x32b)⟩ ∧
      (round = .unbiased → X.get (g, i + 1) = some ⟨scorePc round quarter, .tc .waitLd⟩) ∧
      Run kernel Assumptions.all l g (setRegs (next t) ds vals)
        ((X.tr g).drop (if round = .unbiased then i + 2 else i + 1)) ending ∧
      TraceReach kernel Assumptions.all l g t
        (⟨scorePc round quarter,.tc (.ld (scoreAddress l g stage quarter) vals .s32x32b)⟩ ::
          if round = .unbiased then [⟨scorePc round quarter,.tc .waitLd⟩] else [])
        (setRegs (next t) ds vals) := by
  obtain ⟨ds,hLen,hDecoded,hout⟩ :=
    scoreLoadTemplateDecoded hp round quarter g stage t hpc hf hs hr
  have present (j : Nat) (hJ : j ≤ i + (if round = .unbiased then 1 else 0))
      {s : TState} (hR : Run kernel Assumptions.all l g s ((X.tr g).drop j) ending) :
      (X.tr g).drop j ≠ [] := by
    intro hEmpty
    rw [hEmpty] at hR
    cases hR
    have hLen := List.drop_eq_nil_iff.mp hEmpty
    exact hPresent.elim (by simp) (fun h => (Nat.not_lt_of_ge (hLen.trans hJ)) h)
  let k := fun vals =>
    if round = .unbiased then {setRegs (next t) ds vals with pc := t.pc, sub := 1}
    else setRegs (next t) ds vals
  have hNext : Next kernel Assumptions.all l g t t
      (.tcLd (scoreAddress l g stage quarter) 32 .s32x32b k) := ⟨.refl, hout⟩
  obtain ⟨e, _, he, ⟨vals, hV, rfl, hState⟩, hTail⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨_, _, _, hBad⟩
    cases hBad) hRun (present i (Nat.le_add_right ..) hRun)
  obtain rfl := Option.some.inj hState
  rw [hpc] at he
  let ev : Event := ⟨scorePc round quarter,.tc (.ld (scoreAddress l g stage quarter) vals .s32x32b)⟩
  have hLoad : EStep kernel Assumptions.all l g t ev (some (k vals)) := by
    refine ⟨_,hout,vals,hV,?_,rfl⟩
    rw [hpc]
  by_cases h : round = .unbiased
  · let s := {setRegs (next t) ds vals with pc := t.pc, sub := 1}
    have hS : s.pc = scorePc round quarter := hpc
    have hFs : s.fault = none := by
      exact (setRegsControl (next t) ds vals).1.trans hf
    have ho : out kernel Assumptions.all l g s = .ev (.tc .waitLd (setRegs (next t) ds vals)) := by
      have hc := hS.symm ▸ hDecoded
      rw [out_event hFs hc rfl rfl]
      change Out.ev (tcLdTmpl Assumptions.all l g s _) = _
      have hHook : Assumptions.all.any (·.tcLdWait s.pc) = true := by
        rw [hS, scoreWaitHook, decide_eq_true h]
      have hSubOne : s.sub ≠ 0 := Nat.one_ne_zero
      simp only [tcLdTmpl, hHook, hSubOne, ↓reduceIte, s, next]
      have hSub : (setRegs (next t) ds vals).sub = 0 :=
        (setRegsControl (next t) ds vals).2.trans hs
      have hPc : (setRegs (next t) ds vals).pc = t.pc + 1 := setRegs_pc (next t) ds vals
      exact congrArg (fun v => Out.ev (.tc .waitLd v)) (resetPending hPc hSub)
    have hW : Next kernel Assumptions.all l g s s
        (.tc .waitLd (setRegs (next t) ds vals)) := ⟨.refl, ho⟩
    have hR : Run kernel Assumptions.all l g s ((X.tr g).drop (i + 1)) ending := by
      simpa only [k, s, h, ite_true] using hTail
    obtain ⟨f, _, hGet, hFire, hRest⟩ := hW.continuing_at_nonempty (by
      rintro e ⟨_, hBad⟩
      cases hBad) hR (present (i+1) (by simp [h]) hR)
    obtain ⟨rfl, hU⟩ := hFire
    obtain rfl := Option.some.inj hU
    refine ⟨ds, vals, hLen, hV, hDecoded, he, ?_, ?_, ?_⟩
    · intro _
      simpa only [hS] using hGet
    · simpa only [h, ite_true, Nat.add_assoc] using hRest
    · have hWaitStep : EStep kernel Assumptions.all l g s
          ⟨scorePc round quarter,.tc .waitLd⟩ (some (setRegs (next t) ds vals)) := by
        refine ⟨_,ho,?_,rfl⟩
        rw [hS]
      have hBefore : EStep kernel Assumptions.all l g t ev (some s) := by
        simpa only [k,s,h,ite_true] using hLoad
      simpa only [ev,h,ite_true] using
        (TraceReach.event hBefore (.event hWaitStep (.refl _)))
  · have hBefore : EStep kernel Assumptions.all l g t ev (some (setRegs (next t) ds vals)) := by
      simpa only [k,h,ite_false] using hLoad
    exact ⟨ds,vals,hLen,hV,hDecoded,he,(fun h' => (h h').elim),
      by simpa only [k,h,ite_false] using hTail,
      by simpa only [ev,h,ite_false] using (TraceReach.event hBefore (.refl _))⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (round : Round)
    (quarter : Fin 4) (stage : Fin 2) {g i : Nat} {t : TState} (hpc : t.pc = scorePc round quarter)
    (hf : t.fault = none) (hs : t.sub = 0)
    (hr : t.regs (scoreReg round quarter) = some (b32 (scoreAddress l g stage quarter)))
include hp round quarter stage hpc hf hs hr

theorem scoreLoadTraceDecodedWithReach
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    ∃ ds vals, ds.length = 32 ∧ vals.length = 32 ∧
      kernel.code[scorePc round quarter]? =
        some ⟨none,.tcLd ds (scoreReg round quarter) .s32x32b none⟩ ∧
      X.get (g, i) = some
        ⟨scorePc round quarter, .tc (.ld (scoreAddress l g stage quarter) vals .s32x32b)⟩ ∧
      (round = .unbiased → X.get (g, i + 1) = some ⟨scorePc round quarter, .tc .waitLd⟩) ∧
      Run kernel Assumptions.all l g (setRegs (next t) ds vals)
        ((X.tr g).drop (if round = .unbiased then i + 2 else i + 1)) none ∧
      TraceReach kernel Assumptions.all l g t
        (⟨scorePc round quarter,.tc (.ld (scoreAddress l g stage quarter) vals .s32x32b)⟩ ::
          if round = .unbiased then [⟨scorePc round quarter,.tc .waitLd⟩] else [])
        (setRegs (next t) ds vals) := by
  exact scoreLoadTraceDecodedInPrefix hp round quarter stage hpc hf hs hr hRun (.inl rfl)

/-- The actual load and optional wait return the decoded register state. -/
theorem scoreLoadTraceDecoded (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    ∃ ds vals, ds.length = 32 ∧ vals.length = 32 ∧
      kernel.code[scorePc round quarter]? =
        some ⟨none,.tcLd ds (scoreReg round quarter) .s32x32b none⟩ ∧
      X.get (g, i) = some
        ⟨scorePc round quarter, .tc (.ld (scoreAddress l g stage quarter) vals .s32x32b)⟩ ∧
      (round = .unbiased → X.get (g, i + 1) = some ⟨scorePc round quarter, .tc .waitLd⟩) ∧
      Run kernel Assumptions.all l g (setRegs (next t) ds vals)
        ((X.tr g).drop (if round = .unbiased then i + 2 else i + 1)) none := by
  obtain ⟨ds,vals,hLen,hV,hDecoded,he,hWait,hTail,_⟩ :=
    scoreLoadTraceDecodedWithReach hp round quarter stage hpc hf hs hr hRun
  exact ⟨ds,vals,hLen,hV,hDecoded,he,hWait,hTail⟩

/-- The actual S-load event and, in the unbiased round, its mandatory implicit wait. -/
theorem scoreLoadTrace (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    ∃ ds vals, ds.length = 32 ∧ vals.length = 32 ∧
      X.get (g, i) = some
        ⟨scorePc round quarter, .tc (.ld (scoreAddress l g stage quarter) vals .s32x32b)⟩ ∧
      (round = .unbiased → X.get (g, i + 1) = some ⟨scorePc round quarter, .tc .waitLd⟩) ∧
      Run kernel Assumptions.all l g (setRegs (next t) ds vals)
        ((X.tr g).drop (if round = .unbiased then i + 2 else i + 1)) none := by
  obtain ⟨ds,vals,hLen,hV,_,he,hWait,hTail⟩ :=
    scoreLoadTraceDecoded hp round quarter stage hpc hf hs hr hRun
  exact ⟨ds,vals,hLen,hV,he,hWait,hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
