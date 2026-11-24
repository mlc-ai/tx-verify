-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvAccumulator
import Kernels.TmlFa4Fwd.Proof.Thread.MmaRoleReplay
import Kernels.TmlFa4Fwd.Proof.MmaRoleFrame
import Lemmas.Execution.EventFrameSource
import Lemmas.Flow.Next

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Mma

/-- The steady iteration's closing election is the carried-accumulator marker. -/
def carryMarker : Nat := 2520

/-- The thread has traversed the closing election of a steady PV visit before this event. -/
@[no_expose] def PvPriorSteadyVisit (X : Execution) (i : EvId) : Prop :=
  ∃ j e, 6 ≤ j ∧ j < i.2 ∧ X.get (i.1,j) = some e ∧ e.pc = carryMarker

/-- The carried accumulator identifies an earlier closing election on the same lane. -/
theorem PvPriorSteadyVisit.closingEvent {X : Execution} {i : EvId}
    (h : PvPriorSteadyVisit X i) :
    ∃ j < i.2, ∃ e, X.get (i.1,j) = some e ∧ e.pc = carryMarker := by
  obtain ⟨j,e,_,hJ,hGet,hSite⟩ := h
  exact ⟨j,hJ,e,hGet,hSite⟩

/-- A real closing event in the earlier steady body sets the carried-visit observation. -/
theorem PvPriorSteadyVisit.ofClosingEvent {X : Execution} {i : EvId} {j : Nat} {e : Event}
    (hBody : 6 ≤ j) (hBefore : j < i.2) (hGet : X.get (i.1,j) = some e)
    (hSite : e.pc = carryMarker) : PvPriorSteadyVisit X i :=
  ⟨j,e,hBody,hBefore,hGet,hSite⟩

/-- A set carry flag records an actual earlier event in the steady MMA path. -/
theorem PvPriorSteadyVisit.steadyEvent {X : Execution} {i : EvId}
    (h : PvPriorSteadyVisit X i) :
    ∃ j e, X.get (i.1,j) = some e ∧ 2295 ≤ e.pc ∧ e.pc < 2534 := by
  obtain ⟨j,e,_,_,he,hSite⟩ := h
  exact ⟨j,e,he,hSite.symm ▸ (by decide : 2295 ≤ carryMarker ∧ carryMarker < 2534)⟩

private theorem priorSteadyNext {X : Execution} {g pos : Nat} {ev : Option Event}
    (hPos : 6 ≤ pos) (hActual : ∀ e, ev = some e → X.get (g,pos) = some e) :
    PvPriorSteadyVisit X (g,pos+ev.toList.length) ↔
      PvPriorSteadyVisit X (g,pos) ∨ ∃ e, ev = some e ∧ e.pc = carryMarker := by
  cases ev with
  | none => simp
  | some first =>
    constructor
    · rintro ⟨j,e,hLo,hHi,hGet,hEq⟩
      change j < pos+1 at hHi
      by_cases hLt : j < pos
      · exact .inl ⟨j,e,hLo,hLt,hGet,hEq⟩
      · have hHere : j = pos := by omega
        subst j
        obtain rfl := Option.some.inj ((hActual first rfl).symm.trans hGet)
        exact .inr ⟨first,rfl,hEq⟩
    · rintro (⟨j,e,hLo,hHi,hGet,hEq⟩ | ⟨e,hGet,hEq⟩)
      · exact ⟨j,e,hLo,by change j < pos+1; omega,hGet,hEq⟩
      · exact ⟨pos,e,hPos,Nat.lt_succ_self _,hActual _ hGet,hEq⟩

private def carryEarly (pos : Nat) : Prop := pos ≤ 2290

private def carryInstalling (pos : Nat) : Prop := carryMarker+1 ≤ pos ∧ pos ≤ 2532

private def carryLive (pos : Nat) : Prop :=
  2283 ≤ pos ∧ pos ≤ 2647 ∧ (pos ≤ carryMarker ∨ 2533 ≤ pos)

private instance (n : Nat) : Decidable (carryEarly n) := inferInstanceAs (Decidable (_ ≤ _))

private instance (n : Nat) : Decidable (carryInstalling n) :=
  inferInstanceAs (Decidable (_ ∧ _))

private instance (n : Nat) : Decidable (carryLive n) := inferInstanceAs (Decidable (_ ∧ _))

noncomputable section
attribute [local instance] Classical.propDecidable

private def carryWord (X : Execution) (g pos : Nat) : Value :=
  b32 (if PvPriorSteadyVisit X (g,pos) then 1 else 0)

private def CarryWords (X : Execution) (g pos : Nat) (s : TState) : Prop :=
  6 ≤ pos ∧
  (carryEarly s.pc → ¬ PvPriorSteadyVisit X (g,pos)) ∧
  (carryInstalling s.pc → PvPriorSteadyVisit X (g,pos)) ∧
  (carryLive s.pc → s.regs 7206 = some (carryWord X g pos)) ∧
  (s.pc = 2282 → s.regs 7205 = some (b32 0)) ∧
  (s.pc = 2289 → s.regs 7208 = some (b32 0))

private def carryEdge (src dest : Nat) : Bool :=
  (!decide (carryEarly dest) || decide (carryEarly src)) &&
  (!decide (carryInstalling dest) || decide (carryInstalling src)) &&
  (!decide (carryLive dest) || decide (carryLive src)) &&
  !([2282,2289].contains dest)

private def carryStepCode (pos : Nat) (i : Instr) : Bool :=
  [2281,2282,2288,2289,carryMarker,2532].contains pos ||
    (!(mmaWrites i.op).contains 7206 && carryEdge pos (pos+1) &&
      match i.op with
      | .bra dst _ => carryEdge pos dst
      | .brx .. => false
      | _ => true)

set_option maxRecDepth 100000 in
private theorem carryAudit :
    (((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907).all
      (fun (i,pos) => carryStepCode pos i) = true := by kernel_rfl

private theorem carryCheck {pos : Nat} {ins : Instr}
    (hLo : 1907 ≤ pos) (hHi : pos < 2768)
    (hOrd : [2281,2282,2288,2289,carryMarker,2532].contains pos = false)
    (hc : kernel.code[pos]? = some ins) :
    (mmaWrites ins.op).contains 7206 = false ∧ carryEdge pos (pos+1) = true ∧
      (match ins.op with
      | .bra dst _ => carryEdge pos dst
      | .brx .. => false
      | _ => true) = true := by
  let program := ((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907
  have hMem : (ins,pos) ∈ program := by
    apply List.mem_of_getElem? (i := pos-1907)
    dsimp only [program]
    rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
      Nat.add_sub_of_le hLo,hc]
    rfl
  have h := List.all_eq_true.mp carryAudit (ins,pos) hMem
  simp only [carryStepCode,hOrd,Bool.false_or,Bool.and_eq_true,Bool.not_eq_true'] at h
  exact ⟨h.1.1,h.1.2,h.2⟩

section
variable {l : Launch} {X : Execution} {g pos : Nat}

private theorem carryNoNewVisit {s u : TState} {ev : Option Event} (hPos : 6 ≤ pos)
    (hNot : s.pc ≠ carryMarker) (hw : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e, ev = some e → X.get (g,pos) = some e) :
    PvPriorSteadyVisit X (g,pos+ev.toList.length) ↔ PvPriorSteadyVisit X (g,pos) := by
  rw [priorSteadyNext hPos hActual]
  apply or_iff_left
  rintro ⟨e,rfl,hAt⟩
  rcases hw with ⟨h,_⟩ | ⟨f,h,he⟩
  · cases h
  · obtain rfl := Option.some.inj h
    exact (hNot ((estep_source_pc he).symm.trans hAt)).elim

private theorem ordinaryCarryWords {s u : TState} {ev : Option Event} (hLo : 1907 ≤ s.pc)
    (hHi : s.pc < 2768) (hOrd : [2281,2282,2288,2289,carryMarker,2532].contains s.pc = false)
    (hs : CarryWords X g pos s) (hw : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e, ev = some e → X.get (g,pos) = some e) :
    CarryWords X g (pos+ev.toList.length) u := by
  have hCheck {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :=
    carryCheck hLo hHi hOrd hc
  have hPast := carryNoNewVisit hs.1 (show s.pc ≠ carryMarker by
    intro h; rw [h] at hOrd; cases hOrd) hw hActual
  have hKeep : u.regs 7206 = s.regs 7206 := by
    apply mmaStepReg (by omega) hHi _ hw
    intro ins hc
    simpa using (hCheck hc).1
  have hCore := out_eq_core (show 1904 ≤ s.pc by omega) hHi (l := l) (g := g) (t := s)
  have hEdge : carryEdge s.pc u.pc = true := by
    rcases hw with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
    · have hTau : Tau kernel [] l g s u := by
        unfold Tau at ht ⊢
        rwa [← hCore]
      obtain ⟨ins,hGet⟩ := tau_core_has_code hTau
      rcases tau_core_frame hGet hTau with rfl | h
      · exact (hCheck hGet).2.1
      have hPc := h.pc
      cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
      case bra dst uni => simpa only [hOp,hPc] using (hCheck hGet).2.2
      case brx =>
        have hNo := (hCheck hGet).2.2
        simp only [hOp,Bool.false_eq_true] at hNo
      all_goals exact hPc.symm ▸ (hCheck hGet).2.1
    · obtain ⟨ins,hGet,_,_⟩ := estep_event_source he
      have heCore : EStep kernel [] l g s e (some u) := by
        obtain ⟨tm,hOut,hFire⟩ := he
        exact ⟨tm,hCore ▸ hOut,hFire⟩
      rcases (estep_return_pc heCore (fun _ _ _ h => execLocal_frame h)).2 with h | h
      · rw [h]
        simp [carryEdge]
        simp [carryMarker] at hOrd
        exact ⟨hOrd.2.1,hOrd.2.2.2.1⟩
      · exact h.symm ▸ (hCheck hGet).2.1
  simp only [carryEdge,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',
    decide_eq_false_iff_not,decide_eq_true_eq] at hEdge
  obtain ⟨⟨⟨hEarly,hInstall⟩,hLive⟩,hSeed⟩ := hEdge
  refine ⟨by have := hs.1; omega,?_,?_,?_,?_,?_⟩
  · exact fun h => (not_congr hPast).mpr (hs.2.1 (hEarly.resolve_left (not_not.mpr h)))
  · exact fun h => hPast.mpr (hs.2.2.1 (hInstall.resolve_left (not_not.mpr h)))
  · intro h
    rw [hKeep,carryWord,propext hPast]
    exact hs.2.2.2.1 (hLive.resolve_left (not_not.mpr h))
  · intro h
    rw [h] at hSeed
    cases hSeed
  · intro h
    rw [h] at hSeed
    cases hSeed

set_option linter.unusedSimpArgs false in
private theorem carryMarkerNext {s u : TState} {ev : Option Event} (hPc : s.pc = carryMarker)
    (hs : CarryWords X g pos s) (hw : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e, ev = some e → X.get (g,pos) = some e) :
    u.pc = 2521 ∧ CarryWords X g (pos+ev.toList.length) u := by
  have hc := Flow.code_2520
  rw [← show s.pc = 2520 from hPc] at hc
  rcases hw with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · unfold Tau at ht
    rw [out_eq_core (by rw [hPc]; decide) (by rw [hPc]; decide)] at ht
    exact (tau_core_not_event hc rfl ht).elim
  · obtain ⟨ins,hGet,_,hf⟩ := estep_event_source he
    obtain rfl := Option.some.inj (hGet.symm.trans hc)
    obtain ⟨mk,inst,leader,_,hu⟩ := fires_elect hf
    have hNext : u.pc = 2521 := by rw [hu]; change s.pc+1 = 2521; rw [hPc]; rfl
    have hSeen : PvPriorSteadyVisit X (g,pos+1) :=
      ⟨pos,e,hs.1,Nat.lt_succ_self _,hActual e rfl,(estep_source_pc he).trans hPc⟩
    refine ⟨hNext,by have := hs.1; omega,?_,fun _ => hSeen,?_,?_,?_⟩ <;>
      rw [hNext] <;> simp [carryEarly,carryInstalling,carryLive,carryMarker]

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem carryWordsStep {s u : TState} {ev : Option Event} (hLo : 1907 ≤ s.pc)
    (hHi : s.pc < 2768) (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12))
    (hs : CarryWords X g pos s) (hw : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e, ev = some e → X.get (g,pos) = some e) :
    CarryWords X g (pos+ev.toList.length) u := by
  have hsAt {pc : Nat} {F : List (Nat × Value)} (hpc : s.pc = pc)
      (hSub : 1909 < pc) (hF : Holds s.regs F) : At s pc F :=
    ⟨hpc,hShape.1.2.2 (by omega),hShape.1.2.1,
      mmaRoleReturningNormal (by omega) hHi hw,hF⟩
  have hLocal {pc : Nat} {F G : List (Nat × Value)} (hpc : s.pc = pc)
      (hSub : 1909 < pc) (hEnd : pc+1 ≤ 2768) (hF : Holds s.regs F)
      (hSeg : Seg kernel [] l g 1 pc F (pc+1) G) :
      ev = none ∧ At u (pc+1) G :=
    mmaRoleLocalStepAt (by omega) hEnd hSeg (hsAt hpc hSub hF) hw
  by_cases h2281 : s.pc = 2281
  · have hSeg : Seg kernel [] l g 1 2281 [] 2282 [(7205,b32 0)] := by
      intro t ht
      seg_fp ht using rfl
    obtain ⟨rfl,hu⟩ := hLocal (F := []) h2281 (by decide) (by decide) trivial hSeg
    have hNo := hs.2.1 (h2281.symm ▸ (show carryEarly 2281 by decide))
    refine ⟨hs.1,fun _ => hNo,?_,?_,fun _ => hu.2.2.2.2.1,?_⟩ <;>
      rw [hu.1] <;> simp [carryEarly,carryInstalling,carryLive,carryMarker]
  by_cases h2282 : s.pc = 2282
  · have hSeg : Seg kernel [] l g 1 2282 [(7205,b32 0)] 2283 [(7206,b32 0)] := by
      intro t ht
      seg_fp ht using first | assumption | rfl
    obtain ⟨rfl,hu⟩ := hLocal (F := [(7205,b32 0)]) h2282 (by decide) (by decide)
      ⟨hs.2.2.2.2.1 h2282,trivial⟩ hSeg
    have hNo := hs.2.1 (h2282.symm ▸ (show carryEarly 2282 by decide))
    refine ⟨hs.1,fun _ => hNo,?_,fun _ => ?_,?_,?_⟩
    · rw [hu.1]; simp [carryEarly,carryInstalling,carryLive,carryMarker]
    · exact hu.2.2.2.2.1.trans (by simp [carryWord,hNo])
    · rw [hu.1]; simp [carryEarly,carryInstalling,carryLive,carryMarker]
    · rw [hu.1]; simp [carryEarly,carryInstalling,carryLive,carryMarker]
  by_cases h2288 : s.pc = 2288
  · have hSeg : Seg kernel [] l g 1 2288 [(7206,b32 0)] 2289
        [(7208,b32 0),(7206,b32 0)] := by
      intro t ht
      seg_fp ht using rfl
    have hNo := hs.2.1 (h2288.symm ▸ (show carryEarly 2288 by decide))
    have hZero := hs.2.2.2.1 (h2288.symm ▸ (show carryLive 2288 by decide))
    have hz : s.regs 7206 = some (b32 0) := by simpa [carryWord,hNo] using hZero
    obtain ⟨rfl,hu⟩ := hLocal (F := [(7206,b32 0)]) h2288 (by decide) (by decide) ⟨hz,trivial⟩ hSeg
    refine ⟨hs.1,fun _ => hNo,?_,fun _ => ?_,?_,fun _ => hu.2.2.2.2.1⟩
    · rw [hu.1]; simp [carryEarly,carryInstalling,carryLive,carryMarker]
    · exact hu.2.2.2.2.2.1.trans (by simp [carryWord,hNo])
    · rw [hu.1]; simp [carryEarly,carryInstalling,carryLive,carryMarker]
  by_cases h2289 : s.pc = 2289
  · have hSeg : Seg kernel [] l g 1 2289 [(7208,b32 0)] 2290 [(7206,b32 0)] := by
      intro t ht
      seg_fp ht using first | assumption | rfl
    obtain ⟨rfl,hu⟩ := hLocal (F := [(7208,b32 0)]) h2289 (by decide) (by decide)
      ⟨hs.2.2.2.2.2 h2289,trivial⟩ hSeg
    have hNo := hs.2.1 (h2289.symm ▸ (show carryEarly 2289 by decide))
    refine ⟨hs.1,fun _ => hNo,?_,fun _ => ?_,?_,?_⟩
    · rw [hu.1]; simp [carryEarly,carryInstalling,carryLive,carryMarker]
    · exact hu.2.2.2.2.1.trans (by simp [carryWord,hNo])
    · rw [hu.1]; simp [carryEarly,carryInstalling,carryLive,carryMarker]
    · rw [hu.1]; simp [carryEarly,carryInstalling,carryLive,carryMarker]
  by_cases hMarker : s.pc = carryMarker
  · exact (carryMarkerNext hMarker hs hw hActual).2
  by_cases h2532 : s.pc = 2532
  · have hSeg : Seg kernel [] l g 1 2532 [] 2533 [(7206,b32 1)] := by
      intro t ht
      seg_fp ht using rfl
    obtain ⟨rfl,hu⟩ := hLocal (F := []) h2532 (by decide) (by decide) trivial hSeg
    have hSeen := hs.2.2.1 (h2532.symm ▸ (show carryInstalling 2532 by decide))
    refine ⟨hs.1,?_,?_,fun _ => ?_,?_,?_⟩
    · rw [hu.1]; simp [carryEarly,carryInstalling,carryLive,carryMarker]
    · rw [hu.1]; simp [carryEarly,carryInstalling,carryLive,carryMarker]
    · exact hu.2.2.2.2.1.trans (by simp [carryWord,hSeen])
    · rw [hu.1]; simp [carryEarly,carryInstalling,carryLive,carryMarker]
    · rw [hu.1]; simp [carryEarly,carryInstalling,carryLive,carryMarker]
  apply ordinaryCarryWords hLo hHi _ hs hw hActual
  simp [List.contains_iff_mem,h2281,h2282,h2288,h2289,hMarker,h2532]

private def carryFlag (X : Execution) (g pos : Nat) : Bool :=
  decide (PvPriorSteadyVisit X (g,pos))

private def carryBit (flag : Bool) : Value := b32 (if flag then 1 else 0)

private def FirstFragmentFlag (X : Execution) (g pos : Nat) (b : Fin 4) :=
  MmaLiveReg (pvPc b 0) (pvPc b 0) (pvSite b).enable (.pred (carryFlag X g pos))

set_option maxRecDepth 100000 in
private theorem firstFragmentFlagAudit (b : Fin 4) :
    MmaLiveRegAudit (pvPc b 0) (pvPc b 0) (pvSite b).enable := by
  fin_cases b <;> kernel_rfl

private theorem firstFragmentFlagStep (b : Fin 4) {s u : TState} {ev : Option Event}
    (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768) (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12))
    (hs : CarryWords X g pos s) (hFlag : FirstFragmentFlag X g pos b s)
    (hw : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e, ev = some e → X.get (g,pos) = some e) :
    FirstFragmentFlag X g (pos+ev.toList.length) b u := by
  let first := pvPc b 0
  have hRange : 1909 < first-1 ∧ first ≤ 2768 ∧ carryLive (first-1) := by
    fin_cases b <;> decide
  by_cases hMarker : s.pc = carryMarker
  · have hNext := (carryMarkerNext hMarker hs hw hActual).1
    intro hLive
    have hBefore : 2521 ≠ first := by fin_cases b <;> decide
    have hAfter : first ≠ 2521 := Ne.symm hBefore
    rw [hNext] at hLive
    by_cases hAfter' : first ≤ 2521
    · intro hEnd
      rw [hNext] at hEnd
      exact (hAfter (Nat.le_antisymm hAfter' hEnd)).elim
    · exact (hAfter' hLive).elim
  have hSeen := carryNoNewVisit hs.1 hMarker hw hActual
  have hSame : carryFlag X g (pos+ev.toList.length) = carryFlag X g pos := by
    unfold carryFlag
    rw [propext hSeen]
  have hNormalized : carryWord X g pos = carryBit (carryFlag X g pos) := by
    by_cases hv : PvPriorSteadyVisit X (g,pos)
    · simp [carryWord,carryBit,carryFlag,hv]
    · simp [carryWord,carryBit,carryFlag,hv]
  change MmaLiveReg first first (pvSite b).enable
    (.pred (carryFlag X g (pos+ev.toList.length))) u
  rw [hSame]
  by_cases hp : s.pc+1 = first
  · have hPc : s.pc = first-1 := by omega
    have hSet (flag : Bool) :
        Seg kernel [] l g 1 (first-1) [(7206,carryBit flag)] (first-1+1)
          [((pvSite b).enable,.pred flag)] := by
      fin_cases b <;> cases flag <;> intro t ht <;>
        simp only [carryBit, Bool.false_eq_true, ↓reduceIte] at ht <;>
        seg_fp ht using rfl
    have hWord := (hs.2.2.2.1 (hPc.symm ▸ hRange.2.2)).trans (congrArg some hNormalized)
    have hAt : At s (first-1) [(7206,carryBit (carryFlag X g pos))] :=
      ⟨hPc,hShape.1.2.2 (by omega),hShape.1.2.1,
        mmaRoleReturningNormal (by omega) hHi hw,⟨hWord,trivial⟩⟩
    obtain ⟨_,hu⟩ := mmaRoleLocalStepAt (by omega) (by omega) (hSet _) hAt hw
    exact fun _ _ => hu.2.2.2.2.1
  · exact mmaRoleLiveRegStep (firstFragmentFlagAudit b) hLo hHi hp hFlag hw
end

private theorem firstFragmentReadsCarry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId}
    {b : Fin 4} {d : Nat} {op : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : PvInstruction X i b 0 d op acc mask) :
    acc = carryFlag X i.1 i.2 := by
  obtain ⟨g,index⟩ := i
  have he := hi.decoded
  have hBounds : 1907 < pvPc b 0 ∧ pvPc b 0 < 2768 ∧ pvPc b 0 ∉ registerHintSites := by
    fin_cases b <;> decide
  have hWarp := mmaRoleEventWarp hp hX he hBounds.1 hBounds.2.1 hBounds.2.2
  let Inv := fun pos s => CarryWords X g pos s ∧ FirstFragmentFlag X g pos b s
  obtain ⟨t,o,hFrame,hFire⟩ := mmaRoleReplayOfEvent hp hX he hWarp hBounds.1 hBounds.2.1 Inv
    (by
      intro s hs
      have hNone : ¬ PvPriorSteadyVisit X (g,6) := by
        rintro ⟨j,e,h₁,h₂,h₃,h₄⟩
        exact (Nat.not_lt_of_ge h₁ h₂).elim
      change CarryWords X g 6 s ∧ FirstFragmentFlag X g 6 b s
      refine ⟨⟨le_rfl,fun _ => hNone,?_,?_,?_,?_⟩,?_⟩
      · rw [hs]; simp [carryInstalling,carryMarker]
      · rw [hs]; simp [carryLive]
      · rw [hs]; simp
      · rw [hs]; simp
      · intro hLow
        have hn : ¬ pvPc b 0 ≤ 1908 := by fin_cases b <;> decide
        exact (hn (hs ▸ hLow)).elim)
    (by
      intro s u ev pos hLo hHi hShape hOld hStep hActual
      exact ⟨carryWordsStep hLo hHi hShape hOld.1 hStep hActual,
        firstFragmentFlagStep b hLo hHi hShape hOld.1 hOld.2 hStep hActual⟩)
  have hPc : pvPc b 0 = t.pc := estep_source_pc hFire
  have hReg := hFrame.2 hPc.le hPc.ge
  exact pvAccumulationAtEvent (event_thread_lt hX he) b 0
    (by simp only [pvEnable,Fin.val_zero,↓reduceIte,mmaEnable,readReg,hReg]; rfl) hFire

/-- PV enables D input after its first fragment or after a prior steady visit. -/
theorem PvInstruction.accumulatorUse {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId}
    {b : Fin 4} {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : PvInstruction X i b step d op acc mask) :
    acc = true ↔ 0 < step.val ∨ PvPriorSteadyVisit X i := by
  by_cases hz : step.val = 0
  · have he : step = 0 := Fin.ext hz
    subst step
    rw [firstFragmentReadsCarry hp hX hi]
    simp [carryFlag]
  · simp [hi.accumulatesAfterFirstFragment hp hX hz,Nat.pos_of_ne_zero hz]

end
end PTX.Kernels.TmlFa4Fwd.Thread
