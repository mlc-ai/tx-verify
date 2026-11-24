-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MbarAddressClosure
public import Kernels.TmlFa4Fwd.Proof.MmaStartup
public import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Lemmas.Step.CtaBar
public import Lemmas.Flow.TraceReach
import Kernels.TmlFa4Fwd.Flow.Code.Part029
import Kernels.TmlFa4Fwd.Flow.Code.Part032
import Kernels.TmlFa4Fwd.Flow.Code.Part033
import Kernels.TmlFa4Fwd.Flow.Code.Part034
import Kernels.TmlFa4Fwd.Flow.Code.Part035
import Kernels.TmlFa4Fwd.Flow.Code.Part036
import Kernels.TmlFa4Fwd.Flow.Code.Part037
import Kernels.TmlFa4Fwd.Flow.Code.Part038
import Kernels.TmlFa4Fwd.Flow.Code.Part039
import Kernels.TmlFa4Fwd.Flow.Code.Part040
import Kernels.TmlFa4Fwd.Flow.Code.Part041

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Softmax

noncomputable section

private structure FixedAdd where
  defPc : Nat
  lastPc : Nat
  reg : Nat
  off : Nat
  deriving DecidableEq

private def fixedMmaAdds : List FixedAdd :=
  [⟨2106, 2646, 2562, 8⟩, ⟨2109, 2646, 1188, 80⟩, ⟨2144, 2646, 2537, 32⟩,
   ⟨2275, 2646, 2610, 96⟩, ⟨2276, 2646, 2614, 112⟩, ⟨2277, 2646, 2615, 104⟩,
   ⟨2278, 2646, 2618, 120⟩, ⟨2285, 2533, 1190, 88⟩]

private def FixedAdd.active (f : FixedAdd) (pc : Nat) : Prop :=
  f.defPc < pc ∧ pc ≤ f.lastPc

private instance (f : FixedAdd) (pc : Nat) : Decidable (f.active pc) :=
  inferInstanceAs (Decidable (f.defPc < pc ∧ pc ≤ f.lastPc))

private def mmaMbarFrame (l : Launch) (s : TState) : Prop :=
  RoleShape s ∧ s.regs 1062 = some (b32 12) ∧
  s.regs 2535 = some (b32 l.sharedBase) ∧ s.regs 6495 = some (b32 (l.sharedBase + 144)) ∧
  ∀ f ∈ fixedMmaAdds, f.active s.pc → s.regs f.reg = some (b32 (l.sharedBase + f.off))

private def mmaMbarCode (pc : Nat) (i : Instr) : Bool :=
  [2535, 6495].all (fun r => !(mmaWrites i.op).contains r) &&
  fixedMmaAdds.all (fun f => pc == f.defPc || !(mmaWrites i.op).contains f.reg) &&
  match i.op with
  | .bra target _ => fixedMmaAdds.all (fun f => !decide (f.active target) || decide (f.active pc))
  | .brx .. => false
  | _ => true

private theorem mmaMbarCodeAt {pc : Nat} {i : Instr}
    (hLo : 1907 ≤ pc) (hHi : pc < 2768) (hc : kernel.code[pc]? = some i) :
    mmaMbarCode pc i = true := by
  let code := ((kernel.code.drop 1907).take (2768 - 1907)).zipIdx 1907
  have hAll : code.all (fun (ins, site) => mmaMbarCode site ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (i, pc)
  apply List.mem_of_getElem? (i := pc - 1907)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem fixedMmaAddCode {f : FixedAdd} (hf : f ∈ fixedMmaAdds) :
    kernel.code[f.defPc]? = some ⟨none,
      .int ⟨.add, .int .s 32, false, [some f.reg], [.reg 2535, .imm f.off]⟩⟩ := by
  simp only [fixedMmaAdds, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Flow.code_2106
  · exact Flow.code_2109
  · exact Flow.code_2144
  · exact Flow.code_2275
  · exact Flow.code_2276
  · exact Flow.code_2277
  · exact Flow.code_2278
  · exact Flow.code_2285

private theorem fixedMmaAdd {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s u : TState} {f : FixedAdd} (hF : f ∈ fixedMmaAdds) (hPc : s.pc = f.defPc)
    (hf : s.fault = none) (hb : s.regs 2535 = some (b32 l.sharedBase))
    (ht : Tau kernel [] l g s u) : u.regs f.reg = some (b32 (l.sharedBase + f.off)) := by
  have hMax : f.off ≤ 120 := by
    simp only [fixedMmaAdds, List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hBound : l.sharedBase + f.off < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hu := Option.some.inj ((tauStep_iff.mpr ht).symm.trans
    (evalSharedAdd hPc hf hb hBound (fixedMmaAddCode hF)))
  subst u
  exact Function.update_self _ _ _

private theorem fixedMmaAddrStep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s u : TState} {e : Option Event} (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768)
    (hFrame : mmaMbarFrame l s) (hw : WStep kernel Assumptions.all l g s e u) :
    (1907 ≤ u.pc ∧ u.pc < 2768 ∨ u.pc = 3099 ∧ u.fault = none) ∧ mmaMbarFrame l u := by
  obtain ⟨hPc, hShape, hWarp⟩ := mmaCutStep hLo hHi hw ⟨hFrame.1, hFrame.2.1⟩
  have hPc' : 1907 ≤ u.pc ∧ u.pc < 2768 ∨ u.pc = 3099 ∧ u.fault = none := by simpa using hPc
  have hKeep (r : Nat) (hr : r ∈ [2535, 6495]) : u.regs r = s.regs r := by
    apply mmaStepReg (by omega) hHi _ hw
    intro i hc
    have h := mmaMbarCodeAt hLo hHi hc
    simp only [mmaMbarCode, Bool.and_eq_true] at h
    simpa using List.all_eq_true.mp h.1.1 r hr
  refine ⟨hPc', hShape, hWarp, (hKeep _ (by decide)).trans hFrame.2.2.1,
    (hKeep _ (by decide)).trans hFrame.2.2.2.1, ?_⟩
  intro f hF hActive
  have hFall (hp : u.pc = s.pc + 1) : s.pc = f.defPc ∨ f.active s.pc := by
    unfold FixedAdd.active at hActive ⊢
    omega
  have hPrior (hNe : s.pc ≠ f.defPc) (hBefore : f.active s.pc) :
      u.regs f.reg = some (b32 (l.sharedBase + f.off)) := by
    refine (mmaStepReg (by omega) hHi (fun i hc => ?_) hw).trans (hFrame.2.2.2.2 f hF hBefore)
    have h := mmaMbarCodeAt hLo hHi hc
    simp only [mmaMbarCode, Bool.and_eq_true] at h
    simpa [hNe] using List.all_eq_true.mp h.1.2 f hF
  rcases hw with ⟨_, ht⟩ | ⟨ev, _, he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← out_eq_core (by omega) hHi]
    obtain ⟨i, hc, hf, hStep⟩ := tauScoreSource ht
    by_cases hEq : s.pc = f.defPc
    · exact fixedMmaAdd hp hF hEq hf hFrame.2.2.1 ht'
    apply hPrior hEq
    rcases tau_core_frame hc ht' with rfl | hLocal
    · exact (hFall rfl).resolve_left hEq
    · have h := hLocal.pc
      have hCode := mmaMbarCodeAt hLo hHi hc
      simp only [mmaMbarCode, Bool.and_eq_true] at hCode
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at h
      case bra target uni =>
        have hAll := hCode.2
        rw [ho] at hAll
        rw [h] at hActive
        simpa [hActive] using List.all_eq_true.mp hAll f hF
      case brx => simp [ho] at hCode
      all_goals exact (hFall h).resolve_left hEq
  · have hNe : s.pc ≠ f.defPc := by
      intro hp
      obtain ⟨i, hc, hl, _⟩ := estep_event_source he
      rw [hp, fixedMmaAddCode hF] at hc
      obtain rfl := Option.some.inj hc.symm
      cases hl
    apply hPrior hNe
    have hE : EStep kernel [] l g s ev (some u) := by
      obtain ⟨tm, hOut, hFires⟩ := he
      exact ⟨tm, by rwa [← out_eq_core (by omega) hHi], hFires⟩
    rcases (estep_return_pc hE (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · exact h ▸ hActive
    · exact (hFall h).resolve_left hNe

private theorem fixedMmaAddrWalk {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} {events : List Event} {visits : List Visit}
    (hWalk : Walk kernel Assumptions.all l g s events visits)
    (hPc : 1907 ≤ s.pc ∧ s.pc < 2768 ∨ s.pc = 3099 ∧ s.fault = none)
    (hF : mmaMbarFrame l s) {e : Event} (hm : e ∈ events) (hEnd : e.pc < 2768) :
    ∃ t o, t.pc = e.pc ∧ mmaMbarFrame l t ∧ EStep kernel Assumptions.all l g t e o := by
  rcases hPc with h | h
  · induction hWalk with
    | stop => cases hm
    | @tau s u events visits ht hw ih =>
      obtain ⟨hPc, hF'⟩ := fixedMmaAddrStep hp h.1 h.2 hF (.inl ⟨rfl, ht⟩)
      rcases hPc with h | h
      · exact ih hF' hm h
      · have hRet := mmaEpilogueExitEvents h.1 h.2 (.inl rfl) hF'.2.1 hw _ hm
        omega
    | @ev s u ev events visits he hw ih =>
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨_, _, (estep_source_pc he).symm, hF, he⟩
      · obtain ⟨hPc, hF'⟩ := fixedMmaAddrStep hp h.1 h.2 hF (.inr ⟨_, rfl, he⟩)
        rcases hPc with h | h
        · exact ih hF' hm h
        · have hRet := mmaEpilogueExitEvents h.1 h.2 (.inl rfl) hF'.2.1 hw _ hm
          omega
    | last he =>
      obtain rfl := List.mem_singleton.mp hm
      exact ⟨_, _, (estep_source_pc he).symm, hF, he⟩
  · have hRet := mmaEpilogueExitEvents h.1 h.2 (.inl rfl) hF.2.1 hWalk _ hm
    omega

private theorem mmaMbarSource {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hLo : 2141 ≤ e.pc) (hHi : e.pc < 2768) :
    ∃ t o, t.pc = e.pc ∧ mmaMbarFrame l t ∧ EStep kernel Assumptions.all l g t e o := by
  have hHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hWarp : warpIndex l g = 12 := by
    rcases roleBodyPcOfEvent hp hX he (by omega) hHint with h | h
    · omega
    · split_ifs at h <;> omega
  have hg := Step.CtaBar.thread_lt_of_get hX he
  have hNonzero : 0 < warpIndex l g := by omega
  obtain ⟨t, o, hIndex, ht, hr⟩ :=
    nonzeroCommonPrefixOfLateEvent hp hX hg hNonzero he (by omega)
  have hAt : At t 174 (startupFacts p l) := ht.mono (by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> apply holds_mem ht.2.2.2.2 <;>
    simp [nonzeroBarrierFacts, abiFacts, hWarp])
  obtain ⟨s, hs, hS⟩ := dispatchWarp12 hp hg hAt
  have hF : mmaMbarFrame l s := by
    refine ⟨⟨hS.2.1.symm ▸ Nat.zero_le _, hS.2.2.1, fun _ => hS.2.1⟩, ?_, ?_, ?_, ?_⟩
    · exact holds_mem hS.2.2.2.2 (by simp [startupFacts])
    · exact holds_mem hS.2.2.2.2 (by simp [startupFacts])
    · exact holds_mem hS.2.2.2.2 (by simp [startupFacts])
    · intro f hF hScope
      exfalso
      rw [hS.1] at hScope
      simp only [fixedMmaAdds, List.mem_cons, List.not_mem_nil, or_false] at hF
      rcases hF with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact
        (by decide : ¬ FixedAdd.active _ 1907) hScope
  have hLength : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hSuffix : (X.tr g).drop 5 ≠ [] := by
    intro h
    exact Nat.not_le_of_lt hLength ((List.drop_eq_nil_iff.mp h).trans hIndex)
  obtain ⟨_, hWalk⟩ := walkFromRun (hr.after_local_nonempty (run_rtg hs) hSuffix)
  have hm : e ∈ (X.tr g).drop 5 := by
    apply List.mem_of_getElem? (i := index - 5)
    rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
    exact he
  exact fixedMmaAddrWalk hp hWalk (.inl ⟨hS.1.symm ▸ le_rfl, hS.1.symm ▸ (by decide)⟩) hF hm hHi

/-- The opening K continuation has the two fixed CTA barrier addresses computed before it. -/
theorem openingBarriersOfTrace {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s u : TState} {es : List Event}
    (hs : At s 1935 [(1062,b32 12),(2535,b32 l.sharedBase),(6495,b32 (l.sharedBase+144))])
    (hReach : TraceReach kernel Assumptions.all l g s es u) (hu : u.pc = 2146)
    (hUpper : ∀ {a : TState} {events : List Event},
      TraceReach kernel Assumptions.all l g a events u → a.pc < 2768) :
    u.sub = 0 ∧ u.acc = [] ∧ u.regs 1188 = some (b32 (l.sharedBase+80)) ∧
      u.regs 2562 = some (b32 (l.sharedBase+8)) := by
  have hF : mmaMbarFrame l s := by
    refine ⟨⟨hs.2.1.symm ▸ Nat.zero_le _,hs.2.2.1,fun _ => hs.2.1⟩,
      hs.2.2.2.2.1,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2.1,?_⟩
    intro f hf hActive
    rw [hs.1] at hActive
    simp only [fixedMmaAdds,List.mem_cons,List.not_mem_nil,or_false] at hf
    exfalso
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (by decide : ¬ FixedAdd.active _ 1935) hActive
  have hFinal : mmaMbarFrame l u := by
    have fold {a z : TState} {events : List Event}
        (h : TraceReach kernel Assumptions.all l g a events z) :
        (∀ {b : TState} {fs : List Event},
          TraceReach kernel Assumptions.all l g b fs z → b.pc < 2768) →
        1907 ≤ a.pc → mmaMbarFrame l a → mmaMbarFrame l z := by
      induction h with
      | refl => exact fun _ _ hKeep => hKeep
      | tau hStep hTail ih =>
        intro hUp hLower hKeep
        obtain ⟨hNext,hFrame⟩ := fixedMmaAddrStep hp hLower
          (hUp (.tau hStep hTail)) hKeep (.inl ⟨rfl,hStep⟩)
        exact ih hUp (by rcases hNext with h | h <;> omega) hFrame
      | event hStep hTail ih =>
        intro hUp hLower hKeep
        obtain ⟨hNext,hFrame⟩ := fixedMmaAddrStep hp hLower
          (hUp (.event hStep hTail)) hKeep (.inr ⟨_,rfl,hStep⟩)
        exact ih hUp (by rcases hNext with h | h <;> omega) hFrame
    exact fold hReach hUpper (by rw [hs.1]; decide) hF
  exact ⟨hFinal.1.2.2 (by rw [hu]; decide),hFinal.1.2.1,
    hFinal.2.2.2.2 ⟨2109,2646,1188,80⟩ (by decide) (by rw [hu]; decide),
    hFinal.2.2.2.2 ⟨2106,2646,2562,8⟩ (by decide) (by rw [hu]; decide)⟩

/-- All fixed MMA wait offsets, including the initial K-ready slot. -/
def fixedMmaWaitOffset : Nat → Nat
  | 2145 => 32
  | 2210 => 8
  | 2297 | 2548 => 96
  | 2335 | 2586 => 112
  | 2419 | 2595 => 104
  | 2450 | 2626 => 120
  | _ => 0

/-- Every actual fixed MMA poll has the address in its decoded operand table. -/
theorem mmaFixedWaitAddress {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool} {scope : MbarScope}
    (he : X.get (g, index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [2141, 2145, 2210, 2297, 2335, 2419, 2450, 2548, 2586, 2595, 2626]) :
    target = ⟨.shared, g / l.block, l.sharedBase + fixedMmaWaitOffset pc⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hl : 2141 ≤ pc := by omega
  have hh : pc < 2768 := by omega
  obtain ⟨t, o, ht, hFrame, hStep⟩ := mmaMbarSource hp hX he hl hh
  change t.pc = pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rcases hSite with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ht, Flow.code_2141] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2535 = some (b32 (l.sharedBase + 0)) := hFrame.2.2.1
    simpa [fixedMmaWaitOffset] using
      pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_2145] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2.2 ⟨2144, 2646, 2537, 32⟩
      (by decide) (by rw [ht]; decide)
    simpa [fixedMmaWaitOffset] using
      pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_2210] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2.2 ⟨2106, 2646, 2562, 8⟩
      (by decide) (by rw [ht]; decide)
    simpa [fixedMmaWaitOffset] using
      pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_2297] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2.2 ⟨2275, 2646, 2610, 96⟩
      (by decide) (by rw [ht]; decide)
    simpa [fixedMmaWaitOffset] using
      pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_2335] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2.2 ⟨2276, 2646, 2614, 112⟩
      (by decide) (by rw [ht]; decide)
    simpa [fixedMmaWaitOffset] using
      pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_2419] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2.2 ⟨2277, 2646, 2615, 104⟩
      (by decide) (by rw [ht]; decide)
    simpa [fixedMmaWaitOffset] using
      pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_2450] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2.2 ⟨2278, 2646, 2618, 120⟩
      (by decide) (by rw [ht]; decide)
    simpa [fixedMmaWaitOffset] using
      pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_2548] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2.2 ⟨2275, 2646, 2610, 96⟩
      (by decide) (by rw [ht]; decide)
    simpa [fixedMmaWaitOffset] using
      pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_2586] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2.2 ⟨2276, 2646, 2614, 112⟩
      (by decide) (by rw [ht]; decide)
    simpa [fixedMmaWaitOffset] using
      pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_2595] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2.2 ⟨2277, 2646, 2615, 104⟩
      (by decide) (by rw [ht]; decide)
    simpa [fixedMmaWaitOffset] using
      pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_2626] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2.2 ⟨2278, 2646, 2618, 120⟩
      (by decide) (by rw [ht]; decide)
    simpa [fixedMmaWaitOffset] using
      pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl

/-- Every MMA poll with a fixed local address names an initialized CTA barrier. -/
theorem mmaFixedWaitInitObject {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool} {scope : MbarScope}
    (he : X.get (g, index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [2141, 2145, 2210, 2297, 2335, 2419, 2450, 2548, 2586, 2595, 2626]) :
    ∃ i : Fin 34, target = initObject l (g / l.block) i := by
  rw [mmaFixedWaitAddress hp hX he hSite]
  have h : initializedMbarOffset (fixedMmaWaitOffset pc) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
    rcases hSite with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (unfold initializedMbarOffset; decide)
  obtain ⟨i, hAddr⟩ := initObjectOfOffset (l := l) (cta := g / l.block) h
  exact ⟨i, hAddr⟩

/-- The decoded relative destination of each fixed-address commit. -/
def fixedMmaCommitOffset (pc : Nat) : Nat :=
  match pc with
  | 2208 | 2418 => 80
  | 2270 | 2519 => 88
  | 2274 => 56
  | 2537 => 16
  | 2541 => 24
  | 2642 => 144
  | 2646 => 152
  | _ => 0

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index pc : Nat} {spec : TcCommit.Spec}
    {rank : Fin 16} {target : Loc} (he : X.get (g, index) = some ⟨pc, .tc (.commit spec)⟩)
    (hSite : pc ∈ [2208, 2270, 2274, 2418, 2519, 2537, 2541, 2642, 2646])
include hp hX he hSite

/-- Each actual fixed-address commit resolves to its own decoded destination. -/
theorem mmaFixedCommitExactAddress (hTarget : TcCommit.target spec rank = some target) :
    target = ⟨.shared, g / l.block, l.sharedBase + fixedMmaCommitOffset pc⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hl : 2141 ≤ pc := by omega
  have hh : pc < 2768 := by omega
  obtain ⟨t, o, ht, hFrame, hStep⟩ := mmaMbarSource hp hX he hl hh
  change t.pc = pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  have hg := Step.CtaBar.thread_lt_of_get hX he
  rcases hSite with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ht, Flow.code_2208] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2.2 ⟨2109, 2646, 1188, 80⟩
      (by decide) (by rw [ht]; decide)
    exact commitExactAddress hp hg hb
      (by unfold initializedMbarOffset; decide) hFire rfl hTarget
  · rw [ht, Flow.code_2270] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2535 = some (b32 (l.sharedBase + 0)) := hFrame.2.2.1
    exact commitExactAddress hp hg hb
      (by unfold initializedMbarOffset; decide) hFire rfl hTarget
  · rw [ht, Flow.code_2274] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2535 = some (b32 (l.sharedBase + 0)) := hFrame.2.2.1
    exact commitExactAddress hp hg hb
      (by unfold initializedMbarOffset; decide) hFire rfl hTarget
  · rw [ht, Flow.code_2418] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2.2 ⟨2109, 2646, 1188, 80⟩
      (by decide) (by rw [ht]; decide)
    exact commitExactAddress hp hg hb
      (by unfold initializedMbarOffset; decide) hFire rfl hTarget
  · rw [ht, Flow.code_2519] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2.2 ⟨2285, 2533, 1190, 88⟩
      (by decide) (by rw [ht]; decide)
    exact commitExactAddress hp hg hb
      (by unfold initializedMbarOffset; decide) hFire rfl hTarget
  · rw [ht, Flow.code_2537] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2535 = some (b32 (l.sharedBase + 0)) := hFrame.2.2.1
    exact commitExactAddress hp hg hb
      (by unfold initializedMbarOffset; decide) hFire rfl hTarget
  · rw [ht, Flow.code_2541] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2535 = some (b32 (l.sharedBase + 0)) := hFrame.2.2.1
    exact commitExactAddress hp hg hb
      (by unfold initializedMbarOffset; decide) hFire rfl hTarget
  · rw [ht, Flow.code_2642] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2.1
    exact commitExactAddress hp hg hb
      (by unfold initializedMbarOffset; decide) hFire rfl hTarget
  · rw [ht, Flow.code_2646] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2535 = some (b32 (l.sharedBase + 0)) := hFrame.2.2.1
    exact commitExactAddress hp hg hb
      (by unfold initializedMbarOffset; decide) hFire rfl hTarget

/-- Every MMA commit with a fixed local address names an initialized CTA barrier. -/
theorem mmaFixedCommitAddress (hTarget : TcCommit.target spec rank = some target) :
    ∃ offset ∈ ([16, 24, 56, 80, 88, 144, 152] : List Nat),
      target = ⟨.shared, g / l.block, l.sharedBase + offset⟩ := by
  refine ⟨_, ?_, mmaFixedCommitExactAddress hp hX he hSite hTarget⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  rcases hSite with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end
end PTX.Kernels.TmlFa4Fwd.Mma
