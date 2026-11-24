-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaGroupedCuQTrace
import Kernels.TmlFa4Fwd.Proof.MmaFallbackEntry
import Kernels.TmlFa4Fwd.Proof.MmaFirstRoute
import Kernels.TmlFa4Fwd.Proof.MmaRoleSetup
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvDestination
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.Termination
import Kernels.TmlFa4Fwd.Flow.Code.Part042

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue Prologue
open _root_.PTX.Kernels.TmlFa4Fwd.Mma
open MmaCuQGroup

private theorem fallbackOrderFloor : knownFloors 1981 := by
  set_option maxRecDepth 100000 in
    exact ⟨by kernel_rfl,by kernel_rfl⟩

private theorem fallbackReadOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g j : Nat} {a : Acc} {bytes : List (Option Byte)}
    (he : X.get (g,j) = some (MmaCuQGroup.fallback.readEvent a bytes)) :
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase+4*index),size := 4} := by
  let target : Event := MmaCuQGroup.fallback.readEvent a bytes
  have hg := event_thread_lt hMax.1 he
  have hw := mmaRoleEventWarp hp hMax.1 he (show 1907 < 1999 by decide)
    (show 1999 < 2768 by decide) (show 1999 ∉ registerHintSites by decide)
  obtain ⟨i,b,t,ending,hB,_,hSite,_,ht,_,hr⟩ := firstGroupScanLaunchFrame hp hMax hg hw hCuQ
  have hi : i+1 ≤ j := Nat.succ_le_of_lt (traceOrderOfPcFloor hMax.1
    fallbackOrderFloor.1 fallbackOrderFloor.2 hB he (by omega) (show 1981 ≤ 1999 by decide))
  have hMem : target ∈ (X.tr g).drop (i+1) := by
    apply List.mem_of_getElem? (i := j-(i+1))
    rw [List.getElem?_drop,Nat.add_sub_of_le hi]
    exact he
  obtain ⟨_,hWalk⟩ := walkFromRun hr
  let cta := g/l.block
  let limit := tilePrefix p (min p.batch 31)*p.heads
  have hCta : cta < 2^31 := (NamedBar.cta_lt hg).trans hp.grid.2.2
  obtain ⟨s,hRoute,hs,hKeep⟩ := firstGroupRouteKeeping hp g hCta (by at_select ht)
  rcases advanceWalkLocals hRoute hWalk with hEmpty | ⟨_,_,_,hSW⟩
  · simp [hEmpty] at hMem
  have hRoutePc : s.pc = if cta < limit then 2042 else 1985 := hs.1
  by_cases hFirst : cta < limit
  · have hPc : s.pc = 2042 := by simpa only [ite_eq_left hFirst] using hRoutePc
    exact (noReadAfterGroup .fallback hSW hPc.ge hMem).elim
  have hs' : At s 1985
      ([(1072,b32 cta),(7203,b32 p.batch),(7200,b32 limit)] ++ fallbackAbi p l g) := by
    refine ⟨by simpa only [ite_eq_right hFirst] using hRoutePc,hs.2.1,hs.2.2.1,hs.2.2.2.1,?_⟩
    exact ⟨(hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
      (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),hs.2.2.2.2.1,
      (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
      (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
      (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
      (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
      (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
      (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),trivial⟩
  obtain ⟨u,hInit,hu⟩ := initializeFallbackSearch hp hg hs'
  rcases advanceWalkLocals hInit hSW with hEmpty | ⟨_,_,_,hUW⟩
  · simp [hEmpty] at hMem
  have hF : At u MmaCuQGroup.fallback.site.head (MmaCuQGroup.fallback.facts p l g 0) := by
    apply hu.mono
    apply (holds_append _ _ _).mpr
    exact ⟨⟨holds_lookup hu.2.2.2.2 rfl,holds_lookup hu.2.2.2.2 rfl,
      holds_lookup hu.2.2.2.2 rfl,holds_lookup hu.2.2.2.2 rfl,trivial⟩,
      holds_lookup hu.2.2.2.2 rfl,holds_lookup hu.2.2.2.2 rfl,
      holds_lookup hu.2.2.2.2 rfl,trivial⟩
  exact readWordOfWalk hp .fallback hg (Nat.zero_le _) hF hUW hMem

private def readyFacts (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  (7149,b32 p.batch)::drainRoots p l g

variable {p : Params} {l : Launch}

private theorem preserveReady {g : Nat} {s u : TState} {ev : Option Event} (hLo : 2648 ≤ s.pc)
    (hHi : s.pc < 2693) (hs : Holds s.regs (readyFacts p l g))
    (he : WStep kernel Assumptions.all l g s ev u) : Holds u.regs (readyFacts p l g) := by
  have hCode : ((kernel.code.drop 2648).take (2693-2648)).all
      (fun i => !(mmaWrites i.op).contains 7149) = true := by decide +kernel
  have hBatch := mmaStepReg (r := 7149) (by omega) (by omega) (h := he) (by
    intro i hi
    have hm : i ∈ (kernel.code.drop 2648).take (2693-2648) := by
      apply List.mem_of_getElem? (i := s.pc-2648)
      rwa [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo]
    simpa using List.all_eq_true.mp hCode i hm)
  exact ⟨hBatch.trans hs.1,preserveDrainRoots (by omega) (by omega) he hs.2⟩

private theorem leaveDrainPrep {g : Nat} {s : TState} {es : List Event} {vs : List Visit} {a : Acc}
    {bytes : List (Option Byte)} (hw : Walk kernel Assumptions.all l g s es vs)
    (hMem : MmaCuQGroup.drain.readEvent a bytes ∈ es) (hLo : 2648 ≤ s.pc) (hHi : s.pc < 2693)
    (hShape : RoleShape s) (hRegs : Holds s.regs (readyFacts p l g)) :
    ∃ u rest path, At u 2693 (readyFacts p l g) ∧
      Walk kernel Assumptions.all l g u rest path ∧
      MmaCuQGroup.drain.readEvent a bytes ∈ rest := by
  have advance {s u : TState} {rest : List Event} {path : List Visit} {ev : Option Event}
      (hLo : 2648 ≤ s.pc) (hHi : s.pc < 2693) (hShape : RoleShape s)
      (hRegs : Holds s.regs (readyFacts p l g))
      (he : WStep kernel Assumptions.all l g s ev u)
      (hw : Walk kernel Assumptions.all l g u rest path)
      (hPos : MmaCuQGroup.drain.readEvent a bytes ∈ rest) :
      (2648 ≤ u.pc ∧ u.pc < 2693 ∧ RoleShape u ∧ Holds u.regs (readyFacts p l g)) ∨
        At u 2693 (readyFacts p l g) := by
    have hFrame := preserveReady hLo hHi hRegs he
    obtain ⟨hh | ⟨hExit,hFault⟩,hU⟩ := roleRegionStep 5 hLo hHi hShape he
    · exact .inl ⟨hh.1,hh.2,hU,hFrame⟩
    · have hCases : u.pc = 2693 ∨ u.pc = 2750 := by simpa [roleRegion] using hExit
      rcases hCases with hCut | hOut
      · exact .inr ⟨hCut,hU.2.2 (by omega),hU.2.1,hFault,hFrame⟩
      · exact (noReadAfterGroup .drain hw hOut.ge hPos).elim
  induction hw with
  | stop => cases hMem
  | @tau s u es vs he hw ih =>
    rcases advance hLo hHi hShape hRegs (.inl ⟨rfl,he⟩) hw hMem with
      ⟨hL,hH,hS,hR⟩ | hU
    · exact ih hMem hL hH hS hR
    · exact ⟨u,es,vs,hU,hw,hMem⟩
  | @ev s u e es vs he hw ih =>
    have hRest : MmaCuQGroup.drain.readEvent a bytes ∈ es := by
      rcases List.mem_cons.mp hMem with rfl | hm
      · have hp : s.pc = 2707 := (estep_source_pc he).symm
        omega
      · exact hm
    rcases advance hLo hHi hShape hRegs (.inr ⟨_,rfl,he⟩) hw hRest with
      ⟨hL,hH,hS,hR⟩ | hU
    · exact ih hRest hL hH hS hR
    · exact ⟨u,es,vs,hU,hw,hRest⟩
  | @last s e he =>
    obtain rfl := List.mem_singleton.mp hMem
    have hp : s.pc = 2707 := (estep_source_pc he).symm
    omega

private theorem drainSetupSilence {l : Launch} {g : Nat} {s u : TState}
    {ev : Option Event} (hl : 2693 ≤ s.pc) (hh : s.pc < 2696)
    (h : WStep kernel Assumptions.all l g s ev u) :
    ev = none ∧ Tau kernel Assumptions.all l g s u ∧ u.pc = s.pc+1 := by
  have hCode (ins : Instr) (he : kernel.code[s.pc]? = some ins) :
      ins.op.isLocal = true ∧ schedulerFallsThrough ins.op = true := by
    have hs : s.pc = 2693 ∨ s.pc = 2694 ∨ s.pc = 2695 := by omega
    rcases hs with h | h | h
    · rw [h,Flow.code_2693] at he
      obtain rfl := Option.some.inj he
      decide
    · rw [h,Flow.code_2694] at he
      obtain rfl := Option.some.inj he
      decide
    · rw [h,Flow.code_2695] at he
      obtain rfl := Option.some.inj he
      decide
  rcases h with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← out_eq_core (by omega) (by omega)]
    obtain ⟨i,hc⟩ := tau_core_has_code ht'
    have hLinear := (hCode i hc).2
    refine ⟨rfl,ht,?_⟩
    rcases tau_core_frame hc ht' with rfl | hFrame
    · rfl
    · have hNext := hFrame.pc
      cases hop : i.op <;> simp_all [schedulerFallsThrough,nextPc,BrxTarget]
  · obtain ⟨i,hc,hLocal,_⟩ := estep_event_source he
    rw [(hCode i hc).1] at hLocal
    cases hLocal

private theorem replayDrainSetup {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    {a : Acc} {bytes : List (Option Byte)} (hw : Walk kernel Assumptions.all l g s es vs)
    (hMem : MmaCuQGroup.drain.readEvent a bytes ∈ es) (hLo : 2693 ≤ s.pc) (hHi : s.pc ≤ 2696)
    (hRegs : Holds s.regs (drainRoots p l g)) :
    ∃ u path, run kernel Assumptions.all l g (2696-s.pc) s = some u ∧
      Walk kernel Assumptions.all l g u es path ∧ Holds u.regs (drainRoots p l g) := by
  by_cases hHead : s.pc = 2696
  · exact ⟨s,vs,by rw [hHead,Nat.sub_self]; rfl,hw,hRegs⟩
  induction hw with
  | stop => cases hMem
  | @tau s u es vs he hw ih =>
    obtain ⟨_,_,hPc⟩ := drainSetupSilence hLo (by omega) (.inl ⟨rfl,he⟩)
    have hRu := preserveDrainRoots (by omega) (by omega) (.inl ⟨rfl,he⟩) hRegs
    have hRun {v : TState} (hr : run kernel Assumptions.all l g (2696-u.pc) u = some v) :
        run kernel Assumptions.all l g (2696-s.pc) s = some v := by
      rw [show 2696-s.pc = (2696-u.pc)+1 by omega,run,tauStep_iff.mpr he,Option.bind_some]
      exact hr
    by_cases hu : u.pc = 2696
    · exact ⟨u,vs,hRun (by rw [hu,Nat.sub_self]; rfl),hw,hRu⟩
    · obtain ⟨v,path,hv,hW,hR⟩ := ih hMem (by omega) (by omega) hRu hu
      exact ⟨v,path,hRun hv,hW,hR⟩
  | @ev s u e es vs he hw ih =>
    have hNo : some e = none := (drainSetupSilence hLo (by omega) (.inr ⟨_,rfl,he⟩)).1
    cases hNo
  | @last s e he =>
    obtain rfl := List.mem_singleton.mp hMem
    have hp : s.pc = 2707 := (estep_source_pc he).symm
    omega

private theorem laterDrainReadOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X) {g j : Nat}
    {a : Acc} {bytes : List (Option Byte)}
    (he : X.get (g,j) = some (MmaCuQGroup.drain.readEvent a bytes)) :
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase+4*index),size := 4} := by
  let target : Event := MmaCuQGroup.drain.readEvent a bytes
  have hg := event_thread_lt hMax.1 he
  obtain ⟨i,hi,t,ending,ht,hr⟩ := drainStartOfObservedEvent hp hMax hCuQ he
    (show 2647 ≤ 2707 by decide) (show 2707 < 2763 by decide)
    (show 2707 ∉ registerHintSites by decide) (by intro f h; cases h)
  obtain ⟨_,hw⟩ := walkFromRun hr
  have hMem : target ∈ (X.tr g).drop i := by
    apply List.mem_of_getElem? (i := j-i)
    rw [List.getElem?_drop,Nat.add_sub_of_le hi]
    exact he
  obtain ⟨s,hLoad,hs⟩ := firstDrainBatch hp ht
  rcases advanceWalkLocals hLoad hw with hEmpty | ⟨_,_,_,hSW⟩
  · simp [hEmpty] at hMem
  obtain ⟨u,rest,path,hU,hUW,hFound⟩ := leaveDrainPrep hSW hMem hs.1.ge (by rw [hs.1]; decide)
    ⟨by rw [hs.2.1]; decide,hs.2.2.1,fun _ => hs.2.1⟩ hs.2.2.2.2
  obtain ⟨v,out,hSetup,hVW,hR⟩ := replayDrainSetup hUW hFound hU.1.ge (by rw [hU.1]; decide)
    hU.2.2.2.2.2
  have hCTA : g/l.block+1 < 2^31 := (Nat.succ_le_of_lt
    ((Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).mpr hg)).trans_lt hp.grid.2.2
  have hAt : At u 2693 [(1072,b32 (g/l.block)),(7149,b32 p.batch)] := by
    exact hU.mono ⟨holds_lookup hU.2.2.2.2 rfl,hU.2.2.2.2.1,trivial⟩
  rw [hU.1] at hSetup
  have hV := groupInitFromRun .drain hCTA hAt hSetup
  have hFacts : At v MmaCuQGroup.drain.site.head (MmaCuQGroup.drain.facts p l g 0) :=
    hV.mono ((holds_append _ _ _).mpr ⟨hV.2.2.2.2,hR⟩)
  exact readWordOfWalk hp .drain hg (Nat.zero_le _) hFacts hVW hFound

/-- A recorded CuQ lookup in one of the two repeating MMA scheduler loops. -/
@[no_expose] def MmaGroupedCuQRead (kind : MmaCuQGroup) (X : Execution) (i : EvId)
    (a : Acc) (bytes : List (Option Byte)) : Prop :=
  X.get i = some (kind.readEvent a bytes)

def MmaGroupedCuQAddresses (p : Params) (X : Execution) : Prop :=
  ∀ kind i a bytes, MmaGroupedCuQRead kind X i a bytes →
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase+4*index),size := 4}

theorem MmaGroupedCuQRead.of_fallback {X : Execution} {i : EvId} {a : Acc}
    {bytes : List (Option Byte)} (he : X.get i = some ⟨1999,.rd a bytes⟩) :
    MmaGroupedCuQRead .fallback X i a bytes := he

theorem MmaGroupedCuQRead.of_drain {X : Execution} {i : EvId} {a : Acc}
    {bytes : List (Option Byte)} (he : X.get i = some ⟨2707,.rd a bytes⟩) :
    MmaGroupedCuQRead .drain X i a bytes := he

/-- The fallback and later drain addresses already recorded in any consistent prefix
are bounded by the launch CuQ sentinel. -/
theorem mmaGroupedCuQAddressesOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
    (hProtected : ∀ Y, Consistent l kernel Assumptions.all m Y → DrainCuQProtected p Y) :
    MmaGroupedCuQAddresses p X := by
  intro kind i a bytes he
  obtain ⟨g,j⟩ := i
  obtain ⟨Y,hXY,hMax⟩ := maximalExtension hp hX
  have hGet : X.get (g,j) = some (kind.readEvent a bytes) := he
  have hY := Execution.le_get hXY hGet
  cases kind
  · exact fallbackReadOfMaximal hp hMax (hProtected Y hMax.1) hY
  · exact laterDrainReadOfMaximal hp hMax (hProtected Y hMax.1) hY

end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
