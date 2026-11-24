-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaGroupedCuQControl
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.MmaScanPrefix
import Lemmas.Flow.WriteSpace

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation.MmaCuQGroup
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue Prologue
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

def readEvent (kind : MmaCuQGroup) (a : Acc) (bytes : List (Option Byte)) : Event :=
  ⟨kind.readSite,.rd a bytes⟩

private theorem readImpossibleWithFault (kind : MmaCuQGroup) {l : Launch} {g : Nat}
    {s : TState} {es : List Event} {vs : List Visit} {a : Acc}
    {bytes : List (Option Byte)} (hw : Walk kernel Assumptions.all l g s es vs)
    (hFault : s.fault.isSome = true) (hm : readEvent kind a bytes ∈ es) : False := by
  obtain ⟨f,hF⟩ := Option.isSome_iff_exists.mp hFault
  have hOut : out kernel Assumptions.all l g s = .ev (.ub f) := by simp [out,hF]
  cases hw with
  | stop => cases hm
  | tau ht _ => cases hOut.symm.trans ht
  | ev he _ =>
    obtain ⟨m,ho,hFire⟩ := he
    obtain rfl := Out.ev.inj (hOut.symm.trans ho)
    cases hFire.2
  | last he =>
    obtain rfl := List.mem_singleton.mp hm
    obtain ⟨m,ho,hFire⟩ := he
    obtain rfl := Out.ev.inj (hOut.symm.trans ho)
    have hKind := congrArg Event.kind hFire.1
    cases hKind

set_option maxRecDepth 100000 in
private theorem fallbackFloor : knownFloors 2042 := by
  exact ⟨by kernel_rfl,by kernel_rfl⟩

set_option maxRecDepth 100000 in
private theorem drainFloor : knownFloors 2750 := by
  exact ⟨by kernel_rfl,by kernel_rfl⟩

theorem noReadAfterGroup (kind : MmaCuQGroup) {l : Launch} {g : Nat}
    {s : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs) (hs : kind.site.compare+3 ≤ s.pc)
    {a : Acc} {bytes : List (Option Byte)} (hm : readEvent kind a bytes ∈ es) : False := by
  have hFloor : knownFloors (kind.site.compare+3) := by
    cases kind
    · exact fallbackFloor
    · exact drainFloor
  have h := eventTailEvents hFloor.1 hFloor.2 hw hs _ hm
  have hLt : kind.readSite < kind.site.compare+3 := by cases kind <;> decide
  exact (Nat.not_le_of_gt hLt) h

private theorem branchLocal (kind : MmaCuQGroup) {l : Launch} {g : Nat} {s u : TState}
    {e : Event} (hs : s.pc = kind.site.compare+2)
    (he : EStep kernel Assumptions.all l g s e (some u)) : False := by
  have hk : ∃ p, kernel.code[kind.site.compare+2]? =
      some ⟨some (p,false),.bra kind.site.head false⟩ := by
    cases kind
    · exact ⟨_,Flow.code_2041⟩
    · exact ⟨_,Flow.code_2749⟩
  obtain ⟨pred,hInstr⟩ := hk
  obtain ⟨ins,hCode,hLocal,_⟩ := estep_event_source he
  rw [hs,hInstr] at hCode
  obtain rfl := Option.some.inj hCode
  cases hLocal

private theorem bodyFrame (kind : MmaCuQGroup) {p : Params} {l : Launch} {g first : Nat}
    {s u : TState} {ev : Option Event}
    (hs : kind.site.head+5 ≤ s.pc) (hu : s.pc ≤ kind.site.compare+2)
    (hW : WStep kernel Assumptions.all l g s ev u)
    (hScan : ∀ r ∈ scanFrame kind.site, u.regs r = s.regs r)
    (hF : Holds s.regs (kind.facts p l g first)) :
    Holds u.regs (kind.facts p l g first) := by
  have hLo : 1981 ≤ kind.site.head+5 := by cases kind <;> decide
  have hHi : kind.site.compare+2 < 2768 := by cases kind <;> decide
  change Holds s.regs (groupScanFacts kind.scan first p.batch (g/l.block) ++ drainRoots p l g)
    at hF
  rw [holds_append] at hF
  apply (holds_append _ _ _).mpr
  refine ⟨holdsSchedulerFrame hF.1 hScan ?_,preserveDrainRoots (hLo.trans hs) (hu.trans_lt hHi)
    hW hF.2⟩
  intro pair hPair
  simpa [groupScanFacts,scanFrame,site] using List.mem_map_of_mem (f := Prod.fst) hPair

private theorem loopBodyToBackedge {p : Params} {l : Launch} {g first : Nat}
    (kind : MmaCuQGroup) {s : TState}
    {es : List Event} {vs : List Visit} {a : Acc} {bytes : List (Option Byte)}
    (hw : Walk kernel Assumptions.all l g s es vs) (ht : readEvent kind a bytes ∈ es)
    (hLo : kind.readSite+1 ≤ s.pc) (hHi : s.pc ≤ kind.site.compare+2)
    (hs : At s s.pc (kind.facts p l g first)) :
    ∃ u events path, path.length < vs.length ∧
      At u kind.site.head (kind.facts p l g first) ∧
      Walk kernel Assumptions.all l g u events path ∧ readEvent kind a bytes ∈ events := by
  have hBody : kind.site.head+5 ≤ kind.readSite+1 := by cases kind <;> decide
  induction hw with
  | stop => cases ht
  | @tau s u es vs he hW ih =>
    by_cases hedge : s.pc = kind.site.compare+2
    · obtain ⟨hPc | hPc,hSub,hAcc,hF,hRegs⟩ :=
        scanEndTau kind.scan hedge hs.2.1 hs.2.2.1 he
      · exact ⟨u,es,vs,by simp,⟨hPc,hSub.trans hs.2.1,hAcc.trans hs.2.2.1,
          hF.trans hs.2.2.2.1,hRegs.symm ▸ hs.2.2.2.2⟩,hW,ht⟩
      · exact (noReadAfterGroup kind hW hPc.ge ht).elim
    have hBound : s.pc < kind.site.compare+2 := lt_of_le_of_ne hHi hedge
    obtain ⟨hForward,hHigh,hSub,hAcc,hF,hR⟩ :=
      scanBodyTau kind.scan (hBody.trans hLo) hBound hs.2.1 hs.2.2.1 he
    have hFrame := bodyFrame kind (hBody.trans hLo) hHi (.inl ⟨rfl,he⟩) hR hs.2.2.2.2
    obtain ⟨v,next,path,hLen,hV,hRun,hMem⟩ := ih ht (hLo.trans hForward.le) hHigh
      ⟨rfl,hSub.trans hs.2.1,hAcc.trans hs.2.2.1,hF.trans hs.2.2.2.1,hFrame⟩
    exact ⟨v,next,path,hLen.trans (by simp),hV,hRun,hMem⟩
  | @ev s u e es vs he hW ih =>
    have hFound : readEvent kind a bytes ∈ es := by
      rcases List.mem_cons.mp ht with rfl | hm
      · have hSite : s.pc = kind.readSite := (estep_source_pc he).symm
        omega
      · exact hm
    have hBound : s.pc < kind.site.compare+2 := by
      by_contra! h
      exact branchLocal kind (by omega) he
    obtain ⟨hNext | hFault,hSub,hAcc,hR⟩ :=
      scanBodyEvent kind.scan (hBody.trans hLo) hBound hs.2.1 hs.2.2.1 he
    · have hFrame := bodyFrame kind (hBody.trans hLo) hHi (.inr ⟨_,rfl,he⟩) hR hs.2.2.2.2
      obtain ⟨v,next,path,hLen,hV,hRun,hMem⟩ := ih hFound (by omega) (by omega)
        ⟨rfl,hSub,hAcc,hNext.2.trans hs.2.2.2.1,hFrame⟩
      exact ⟨v,next,path,hLen.trans (by simp),hV,hRun,hMem⟩
    · exact (readImpossibleWithFault kind hW hFault.2 hFound).elim
  | @last s e he =>
    obtain rfl := List.mem_singleton.mp ht
    have hSite : s.pc = kind.readSite := (estep_source_pc he).symm
    omega

private theorem emittedRead {l : Launch} {g : Nat} {s : TState} {o : Option TState}
    {a : Acc} {k : List (Option Byte) → TState}
    (hOut : out kernel Assumptions.all l g s = .ev (.read a k))
    {e : Event} (he : EStep kernel Assumptions.all l g s e o) :
    ∃ bytes, e = ⟨s.pc,.rd a bytes⟩ ∧ o = some (k bytes) := by
  obtain ⟨op,ho,hF⟩ := he
  obtain rfl := Out.ev.inj (ho.symm.trans hOut)
  obtain ⟨bs,_,rfl,rfl⟩ := hF
  exact ⟨bs,rfl,rfl⟩

private theorem isNotEmpty {kind : MmaCuQGroup} {a : Acc} {bytes : List (Option Byte)}
    {es : List Event} (h : readEvent kind a bytes ∈ es) : es ≠ [] :=
  fun he => by simp [he] at h

private theorem advanceFrame (kind : MmaCuQGroup) {p : Params} {l : Launch} {g : Nat} :
    ((kernel.code.drop kind.site.head).take 5).all
      (fun i => ((drainRoots p l g).map Prod.fst).all
        (fun r => !(writesRegs i.op).contains r)) = true := by
  simp only [drainRoots,List.map_cons,List.map_nil]
  cases kind <;> decide +kernel

/-- Every actual lookup in either repeated MMA scheduler search addresses a launch word.
The proof follows the recorded loop bodies and stops at the target read. -/
theorem readWordOfWalk {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (kind : MmaCuQGroup) {g : Nat} (hg : g < l.threads) :
    ∀ {s : TState} {first : Nat} {events : List Event} {visits : List Visit}
      {a : Acc} {bytes : List (Option Byte)},
      first ≤ p.batch → At s kind.site.head (kind.facts p l g first) →
      Walk kernel Assumptions.all l g s events visits →
      readEvent kind a bytes ∈ events →
      ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase+4*index),size := 4} := by
  intro s first events visits a bytes hFirst hs hw ht
  let cta := g/l.block
  have hCTA : cta+1 < 2^31 := (Nat.succ_le_of_lt
    ((Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).mpr hg)).trans_lt hp.grid.2.2
  have hBatch := hp.shape.2.1
  have hBatchRoom := hp.shape.2.2.2.2.2
  generalize hFuel : visits.length = fuel
  induction fuel using Nat.strong_induction_on generalizing s first events visits with
  | h fuel ih =>
    obtain ⟨v,hVRun,hV⟩ := advanceGroupScanPreserving kind.scan
      (show first+31 < 2^31 by omega) hBatch (advanceFrame kind) hs
    rcases advanceWalkLocals hVRun hw with hEmpty | ⟨vvis,hVLen,_,hVW⟩
    · exact (isNotEmpty ht hEmpty).elim
    let next := first+31
    by_cases hClip : p.batch ≤ next
    · have hOut : At v kind.site.compare
        [(kind.site.work,b32 (cta+1)),(kind.site.cta,b32 cta)] := by
        rw [ite_eq_left hClip] at hV
        exact hV.mono ⟨hV.2.2.2.2.2.1,hV.2.2.2.2.2.2.2.2.2.1,trivial⟩
      obtain ⟨u,hExit,hU⟩ := exhaustedGroupScan kind.scan hCTA hOut
      rcases advanceWalkLocals hExit hVW with hEmpty | ⟨_,_,_,hUW⟩
      · exact (isNotEmpty ht hEmpty).elim
      exact (noReadAfterGroup kind hUW hU.1.ge ht).elim
    have hNext : next < p.batch := Nat.lt_of_not_ge hClip
    have hAt : At v (kind.site.head+5) ((kind.site.advanced,b32 next)::kind.facts p l g next) := by
      rw [ite_eq_right hClip,Nat.min_eq_left hNext.le] at hV
      exact hV.mono ⟨hV.2.2.2.2.1,hV.2.2.2.2.2.2⟩
    obtain ⟨u,hGate,hU⟩ := readGate hp kind hNext.le hAt
    rcases advanceWalkLocals hGate hVW with hEmpty | ⟨uvis,hULen,_,hUW⟩
    · exact (isNotEmpty ht hEmpty).elim
    have hScan {r : TState} {rest : List Event} {rvis : List Visit}
        (hSmall : rvis.length ≤ uvis.length) (hStart : r.pc = kind.readSite+1)
        (hAt : At r r.pc (kind.facts p l g next))
        (hW : Walk kernel Assumptions.all l g r rest rvis)
        (hMem : readEvent kind a bytes ∈ rest) :
        ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase+4*index),size := 4} := by
      have hBodyHi : kind.readSite+1 ≤ kind.site.compare+2 := by cases kind <;> decide
      obtain ⟨r',rest',rvis',hLen,hR,hRW,hFound⟩ :=
        loopBodyToBackedge kind hW hMem hStart.ge (hStart.symm ▸ hBodyHi) hAt
      exact ih rvis'.length (by omega) hNext.le hR hRW hFound rfl
    by_cases hi : next+laneOf l g ≤ p.batch
    · rw [ite_eq_right (Nat.not_lt_of_ge hi)] at hU
      obtain ⟨r,hAddress,hR,hOut⟩ := readAddress hp kind hi hU
      rcases advanceWalkLocals hAddress hUW with hEmpty | ⟨rvis,hRLen,_,hRW⟩
      · exact (isNotEmpty ht hEmpty).elim
      cases hRW with
      | stop => cases ht
      | tau he _ => cases hOut.symm.trans he
      | last he =>
        obtain ⟨_,_,hEnd⟩ := emittedRead hOut he
        cases hEnd
      | @ev r r' e rest rvis' he hTail =>
        obtain ⟨data,hE,hState⟩ := emittedRead hOut he
        rcases List.mem_cons.mp ht with hHere | hLater
        · have hAcc := (Kind.rd.inj (congrArg Event.kind (hHere.trans hE))).1
          exact ⟨next+laneOf l g,hi,hAcc⟩
        have lo : kind.site.head+5 ≤ kind.readSite := by cases kind <;> decide
        have hi' : kind.readSite < kind.site.compare+2 := by cases kind <;> decide
        obtain ⟨hProg | hFault,hSub,hAcc,hRegs⟩ :=
          scanBodyEvent kind.scan (hR.1.symm ▸ lo) (hR.1.symm ▸ hi') hR.2.1 hR.2.2.1 he
        · have hKeep := bodyFrame kind (hR.1.symm ▸ lo) (hR.1.symm ▸ hi'.le)
            (.inr ⟨_,rfl,he⟩) hRegs hR.2.2.2.2
          exact hScan (by simp at hRLen; omega) (hProg.1.trans (congrArg (·+1) hR.1))
            ⟨rfl,hSub,hAcc,hProg.2.trans hR.2.2.2.1,hKeep⟩ hTail hLater
        · exact (readImpossibleWithFault kind hTail hFault.2 hLater).elim
    · rw [ite_eq_left (Nat.lt_of_not_ge hi)] at hU
      exact hScan le_rfl hU.1
        ⟨rfl,hU.2.1,hU.2.2.1,hU.2.2.2.1,hU.2.2.2.2.2⟩ hUW ht

end PTX.Kernels.TmlFa4Fwd.Thread.Allocation.MmaCuQGroup
