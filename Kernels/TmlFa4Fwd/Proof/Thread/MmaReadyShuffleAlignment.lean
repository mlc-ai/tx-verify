-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal
public import Kernels.TmlFa4Fwd.Proof.MmaReleaseOrdinals
public import Lemmas.Flow.PollSynced
import Lemmas.Flow.PollRendezvous
import Lemmas.Order.ElectSiteOrdinal
import Kernels.TmlFa4Fwd.Proof.Thread.MmaShuffleOrdinal
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Mma

private theorem fullMember (l : Launch) (g : Nat) : electMember (2^32-1) (laneOf l g) := by
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  exact ⟨hLane,by rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hLane⟩

private theorem sitesBeforeShuffleLe {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (sites : Nat → Bool)
    {g h i j rank : Nat} (hWarp : SameWarp l g h)
    (ha : X.ShflK (g,i) rank) (hb : X.ShflK (h,j) rank) :
    ElectOrd.siteOrdinal sites X g i ≤ ElectOrd.siteOrdinal sites X h j := by
  let n := ElectOrd.siteOrdinal sites X h j
  by_contra! hCount
  have hBound : n < ((X.tr g).take i).countP (ElectOrd.atSites sites) := hCount
  obtain ⟨a,haBefore,ev,hEv,hMark,hOrd⟩ := Flow.exists_nth (ElectOrd.atSites sites)
    (X.tr g) (n := n) (k := i) hBound
  obtain ⟨site,mask,inst,leader,rfl⟩ :
      ∃ site mask inst leader, ev = ⟨site,.elect mask inst leader⟩ := by
    obtain ⟨pc,k⟩ := ev
    cases k <;> simp_all only [ElectOrd.atSites,isElectEv,Bool.false_and,Bool.false_eq_true,
      Bool.true_and]
    exact ⟨_,_,_,_,rfl⟩
  have he : X.Elect (g,a) site mask inst leader := hEv
  have hFull := Thread.actualFullElectionMask hX he
  obtain ⟨b,hPeer⟩ := ElectOrd.partner hX hWarp he (hFull.symm ▸ fullMember l h)
  have hParts := hPeer
  obtain ⟨site₁,site₂,mask₁,mask₂,label,lead₁,lead₂,hLeft,hRight⟩ := hParts
  have hSite : site₁ = site :=
    congrArg Event.pc (Option.some.inj (hLeft.symm.trans hEv))
  have hSame := (hX.elect.2.1 _ _ _ _ _ _ _ _ _ hLeft hRight hWarp).1
  have hMarked : ElectOrd.atSites sites ⟨site₂,.elect mask₂ label lead₂⟩ = true := by
    rw [← hSame,hSite]
    simpa only [ElectOrd.atSites,isElectEv,Bool.true_and] using hMark
  have hRightBefore : b < j := by
    by_contra! hBad
    have hMate := hb
    obtain ⟨⟨pc,mode,x,y,z,recv,ok,hShfl⟩,_⟩ := hMate
    have hNe : b ≠ j := by
      rintro rfl
      cases congrArg Event.kind (Option.some.inj (hRight.symm.trans hShfl))
    have hEarlier : j < b := by omega
    have hA : DepStep l kernel X (.thread (g,a),true) (.thread (g,i),false) :=
      DepStep.of_resumes l (Resumes.of_blocking (b := true) hEv rfl ⟨rfl,haBefore,ha.lt⟩)
    have hSh : DepStep l kernel X (.thread (g,i),false) (.thread (h,j),true) :=
      DepStep.of_witness l (shfl_witness hX hWarp ha hb)
    have hB : DepStep l kernel X (.thread (h,j),true) (.thread (h,b),false) :=
      DepStep.of_resumes l (Resumes.of_blocking (b := true) hShfl rfl
        ⟨rfl,hEarlier,ElectOrd.lt_len hRight⟩)
    have hE := ElectOrd.depStep hX (sameWarp_symm hWarp)
      (show ElectOrd.Partner X (h,b) (g,a) from hPeer.symm)
    exact hX.depStepAcyclic _ (((Relation.TransGen.single hA).tail hSh).tail hB |>.tail hE)
  have hOrd' := ElectOrd.siteOrdinal_eq hX sites hWarp
    (fun _ _ _ _ _ _ hh => (Thread.actualFullElectionMask hX hh).symm ▸ fullMember l h)
    (fun _ _ _ _ _ _ hg => (Thread.actualFullElectionMask hX hg).symm ▸ fullMember l g) hPeer
  have hNext := countP_take_succ hRight hMarked
  have hMono := countP_take_mono (ElectOrd.atSites sites) (X.tr h)
    (show b+1 ≤ j by omega)
  change ((X.tr g).take a).countP (ElectOrd.atSites sites) =
    ((X.tr h).take b).countP (ElectOrd.atSites sites) at hOrd'
  dsimp only [n,ElectOrd.siteOrdinal] at hOrd
  omega

/-- Matching shuffles cut the same elections at any selected sites. A crossing
between a matching shuffle and a matching election would create a dependency cycle. -/
theorem electionSitesAtMatchedShuffle {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (sites : Nat → Bool)
    {g h i j rank : Nat} (hWarp : SameWarp l g h)
    (ha : X.ShflK (g,i) rank) (hb : X.ShflK (h,j) rank) :
    ElectOrd.siteOrdinal sites X g i = ElectOrd.siteOrdinal sites X h j :=
  Nat.le_antisymm (sitesBeforeShuffleLe hX sites hWarp ha hb)
    (sitesBeforeShuffleLe hX sites (sameWarp_symm hWarp) hb ha)

private theorem readyProjectionCount (events : List Event) :
    (events.filterMap readyEvent).length = events.countP (readyAtSite 0) +
      events.countP (readyAtSite 1) + events.countP (readyAtSite 2) +
      events.countP (readyAtSite 3) := by
  induction events with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.filterMap_cons,List.countP_cons]
    obtain ⟨pos,kind⟩ := e
    cases kind <;> simp only [readyEvent,readyAtSite] <;> try exact ih
    case wait loc parity ok acquire scope =>
      cases ok
      · exact ih
      have hHead : (List.finRange 4).any (fun i => readyHead i == pos) =
        (2145 == pos || 2294 == pos || 2352 == pos || 2545 == pos) := by
        simp [List.finRange,List.ofFn_succ,readyHead,Bool.or_assoc]
      simp only [hHead,show (slotWait 0).pc = 2145 from rfl,
        show (slotWait 1).pc = 2294 from rfl,show (slotWait 2).pc = 2352 from rfl,
        show (slotWait 3).pc = 2545 from rfl]
      by_cases hA : pos = 2145
      · subst pos; simp; omega
      by_cases hB : pos = 2294
      · subst pos; simp; omega
      by_cases hC : pos = 2352
      · subst pos; simp; omega
      by_cases hD : pos = 2545
      · subst pos; simp; omega
      simp [hA,hB,hC,hD,Ne.symm hA,Ne.symm hB,Ne.symm hC,Ne.symm hD,ih]

/-- Matching shuffles at the same station have the same ready cursor, regardless of
how many unsuccessful polls the lanes took on their way there. -/
theorem readyUsesAtMatchedShuffle {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g h i j rank site : Nat} (hWarp : SameWarp l g h)
    {a b : Event} (ha : X.ShflK (g,i) rank) (hb : X.ShflK (h,j) rank)
    (hA : X.get (g,i) = some a) (hB : X.get (h,j) = some b)
    (hSiteA : a.pc = site) (hSiteB : b.pc = site)
    (hBounds : 2145 ≤ site ∧ site < 2768)
    (hAvoid : ∀ r : Fin 4, site ≠ (slotWait r).pc + 1)
    (hg : Prologue.warpIndex l g = 12) (hh : Prologue.warpIndex l h = 12) :
    let x := atPrefix l X g i
    let y := atPrefix l X h j
    x.kvAcquires 0 + x.kvAcquires 1 + x.kvAcquires 2 =
      y.kvAcquires 0 + y.kvAcquires 1 + y.kvAcquires 2 := by
  dsimp only
  have hG := readyUsesAtPrefix hp hX (event_thread_lt hX hA) hg i
  have hH := readyUsesAtPrefix hp hX (event_thread_lt hX hB) hh j
  rw [← hG,← hH,readyProjectionCount,readyProjectionCount]
  have equal (r : Fin 4) :
      ((X.tr g).take i).countP (readyAtSite r) = ((X.tr h).take j).countP (readyAtSite r) := by
    rw [readyBalanceAtEvent hp hX r hA (hSiteA.symm ▸ hBounds.1) (hSiteA.symm ▸ hBounds.2)
          (hSiteA.symm ▸ hAvoid r),
        readyBalanceAtEvent hp hX r hB (hSiteB.symm ▸ hBounds.1) (hSiteB.symm ▸ hBounds.2)
          (hSiteB.symm ▸ hAvoid r),
        hSiteA,hSiteB,electionSitesAtMatchedShuffle hX _ hWarp ha hb]
  rw [equal 0,equal 1,equal 2,equal 3]

private theorem pollBeforeOfElectionCount {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (sites : Nat → Bool)
    {g h i j pc phase : Nat} {loc : Loc} {ok acq : Bool} {scope : MbarScope} {f : Event}
    (hw : SameWarp l g h) (he : X.get (g,i) = some ⟨pc,.wait loc phase ok acq scope⟩)
    (hf : X.get (h,j) = some f)
    (hCount : ElectOrd.siteOrdinal sites X g i < ElectOrd.siteOrdinal sites X h j) :
    PollBefore l kernel X (g,i) (h,j) := by
  let rank := ElectOrd.siteOrdinal sites X g i
  obtain ⟨b,hBefore,e,hGet,hSite,hRank⟩ :=
    Flow.exists_nth (ElectOrd.atSites sites) (X.tr h) (n := rank) (k := j) hCount
  obtain ⟨epc,mask,inst,leader,rfl⟩ :
      ∃ epc mask inst leader, e = ⟨epc,.elect mask inst leader⟩ := by
    obtain ⟨pos,kind⟩ := e
    cases kind <;> simp_all only [ElectOrd.atSites,isElectEv,Bool.false_and,Bool.false_eq_true,
      Bool.true_and]
    exact ⟨_,_,_,_,rfl⟩
  have hElect : X.Elect (h,b) epc mask inst leader := hGet
  obtain ⟨a,hPair⟩ := ElectOrd.partner hX (sameWarp_symm hw) hElect
    ((Thread.actualFullElectionMask hX hElect).symm ▸ fullMember l g)
  have hSameRank := ElectOrd.siteOrdinal_eq hX sites (sameWarp_symm hw)
    (fun _ _ _ _ _ _ hs => (Thread.actualFullElectionMask hX hs).symm ▸ fullMember l g)
    (fun _ _ _ _ _ _ hs => (Thread.actualFullElectionMask hX hs).symm ▸ fullMember l h) hPair
  have hParts := hPair
  obtain ⟨s₁,s₂,m₁,m₂,n,l₁,l₂,hLater,hEarlier⟩ := hParts
  have hFirst : s₁ = epc := congrArg Event.pc (Option.some.inj (hLater.symm.trans hGet))
  have hEqual := (hX.elect.2.1 _ _ _ _ _ _ _ _ _ hLater hEarlier (sameWarp_symm hw)).1
  have hMarked : ElectOrd.atSites sites ⟨s₂,.elect m₂ n l₂⟩ = true := by
    rw [← hEqual,hFirst]
    simpa only [ElectOrd.atSites,isElectEv,Bool.true_and] using hSite
  have hNE : a ≠ i := fun h => by
    subst a
    cases congrArg Event.kind (Option.some.inj (hEarlier.symm.trans he))
  have hAfter : i < a := by
    by_contra! hTooEarly
    have hStrict : a < i := (Nat.lt_of_le_of_ne hTooEarly hNE)
    have hStep := countP_take_succ hEarlier hMarked
    have hMono := countP_take_mono (ElectOrd.atSites sites) (X.tr g)
      (show a+1 ≤ i by omega)
    change ((X.tr h).take b).countP (ElectOrd.atSites sites) =
      ((X.tr g).take a).countP (ElectOrd.atSites sites) at hSameRank
    change ((X.tr h).take b).countP (ElectOrd.atSites sites) =
      ((X.tr g).take i).countP (ElectOrd.atSites sites) at hRank
    omega
  exact ⟨a,hAfter,.tail (.single (.inl (ElectOrd.depStep hX hw hPair.symm)))
    (.inl (ElectOrd.resumes hLater hBefore (len_of_get hf)))⟩

/-- MMA lanes reaching one cache gate either use the same object or are separated by
an actual release election. Retry polls use the same logical cursor as the successful poll. -/
theorem readyPollObjectsAgreeOrOrdered {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g h i j pc phase phase' : Nat} {a b : Loc} {ok ok' acq acq' : Bool} {scope scope' : MbarScope}
    (hw : SameWarp l g h) (hg : Prologue.warpIndex l g = 12)
    (he : X.get (g,i) = some ⟨pc,.wait a phase ok acq scope⟩)
    (hf : X.get (h,j) = some ⟨pc,.wait b phase' ok' acq' scope'⟩)
    (hGate : ∃ r : Fin 4, pc = readyHead r) :
    a = b ∨ PollBefore l kernel X (g,i) (h,j) ∨ PollBefore l kernel X (h,j) (g,i) := by
  by_cases hOrder :
      PollBefore l kernel X (g,i) (h,j) ∨ PollBefore l kernel X (h,j) (g,i)
  · exact .inr hOrder
  refine .inl ?_
  have hh : Prologue.warpIndex l h = 12 := by
    have hSame : Prologue.warpIndex l g = Prologue.warpIndex l h := hw.2
    rw [← hSame,hg]
  obtain ⟨_,ha⟩ := readyAttemptUseAtPrefix hp hX hg he hGate
  obtain ⟨_,hb⟩ := readyAttemptUseAtPrefix hp hX hh hf hGate
  have equal (r : Fin 4) :
      ((X.tr g).take i).countP (readyAtSite r) = ((X.tr h).take j).countP (readyAtSite r) := by
    obtain ⟨gate,hPc⟩ := hGate
    have hBounds : 2145 ≤ pc ∧ pc < 2768 :=
      hPc.symm ▸ (by decide : ∀ gate : Fin 4, 2145 ≤ readyHead gate ∧ readyHead gate < 2768) gate
    have hAvoid : pc ≠ (slotWait r).pc + 1 :=
      hPc.symm ▸ (by decide : ∀ a b : Fin 4, readyHead a ≠ (slotWait b).pc + 1) gate r
    rw [readyBalanceAtEvent hp hX r he hBounds.1 hBounds.2 hAvoid,
      readyBalanceAtEvent hp hX r hf hBounds.1 hBounds.2 hAvoid]
    let sites := fun n => n == (slotElect r).pc
    have hSame : ElectOrd.siteOrdinal sites X g i = ElectOrd.siteOrdinal sites X h j := by
      by_contra hNe
      rcases Nat.lt_or_gt_of_ne hNe with hLt | hGt
      · exact hOrder (.inl (pollBeforeOfElectionCount hX sites hw he hf hLt))
      · exact hOrder (.inr (pollBeforeOfElectionCount hX sites (sameWarp_symm hw) hf he hGt))
    rw [hSame]
  have hUse : (((X.tr g).take i).filterMap readyEvent).length =
      (((X.tr h).take j).filterMap readyEvent).length := by
    rw [readyProjectionCount,readyProjectionCount,equal 0,equal 1,equal 2,equal 3]
  have hCta : g / l.block = h / l.block := hw.1.2.2
  rw [hUse] at ha
  simp only [readyOperand,hCta] at ha
  exact congrArg Prod.fst (ha.trans hb.symm)


end PTX.Kernels.TmlFa4Fwd.Thread.Mma
