-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueStartupUnique
public import Kernels.TmlFa4Fwd.Proof.PrologueNonzeroTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Lemmas.Flow.ElectActor
public import Lemmas.Flow.NotInit
public import Lemmas.Flow.ContinuingEvent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Flow PTX.Proof PTX.EventFrame

private def initSitePcs : List Nat := (List.finRange 34).map (fun i => (initSite i).pc)

private theorem initSitesCoverCode :
    kernel.code.zipIdx.all (fun (i, pc) => !initOp i.op || initSitePcs.contains pc) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

/-- An actual mbarrier initialization event occurs at one of the 34 decoded prologue sites. -/
theorem actualInitSite {l : Launch} {A : List Assumption} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel A m X) {e : EvId} {pc cnt : Nat} {loc : Loc}
    (he : X.get e = some ⟨pc, .mbInit loc cnt⟩) :
    ∃ i : Fin 34, (initSite i).pc = pc := by
  rcases get_source hX he with ⟨_, h⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases h
  have hCode := List.all_eq_true.mp initSitesCoverCode _ (List.mk_mem_zipIdx_iff_getElem?.mpr hc)
  have hOp : initOp ins.op = true := by
    cases h : initOp ins.op
    · exact (notInit_of_op h hf loc cnt rfl).elim
    · rfl
  have hMem : pc ∈ initSitePcs := by
    apply List.contains_iff_mem.mp
    simpa only [hOp, Bool.not_true, Bool.false_or] using hCode
  obtain ⟨i, _, hEq⟩ := List.mem_map.mp hMem
  exact ⟨i, hEq⟩

private theorem initializerRange (i : Fin 34) :
    36 ≤ (initSite i).pc ∧ (initSite i).pc < 172 := by
  fin_cases i <;> decide

private theorem initAfterBroadcasts {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g j cnt : Nat}
    (hg : g < l.threads) {loc : Loc} (site : Fin 34)
    (he : X.get (g, j) = some ⟨(initSite site).pc, .mbInit loc cnt⟩) : 3 ≤ j := by
  by_contra hn
  have hBound : j < 3 := by omega
  interval_cases j
  · exact Kind.noConfusion (congrArg Event.kind (firstSharedValue hp hX g hg he))
  · exact Kind.noConfusion (congrArg Event.kind (secondWarpValue hp hX g hg he))
  · exact Kind.noConfusion (congrArg Event.kind (thirdWarpValue hp hX g hg he))

/-- Only warp zero can issue an initialization, even if the execution ends in startup. -/
theorem actualInitWarpZero {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g j pc cnt : Nat}
    (hg : g < l.threads) {loc : Loc} (he : X.get (g, j) = some ⟨pc, .mbInit loc cnt⟩) :
    warpIndex l g = 0 := by
  obtain ⟨site, rfl⟩ := actualInitSite hX he
  have hRange := initializerRange site
  by_contra hWarp
  have hFirst := initAfterBroadcasts hp hX hg site he
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have h0 : 0 < (X.tr g).length := by omega
  have h1 : 1 < (X.tr g).length := by omega
  have h2 : 2 < (X.tr g).length := by omega
  have hTrace : X.tr g = (X.tr g)[0] :: (X.tr g)[1] :: (X.tr g)[2] :: (X.tr g).drop 3 := by
    have h0' := List.drop_eq_getElem_cons h0
    have h1' := List.drop_eq_getElem_cons h1
    rw [List.drop_eq_getElem_cons h2] at h1'
    rw [h1'] at h0'
    exact h0'
  obtain ⟨t, o, hPc, hFault, hBase, hIndex, _, _, _, hr⟩ := broadcastPrefix hp hX g hg hTrace
  obtain ⟨s, hs, hSPc, _⟩ := nonzeroWarpWith (A := Assumptions.all) hp g (warpIndex l g) t
    (by omega) (warpIndex_lt hp g) hPc hFault hIndex hBase
  have hGet : ((X.tr g).drop 3)[j-3]? = some ⟨(initSite site).pc, .mbInit loc cnt⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hFirst]
    exact he
  have hMem := List.mem_of_getElem? hGet
  have hSuffix := hr.after_local_nonempty (run_rtg hs) (by
    intro hn
    simp [hn] at hMem)
  have hLower := runAtOrPastStartupPc (by decide : 172 ≤ 174) hSPc.ge hSuffix _ hMem
  change 172 ≤ (initSite site).pc at hLower
  omega

private theorem afterInitializer {l : Launch} {g pc cnt : Nat} {s u : TState} {loc : Loc}
    (he : EStep kernel Assumptions.all l g s ⟨pc, .mbInit loc cnt⟩ (some u)) :
    u.pc = pc+1 := by
  have hPc : s.pc = pc := (estep_source_pc he).symm
  obtain ⟨i, _, _, hf⟩ := estep_event_source he
  have hInit : initOp i.op = true := by
    cases h : initOp i.op
    · exact (notInit_of_op h hf loc cnt rfl).elim
    · rfl
  have hAdv : AdvancesOp i.op := by
    cases hOp : i.op <;> simp only [hOp, initOp, Bool.false_eq_true] at hInit
    trivial
  rw [fires_next hAdv hf]
  exact congrArg (·+1) hPc

private theorem initPcOneIndex {l : Launch} {g pc : Nat} {s : TState}
    {events : List Event} {o : Option TState} (hPc : pc < 174)
    (hr : Run kernel Assumptions.all l g s events o) :
    ∀ (i j : Nat) (a b : Loc) (na nb : Nat), i < j →
      events[i]? = some ⟨pc, .mbInit a na⟩ → events[j]? = some ⟨pc, .mbInit b nb⟩ → False := by
  induction hr with
  | nil => simp
  | step _ he hRest ih =>
    intro i j a b na nb hLt hi hj
    cases j with
    | zero => omega
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        rw [hi] at he
        have hAfter := afterInitializer he
        have hBad := runAtOrPastStartupPc (by omega : pc+1 ≤ 174) hAfter.ge hRest
          _ (List.mem_of_getElem? hj)
        change pc+1 ≤ pc at hBad
        omega
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi
        exact ih i j a b na nb (by omega) hi hj
  | last _ _ =>
    intro i j a b na nb hLt hi hj
    have h := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_cons, List.length_nil] at h
    omega

/-- Each initializer instruction can occur at most once on a lane's actual trace. -/
theorem actualInitPcUnique {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i j pc na nb : Nat} {a b : Loc}
    (hg : g < l.threads) (hi : X.get (g, i) = some ⟨pc, .mbInit a na⟩)
    (hj : X.get (g, j) = some ⟨pc, .mbInit b nb⟩) : i = j := by
  obtain ⟨site, hSite⟩ := actualInitSite hX hi
  have hRange := initializerRange site
  have hPc : pc < 174 := by omega
  obtain ⟨_, hr⟩ := hX.thr g hg
  rcases lt_trichotomy i j with h | h | h
  · exact (initPcOneIndex hPc hr i j a b na nb h hi hj).elim
  · exact h
  · exact (initPcOneIndex hPc hr j i b a nb na h hj hi).elim

private theorem initGroupCover (i : Fin 34) : ∃ j : Fin 16, i ∈ initGroup j := by
  fin_cases i <;> decide

/-- Every recorded initializer has its decoded object and count, and is issued by the actual
leader of its warp-zero election. The trace can end at the initializer itself. -/
theorem actualInitializer {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g j pc cnt : Nat}
    (hg : g < l.threads) {loc : Loc} (he : X.get (g, j) = some ⟨pc, .mbInit loc cnt⟩) :
    ∃ (site : Fin 34) (round : Fin 16) (e inst : Nat),
      loc = initObject l (g/l.block) site ∧ cnt = (initSite site).count ∧ pc = (initSite site).pc ∧
      warpIndex l g = 0 ∧
      X.Elect (g, e) (electSite round).pc (2^32-1) inst (laneOf l g) := by
  obtain ⟨site, rfl⟩ := actualInitSite hX he
  have hWarp := actualInitWarpZero hp hX hg he
  have hFirst := initAfterBroadcasts hp hX hg site he
  have hJ : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hAvail (n : Nat) (q : Nat) (hBound : q ≤ (initSite site).pc)
      (hEarlier : EarlierEvents X g n q) : n ≤ j := by
    by_contra hn
    have hBad := hEarlier j (by omega) _ he
    change (initSite site).pc < q at hBad
    omega
  obtain ⟨round, hRound⟩ := initGroupCover site
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hRound
  have hGroupPc := (groupCode round k site hk).1
  have hStartPc : initRoundPc round.val = (electSite round).pc := dite_eq_left round.isLt
  have hRoundPc : initRoundPc round.val ≤ (initSite site).pc := by rw [hStartPc, hGroupPc]; omega
  obtain ⟨n, s, hn, _, hCur, hAt, hEarlier, _⟩ :=
    prefixInitRound hp hX hg hWarp (by omega)
      (fun n _ q hBound hpast => lt_of_le_of_lt (hAvail n q hBound hpast) hJ)
      round.val (by omega) hRoundPc
  rw [hStartPc] at hAt hEarlier
  have hStart : n ≤ j := hAvail n _ (by omega) hEarlier
  have hCursor : InitElectCursor l X g n round s :=
    ⟨hCur, hAt.1, hAt.2.2.2.1, hEarlier, fun hn => (by omega : False).elim⟩
  have hTake : k+1 ≤ (initGroup round).length := (List.getElem?_eq_some_iff.mp hk).1
  have hIssuer : InitIssuerOn l X g (fun _ => True) (· ∈ (initGroup round).take (k+1)) := by
    intro i index t hi _ hC _ hPrev _ hPc hFault hBase hCount
    obtain ⟨u, hu⟩ := List.mem_iff_getElem?.mp hi
    have hLength := (List.getElem?_eq_some_iff.mp hu).1
    simp only [List.length_take, Nat.min_eq_left hTake] at hLength
    rw [List.getElem?_take_of_lt hLength] at hu
    have hI := (groupCode round u i hu).1
    exact initializerAtCursor hp i hC
      (lt_of_le_of_lt (hAvail index _ (by omega) hPrev) hJ) hPc hFault hBase hCount
  obtain ⟨inst, leader, t, hElect, hAfter, hState, _, _, hGet⟩ :=
    initGroupPrefixUsing hTake hIssuer (by simp) hCursor hAt (by omega)
  by_cases hLeader : laneOf l g = leader
  · have hSiteEvent := hGet hLeader k (by omega) site hk
    have hOther : X.get (g, n+1+k) =
        some ⟨(initSite site).pc, .mbInit (initObject l (g/l.block) site) (initSite site).count⟩ :=
      hSiteEvent
    have hSame := actualInitPcUnique hX hg he hOther
    rw [hSame, hOther] at he
    obtain ⟨hLoc, hCount⟩ := Kind.mbInit.inj (congrArg Event.kind (Option.some.inj he.symm))
    exact ⟨site, round, n, inst, hLoc, hCount, rfl, hWarp, hLeader.symm ▸ hElect⟩
  · simp only [hLeader, ↓reduceIte, Nat.add_zero] at hAfter hState
    have hN : n < j := by
      by_contra hNo
      have hEq : n = j := by omega
      change X.get (g, n) = some ⟨(electSite round).pc, .elect (2^32-1) inst leader⟩ at hElect
      rw [hEq, he] at hElect
      exact Kind.noConfusion (congrArg Event.kind (Option.some.inj hElect))
    have hTail : ((X.tr g).drop (n+1))[j-(n+1)]? =
        some ⟨(initSite site).pc, .mbInit loc cnt⟩ := by
      rw [List.getElem?_drop, Nat.add_sub_of_le (by omega)]
      exact he
    have hMem := List.mem_of_getElem? hTail
    obtain ⟨_, u, _, hLocal, o, hRun⟩ := hAfter
    have hMoved := hRun.after_local_nonempty hLocal (fun hEmpty => by simp [hEmpty] at hMem)
    have hLt := initializerRange site
    have hSkip := groupExit round
    have hBad := runAtOrPastStartupPc (by omega : (initSite site).pc+1 ≤ 174)
      (by rw [hState.1, hSkip, hGroupPc]; omega) hMoved _ hMem
    change (initSite site).pc+1 ≤ (initSite site).pc at hBad
    omega

/-- In any consistent execution, including an unfinished one, an mbarrier object can have
at most one initialization record. Its arrival count is unique as well. -/
theorem actualInitializerUnique {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {e f : EvId}
    {loc : Loc} {cnt other : Nat} (he : X.MbInit e loc cnt) (hf : X.MbInit f loc other) :
    e = f ∧ cnt = other := by
  obtain ⟨g, i⟩ := e
  obtain ⟨h, j⟩ := f
  obtain ⟨pc, he⟩ := he
  obtain ⟨qc, hf⟩ := hf
  have hg : g < l.threads := by
    by_contra hn
    have hEmpty := hX.outside g (by omega)
    simp [Execution.get, hEmpty] at he
  have hh : h < l.threads := by
    by_contra hn
    have hEmpty := hX.outside h (by omega)
    simp [Execution.get, hEmpty] at hf
  obtain ⟨a, r, n, ni, hLocA, hCntA, hPcA, hWarpA, hElectA⟩ := actualInitializer hp hX hg he
  obtain ⟨b, s, k, ki, hLocB, hCntB, hPcB, hWarpB, hElectB⟩ := actualInitializer hp hX hh hf
  have hObject := hLocA.symm.trans hLocB
  have hCta : g/l.block = h/l.block := congrArg Loc.cta hObject
  rw [← hCta] at hObject
  have hSite : a = b := by
    by_contra hn
    exact initObject_ne hn hObject
  subst b
  have hSame : SameWarp l g h := ⟨⟨hg, hh, hCta⟩, hWarpA.trans hWarpB.symm⟩
  have hLeader := hX.elect.2.2 _ _ _ _ _ _ _ _ _ hElectA hElectB hSame
  have hThread := sameWarp_eq_of_lane_eq hSame hLeader
  subst h
  rw [hPcA] at he
  rw [hPcB] at hf
  exact ⟨congrArg (g, ·) (actualInitPcUnique hX hg he hf), hCntA.trans hCntB.symm⟩

end PTX.Kernels.TmlFa4Fwd.Prologue
