-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingCursor
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Proof.LoaderWarmIterationCursor
import Kernels.TmlFa4Fwd.Proof.LoaderSteadyIterationCursor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader
  (reuseArrival recurringPacketSite copyCommitCode copyCommitPc loaderOutCore
    packetArrivalStepFrame loaderPipelineCutOp prefixProjectedCutOrEvent packetPlanePc
    warmProjectedRoundOfObservedEvent steadyProjectedRoundOfObservedEvent
    loaderShuffleTail rankedLoaderStep LoaderRankedInstr)

noncomputable section

private def publicationSites : List Nat := [1137, 1342, 1602, 1735]

private def sitesFrom (stop pos : Nat) : Nat :=
  publicationSites.countP (fun n => pos ≤ n && n < stop)

private theorem endsProjection (stop : Nat) : sitesFrom stop stop = 0 := by
  apply List.countP_eq_zero.mpr
  intro n hn
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

private theorem sitesFromStep {pos stop : Nat} (hPos : pos < stop) :
    sitesFrom stop pos = (if publicationSites.contains pos then 1 else 0) +
      sitesFrom stop (pos + 1) := by
  unfold sitesFrom publicationSites
  by_cases h0 : pos = 1137
  · subst pos
    simp [List.countP_cons, hPos]
    omega
  by_cases h1 : pos = 1342
  · subst pos
    simp [List.countP_cons, hPos]
    omega
  by_cases h2 : pos = 1602
  · subst pos
    simp [List.countP_cons, hPos]
    omega
  by_cases h3 : pos = 1735
  · subst pos
    simp [hPos]
  have hAt (n : Nat) (h : pos ≠ n) : pos ≤ n ↔ pos + 1 ≤ n := by omega
  simp [List.countP_cons, h0, h1, h2, h3, hAt _ h0, hAt _ h1, hAt _ h2, hAt _ h3]

private theorem publicationSite {pos : Nat} (hp : publicationSites.contains pos = true) :
    ∃ site : Fin 4, pos = reuseArrival site := by
  have hMem := List.contains_iff_mem.mp hp
  simp only [publicationSites, List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with rfl | rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

private theorem siteList (site : Fin 4) : publicationSites.contains (reuseArrival site) = true := by
  fin_cases site <;> decide

private def rankEdge (stop pc : Nat) (op : Op) : Bool :=
  match op with
  | .bra target _ => sitesFrom stop pc == sitesFrom stop target
  | .brx .. => false
  | _ => true

private def rankWindow (start stop : Nat) : Prop :=
  (((kernel.code.drop start).take (stop - start)).zipIdx start).all
    (fun (i, pc) => rankEdge stop pc i.op) = true

private theorem branchRank {start stop pc : Nat} {i : Instr}
    (audit : rankWindow start stop) (hStart : start ≤ pc) (hStop : pc < stop)
    (hc : kernel.code[pc]? = some i)
    {target : Nat} (hn : target = nextPc i.op pc ∨ BrxTarget i.op target) :
    target = pc + 1 ∨ sitesFrom stop pc = sitesFrom stop target := by
  have hAt : (((kernel.code.drop start).take (stop - start)).zipIdx start)[pc - start]? =
      some (i, pc) := by
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hStart, hc]
    simp
  have hRank := List.all_eq_true.mp audit (i, pc) (List.mem_of_getElem? hAt)
  cases hop : i.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hn
  case bra dst uni =>
    subst target
    exact .inr (by simpa [rankEdge, hop] using hRank)
  case brx => simp [rankEdge, hop] at hRank
  all_goals exact .inl hn

private theorem publicationCountStep {l : Launch} {g start stop : Nat} {s u : TState}
    {ev : Option Event} (hRange : 174 ≤ start ∧ stop ≤ 1901)
    (hAudit : rankWindow start stop) (hStart : start ≤ s.pc) (hStop : s.pc < stop)
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    sitesFrom stop s.pc = ev.toList.countP recurringPublicationMark + sitesFrom stop u.pc := by
  have hOut := loaderOutCore (show 174 ≤ s.pc by omega) (show s.pc < 1906 by omega)
    (l := l) (g := g) (t := s)
  rcases hStep with ⟨rfl, hTau⟩ | ⟨e, rfl, he⟩
  · have hCore : Tau kernel [] l g s u := by
      unfold Tau at hTau ⊢
      rwa [← hOut]
    have hNo : publicationSites.contains s.pc = false := by
      apply Bool.eq_false_iff.mpr
      intro hSite
      obtain ⟨site, hp⟩ := publicationSite hSite
      have hCode := (copyCommitCode (recurringPacketSite site)).2
      change kernel.code[reuseArrival site]? = _ at hCode
      rw [← hp] at hCode
      exact tau_core_not_event hCode rfl hCore
    obtain ⟨i, hc⟩ := tau_core_has_code hCore
    have hNext : u.pc = s.pc + 1 ∨ sitesFrom stop s.pc = sitesFrom stop u.pc := by
      rcases tau_core_frame hc hCore with rfl | h
      · exact .inl rfl
      · exact branchRank hAudit hStart hStop hc h.pc
    rcases hNext with h | h
    · rw [sitesFromStep hStop, hNo, h]
      rfl
    · simpa using h
  · have hCore : EStep kernel [] l g s e (some u) := by
      obtain ⟨tmpl, ho, hf⟩ := he
      exact ⟨tmpl, hOut.symm.trans ho, hf⟩
    cases hSite : publicationSites.contains s.pc
    · have hNo : recurringPublicationMark e = false := by
        apply Bool.eq_false_iff.mpr
        intro hMark
        obtain ⟨site, _, rfl⟩ := (recurringPublicationMark_iff e).mp hMark
        have hp := estep_source_pc he
        change reuseArrival site = s.pc at hp
        rw [← hp, siteList site] at hSite
        cases hSite
      rcases (estep_return_pc hCore (fun _ _ _ h => execLocal_frame h)).2 with hp | hp
      · simp [hNo, hp]
      · rw [sitesFromStep hStop, hp, hSite]
        simp [hNo]
    · obtain ⟨site, hp⟩ := publicationSite hSite
      obtain ⟨target, hKind, rfl⟩ := packetArrivalStepFrame (recurringPacketSite site) hp he
      have hMark : recurringPublicationMark e = true := by
        apply (recurringPublicationMark_iff e).mpr
        refine ⟨site, target, ?_⟩
        cases e
        simp only [Event.mk.injEq]
        exact ⟨(estep_source_pc he).trans hp, hKind⟩
      rw [sitesFromStep hStop, hSite]
      simp [hMark, next]

/-- The loader's warm and steady loop cuts each delimit one K/V pair. -/
def cacheRoundStart (steady : Bool) : Nat := if steady then 1396 else 917

def cacheRoundStop (steady : Bool) : Nat := if steady then 1741 else 1348

/-- The number of recurring arrivals yet to issue in a checked warm or steady traversal. -/
@[no_expose] def cacheRoundRemaining (steady : Bool) (pc : Nat) : Nat :=
  sitesFrom (cacheRoundStop steady) pc

private theorem projectedRoundStep (steady : Bool) {l : Launch} {g : Nat} {s u : TState}
    {event : Option Event} (hLo : cacheRoundStart steady ≤ s.pc)
    (hHi : s.pc < cacheRoundStop steady) (hStep : WStep kernel Assumptions.all l g s event u) :
    cacheRoundRemaining steady s.pc =
      event.toList.countP recurringPublicationMark + cacheRoundRemaining steady u.pc :=
  publicationCountStep
    (by cases steady <;> decide : 174 ≤ cacheRoundStart steady ∧ cacheRoundStop steady ≤ 1901)
    (by cases steady <;> set_option maxRecDepth 100000 in kernel_rfl) hLo hHi hStep

/-- Select the cache publication or warp shuffle projection of the same loader walk. -/
def cacheRoundMark (shuffles : Bool) : Event → Bool :=
  if shuffles then Execution.isShfl else recurringPublicationMark

/-- The two projections retain their own decoded suffix counts. -/
def cacheRoundProjection (steady shuffles : Bool) (pc : Nat) : Nat :=
  if shuffles then loaderShuffleTail (cacheRoundStop steady) pc else cacheRoundRemaining steady pc

theorem cacheRoundProjectionStop (steady shuffles : Bool) :
    cacheRoundProjection steady shuffles (cacheRoundStop steady) = 0 := by
  cases shuffles
  · exact endsProjection _
  · simp [cacheRoundProjection,loaderShuffleTail]

theorem cacheRoundProjectionStart (steady shuffles : Bool) :
    cacheRoundProjection steady shuffles (cacheRoundStart steady) = if shuffles then 64 else 2 := by
  cases steady <;> cases shuffles <;> set_option maxRecDepth 100000 in kernel_rfl

/-- Each real step preserves both suffix projections. -/
theorem cacheRoundProjectionStep (steady : Bool) {l : Launch} {g : Nat} {s u : TState}
    {event : Option Event} (hLo : cacheRoundStart steady ≤ s.pc)
    (hHi : s.pc < cacheRoundStop steady) (hStep : WStep kernel Assumptions.all l g s event u)
    (shuffles : Bool) :
    cacheRoundProjection steady shuffles s.pc =
      event.toList.countP (cacheRoundMark shuffles) +
        cacheRoundProjection steady shuffles u.pc := by
  cases shuffles
  · exact projectedRoundStep steady hLo hHi hStep
  · have hCode : (((kernel.code.drop (cacheRoundStart steady)).take
          (cacheRoundStop steady-cacheRoundStart steady)).zipIdx (cacheRoundStart steady)).all
        (fun (ins,pc) => LoaderRankedInstr (cacheRoundStop steady) pc ins) = true := by
      cases steady <;> set_option maxRecDepth 100000 in kernel_rfl
    have hRange : 174 ≤ cacheRoundStart steady ∧
        cacheRoundStart steady ≤ cacheRoundStop steady ∧ cacheRoundStop steady ≤ 1901 := by
      cases steady <;> decide
    exact rankedLoaderStep hRange hCode hLo hHi hStep

-- A K vector precedes both publications in its own traversal.
theorem keyProjectionAtCopy (steady : Bool) (pair : Fin 16) (upper : Bool) :
    let site : Fin 4 := if steady then 2 else 0
    let pc := packetPlanePc (recurringPacketSite site) pair upper
    cacheRoundRemaining steady pc = 2 ∧
      loaderShuffleTail (cacheRoundStop steady) pc + (2*pair.val+2) = 64 := by
  cases steady <;> fin_cases pair <;> cases upper <;>
    set_option maxRecDepth 100000 in decide +kernel

/-- A V vector precedes just the V publication of its traversal. -/
theorem valueProjectionAtCopy (steady : Bool) (pair : Fin 16) (upper : Bool) :
    let site : Fin 4 := if steady then 3 else 1
    let pc := packetPlanePc (recurringPacketSite site) pair upper
    cacheRoundRemaining steady pc = 1 ∧
      loaderShuffleTail (cacheRoundStop steady) pc + (2*pair.val+2) = 32 := by
  cases steady <;> fin_cases pair <;> cases upper <;>
    set_option maxRecDepth 100000 in decide +kernel

private theorem cacheRoundRemainingPositive (steady : Bool) {event : Event}
    (he : recurringVectorEvent event)
    (hLo : cacheRoundStart steady ≤ event.pc) (hHi : event.pc < cacheRoundStop steady) :
    0 < cacheRoundRemaining steady event.pc := by
  obtain ⟨site, pair, upper, spec, rfl⟩ := he
  have hAudit : ∀ (s : Bool) (site : Fin 4) (pair : Fin 16) (upper : Bool),
      let pos := packetPlanePc (recurringPacketSite site) pair upper
      cacheRoundStart s ≤ pos → pos < cacheRoundStop s → 0 < cacheRoundRemaining s pos := by
    decide +kernel
  exact hAudit steady site pair upper hLo hHi

/-- An issued recurring publication is included in the remaining round count. -/
theorem cacheRoundArrivalRemainingPositive (steady : Bool) {event : Event}
    (he : recurringPublicationMark event = true)
    (hLo : cacheRoundStart steady ≤ event.pc) (hHi : event.pc < cacheRoundStop steady) :
    0 < cacheRoundRemaining steady event.pc := by
  obtain ⟨site, _, rfl⟩ := (recurringPublicationMark_iff event).mp he
  have audit : ∀ (s : Bool) (site : Fin 4),
      cacheRoundStart s ≤ reuseArrival site → reuseArrival site < cacheRoundStop s →
        0 < cacheRoundRemaining s (reuseArrival site) := by decide
  exact audit steady site hLo hHi

variable {l : Launch} {X : Execution} {g index round bound : Nat}

/-- The warm traversal's recorded cache event belongs to one of two
current-generation packets and is limited by the warm count. -/
theorem warmCacheUseBoundOfEntry (warp : Fin 2) (hTrip : bound < 2 ^ 31)
    (hRound : round < min bound 9) {s : TState} {ending : Option TState} {F : List (Nat × Value)}
    (hShared : (2535, b32 l.sharedBase) ∈ F) (hWarp : (1062, b32 (14 + warp.val)) ∈ F)
    (hBody : ∀ n, ((kernel.code.drop 917).take (1348 - 917)).all
      (fun ins => loaderPipelineCutOp 917 1348 n
        ([7174, 1091] ++ F.map Prod.fst) ins.op) = true)
    (hTail : ((kernel.code.drop 1348).take 4).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 917 ([(7174, b32 round), (1091, b32 bound)] ++ F))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hCursor : recurringUseBefore X (g, index) = 2 * (round + 1)) {j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hBefore : index ≤ j)
    (hEvent : recurringVectorEvent e ∨ recurringPublicationMark e = true) (hLo : 917 ≤ e.pc)
    (hHi : e.pc < 1348) :
    recurringUseBefore X (g, j) < 2 * (min bound 9 + 1) := by
  have hSafe : ∀ fault, e.kind ≠ .ub fault := by
    rcases hEvent with ⟨_, _, _, _, rfl⟩ | hMark
    · exact fun _ h => by cases h
    · obtain ⟨_, _, rfl⟩ := (recurringPublicationMark_iff e).mp hMark
      exact fun _ h => by cases h
  obtain ⟨iteration, hOrder, hLimit, hCount⟩ :=
    warmProjectedRoundOfObservedEvent warp hTrip hRound hShared hWarp hBody hTail
      (cacheRoundRemaining false) recurringPublicationMark (endsProjection 1348)
      (projectedRoundStep false) hs hr he hBefore hHi hSafe
  dsimp only [recurringUseBefore] at hCursor ⊢
  have hCap : cacheRoundRemaining false 917 = 2 := by decide
  rw [hCap] at hCount
  have hWithin := hEvent.elim (fun h => cacheRoundRemainingPositive false h hLo hHi)
    (fun h => cacheRoundArrivalRemainingPositive false h hLo hHi)
  omega

/-- The steady loop uses the same request-relative cursor once its warm prefix
has published the earlier pairs. -/
theorem steadyCopyUseBoundOfEntry (warp : Fin 2) (hTrip : bound < 2 ^ 31) (hRound : round < bound)
    {s : TState} {ending : Option TState} {F : List (Nat × Value)}
    (hShared : (2535, b32 l.sharedBase) ∈ F) (hWarp : (1062, b32 (14 + warp.val)) ∈ F)
    (hBody : ∀ n, ((kernel.code.drop 1396).take (1741 - 1396)).all
      (fun ins => loaderPipelineCutOp 1396 1741 n
        ([7181, 1091] ++ F.map Prod.fst) ins.op) = true)
    (hTail : ((kernel.code.drop 1741).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 1396 ([(7181, b32 round), (1091, b32 bound)] ++ F))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hCursor : recurringUseBefore X (g, index) ≤ 2 * (round + 1)) {j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hBefore : index ≤ j) (hVector : recurringVectorEvent e)
    (hLo : 1396 ≤ e.pc) (hHi : e.pc < 1741) :
    recurringUseBefore X (g, j) < 2 * (bound + 1) := by
  have hSafe : ∀ fault, e.kind ≠ .ub fault := by
    obtain ⟨_, _, _, _, rfl⟩ := hVector
    exact fun _ h => by cases h
  obtain ⟨iteration, hOrder, hLimit, hCount⟩ :=
    steadyProjectedRoundOfObservedEvent warp hTrip hRound hShared hWarp hBody hTail
      (cacheRoundRemaining true) recurringPublicationMark (endsProjection 1741)
      (projectedRoundStep true) hs hr he hBefore hHi hSafe
  dsimp only [recurringUseBefore] at hCursor ⊢
  have hCap : cacheRoundRemaining true 1396 = 2 := by decide
  rw [hCap] at hCount
  have hWithin := cacheRoundRemainingPositive true hVector hLo hHi
  omega

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
