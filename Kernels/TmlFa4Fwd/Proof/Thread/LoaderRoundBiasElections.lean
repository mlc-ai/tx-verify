-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundSecondWarp
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmBiasExpectationProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderRepeatedBiasCoordinates
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmFirstPackFrame
import all Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderActualCacheUseBound
import Lemmas.Flow.RecordedCheckpointPath
import Lemmas.Flow.ContinuingEvent
import Lemmas.Flow.ReturningPrefix
import Lemmas.Order.ElectSiteOrdinal
import Kernels.TmlFa4Fwd.Flow.Code.Part017
import Kernels.TmlFa4Fwd.Flow.Code.Part018
import Lemmas.Flow.CountTake
import Lemmas.Flow.NthEv
import all Kernels.TmlFa4Fwd.Proof.Thread.SchedulerElectProgress
import Kernels.TmlFa4Fwd.Proof.Thread.MmaShuffleOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The six warm Bias elections: the stage-zero expectation and boxes, then stage one. -/
def warmBiasSite : Fin 6 → Nat
  | 0 => 1149
  | 1 => 1154
  | 2 => 1164
  | 3 => 1178
  | 4 => 1183
  | 5 => 1192

/-- The count of a lane's earlier elections at one warm Bias site. -/
def warmBiasSiteCount (X : Execution) (t index : Nat) (k : Fin 6) : Nat :=
  ElectOrd.siteOrdinal (fun pc => pc == warmBiasSite k) X t index

set_option maxRecDepth 100000 in
private theorem warmBiasSiteNoReturn {l : Launch} {t : Nat} {s u : TState} {es : List Event}
    (k : Fin 6) (hReach : TraceReach kernel Assumptions.all l t s es u)
    (hs : warmBiasSite k < s.pc ∧ s.pc ≤ 1239)
    (hCount : es.countP Execution.isShfl = 0) :
    warmBiasSite k < u.pc ∧ u.pc ≤ 1239 := by
  let lo := warmBiasSite k+1
  have hLo : 174 ≤ lo := by fin_cases k <;> decide
  have hStart : 1149 ≤ lo ∧ lo ≤ 1240 := by fin_cases k <;> decide
  have hRank : (((kernel.code.drop lo).take (1240-lo)).zipIdx lo).all
      (fun (i,k) => LoaderRankedInstr 1240 k i) = true := by
    fin_cases k <;> kernel_rfl
  have hTail : ∀ pos ∈ List.range 91, loaderShuffleTail 1240 (1149+pos) = 1 := by
    decide +kernel
  have hAudit : ∀ edge ∈ loaderBackEdges, lo ≤ edge.1 → edge.1 ≤ 1239 → lo ≤ edge.2 := by
    fin_cases k <;> decide
  have step {a b : TState} {e : Option Event} (h : WStep kernel Assumptions.all l t a e b)
      (hA : warmBiasSite k < a.pc ∧ a.pc ≤ 1239)
      (hz : e.toList.countP Execution.isShfl = 0) :
      warmBiasSite k < b.pc ∧ b.pc ≤ 1239 := by
    have hPc : lo ≤ a.pc ∧ a.pc < 1240 := ⟨hA.1,by omega⟩
    have hFloor : lo ≤ b.pc := by
      by_contra! hn
      rcases h with ⟨rfl,ht⟩ | ⟨ev,rfl,he⟩
      · have hedge := loaderTauBackEdge (hLo.trans hPc.1) (by omega) (by omega) ht
        exact (Nat.not_le_of_lt hn) (hAudit _ hedge hPc.1 hA.2)
      · have he' : EStep kernel [] l t a ev (some b) := by
          obtain ⟨tmpl,hO,hF⟩ := he
          exact ⟨tmpl,by rwa [← loaderOutCore (hLo.trans hPc.1) (by omega)],hF⟩
        rcases (estep_return_pc he' (fun _ _ _ h => execLocal_frame h)).2 <;> omega
    have hCeiling : b.pc ≤ 1239 := by
      have hEq := rankedLoaderStep (start := lo) (stop := 1240)
        ⟨hLo,hStart.2,by decide⟩ hRank hPc.1 hPc.2 h
      have hT := hTail (a.pc-1149) (List.mem_range.mpr (by omega))
      rw [Nat.add_sub_of_le (hStart.1.trans hPc.1)] at hT
      rw [hT,hz,Nat.zero_add] at hEq
      by_contra! hn
      have hDrop : ((kernel.code.take 1240).drop b.pc) = [] :=
        List.drop_eq_nil_of_le (by rw [List.length_take]; omega)
      simp [loaderShuffleTail,hDrop] at hEq
    exact ⟨hFloor,hCeiling⟩
  induction hReach with
  | refl => exact hs
  | tau ht _ ih => exact ih (step (.inl ⟨rfl,ht⟩) hs rfl) hCount
  | @event a b c rest e he _ ih =>
    by_cases hMark : Execution.isShfl e = true
    · simp [hMark] at hCount
    · have hMark' := Bool.eq_false_iff.mpr hMark
      simp only [List.countP_cons,hMark',Bool.false_eq_true,ite_false] at hCount
      exact ih (step (.inr ⟨_,rfl,he⟩) hs (by simp [hMark'])) hCount

private theorem warmBiasSiteCode (k : Fin 6) : ∃ dst pred,
    kernel.code[warmBiasSite k]? = some ⟨none,.warp {
      kind := .elect, ty := none, dsts := [some dst,some pred],
      srcs := [], mask := some (.imm (-1)) }⟩ := by
  fin_cases k
  · exact ⟨_,_,Flow.code_1149⟩
  · exact ⟨_,_,Flow.code_1154⟩
  · exact ⟨_,_,Flow.code_1164⟩
  · exact ⟨_,_,Flow.code_1178⟩
  · exact ⟨_,_,Flow.code_1183⟩
  · exact ⟨_,_,Flow.code_1192⟩

private theorem warmBiasSiteReturns {l : Launch} {t : Nat} {s : TState} {o : Option TState}
    (k : Fin 6) {mask inst leader : Nat}
    (he : EStep kernel Assumptions.all l t s ⟨warmBiasSite k,.elect mask inst leader⟩ o) :
    ∃ u, o = some u ∧ u.pc = warmBiasSite k+1 := by
  have hPc : s.pc = warmBiasSite k := (estep_source_pc he).symm
  have hFault : s.fault = none := by
    cases h : s.fault with
    | none => rfl
    | some f =>
      obtain ⟨tm,hOut,hFire⟩ := he
      simp only [out,h,Out.ev.injEq] at hOut
      subst tm
      cases congrArg Event.kind hFire.1
  obtain ⟨dst,pred,hCode⟩ := warmBiasSiteCode k
  have hOut := inputElectOut (l := l) (g := t) hPc hFault (by fin_cases k <;> decide)
    (by fin_cases k <;> decide) hCode
  obtain ⟨tm,hEq,hFire⟩ := he
  rw [hOut,Out.ev.injEq] at hEq
  subst tm
  obtain ⟨_,ld,_,hState⟩ := hFire
  exact ⟨_,hState,congrArg (·+1) hPc⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- An election at a warm Bias site lies in a warm round, after the K packet of that round. -/
theorem warmBiasSiteRank (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch lane j : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch) (hl : lane < 32)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (k : Fin 6) {mask inst leader : Nat}
    (he : X.Elect (warpLane l g lane,j) (warmBiasSite k) mask inst leader) :
    ∃ round < warmRounds p l g batch,
      ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl =
        primingSearchShuffleCount batch+96+64*round := by
  let t := warpLane l g lane
  let e : Event := ⟨warmBiasSite k,.elect mask inst leader⟩
  have hEvent : X.get (t,j) = some e := he
  have hCTA : g/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  have hPc : 917 ≤ e.pc := by change 917 ≤ warmBiasSite k; fin_cases k <;> decide
  obtain ⟨bb,hb',lo,hi,hProjection⟩ := actualWarmCacheProjectionOrAfter hp hX hg hw hl
    (fun _ _ _ _ => loaderOutputWrites hFrame) hCTA hEvent hPc
    (.inl (show warmBiasSite k < 1353 by fin_cases k <;> decide)) (by intro _ h; cases h)
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hCTA
  have hBatch : bb = batch := (hUnique bb ⟨hb',lo,hi⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
  subst bb
  rcases hProjection with ⟨_,round,hRound,_,hWell⟩ | ⟨hLate,_⟩
  · have hTail : loaderShuffleTail 1348 (warmBiasSite k) = 32 := by
      fin_cases k <;> kernel_rfl
    change _ + loaderShuffleTail 1348 (warmBiasSite k) = _ at hWell
    rw [hTail] at hWell
    exact ⟨round,hRound,by omega⟩
  · have h : 1353 ≤ warmBiasSite k := hLate
    fin_cases k <;> simp [warmBiasSite] at h

theorem warmBiasSite_atSites {k : Fin 6} {mask inst leader : Nat} :
    ElectOrd.atSites (fun pc => pc == warmBiasSite k)
      ⟨warmBiasSite k,.elect mask inst leader⟩ = true := by
  simp [ElectOrd.atSites,isElectEv]

private theorem atSitesElect {k : Fin 6} {e : Event}
    (h : ElectOrd.atSites (fun pc => pc == warmBiasSite k) e = true) :
    ∃ mask inst leader, e = ⟨warmBiasSite k,.elect mask inst leader⟩ := by
  obtain ⟨pc,kind⟩ := e
  cases kind <;> simp [ElectOrd.atSites,isElectEv] at h
  case elect mask inst leader =>
    subst h
    exact ⟨mask,inst,leader,rfl⟩

/-- After an election at a warm Bias site, the lane cannot reach that site or an earlier
point of the round again without a shuffle. -/
private theorem noReturnAfterSiteElection {l : Launch} {X : Execution} {t : Nat}
    (k : Fin 6) {j stop : Nat} {mask inst leader : Nat}
    (he : X.Elect (t,j) (warmBiasSite k) mask inst leader) (hj : j < stop)
    {target : TState}
    (hTarget : TraceReach kernel Assumptions.all l t {} ((X.tr t).take stop) target)
    (hPc : target.pc ≤ warmBiasSite k)
    (hZero : ((X.tr t).take stop).countP Execution.isShfl =
      ((X.tr t).take j).countP Execution.isShfl) : False := by
  let xs := X.tr t
  let e : Event := ⟨warmBiasSite k,.elect mask inst leader⟩
  have hEvent : xs[j]? = some e := he
  obtain ⟨q,hQ,hLocal⟩ := hTarget.returnedPrefix
  have hIn : (xs.take stop)[j]? = some e := by rwa [List.getElem?_take_of_lt hj]
  obtain ⟨t1,o,hPath,hStep⟩ := hQ.before_event hIn
  rw [List.take_take,Nat.min_eq_left hj.le] at hPath
  obtain ⟨u,rfl,hU⟩ := warmBiasSiteReturns k hStep
  obtain ⟨q1,hQ1,hLocal1⟩ := hPath.returnedPrefix
  have hPrefix : Run kernel Assumptions.all l t {} (xs.take (j+1)) (some u) := by
    have ht : xs.take (j+1) = xs.take j ++ [e] := by
      rw [List.take_add_one,hEvent,Option.toList_some]
    rw [ht]
    exact hQ1.snoc hLocal1 hStep
  let rest := (xs.drop (j+1)).take (stop-(j+1))
  have hTrunc : xs.take stop = xs.take (j+1) ++ rest := by
    conv_lhs => rw [← Nat.add_sub_of_le (show j+1 ≤ stop by omega)]
    rw [List.take_add]
  have hTail : Run kernel Assumptions.all l t u rest (some q) := by
    apply hPrefix.after_returned_prefix
    rw [← hTrunc]
    exact hQ
  have hCore := hTail.returning_reach.append (.of_local hLocal)
  rw [List.append_nil] at hCore
  have hRest : rest.countP Execution.isShfl = 0 := by
    have h := hZero
    rw [hTrunc,List.countP_append,countP_take_succ_false (p := Execution.isShfl) he rfl] at h
    omega
  have hAfter : warmBiasSite k < u.pc ∧ u.pc ≤ 1239 := by
    rw [hU]
    fin_cases k <;> decide
  have h := (warmBiasSiteNoReturn k hCore hAfter hRest).1
  omega

/-- At a point of round `round` before a warm Bias site, a lane has elected at that site
at most once per earlier warm round. Each election carries the rank of its round, and
two elections of one round would need a return without a shuffle. -/
theorem warmBiasSiteCountUpper (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch lane pos round : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch) (hl : lane < 32)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (k : Fin 6) {target : TState}
    (hTarget : TraceReach kernel Assumptions.all l (warpLane l g lane) {}
      ((X.tr (warpLane l g lane)).take pos) target) (hPc : target.pc ≤ warmBiasSite k)
    (hRank : ((X.tr (warpLane l g lane)).take pos).countP Execution.isShfl ≤
      primingSearchShuffleCount batch+96+64*round) :
    warmBiasSiteCount X (warpLane l g lane) pos k ≤ round := by
  by_contra! hMore
  unfold warmBiasSiteCount ElectOrd.siteOrdinal at hMore
  have hAll : ∀ n ≤ round, ∃ j e, j < pos ∧ X.get (warpLane l g lane,j) = some e ∧
      ElectOrd.atSites (fun pc => pc == warmBiasSite k) e = true ∧ ((X.tr (warpLane l g lane)).take
          j).countP (ElectOrd.atSites (fun pc => pc == warmBiasSite k)) = n ∧
      primingSearchShuffleCount batch+96+64*n ≤ ((X.tr (warpLane l g lane)).take j).countP
          Execution.isShfl := by
    intro n hn
    induction n with
    | zero =>
      obtain ⟨j,e,hj,he,hs,hc⟩ := exists_nthEv (X := X) (p := ElectOrd.atSites (fun pc => pc ==
          warmBiasSite k)) (g := warpLane l g lane)
        (k := pos) (n := 0) (by omega)
      obtain ⟨mask,inst,leader,rfl⟩ := atSitesElect hs
      obtain ⟨ρ,_,hρ⟩ := warmBiasSiteRank hp hX hFrame hg hw hb hl hLo hHi k (j := j) he
      exact ⟨j,_,hj,he,hs,hc,by omega⟩
    | succ n ih =>
      obtain ⟨j₀,e₀,hj₀,he₀,hs₀,hc₀,hr₀⟩ := ih (by omega)
      obtain ⟨j,e,hj,he,hs,hc⟩ := exists_nthEv (X := X) (p := ElectOrd.atSites (fun pc => pc ==
          warmBiasSite k)) (g := warpLane l g lane)
        (k := pos) (n := n+1) (by omega)
      obtain ⟨mask,inst,leader,rfl⟩ := atSitesElect hs
      obtain ⟨mask₀,inst₀,leader₀,rfl⟩ := atSitesElect hs₀
      have hOrder : j₀ < j := by
        by_contra! h
        have := countP_take_mono (ElectOrd.atSites (fun pc => pc == warmBiasSite k)) (X.tr
            (warpLane l g lane)) h
        omega
      obtain ⟨ρ,_,hρ⟩ := warmBiasSiteRank hp hX hFrame hg hw hb hl hLo hHi k (j := j) he
      obtain ⟨ρ₀,_,hρ₀⟩ := warmBiasSiteRank hp hX hFrame hg hw hb hl hLo hHi k (j := j₀) he₀
      have hMono := countP_take_mono Execution.isShfl (X.tr (warpLane l g lane)) hOrder.le
      have hNe : ρ ≠ ρ₀ := by
        intro hEq
        have hRun := TraceReach.returnedPrefix hTarget
        obtain ⟨q,hQ,_⟩ := hRun
        have hIn : ((X.tr (warpLane l g lane)).take pos)[j]? = some ⟨warmBiasSite k,.elect mask
            inst leader⟩ := by
          rw [List.getElem?_take_of_lt hj]
          exact he
        obtain ⟨t2,o2,hPath2,hStep2⟩ := hQ.before_event hIn
        rw [List.take_take,Nat.min_eq_left hj.le] at hPath2
        exact noReturnAfterSiteElection k he₀ hOrder hPath2
          (le_of_eq (estep_source_pc hStep2).symm) (by rw [hρ,hρ₀,hEq])
      exact ⟨j,_,hj,he,hs,hc,by omega⟩
  obtain ⟨j,e,hj,he,hs,_,hr⟩ := hAll round le_rfl
  obtain ⟨mask,inst,leader,rfl⟩ := atSitesElect hs
  have hMono := countP_take_mono Execution.isShfl (X.tr (warpLane l g lane)) hj.le
  exact noReturnAfterSiteElection k he hj hTarget hPc (by omega)

private theorem fullMember {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {pc mask inst lead : Nat}
    (h : X.Elect i pc mask inst lead) (peer : Nat) : electMember mask (laneOf l peer) := by
  rw [Thread.actualFullElectionMask hX h]
  have hLane : laneOf l peer < 32 := Nat.mod_lt _ (by decide)
  refine ⟨hLane,?_⟩
  rw [Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
  exact hLane

/-- A recorded checkpoint reaches its current state along the lane's actual prefix. -/
theorem warpPrefixReach {l : Launch} {X : Execution}
    {g pc shuffles votes : Nat} {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g pc F shuffles votes ends) (lane : Nat) (hl : lane < 32) :
    TraceReach kernel Assumptions.all l (warpLane l g lane) {}
      ((X.tr (warpLane l g lane)).take (cur.pos lane)) (cur.state lane) := by
  have h := (cur.recorded lane hl).returning_reach.append (.of_local (cur.localSteps lane hl))
  rwa [List.append_nil] at h

/-- At a warm Bias site of round `round`, every lane has elected there exactly once per
earlier round, so each lane's partner of the current election is its own next election. -/
theorem warmBiasPartnerBound (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round shuffles votes : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (k : Fin 6) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (warmBiasSite k) F shuffles votes ends)
    (hRank : shuffles = primingSearchShuffleCount batch+96+64*round)
    (hLower : ∀ lane < 32, round ≤ warmBiasSiteCount X (warpLane l g lane) (cur.pos lane) k) :
    ∀ lane < 32, ∀ peer < 32, ∀ {j pc' mask mask' inst leader lead'},
      X.Elect (warpLane l g peer,cur.pos peer) (warmBiasSite k) mask inst leader →
      X.Elect (warpLane l g lane,j) pc' mask' inst lead' → cur.pos lane ≤ j := by
  intro lane hl peer hPeer j pc' mask mask' inst leader lead' he hf
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hw' : SameWarp l (warpLane l g peer) (warpLane l g lane) :=
    Step.sameWarp_trans (sameWarp_symm (Step.sameWarp_lane hBlock hg hPeer).1)
      (Step.sameWarp_lane hBlock hg hl).1
  have hSite := (hX.elect.2.1 _ _ _ _ _ _ _ _ _ he hf hw').1
  have hEq := ElectOrd.siteOrdinal_eq hX (fun pc => pc == warmBiasSite k) hw'
    (fun _ _ _ _ _ _ h => fullMember hX h _) (fun _ _ _ _ _ _ h => fullMember hX h _)
    ⟨_,_,_,_,_,_,_,he,hf⟩
  have upper (q : Nat) (hq : q < 32) :
      warmBiasSiteCount X (warpLane l g q) (cur.pos q) k ≤ round :=
    warmBiasSiteCountUpper hp hX hFrame hg hw hb hq hLo hHi k (warpPrefixReach cur q hq)
      (le_of_eq (cur.checkpoint q hq).1) (le_of_eq ((cur.ordinals.shfl q hq).trans hRank))
  have hPeerExact : warmBiasSiteCount X (warpLane l g peer) (cur.pos peer) k = round :=
    Nat.le_antisymm (upper peer hPeer) (hLower peer hPeer)
  by_contra! hEarly
  have hf' : X.Elect (warpLane l g lane,j) (warmBiasSite k) mask' inst lead' := hSite ▸ hf
  have hSucc := countP_take_succ (p := ElectOrd.atSites (fun pc => pc == warmBiasSite k))
    hf' warmBiasSite_atSites
  have hMono := countP_take_mono (ElectOrd.atSites (fun pc => pc == warmBiasSite k))
    (X.tr (warpLane l g lane)) (show j+1 ≤ cur.pos lane by omega)
  have hUp := upper lane hl
  unfold warmBiasSiteCount ElectOrd.siteOrdinal at hPeerExact hUp hEq
  omega

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
