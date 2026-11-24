-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.DrainInOrder
import Lemmas.Step.WarpElect
public import Lemmas.Order.ElectOrdinal
import Lemmas.Protocol.ElectCount
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof PTX.Assumption Prologue

noncomputable section

private theorem cursorElection {l : Launch} {X : Execution} {g site shuffles votes : Nat}
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g site F shuffles votes ends) {post : Nat → Nat → TState}
    {lane : Nat} (hl : lane < 32)
    (hOut : out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
      .ev (.elect 4294967295 (post lane)))
    (hMore : cur.pos lane < (X.tr (warpLane l g lane)).length) :
    ∃ inst leader, X.Elect (warpLane l g lane,cur.pos lane) site 4294967295 inst leader ∧
      Run kernel Assumptions.all l (warpLane l g lane) {}
        ((X.tr (warpLane l g lane)).take (cur.pos lane+1)) (some (post lane leader)) ∧
      Run kernel Assumptions.all l (warpLane l g lane) (post lane leader)
        ((X.tr (warpLane l g lane)).drop (cur.pos lane+1)) (ends lane) := by
  have hn := Next.mk (cur.localSteps lane hl) hOut
  obtain ⟨_,_,he,⟨inst,leader,rfl,hRet⟩,hTail⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_,_,_,h⟩; cases h) (cur.continuation lane hl)
    (fun h => (Nat.not_le_of_lt hMore) (List.drop_eq_nil_iff.mp h))
  obtain rfl := Option.some.inj hRet
  refine ⟨inst,leader,?_,?_,hTail⟩
  · change X.get (warpLane l g lane,cur.pos lane) =
      some ⟨site,.elect 4294967295 inst leader⟩
    rw [(cur.checkpoint lane hl).1] at he
    exact he
  · rw [List.take_succ_eq_append_getElem hMore,(List.getElem?_eq_some_iff.mp he).2]
    exact (cur.recorded lane hl).snoc hn.steps ⟨_,hOut,inst,leader,rfl,rfl⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g site shuffles votes : Nat} (hg : g < l.threads)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g site F shuffles votes ends) (post : Nat → Nat → TState)
    (G : Nat → Nat → List (Nat × Value))
include hp hMax hg cur post G

private theorem SchedulerWarpReached.consumeElectionWithPartnerBound
    (hPartner : ∀ lane < 32, ∀ peer < 32, ∀ {j pc' mask mask' inst leader lead'},
      X.Elect (warpLane l g peer,cur.pos peer) site mask inst leader →
      X.Elect (warpLane l g lane,j) pc' mask' inst lead' → cur.pos lane ≤ j)
    (hOut : ∀ lane < 32, out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
      .ev (.elect 4294967295 (post lane)))
    (hPost : ∀ lane < 32, ∀ leader, At (post lane leader) (site+1) (G lane leader)) :
    ∃ leader : Fin 32, ∃ done : SchedulerWarpReached l X g (site+1)
      (fun lane => G lane leader) shuffles votes ends,
      ∀ lane < 32, done.pos lane = cur.pos lane+1 ∧
        ∃ inst, X.Elect (warpLane l g lane,cur.pos lane) site 4294967295 inst leader := by
  classical
  let thread := warpLane l g
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hSame (lane : Nat) (hl : lane < 32) := (Step.sameWarp_lane hBlock hg hl).1
  obtain ⟨leader,hLeader,hDet⟩ :=
    Step.exists_leader hMax.1 (g := g) (PTX.electMember_full l g)
  have hMore (lane : Nat) (hl : lane < 32) : cur.pos lane < (X.tr (thread lane)).length := by
    by_contra! hNo
    have hLen := Nat.le_antisymm (cur.bounded lane hl) hNo
    have hAll (q : Nat) (hq : q < 32) : cur.pos q = (X.tr (thread q)).length := by
      apply Nat.le_antisymm (cur.bounded q hq)
      by_contra! hYes
      obtain ⟨inst,nextLead,he,_,_⟩ := cursorElection cur hq (hOut q hq) hYes
      have hPeers := Step.sameWarp_trans (sameWarp_symm (hSame q hq)) (hSame lane hl)
      obtain ⟨j,pc,pc',mask,mask',label,a,b,hSource,hPeer⟩ :=
        ElectOrd.partner hMax.1 hPeers he (PTX.electMember_full l (thread lane))
      have hSite : site = pc := congrArg Event.pc (Option.some.inj (he.symm.trans hSource))
      have hAfter := hPartner lane hl q hq (hSite.symm ▸ hSource) hPeer
      rw [hLen] at hAfter
      exact (Nat.not_lt_of_ge hAfter) (len_of_get hPeer)
    apply hMax.not_grows
    refine Step.elect_counted_extension (pc := site) hMax.1 hg
      (fun lane hMem => ⟨_,Step.sameWarp_lane hBlock hg hMem.1⟩)
      (fun h _ => PTX.electMember_full l h) hLeader hDet ?_ ?_ ?_ ?_
    · intro h hh
      let k := laneOf l h
      have hk : k < 32 := Nat.mod_lt _ (by decide)
      have hEq : thread k = h := Step.warpLane_of_sameWarp hh
      apply Or.inl
      intro hNil
      have hL := hAll k hk
      rw [hEq,hNil,List.length_nil] at hL
      exact (Nat.ne_of_gt (cur.positive k hk)) hL
    · intro h hh
      let k := laneOf l h
      have hk : k < 32 := Nat.mod_lt _ (by decide)
      have hEq : thread k = h := Step.warpLane_of_sameWarp hh
      exact hEq ▸ cur.released k hk (hAll k hk)
    · intro h hh inst
      let k := laneOf l h
      have hk : k < 32 := Nat.mod_lt _ (by decide)
      have hEq : thread k = h := Step.warpLane_of_sameWarp hh
      rw [← hEq]
      have hRun := cur.recorded k hk
      rw [List.take_of_length_le (hAll k hk).ge] at hRun
      exact ⟨cur.before k,cur.state k,_,hRun,cur.localSteps k hk,
        ⟨_,hOut k hk,inst,leader,by rw [(cur.checkpoint k hk).1],rfl⟩⟩
    · intro inst
      exact Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl
        (noNewRead_appendLanes fun _ => by rfl)
  have hLane (lane : Nat) (hl : lane < 32) : ∃ inst,
      X.Elect (thread lane,cur.pos lane) site 4294967295 inst leader ∧
      Run kernel Assumptions.all l (thread lane) {} ((X.tr (thread lane)).take (cur.pos lane+1))
        (some (post lane leader)) ∧
      Run kernel Assumptions.all l (thread lane) (post lane leader)
        ((X.tr (thread lane)).drop (cur.pos lane+1)) (ends lane) := by
    obtain ⟨inst,q,he,hPast,hTail⟩ := cursorElection cur hl (hOut lane hl) (hMore lane hl)
    have hEq := hDet _ _ _ _ (hSame lane hl) he
    subst q
    exact ⟨inst,he,hPast,hTail⟩
  have hS (lane : Nat) (hl : lane < 32) :
      ((X.tr (thread lane)).take (cur.pos lane+1)).countP Execution.isShfl = shuffles := by
    obtain ⟨_,he,_,_⟩ := hLane lane hl
    rw [countP_take_succ_false he rfl]
    exact cur.ordinals.shfl lane hl
  have hV (lane : Nat) (hl : lane < 32) :
      ((X.tr (thread lane)).take (cur.pos lane+1)).countP isFullWarpVote = votes := by
    obtain ⟨_,he,_,_⟩ := hLane lane hl
    rw [countP_take_succ_false he rfl]
    exact cur.ordinals.vote lane hl
  let done : SchedulerWarpReached l X g (site+1) (fun lane => G lane leader)
      shuffles votes ends :=
    ⟨⟨fun lane => cur.pos lane+1,(post · leader),(post · leader),⟨hS,hV⟩,
      fun lane hl => (Classical.choose_spec (hLane lane hl)).2.2,fun _ _ => .refl,
      fun lane hl => hPost lane hl leader⟩,
      fun _ _ => Nat.succ_pos _,hMore,
      fun lane hl hLen => by
        have he := (Classical.choose_spec (hLane lane hl)).1
        constructor
        intro pc kind hGet _
        have hIdx : (X.tr (thread lane)).length-1 = cur.pos lane := by
          change cur.pos lane+1 = (X.tr (thread lane)).length at hLen
          omega
        rw [hIdx]
        exact elect_ready hMax.1 he,
      fun lane hl => (Classical.choose_spec (hLane lane hl)).2.1⟩
  exact ⟨⟨leader,hLeader.1⟩,done,fun lane hl => ⟨rfl,_,(Classical.choose_spec (hLane lane hl)).1⟩⟩

/-- A reached full-warp election at its first encounter chooses one real leader and continues
every lane's actual trace. -/
theorem SchedulerWarpReached.consumeElection
    (hFirst : ∀ lane < 32, ∀ j < cur.pos lane, ∀ mask inst leader,
      ¬ X.Elect (warpLane l g lane,j) site mask inst leader)
    (hOut : ∀ lane < 32, out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
      .ev (.elect 4294967295 (post lane)))
    (hPost : ∀ lane < 32, ∀ leader, At (post lane leader) (site+1) (G lane leader)) :
    ∃ leader : Fin 32, ∃ done : SchedulerWarpReached l X g (site+1)
      (fun lane => G lane leader) shuffles votes ends,
      ∀ lane < 32, done.pos lane = cur.pos lane+1 ∧
        ∃ inst, X.Elect (warpLane l g lane,cur.pos lane) site 4294967295 inst leader := by
  apply cur.consumeElectionWithPartnerBound hp hMax hg post G _ hOut hPost
  intro lane hl peer hPeer j other mask mask' inst leader lead' he hf
  have hw : SameWarp l (warpLane l g peer) (warpLane l g lane) :=
    Step.sameWarp_trans (sameWarp_symm (Step.sameWarp_lane (by rw [hp.block]) hg hPeer).1)
      (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
  have hSite := (hMax.1.elect.2.1 _ _ _ _ _ _ _ _ _ he hf hw).1
  by_contra! hEarlier
  exact hFirst lane hl j hEarlier mask' inst lead' (hSite.symm ▸ hf)

/-- A shared election ordinal aligns repeated full-warp elections in the actual trace. -/
theorem SchedulerWarpReached.consumeElectionAtOrdinal (hOrdinal : ElectOrdinal l X) (ordinal : Nat)
    (hCut : ∀ lane < 32, elections X (warpLane l g lane) (cur.pos lane) = ordinal)
    (hOut : ∀ lane < 32, out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
      .ev (.elect 4294967295 (post lane)))
    (hPost : ∀ lane < 32, ∀ leader, At (post lane leader) (site+1) (G lane leader)) :
    ∃ leader : Fin 32, ∃ done : SchedulerWarpReached l X g (site+1)
      (fun lane => G lane leader) shuffles votes ends,
      ∀ lane < 32, done.pos lane = cur.pos lane+1 ∧
        ∃ inst, X.Elect (warpLane l g lane,cur.pos lane) site 4294967295 inst leader := by
  apply cur.consumeElectionWithPartnerBound hp hMax hg post G _ hOut hPost
  intro lane hl peer hPeer j other mask mask' inst leader lead' he hf
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hw : SameWarp l (warpLane l g peer) (warpLane l g lane) :=
    Step.sameWarp_trans (sameWarp_symm (Step.sameWarp_lane hBlock hg hPeer).1)
      (Step.sameWarp_lane hBlock hg hl).1
  by_contra! hEarlier
  have hOther := hOrdinal hw he hf
  change elections X (warpLane l g peer) (cur.pos peer) =
    elections X (warpLane l g lane) j at hOther
  have hCount := ElectOrd.elections_succ hf
  have hMono := countP_take_mono isElectEv (X.tr (warpLane l g lane))
    (show j+1 ≤ cur.pos lane by omega)
  change elections X (warpLane l g lane) (j+1) ≤
    elections X (warpLane l g lane) (cur.pos lane) at hMono
  rw [hCut peer hPeer] at hOther
  rw [hCut lane hl,hCount,← hOther] at hMono
  omega

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
