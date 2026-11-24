-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaWarpPollProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaPollOrdinalReturn
public import Lemmas.Order.ElectOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Prologue Epilogue
open Correction (OpeningTripCursor)

noncomputable section

/-- The returned cursor's exact successful-poll and election counters. -/
def WarpOrdinalPollAdvance (l : Launch) (X : Execution) (g : Nat) (site : Fin 14)
    (addr phase shuffles votes : Nat) (F : Nat → List (Nat × Value))
    (ends : Nat → Option TState)
    (cur : SchedulerWarpReached l X g (waitSite site).pc F shuffles votes ends) : Prop :=
    ∃ next : SchedulerWarpReached l X g ((waitSite site).pc+3) F shuffles votes ends,
      ∀ lane < 32, cur.pos lane < next.pos lane ∧
        X.get (warpLane l g lane,next.pos lane-1) =
          some ⟨(waitSite site).pc,.wait ⟨.shared,g/l.block,addr⟩ phase true true .cta⟩ ∧
        (∀ other, okPolls other ((X.tr (warpLane l g lane)).take (next.pos lane)) =
          okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane)) +
            if other = ⟨.shared,g/l.block,addr⟩ then 1 else 0) ∧
        elections X (warpLane l g lane) (next.pos lane) =
          elections X (warpLane l g lane) (cur.pos lane)

/-- A warp acquire consumes exactly one generation of its object. Failed retries
preserve the counters for every other object and every warp collective. -/
theorem mmaWarpOrdinalPollReturnedOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g addr phase gen shuffles votes : Nat} (hg : g < l.threads) (site : Fin 14)
    (hAddr : addr < 2^32) (hAlign : addr%8 = 0) (hPhase : phase < 2)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (waitSite site).pc F shuffles votes ends)
    (hOperands : ∀ lane < 32, (∀ pair ∈ F lane, pair.1 ≠ (waitSite site).result) ∧
      ((waitSite site).base,b32 addr) ∈ F lane ∧ ((waitSite site).phase,b32 phase) ∈ F lane)
    (hOrdinal : ∀ lane < 32,
      okPolls ⟨.shared,g/l.block,addr⟩ ((X.tr (warpLane l g lane)).take (cur.pos lane)) = gen)
    (hReady : ∀ lane < 32, okPolls ⟨.shared,g/l.block,addr⟩ (X.tr (warpLane l g lane)) = gen →
      let log := X.objects ⟨.shared,g/l.block,addr⟩
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase%2 ≠ phase%2) :
    WarpOrdinalPollAdvance l X g site addr phase shuffles votes F ends cur := by
  classical
  unfold WarpOrdinalPollAdvance
  let th := warpLane l g
  let loc : Loc := ⟨.shared,g/l.block,addr⟩
  let ev (ok : Bool) : Event := ⟨(waitSite site).pc,.wait loc phase ok true .cta⟩
  have hEach (lane : Nat) (hl : lane < 32) :
      ∃ d : OpeningTripCursor l X (th lane) ((waitSite site).pc+3) (F lane),
        d.ending = ends lane ∧ cur.pos lane < d.pos ∧
        X.get (th lane,d.pos-1) = some (ev true) ∧
        (∀ other, okPolls other ((X.tr (th lane)).take d.pos) =
          okPolls other ((X.tr (th lane)).take (cur.pos lane)) + if other = loc then 1 else 0) ∧
        (∀ test : Event → Bool, test (ev false) = false → test (ev true) = false →
          ((X.tr (th lane)).take d.pos).countP test =
            ((X.tr (th lane)).take (cur.pos lane)).countP test) := by
    have hSame := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
    have hCta : (th lane)/l.block = g/l.block := hSame.1.2.2.symm
    let c : OpeningTripCursor l X (th lane) (waitSite site).pc (F lane) :=
      ⟨cur.pos lane,cur.before lane,cur.state lane,ends lane,cur.positive lane hl,
        cur.bounded lane hl,
        cur.released lane hl,cur.checkpoint lane hl,cur.recorded lane hl,cur.continuation lane hl,
        cur.localSteps lane hl⟩
    obtain ⟨fresh,base,parity⟩ := hOperands lane hl
    obtain ⟨d,hPos,hEnd,he,hCount,n,tail,hn,hTrace⟩ :=
      pollOrdinalReturnedWithTraceOfMaximal hMax (g := th lane) (gen := gen)
        hSame.1.2.1 site
        hAddr hAlign hPhase fresh base parity c (by rw [hCta]; exact hOrdinal lane hl)
        (fun h => by rw [hCta] at h ⊢; exact hReady lane hl h)
    refine ⟨d,hEnd,hPos,by simpa only [hCta,ev,loc] using he,
      fun other => by simpa only [hCta,loc,c] using hCount other,?_⟩
    intro test hf ht
    change d.pos = cur.pos lane+n+1 at hn
    let accepted := List.replicate n (ev false) ++ [ev true]
    have hLength : accepted.length = n+1 := by simp [accepted]
    have hCut : (X.tr (th lane)).drop (cur.pos lane) = accepted ++ tail := by
      simpa only [c,hCta,ev,loc,accepted,List.append_assoc,List.singleton_append] using hTrace
    have hQuiet : accepted.countP test = 0 := by simp [accepted,hf,ht]
    rw [hn,Nat.add_assoc,List.take_add,hCut,← hLength,List.take_append_length,
      List.countP_append,hQuiet,Nat.add_zero]
  choose! next hEnd hPos hEvent hCounts hKeep using hEach
  let pos lane := if hl : lane < 32 then (next lane hl).pos else cur.pos lane
  let before lane := if hl : lane < 32 then (next lane hl).before else cur.before lane
  let state lane := if hl : lane < 32 then (next lane hl).ready else cur.state lane
  have hOrd : WarpOrdinals l X g pos shuffles votes :=
    ⟨fun lane hl => by
        simpa only [pos,dite_eq_left hl] using
          (hKeep lane hl _ rfl rfl).trans (cur.ordinals.shfl lane hl),
      fun lane hl => by
        simpa only [pos,dite_eq_left hl] using
          (hKeep lane hl _ rfl rfl).trans (cur.ordinals.vote lane hl)⟩
  refine ⟨⟨⟨pos,before,state,hOrd,?_,?_,?_⟩,?_,?_,?_,?_⟩,?_⟩
  · intro lane hl
    simpa only [pos,before,dite_eq_left hl,hEnd lane hl] using (next lane hl).remaining
  · exact fun lane hl => by
      simpa only [before,state,dite_eq_left hl] using (next lane hl).localSteps
  · exact fun lane hl => by simpa only [state,dite_eq_left hl] using (next lane hl).checkpoint
  · exact fun lane hl => by simpa only [pos,dite_eq_left hl] using (next lane hl).positive
  · exact fun lane hl => by simpa only [pos,dite_eq_left hl] using (next lane hl).bounded
  · exact fun lane hl => by simpa only [pos,dite_eq_left hl] using (next lane hl).released
  · exact fun lane hl => by simpa only [pos,before,dite_eq_left hl] using (next lane hl).recorded
  · intro lane hl
    simpa only [pos,dite_eq_left hl,elections,th,loc,ev] using
      And.intro (hPos lane hl)
        (And.intro (hEvent lane hl) (And.intro (hCounts lane hl) (hKeep lane hl isElectEv rfl rfl)))

end
end PTX.Kernels.TmlFa4Fwd.Mma
