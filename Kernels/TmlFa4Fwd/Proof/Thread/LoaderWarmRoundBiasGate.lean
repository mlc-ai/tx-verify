-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRoundBiasElections
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasCredits
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderFirstWarmBias
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPollProgress
import Kernels.TmlFa4Fwd.Flow.Code.Part017
import Kernels.TmlFa4Fwd.Flow.Code.Part018

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue PTX.MBarrier
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The Bias-empty wait of each warm stage. -/
def warmBiasEmptyWait : Fin 2 → DrainWaitSite
  | 0 => ⟨1146,9613,2039,7177⟩
  | 1 => ⟨1175,9614,2052,7178⟩

private theorem warmBiasEmptyWaitCode (stage : Fin 2) :
    LoaderWaitCode (warmBiasEmptyWait stage) := by
  fin_cases stage
  · exact ⟨Flow.code_1146,Flow.code_1147,Flow.code_1148⟩
  · exact ⟨Flow.code_1175,Flow.code_1176,Flow.code_1177⟩

/-- The stage-zero Bias frame of warm round `round`: both stage-zero Bias addresses and the
V carry with the round's Bias phases. -/
def warmRoundBiasFrame (p : Params) (l : Launch) (g batch round lane : Nat) :
    List (Nat × Value) :=
  [(1140,b32 (l.sharedBase+320)),(2039,b32 (l.sharedBase+336))] ++
    warmRoundValueCarry p l g batch round lane

/-- Warp 14 takes the Bias arm after the K publication of warm round `round`. -/
theorem WarmRoundKeyPublished.biasGate {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g batch round : Nat} (hw : warpIndex l g = 14)
    (c : WarmRoundKeyPublished p l X g batch round) :
    ∃ gate : SchedulerWarpReached l X g 1146 (warmRoundBiasFrame p l g batch round)
        c.shuffles c.votes c.ends, gate.pos = c.reached.pos := by
  obtain ⟨entry,hEntry⟩ := c.valueEntry
  obtain ⟨gate,hGate⟩ := entry.advanceLocalWithPosition (pc' := 1146)
    (G := warmRoundBiasFrame p l g batch round) (by
    intro lane hl
    let t := warpLane l g lane
    let F := warmRoundValueCarry p l g batch round lane
    have hs := entry.checkpoint lane hl
    have hF : Holds (entry.state lane).regs F := hs.2.2.2.2
    have hRole : (entry.state lane).regs 123 = some (.pred false) := by
      have h : (entry.state lane).regs 123 =
          some (.pred (decide (warpIndex l g ≠ 14))) := holds_mem hF (by
            simp [F,warmRoundValueCarry,warmRoundKeyCarry,warmRoundPagesFrame,warmRoundFrame,
              openingWarmFrame])
      simpa only [hw,show decide ((14 : Nat) ≠ 14) = false by decide] using h
    obtain ⟨u,hu,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := t)
      Flow.code_1143 false hs hRole (by simp)
    have huA := (loaderLinear (regs := []) (by decide) (by decide) hs.1
      (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu).1
    have ht : At u 1144 ([(2535,b32 l.sharedBase)]++F) :=
      hU.mono ⟨holds_mem hU.2.2.2.2 (by
        simp [warmRoundValueCarry,warmRoundKeyCarry,warmRoundPagesFrame,warmRoundFrame,
          openingWarmFrame,warmStartFrame]),hU.2.2.2.2⟩
    have hSeg : Seg kernel [] l t 2 1144 [(2535,b32 l.sharedBase)] 1146
        [(1140,b32 (l.sharedBase+320)),(2039,b32 (l.sharedBase+336))] := by
      have hMem := hp.shared.2.1
      have hBase : l.sharedBase < 2^32 := by omega
      have hReady : l.sharedBase+320 < 2^32 := by omega
      have hEmpty : l.sharedBase+336 < 2^32 := by omega
      intro s h
      seg_fp h using norm_bits [Nat.mod_eq_of_lt hBase,Nat.mod_eq_of_lt hReady,
        Nat.mod_eq_of_lt hEmpty]
    obtain ⟨v,hv,hV⟩ := roundStraightFrame (by decide) (by decide)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hSeg ht
    exact ⟨v,run_rtg (run_comp huA hv),hV⟩)
  exact ⟨gate,hGate.trans hEntry⟩

/-- The Bias-empty wait of a warm stage passes once the object's final phase has the parity
that the round expects. The hypothesis is only needed for a lane whose remaining trace
consists of failed polls. -/
theorem warmBiasEmptyAcquireOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g round shuffles votes : Nat} (hg : g < l.threads) (stage : Fin 2)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (warmBiasEmptyWait stage).pc F shuffles votes ends)
    (hFresh : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ≠ (warmBiasEmptyWait stage).result)
    (hBase : ∀ lane < 32,
      ((warmBiasEmptyWait stage).base,b32 (l.sharedBase+(336+8*stage.val))) ∈ F lane)
    (hParity : ∀ lane < 32,
      ((warmBiasEmptyWait stage).phase,b32 (round%2)) ∈ F lane)
    (hReady : ∀ lane < 32,
      (∀ e ∈ (X.tr (warpLane l g lane)).drop (cur.pos lane),
        ∃ loc, e.kind = .wait loc (round%2) false true .cta) →
      let log := X.objects (biasEmptyObject l (g/l.block) stage)
      ∃ s, stateBefore log log.length = some s ∧ s.phase%2 ≠ round%2) :
    ∃ done : SchedulerWarpReached l X g ((warmBiasEmptyWait stage).pc+3) F shuffles votes
        ends,
      ∀ lane < 32, cur.pos lane < done.pos lane ∧
        ∀ i, cur.pos lane ≤ i → i < done.pos lane →
          ∀ a, ¬ X.Access (warpLane l g lane,i) a true := by
  let addr := l.sharedBase+(336+8*stage.val)
  have hAddr : addr < 2^32 := by have := hp.shared.2.1; have := stage.isLt; dsimp [addr]; omega
  have hAlign : addr%8 = 0 := by have := hp.shared.1; dsimp [addr]; omega
  have hPhase : round%2 < 2 := Nat.mod_lt _ (by decide)
  obtain ⟨done,hTrace⟩ := loaderWarpWaitOfBlockedPhaseTrace hMax hg (by rw [hp.block])
    (warmBiasEmptyWaitCode stage) (by fin_cases stage <;> decide) hAddr hAlign hPhase cur
    hFresh hBase hParity
    (fun lane hl {_ _} _ _ _ hFailed => by
      obtain ⟨s,hState,hPh⟩ := hReady lane hl (by
        intro e hE
        exact ⟨_,congrArg Event.kind (hFailed _ hE)⟩)
      refine ⟨s,hState,?_⟩
      rwa [Nat.mod_mod])
  refine ⟨done,fun lane hl => ?_⟩
  obtain ⟨n,hPos,hRun⟩ := hTrace lane hl
  refine ⟨by omega,?_⟩
  intro i hLo hHi a hAccess
  let t := warpLane l g lane
  have hGet : ∃ ok, X.get (t,i) = some ⟨(warmBiasEmptyWait stage).pc,
      .wait ⟨.shared,t/l.block,addr⟩ (round%2) ok true .cta⟩ := by
    have hx := congrArg (fun es : List Event => es[i-cur.pos lane]?) hRun
    simp only at hx
    rw [List.getElem?_drop,Nat.add_sub_of_le hLo] at hx
    by_cases hFirst : i-cur.pos lane < n
    · rw [List.getElem?_append_left (by simpa using hFirst),
        List.getElem?_replicate,ite_eq_left hFirst] at hx
      exact ⟨false,hx⟩
    · have hEq : i-cur.pos lane = n := by omega
      rw [hEq,List.getElem?_append_right (by simp),List.length_replicate,Nat.sub_self] at hx
      exact ⟨true,hx⟩
  obtain ⟨ok,h⟩ := hGet
  rcases hAccess with ⟨_,_,hf⟩ | ⟨_,⟨pc,hf⟩,_⟩ | ⟨_,_,pc,hf⟩
  · cases hf
  · cases congrArg Event.kind (Option.some.inj (h.symm.trans hf))
  · cases congrArg Event.kind (Option.some.inj (h.symm.trans hf))

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
