-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRoundBiasElections
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRoundBiasSteps
import all Kernels.TmlFa4Fwd.Proof.Thread.SchedulerElectProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderFirstWarmBias
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryOperandsProgress
import Kernels.TmlFa4Fwd.Proof.PrologueNonzeroTrace
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Flow.Code.Part017
import Kernels.TmlFa4Fwd.Flow.Code.Part018

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- No event of lane `t` in positions `a` to `b` writes memory. -/
def QuietSpan (X : Execution) (t a b : Nat) : Prop :=
  ∀ i, a ≤ i → i < b → ∀ d, ¬ X.Access (t,i) d true

theorem QuietSpan.trans {X : Execution} {t a b c : Nat} (h₁ : QuietSpan X t a b)
    (h₂ : QuietSpan X t b c) : QuietSpan X t a c := by
  intro i hLo hHi d
  by_cases h : i < b
  · exact h₁ i hLo h d
  · exact h₂ i (by omega) hHi d

theorem QuietSpan.refl (X : Execution) (t a : Nat) : QuietSpan X t a a :=
  fun _ h₁ h₂ => absurd (lt_of_le_of_lt h₁ h₂) (Nat.lt_irrefl _)

/-- An event that neither stores nor performs an atomic update writes no memory. -/
theorem QuietSpan.single {X : Execution} {t i pc : Nat} {k : Kind}
    (h : X.get (t,i) = some ⟨pc,k⟩) (hw : ∀ a d, k ≠ .wr a d)
    (hr : ∀ a o n, k ≠ .rmw a o n) : QuietSpan X t i (i+1) := by
  intro j hLo hHi d hAccess
  have hj : j = i := by omega
  subst j
  rcases hAccess with ⟨_,_,hf⟩ | ⟨_,⟨_,hf⟩,_⟩ | ⟨_,_,_,hf⟩
  · cases hf
  · exact hw _ _ (congrArg Event.kind (Option.some.inj (h.symm.trans hf)))
  · exact hr _ _ _ (congrArg Event.kind (Option.some.inj (h.symm.trans hf)))

/-- The parameter address of the Bias tensor map that the loader keeps in register 7289. -/
def warmBiasMap : Value := .ptr 64 false (.param (param 11)) 0

set_option maxRecDepth 4096 in
/-- Every recorded loader checkpoint before the drain still holds the Bias map address. -/
theorem warmBiasMapAt {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pc shuffles votes : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hPc : pc < 1901) (hRank : 5 ≤ shuffles) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g pc F shuffles votes ends)
    (lane : Nat) (hl : lane < 32) :
    (cur.state lane).regs 7289 = some warmBiasMap := by
  let t := warpLane l g lane
  have hSame : SameWarp l g t := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
  have hWarp : 0 < warpIndex l t := by
    have h := hSame.2
    change warpIndex l g = warpIndex l t at h
    omega
  have hSize := cur.bounded lane hl
  have hPos : 5 ≤ cur.pos lane := by
    have hBound : ((X.tr t).take (cur.pos lane)).countP Execution.isShfl ≤
        ((X.tr t).take (cur.pos lane)).length := List.countP_le_length
    rw [cur.ordinals.shfl lane hl,List.length_take] at hBound
    omega
  obtain ⟨base,_,hBase,_,hPast,_⟩ := nonzeroCommonPrefix hp hX hSame.1.2.1 hWarp (hPos.trans hSize)
  obtain ⟨_,hAbi⟩ := actualReachBetween hPos hPast (cur.recorded lane hl) (cur.localSteps lane hl)
  exact loaderBiasMapPreserved hAbi (by rw [hBase.1])
    (by rw [(cur.checkpoint lane hl).1]; exact hPc) (ringShapeOfAt hBase)
    (holds_mem hBase.2.2.2.2 (by simp [nonzeroBarrierFacts,abiFacts]))

/-- A full-warp election at a warm Bias site of round `round`: every lane elects at its own
cursor, and its count of elections at that site reaches `round+1`. -/
theorem consumeWarmBiasElection {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round shuffles votes : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (k : Fin 6)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (warmBiasSite k) F shuffles votes ends)
    (hRank : shuffles = primingSearchShuffleCount batch+96+64*round)
    (hLower : ∀ lane < 32, round ≤ warmBiasSiteCount X (warpLane l g lane) (cur.pos lane) k)
    {dst pred : Nat}
    (hCode : kernel.code[warmBiasSite k]? = some ⟨none,.warp {
      kind := .elect, ty := none, dsts := [some dst,some pred],
      srcs := [], mask := some (.imm (-1)) }⟩)
    (hFresh : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ≠ dst ∧ pair.1 ≠ pred) :
    ∃ leader : Fin 32, ∃ done : SchedulerWarpReached l X g (warmBiasSite k+1)
      (fun lane => (pred,.pred (lane == leader.val)) :: F lane) shuffles votes ends,
      ∀ lane < 32, done.pos lane = cur.pos lane+1 ∧
        round+1 ≤ warmBiasSiteCount X (warpLane l g lane) (done.pos lane) k ∧
        ∃ inst, X.Elect (warpLane l g lane,cur.pos lane) (warmBiasSite k) 4294967295 inst
          leader := by
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  let post (lane leader : Nat) := inputElectReturn l (warpLane l g lane) (cur.state lane)
    dst pred leader
  let G (lane leader : Nat) := (pred,.pred (lane == leader)) :: F lane
  obtain ⟨leader,done,hDone⟩ := cur.consumeElectionWithPartnerBound hp hMax hg post G
    (warmBiasPartnerBound hp hMax.1 hFrame hg hw hb hLo hHi k cur hRank hLower)
    (fun lane hl => inputElectOut (cur.checkpoint lane hl).1 (cur.checkpoint lane hl).2.2.2.1
      (by fin_cases k <;> decide) (by fin_cases k <;> decide) hCode)
    (fun lane hl ld => by
      have hs := cur.checkpoint lane hl
      have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
      refine ⟨by simp [post,inputElectReturn,next,setReg,hs.1],hs.2.1,hs.2.2.1,hs.2.2.2.1,?_,?_⟩
      · simp [post,inputElectReturn,next,setReg,hLane]
      · exact holds_update (holds_update hs.2.2.2.2 (fun q hq => (hFresh lane hl q hq).1))
          (fun q hq => (hFresh lane hl q hq).2))
  refine ⟨leader,done,fun lane hl => ?_⟩
  obtain ⟨hPos,inst,he⟩ := hDone lane hl
  refine ⟨hPos,?_,inst,he⟩
  have hSucc := countP_take_succ (p := ElectOrd.atSites (fun pc => pc == warmBiasSite k))
    he warmBiasSite_atSites
  have h := hLower lane hl
  unfold warmBiasSiteCount ElectOrd.siteOrdinal at h ⊢
  rw [hPos]
  omega

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
