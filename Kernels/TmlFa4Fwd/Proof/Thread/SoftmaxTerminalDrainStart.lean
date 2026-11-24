-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalCursor
public import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalStatisticsCredit
public import Kernels.TmlFa4Fwd.Proof.Thread.RowDrainFirstWords
import Lemmas.Step.ProtectedReadProgress
import Kernels.TmlFa4Fwd.Flow.Code.Part119

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Correction Thread

/-- Return to the active scheduler after the terminal statistics publication.
The publication's own cursor supplies the exact continuation and retained registers. -/
theorem terminalDrainStartOfPublication {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (warp : Fin 8) (hw : warp.val = warpIndex l g)
    {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g 7616 ((5127,b32 (3+warp.val))::F))
    (hSync : c.pos+1 = (X.tr g).length →
      CtaBarrier.Released l.block (X.barriers (g/l.block)) (3+warpIndex l g)
        (((X.tr g).take c.pos).countP (Execution.isBarId (3+warpIndex l g)))) :
    Scores.Publishes X (g,c.pos) .final ∧
      ∃ next : OpeningTripCursor l X g 7617 F, next.pos = c.pos+1 := by
  obtain ⟨he,hPrefix,hTail⟩ := statsArrivalOfMaximal hp none warp hg c.positive c.bounded
    (c.checkpoint.mono ⟨c.checkpoint.2.2.2.2.1,trivial⟩)
    c.recorded c.localSteps c.remaining (fun h => ⟨X,hMax,rfl,c.released h⟩)
  have hPub : Scores.Publishes X (g,c.pos) .final := ⟨_,he,rfl⟩
  have hRelease (hLast : c.pos+1 = (X.tr g).length) : Step.Released l X g :=
    Protocol.Statistics.terminalProducerReleasedOfSynchronization hp hMax.1 hg
      (hw ▸ warp.isLt) hPub hLast (hSync hLast)
  exact ⟨hPub,⟨⟨c.pos+1,next c.ready,next c.ready,c.ending,Nat.succ_pos _,len_of_get he,
    hRelease,c.checkpoint.next.mono c.checkpoint.2.2.2.2.2,hPrefix,hTail,.refl⟩,rfl⟩⟩

/-- The first scheduler word after publication is the protected CuQ endpoint
of this lane, or the initialized zero when the lane is outside the first group. -/
def terminalFirstWord (p : Params) (l : Launch) (g : Nat) : Nat :=
  if laneOf l g ≤ p.batch then p.qOffset (laneOf l g) else 0

/-- The actual post-publication lane reaches its first scheduler shuffle,
including a real protected CuQ read when the lane is selected by the guard. -/
theorem terminalDrainFirstShuffleOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g : Nat} (hg : g < l.threads)
    (c : OpeningTripCursor l X g 7617 (RowDrainRole.softmax.guarded p l g)) :
    Nonempty (OpeningTripCursor l X g 7622
      ((7259,b32 (terminalFirstWord p l g))::RowDrainRole.softmax.roots p l g)) := by
  let role := RowDrainRole.softmax
  let F := role.guarded p l g
  let a := next (setReg c.ready 7259 (b32 0))
  have hFirst : run kernel [] l g 1 c.ready = some a := by
    apply run_local Flow.code_7617 rfl c.checkpoint
    rw [execLocalA_nil,execLocal_move rfl]
    rfl
  have hMove := role.drainLocals (n := 1) (by decide) (by decide) c.checkpoint.1 (by simp) hFirst
  have hAt : At a 7618 ((7259,b32 0)::F) := c.checkpoint.set (by
    simp [RowDrainRole.guarded,RowDrainRole.guardReg,RowDrainRole.roots,
      RowDrainRole.batchReg,RowDrainRole.frame,RowDrainRole.laneReg,RowDrainRole.ctaReg])
  let flag := decide (p.batch < laneOf l g)
  have hFlag : a.regs 652 = some (.pred flag) := hAt.2.2.2.2.2.1
  obtain ⟨u,hBranch,hu⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_7618 flag hAt hFlag (by simp)
  have hTau := role.drainLocals (n := 1) (by decide) (by decide) hAt.1 (by simp) hBranch
  have hPath := c.localSteps.trans (hMove.trans hTau)
  by_cases hLane : laneOf l g ≤ p.batch
  · have hFalse : flag = false := decide_eq_false (by omega)
    have hu' : At u 7619 (role.roots p l g) := by
      rw [hFalse] at hu
      exact hu.mono hu.2.2.2.2.2.2
    obtain ⟨t,ht,hRead⟩ := role.firstTemplate hp hLane hu'
    let a : Acc := {loc := globalLoc (p.cuQBase+4*laneOf l g),size := 4}
    let value := b32 (p.qOffset (laneOf l g))
    let bytes := value.toBytes.map some
    have hValue : HasValue m a.loc value := by
      simpa [a,value,b32,HasValue,Value.bytes] using hp.cuQ (laneOf l g) hLane
    have hn : Next kernel Assumptions.all l g c.before t (.read a (afterLoad t [7259])) :=
      ⟨hPath.trans hRead.steps,hRead.stop⟩
    obtain ⟨he,hPre,hTail⟩ := Step.protected_read_of_maximal hMax hg
      (a := a) (value := value) rfl hValue (hCuQ _ hLane) hn c.recorded c.remaining c.positive
        c.bounded c.released (Assumptions.wf_snoc_initial hMax.1)
    have hRebuild := PTX.Proof.rebuild_scalar (v := value) (by decide : 0 < 4) rfl
    have hState : afterLoad t [7259] bytes = next (setReg t 7259 value) := by
      rw [afterLoad_ok ht.2.1 ht.2.2.1 hRebuild]
      simp [next,setReg,ht.2.1,ht.2.2.1]
    rw [hState] at hPre hTail
    have hFrame : At (next (setReg t 7259 value)) 7622 ((7259,value)::role.roots p l g) :=
      (ht.mono ht.2.2.2.2.2).set (by simp [role,RowDrainRole.roots,RowDrainRole.batchReg,
        RowDrainRole.frame,RowDrainRole.laneReg,RowDrainRole.ctaReg])
    have hRelease := releasedIfLast (l := l) he (by simp [Kind.resume])
    exact ⟨⟨c.pos+1,_,_,c.ending,Nat.succ_pos _,len_of_get he,hRelease,
      by simpa only [terminalFirstWord,ite_eq_left hLane,value] using hFrame,hPre,hTail,.refl⟩⟩
  · have hTrue : flag = true := decide_eq_true (by omega)
    rw [hTrue] at hu
    have hFrame : At u 7622 ((7259,b32 (terminalFirstWord p l g))::role.roots p l g) := by
      simp only [terminalFirstWord,ite_eq_right hLane]
      exact hu.mono ⟨hu.2.2.2.2.1,hu.2.2.2.2.2.2⟩
    exact ⟨⟨c.pos,c.before,u,c.ending,c.positive,c.bounded,c.released,hFrame,
      c.recorded,c.remaining,hPath⟩⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
