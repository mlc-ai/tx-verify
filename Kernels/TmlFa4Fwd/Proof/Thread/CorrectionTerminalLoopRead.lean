-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalLoopEntry
import Kernels.TmlFa4Fwd.Flow.Code.Part142
import Lemmas.Flow.CountTake
import Lemmas.Step.ProtectedReadProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

/-- Protected cumulative words entering the down shuffle of a later group. -/
def terminalLaterWord (p : Params) (l : Launch) (g first : Nat) : Nat :=
  drainCuQ p (first+laneOf l g)

def terminalLaterDownFrame (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  [(7281,b32 (terminalLaterWord p l g first)),(1660,b32 (first+laneOf l g)),
    (756,.pred (decide (laneOf l g = 31)))] ++ terminalLaterGroupFrame p l g first

private def terminalGroupWords (p : Params) (l : Launch) (g first : Nat) :
    List (Nat × Value) :=
  (7281,b32 (terminalLaterWord p l g first))::(1660,b32 (first+laneOf l g))::
    terminalLaterGroupFrame p l g first

private theorem prepareLaterDown {p : Params} {l : Launch} {g first : Nat} {t : TState}
    (ht : At t 9145 (terminalGroupWords p l g first)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 9146 (terminalLaterDownFrame p l g first) := by
  have hLane : laneOf l g < 2^32 := (Nat.mod_lt _ (by decide : 0 < 32)).trans (by decide)
  have hs : At t 9145 [(1616,b32 (laneOf l g))] := by
    apply ht.mono
    exact ⟨holds_lookup ht.2.2.2.2 rfl,trivial⟩
  have hLane64 : laneOf l g < 2^64 := hLane.trans (by decide)
  have hCore : ∃ u, run kernel [] l g 1 t = some u ∧
      At u 9146 [(756,.pred (decide (laneOf l g = 31)))] := by
    seg_fp hs using
      (simp [compare,truncBits_ofNat hLane (by decide),toNat_ofNat_lt hLane64,
        show (truncBits 32 31#64).toNat = 31 by decide]
       all_goals omega)
  obtain ⟨u,hr,hu⟩ := hCore
  obtain ⟨hPath,hKeep⟩ := terminalLocalsKeep ht (by decide) (by decide) (by
    dsimp only [terminalGroupWords,terminalLaterGroupFrame,RowDrainRole.roots,
      RowDrainRole.frame,RowDrainRole.batchReg,RowDrainRole.laneReg,RowDrainRole.ctaReg,
      List.cons_append,List.nil_append,List.map]
    decide +kernel) (by simp) hr
  exact ⟨u,hPath,hu.mono ⟨hKeep.1,hKeep.2.1,hu.2.2.2.2.1,hKeep.2.2⟩⟩

private theorem laterReadCursor {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g first : Nat} (hg : g < l.threads)
    (c : OpeningTripCursor l X g 9141 (terminalSearchRead p l g first)) :
    ∃ u : OpeningTripCursor l X g 9145 (terminalGroupWords p l g first),
      u.ending = c.ending ∧
      (∀ f : Event → Bool, (∀ a b, f ⟨9144,.rd a b⟩ = false) →
        ((X.tr g).take u.pos).countP f = ((X.tr g).take c.pos).countP f) := by
  let index := first+laneOf l g
  let F := terminalSearchRead p l g first
  let group := terminalLaterGroupFrame p l g first
  let carry := (1660,b32 index)::group
  have hCk : At c.ready 9141 F := c.checkpoint
  obtain ⟨s,hBranch,hs⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_9141 (decide (p.batch < index)) hCk hCk.2.2.2.2.2.1 (by simp)
  have hPath := c.localSteps.trans
    (RowDrainRole.correction.drainLocals (by decide) (by decide) hCk.1 (by simp) hBranch)
  by_cases hi : index ≤ p.batch
  · have hAt : At s 9142 carry := by
      simpa only [decide_eq_false (Nat.not_lt_of_ge hi),Bool.false_eq_true,ite_false] using
        hs.mono (G := carry) ⟨hs.2.2.2.2.1,hs.2.2.2.2.2.2.2⟩
    have hRange := hp.ranges ⟨p.cuQBase,4*(p.batch+1)⟩ (by simp [Params.inputRegions])
    change p.cuQBase+4*(p.batch+1) ≤ 2^64 at hRange
    have h31 : index < 2^31 := hi.trans_lt hp.shape.2.1
    have h32 : index < 2^32 := by omega
    have hOff : 4*index < 2^64 := by omega
    have hBase : p.cuQBase < 2^64 := by omega
    have hAddr : p.cuQBase+4*index < 2^64 := by omega
    have h4 : toSigned 32 (truncBits 32 (BitVec.ofInt 64 4)) = 4 := rfl
    have hOffset : BitVec.ofInt 64 ((index : Int)*4) = BitVec.ofNat 64 (4*index) := by
      change BitVec.ofInt 64 ((index : Int) * ((4 : Nat) : Int)) = _
      rw [← Int.natCast_mul,BitVec.ofInt_natCast,Nat.mul_comm]
    have hOperands : At s 9142 [(1660,b32 index),(7506,b64 p.cuQBase)] :=
      hAt.mono ⟨hAt.2.2.2.2.1,holds_lookup hAt.2.2.2.2 rfl,trivial⟩
    have hAddress : Seg kernel [] l g 2 9142 [(1660,b32 index),(7506,b64 p.cuQBase)]
        9144 [(9533,b64 (p.cuQBase+4*index))] := by
      intro t ht
      seg_fp ht using simp only [b64,truncBits_ofNat h32 (by decide),
        RowDrainRole.signedWord h31,h4,show (some IType.s == some IType.s) = true from rfl,
        ↓reduceIte,show 2*32 = 64 from rfl,hOffset,truncBits_ofNat hOff (by decide),
        truncBits_ofNat hBase (by decide),← BitVec.ofNat_add,truncBits_ofNat hAddr (by decide)]
    obtain ⟨t,hRun,ht⟩ := hAddress.apply hOperands
    obtain ⟨hLocal,hKeep⟩ := terminalLocalsKeep hAt (by decide) (by decide) (by
      dsimp only [carry,group,terminalLaterGroupFrame,RowDrainRole.roots,
        RowDrainRole.frame,RowDrainRole.batchReg,RowDrainRole.laneReg,RowDrainRole.ctaReg,
        List.cons_append,List.nil_append,List.map]
      decide +kernel) (by decide +kernel) hRun
    let a : Acc := {loc := globalLoc (p.cuQBase+4*index),size := 4}
    let word := b32 (p.qOffset index)
    let bytes := word.toBytes.map some
    have hAl := hp.alignment.2.2.2.2.2.2.2.2.1
    have hAlign : (p.cuQBase+4*index)%4 = 0 := by omega
    have hCore := RowDrainRole.correction.drainCore (l := l) (g := g) (s := t)
      (by rw [ht.1]; decide) (by rw [ht.1]; decide)
    have hOut : out kernel Assumptions.all l g t = .ev (.read a (afterLoad t [7281])) := by
      rw [hCore,out_event ht.2.2.2.1 (ht.1.symm ▸ Flow.code_9144) rfl rfl]
      exact congrArg Out.ev (loadTmpl_global ht.2.1 ht.2.2.2.2.1 hAddr (by decide) hAlign)
    have hn : Next kernel Assumptions.all l g c.before t (.read a (afterLoad t [7281])) :=
      ⟨hPath.trans hLocal,hOut⟩
    have hInitial : HasValue m a.loc word := by
      simpa [a,word,b32,HasValue,Value.bytes] using hp.cuQ index hi
    obtain ⟨he,hPast,hTail⟩ := Step.protected_read_of_maximal hMax hg
      (a := a) (value := word) rfl hInitial (hCuQ _ hi) hn c.recorded c.remaining c.positive
      c.bounded c.released (Assumptions.wf_snoc_initial hMax.1)
    have hRebuild := PTX.Proof.rebuild_scalar (v := word) (by decide : 0 < 4) rfl
    have hState : afterLoad t [7281] bytes = next (setReg t 7281 word) := by
      rw [afterLoad_ok ht.2.1 ht.2.2.1 hRebuild]
      simp [next,setReg,ht.2.1,ht.2.2.1]
    rw [hState] at hPast hTail
    have hu : At (next (setReg t 7281 word)) 9145 (terminalGroupWords p l g first) := by
      have hSet := (ht.mono hKeep : At t 9144 carry).set (r := 7281) (v := word) (by
        simp [carry,group,terminalLaterGroupFrame,RowDrainRole.roots,
          RowDrainRole.frame,RowDrainRole.batchReg,RowDrainRole.laneReg,RowDrainRole.ctaReg])
      simpa only [terminalGroupWords,terminalLaterWord,drainCuQ,index,ite_eq_left hi] using hSet
    refine ⟨⟨c.pos+1,_,_,c.ending,Nat.succ_pos _,len_of_get he,
      Prologue.releasedIfLast he (by simp [Kind.resume]),hu,hPast,hTail,.refl⟩,rfl,?_⟩
    intro f hf
    exact countP_take_succ_false (p := f) he (ht.1.symm ▸ hf a bytes)
  · have hu : At s 9145 (terminalGroupWords p l g first) := by
      have hAt : At s 9145 F := by
        simpa only [decide_eq_true (Nat.lt_of_not_ge hi),ite_true] using hs
      have hWord : terminalLaterWord p l g first = 0 := by
        simp [terminalLaterWord,drainCuQ,index,hi]
      rw [terminalGroupWords,hWord]
      exact hAt.mono ⟨hAt.2.2.2.2.2.2.1,hAt.2.2.2.2.1,hAt.2.2.2.2.2.2.2⟩
    exact ⟨⟨c.pos,c.before,s,c.ending,c.positive,c.bounded,c.released,hu,
      c.recorded,c.remaining,hPath⟩,rfl,fun _ _ => rfl⟩

/-- A later group issues every guarded CuQ read and reaches the real down shuffle. -/
theorem terminalDrainReadsNextGroup {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g first shuffles votes : Nat}
    (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 9141
      (fun lane => terminalSearchRead p l (warpLane l g lane) first) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 9146
      (fun lane => terminalLaterDownFrame p l (warpLane l g lane) first) shuffles votes ends) := by
  classical
  let thread := warpLane l g
  let F := fun lane => terminalLaterDownFrame p l (thread lane) first
  have hEach (lane : Nat) (hl : lane < 32) :
      ∃ u : OpeningTripCursor l X (thread lane) 9146 (F lane),
        u.ending = ends lane ∧
        ((X.tr (thread lane)).take u.pos).countP Execution.isShfl = shuffles ∧
        ((X.tr (thread lane)).take u.pos).countP isFullWarpVote = votes := by
    let c : OpeningTripCursor l X (thread lane) 9141
        (terminalSearchRead p l (thread lane) first) :=
      ⟨cur.pos lane,cur.before lane,cur.state lane,ends lane,cur.positive lane hl,
        cur.bounded lane hl,cur.released lane hl,cur.checkpoint lane hl,cur.recorded lane hl,
        cur.continuation lane hl,cur.localSteps lane hl⟩
    have hb : l.block%32 = 0 := by rw [hp.block]
    obtain ⟨u,hEnd,hCount⟩ := laterReadCursor hp hMax hCuQ
      (Step.sameWarp_lane hb hg hl).1.1.2.1 c
    obtain ⟨v,hLocal,hv⟩ := prepareLaterDown u.checkpoint
    exact ⟨⟨u.pos,u.before,v,u.ending,u.positive,u.bounded,u.released,hv,u.recorded,u.remaining,
      u.localSteps.trans hLocal⟩,hEnd,
      (hCount _ (fun _ _ => rfl)).trans (cur.ordinals.shfl lane hl),
      (hCount _ (fun _ _ => rfl)).trans (cur.ordinals.vote lane hl)⟩
  have hData (lane : Nat) (hl : lane < 32) : ∃ (pos : Nat) (before ready : TState),
      0 < pos ∧ pos ≤ (X.tr (thread lane)).length ∧
      (pos = (X.tr (thread lane)).length → Step.Released l X (thread lane)) ∧
      ((X.tr (thread lane)).take pos).countP Execution.isShfl = shuffles ∧
      ((X.tr (thread lane)).take pos).countP isFullWarpVote = votes ∧
      Run kernel Assumptions.all l (thread lane) {} ((X.tr (thread lane)).take pos) (some before) ∧
      Run kernel Assumptions.all l (thread lane) before ((X.tr (thread lane)).drop pos)
        (ends lane) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) before ready ∧
      At ready 9146 (F lane) := by
    obtain ⟨u,hE,hS,hV⟩ := hEach lane hl
    exact ⟨u.pos,u.before,u.ready,u.positive,u.bounded,u.released,hS,hV,
      u.recorded,hE ▸ u.remaining,u.localSteps,u.checkpoint⟩
  let _ : Nonempty TState := ⟨cur.state 0⟩
  choose! pos before ready hPos hBound hRel hSh hV hRec hTail hLocal hAt using hData
  exact ⟨⟨⟨pos,before,ready,⟨hSh,hV⟩,hTail,hLocal,hAt⟩,hPos,hBound,hRel,hRec⟩⟩

end PTX.Kernels.TmlFa4Fwd.Correction
