-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalFirstRoute
import Kernels.TmlFa4Fwd.Proof.MmaScanCounter
import Kernels.TmlFa4Fwd.Flow.Code.Part142

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread Mma

/-- The next group's index, preceding cutoff, and scheduler operands. -/
def terminalLaterGroupFrame (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  [(7285,b32 first),(7280,b32 (tilePrefix p first*p.heads)),(1658,b32 (g/l.block+1)),
    (7143,b32 p.heads)] ++ RowDrainRole.correction.roots p l g

def terminalSearchRead (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  [(1660,b32 (first+laneOf l g)),(755,.pred (decide (p.batch < first+laneOf l g))),
    (7281,b32 0)] ++ terminalLaterGroupFrame p l g first

/-- Transport straight-line local progression and its checked register frame. -/
theorem terminalLocalsKeep {l : Launch} {g start n : Nat} {s t : TState}
    {F : List (Nat × Value)} (hs : At s start F)
    (hLo : RowDrainRole.correction.start ≤ start)
    (hHi : start+n ≤ RowDrainRole.correction.exitFloor)
    (hWrites : ((kernel.code.drop start).take n).all
      (fun ins => (F.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) = true)
    (hStraight : ((kernel.code.drop start).take (n-1)).all
      (fun ins => schedulerFallsThrough ins.op) = true)
    (hRun : run kernel [] l g n s = some t) :
    Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t ∧ Holds t.regs F := by
  refine ⟨RowDrainRole.correction.drainLocals hLo hHi hs.1 hStraight hRun,?_⟩
  exact holdsSchedulerFrame hs.2.2.2.2
    (fun _ hr => schedulerLocalFrame hWrites hStraight hRun hs.1.ge (by rw [hs.1]) hr)
    (fun _ h => List.mem_map_of_mem h)

private theorem laterReadGuard {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g first : Nat} (hFirst : first < p.batch) {t : TState}
    (ht : At t 9138 ((1659,b32 first)::terminalLaterGroupFrame p l g first)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 9141 (terminalSearchRead p l g first) := by
  let lane := laneOf l g
  let ix := first+lane
  let F := terminalLaterGroupFrame p l g first
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hBatch := hp.shape.2.1
  have hTotal := hp.shape.2.2.2.2.2
  change p.qOffset p.batch + 256 * p.batch < 2^30 at hTotal
  have hIndex : ix < 2^31 := by dsimp only [ix]; omega
  have hFirst32 : first < 2^32 := by omega
  have hLane32 : lane < 2^32 := by omega
  have hIdx32 : ix < 2^32 := by omega
  have hBatch32 : p.batch < 2^32 := by omega
  have hArgs : At t 9138 [(1659,b32 first),(1616,b32 lane),(7153,b32 p.batch)] :=
    ht.mono ⟨holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,
      holds_lookup ht.2.2.2.2 rfl,trivial⟩
  have hSegment : Seg kernel [] l g 3 9138
      [(1659,b32 first),(1616,b32 lane),(7153,b32 p.batch)] 9141
      [(1660,b32 ix),(755,.pred (decide (p.batch < ix))),(7281,b32 0)] := by
    intro t ht
    seg_fp ht using
      first
      | rfl
      | simp only [ix,b32,← BitVec.ofNat_add,truncBits_ofNat hFirst32 (by decide),
          truncBits_ofNat hIdx32 (by decide),truncBits_ofNat hLane32 (by decide),
          truncBits_ofNat hBatch32 (by decide),compare,Option.getD_some,
          RowDrainRole.signedWord hIndex,RowDrainRole.signedWord hBatch,Int.ofNat_lt,gt_iff_lt]
  obtain ⟨u,hu,hU⟩ := hSegment.apply hArgs
  have hF : At t 9138 F := ht.mono ht.2.2.2.2.2
  obtain ⟨hr,hKeep⟩ := terminalLocalsKeep hF (by decide) (by decide) (by
    change ((kernel.code.drop 9138).take 3).all (fun ins =>
      [7285,7280,1658,7143,7153,1616,7506,1618].all
        (fun r => !(writesRegs ins.op).contains r)) = true
    decide +kernel) (by decide +kernel) hu
  exact ⟨u,hr,hU.mono ⟨hU.2.2.2.2.1,hU.2.2.2.2.2.1,hU.2.2.2.2.2.2.1,hKeep⟩⟩

private theorem laterGroupPath {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g first : Nat} (hMore : first+31 < p.batch) {t : TState}
    (ht : At t 9133 (terminalSearchFrame p l g first)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 9141 (terminalSearchRead p l g (first+31)) := by
  let cta := g/l.block
  let F := [(7280,b32 (terminalCutoff p first)),(7143,b32 p.heads),
    (1616,b32 (laneOf l g)),(7506,b64 p.cuQBase)]
  have hNext : first+31 < 2^31 := hMore.trans hp.shape.2.1
  have hAt : At t 9133 (groupScanFacts .correctionDrain first p.batch cta ++ F) := by
    apply ht.mono
    apply (holds_append ..).mpr
    exact ⟨⟨holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,
      holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,trivial⟩,
      ⟨holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,
        holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,trivial⟩⟩
  obtain ⟨s,hs,hS⟩ := advanceGroupScanPreserving (l := l) (g := g) .correctionDrain
    hNext hp.shape.2.1 (by
      change ((kernel.code.drop 9133).take 5).all (fun i =>
        [7280,7143,1616,7506].all (fun r => !(writesRegs i.op).contains r)) = true
      decide +kernel) hAt
  rw [ite_eq_right (Nat.not_le_of_lt hMore),Nat.min_eq_left hMore.le] at hS
  have hBefore : terminalCutoff p first = tilePrefix p (first+31)*p.heads := by
    unfold terminalCutoff
    rw [Nat.min_eq_right hMore.le]
  have hReady : At s 9138 ((1659,b32 (first+31))::terminalLaterGroupFrame p l g (first+31)) := by
    apply hS.mono
    have hRegs := hS.2.2.2.2
    have hOld : s.regs 7280 = some (b32 (terminalCutoff p first)) :=
      holds_lookup hRegs rfl
    rw [hBefore] at hOld
    exact ⟨hRegs.1,holds_lookup hRegs rfl,hOld,holds_lookup hRegs rfl,holds_lookup hRegs rfl,
      holds_lookup hRegs rfl,holds_lookup hRegs rfl,holds_lookup hRegs rfl,holds_lookup hRegs rfl,
      trivial⟩
  obtain ⟨u,hu,hU⟩ := laterReadGuard hp hMore hReady
  exact ⟨u,(run_rtg hs).trans hu,hU⟩

/-- An active CTA that misses the current group must reach the next actual read guard. -/
theorem terminalLaterGroupEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g first shuffles votes : Nat} (hMore : first+31 < p.batch)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 9133
      (fun lane => terminalSearchFrame p l (warpLane l g lane) first) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 9141
      (fun lane => terminalSearchRead p l (warpLane l g lane) (first+31)) shuffles votes ends) := by
  apply cur.advanceLocal
  intro lane hl
  exact laterGroupPath hp hMore (cur.checkpoint lane hl)

end PTX.Kernels.TmlFa4Fwd.Correction
