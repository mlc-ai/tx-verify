-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalTotal
import Kernels.TmlFa4Fwd.Flow.Code.Part142

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

def terminalCutoff (p : Params) (first : Nat) : Nat :=
  tilePrefix p (min p.batch (first+31))*p.heads

def terminalFirstTotalFrame (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  (7284,b32 (terminalGroupTotal p 0))::
    (7283,b32 (prefixWindow (groupLaneTiles p 0) 32 (laneOf l g)))::
      terminalFirstCountFrame p l g

def terminalSelectedFrame (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  [(7286,b32 (terminalCutoff p first)),(7285,b32 first),
    (7284,b32 (terminalGroupTotal p first)),
    (7283,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l g))),
    (7282,b32 (groupLaneTiles p first (laneOf l g))),(7143,b32 p.heads)] ++
    RowDrainRole.correction.roots p l g

def terminalSearchFrame (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  [(1658,b32 (g/l.block+1)),(7285,b32 first),(7280,b32 (terminalCutoff p first)),
    (7143,b32 p.heads)] ++ RowDrainRole.correction.roots p l g

private theorem firstTerminalRoute {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} (hg : g < l.threads) {t : TState}
    (ht : At t 9126 (terminalFirstTotalFrame p l g)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (if g/l.block < terminalCutoff p 0 then At u 9187 (terminalSelectedFrame p l g 0)
       else At u 9133 (terminalSearchFrame p l g 0)) := by
  let cta := g/l.block
  let bound := terminalCutoff p 0
  let total := terminalGroupTotal p 0
  let chosen := decide (cta < bound)
  let F := terminalFirstTotalFrame p l g
  have hCta : cta < 2^31 := (NamedBar.cta_lt hg).trans hp.grid.2.2
  have hBound : bound < 2^31 := hp.prefixWork_signed (Nat.min_le_left ..)
  have hTotal : total < 2^31 := hp.groupWindow_signed (Nat.zero_le p.batch)
    (by decide : 31 < 32) 32
  have hProduct : total*p.heads = bound := by
    change terminalGroupTotal p 0 * p.heads = _
    rw [terminalFirstTotal]
    rfl
  have hArgs : At t 9126 [(7284,b32 total),(7143,b32 p.heads),(1618,b32 cta)] :=
    ht.mono ⟨holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,
      holds_lookup ht.2.2.2.2 rfl,trivial⟩
  have hSegment : Seg kernel [] l g 3 9126
      [(7284,b32 total),(7143,b32 p.heads),(1618,b32 cta)] 9129
      [(753,.pred chosen),(7286,b32 bound),(7285,b32 0)] := by
    intro t ht
    seg_fp ht using
      first
      | rfl
      | simp only [b32,← BitVec.ofNat_mul,hProduct,compare,Option.getD_some,
        truncBits_ofNat (show total < 2^32 by omega) (by decide),
        truncBits_ofNat (hp.heads_signed.trans (by decide : 2^31 < 2^32)) (by decide),
        truncBits_ofNat (show bound < 2^32 by omega) (by decide),
        truncBits_ofNat (show cta < 2^32 by omega) (by decide),
        RowDrainRole.signedWord hBound,RowDrainRole.signedWord hCta,gt_iff_lt,Int.ofNat_lt,chosen]
  obtain ⟨v,hRun,hv⟩ := hSegment.apply hArgs
  have hSaved : Holds v.regs F := holdsSchedulerFrame ht.2.2.2.2
    (fun r hr => schedulerLocalFrame (lo := 9126) (len := 3)
      (by
        change ((kernel.code.drop 9126).take 3).all
          (fun i => [7284,7283,7143,7282,7153,1616,7506,1618].all
            (fun r => !(writesRegs i.op).contains r)) = true
        decide +kernel)
      (by decide +kernel) hRun ht.1.ge (by rw [ht.1]) hr)
    (fun _ hm => List.mem_map_of_mem hm)
  have hAt : At v 9129 ((753,.pred chosen)::(7286,b32 bound)::(7285,b32 0)::F) :=
    hv.mono ⟨hv.2.2.2.2.1,hv.2.2.2.2.2.1,hv.2.2.2.2.2.2.1,hSaved⟩
  obtain ⟨s,hBra,hS⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_9129 chosen hAt hAt.2.2.2.2.1 (by simp)
  let role := RowDrainRole.correction
  have hPath :=
    (role.drainLocals (by decide) (by decide) ht.1 (by decide +kernel) hRun).trans
      (role.drainLocals (by decide) (by decide) hAt.1 (by simp) hBra)
  by_cases hC : cta < bound
  · rw [show chosen = true from decide_eq_true hC] at hS
    refine ⟨s,hPath,?_⟩
    rw [ite_eq_left hC]
    exact hS.mono ⟨holds_lookup hS.2.2.2.2 rfl,holds_lookup hS.2.2.2.2 rfl,
      holds_lookup hS.2.2.2.2 rfl,holds_lookup hS.2.2.2.2 rfl,holds_lookup hS.2.2.2.2 rfl,
      holds_lookup hS.2.2.2.2 rfl,hS.2.2.2.2.2.2.2.2.2.2.2⟩
  · rw [show chosen = false from decide_eq_false hC] at hS
    have hBelow : cta+1 < 2^32 := by omega
    have hTail : Seg kernel [] l g 3 9130 [(1618,b32 cta),(7286,b32 bound)] 9133
        [(1658,b32 (cta+1)),(7285,b32 0),(7280,b32 bound)] := by
      intro t ht
      seg_fp ht using
        first
        | rfl
        | simp only [b32,show truncBits 32 (BitVec.ofInt 64 1) = BitVec.ofNat 64 1 from rfl,
            ← BitVec.ofNat_add,truncBits_ofNat (show cta < 2^32 by omega) (by decide),
            truncBits_ofNat hBelow (by decide)]
    have hArgs' : At s 9130 [(1618,b32 cta),(7286,b32 bound)] :=
      hS.mono ⟨holds_lookup hS.2.2.2.2 rfl,holds_lookup hS.2.2.2.2 rfl,trivial⟩
    obtain ⟨u,hu,hU⟩ := hTail.apply hArgs'
    let keep := (7143,b32 p.heads)::RowDrainRole.correction.roots p l g
    have hKeep : Holds u.regs keep := holdsSchedulerFrame
      (show Holds s.regs keep from
        ⟨holds_lookup hS.2.2.2.2 rfl,hS.2.2.2.2.2.2.2.2.2.2.2⟩)
      (fun r hr => schedulerLocalFrame (lo := 9130) (len := 3)
        (by
          change ((kernel.code.drop 9130).take 3).all
            (fun i => [7143,7153,1616,7506,1618].all
              (fun r => !(writesRegs i.op).contains r)) = true
          decide +kernel)
        (by decide +kernel) hu hArgs'.1.ge (by rw [hArgs'.1]) hr)
      (fun _ hm => List.mem_map_of_mem hm)
    refine ⟨u,hPath.trans (role.drainLocals (by decide) (by decide) hArgs'.1
      (by decide +kernel) hu),?_⟩
    rw [ite_eq_right hC]
    exact hU.mono ⟨hU.2.2.2.2.1,hU.2.2.2.2.2.1,hU.2.2.2.2.2.2.1,hKeep⟩

/-- The first correction terminal group is selected or opens the next group on the trace. -/
theorem terminalFirstRouteOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g n votes : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 9126
      (fun lane => terminalFirstTotalFrame p l (warpLane l g lane)) n votes ends) :
    if g/l.block < terminalCutoff p 0 then
      Nonempty (SchedulerWarpReached l X g 9187
        (fun lane => terminalSelectedFrame p l (warpLane l g lane) 0) n votes ends)
    else Nonempty (SchedulerWarpReached l X g 9133
      (fun lane => terminalSearchFrame p l (warpLane l g lane) 0) n votes ends) := by
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  by_cases hCut : g/l.block < terminalCutoff p 0
  · rw [ite_eq_left hCut]
    apply cur.advanceLocal
    intro lane hl
    have hSame := (Step.sameWarp_lane hBlock hg hl).1
    obtain ⟨u,hLocal,hAt⟩ := firstTerminalRoute hp hSame.1.2.1 (cur.checkpoint lane hl)
    rw [← hSame.1.2.2,ite_eq_left hCut] at hAt
    exact ⟨u,hLocal,hAt⟩
  · rw [ite_eq_right hCut]
    apply cur.advanceLocal
    intro lane hl
    have hSame := (Step.sameWarp_lane hBlock hg hl).1
    obtain ⟨u,hLocal,hAt⟩ := firstTerminalRoute hp hSame.1.2.1 (cur.checkpoint lane hl)
    rw [← hSame.1.2.2,ite_eq_right hCut] at hAt
    exact ⟨u,hLocal,hAt⟩

end PTX.Kernels.TmlFa4Fwd.Correction
