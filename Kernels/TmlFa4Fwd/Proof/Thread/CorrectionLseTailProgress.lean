-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionLseHeadProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionLseStoreProgress
import Kernels.TmlFa4Fwd.Proof.CorrectionLseComplete
import Kernels.TmlFa4Fwd.Proof.CorrectionLseZero

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue

private def localCursor {l : Launch} {X : Execution} {g pc pc' : Nat}
    {F F' : List (Nat × Value)} (c : OpeningTripCursor l X g pc F) {u : TState}
    (hAt : At u pc' F')
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) c.ready u) :
    OpeningTripCursor l X g pc' F' :=
  ⟨c.pos,c.before,u,c.ending,c.positive,c.bounded,c.released,hAt,c.recorded,c.remaining,
    c.localSteps.trans hLocal⟩

private theorem lseFresh {F : List (Nat × Value)} (stage : Fin 2)
    (h : (F.map Prod.fst).all (fun r => decide
      (r ≠ lseLogReg stage ∧ r ≠ lseFmaReg stage ∧ r ≠ lseMulReg stage ∧ r ≠ lseOutReg stage)) =
      true) :
    ∀ rv ∈ F, rv.1 ≠ lseLogReg stage ∧ rv.1 ≠ lseFmaReg stage ∧
      rv.1 ≠ lseMulReg stage ∧ rv.1 ≠ lseOutReg stage :=
  fun _ hm => of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))

/-- A lane in a maximal execution has made both guarded LSE writes and can search
for another request. The retained frame includes the final staging phase. -/
structure LseTailReached (p : Params) (l : Launch) (X : Execution) (g batch : Nat) where
  source : LseHeadReached p l X g batch
  cursor : OpeningTripCursor l X g (lseGuardPc 1+2) source.source.staging.words.chunkFrame

theorem LseHeadReached.tailOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch : Nat} (hg : g < l.threads) (hw : warpIndex l g < 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (c : LseHeadReached p l X g batch) : Nonempty (LseTailReached p l X g batch) := by
  let words := c.source.staging.words
  let F := words.chunkFrame
  let coord := assignedCoordinates p batch (g/l.block)
  let packed := (9525,b64 (p.lseLoc (p.qOffset batch) coord.2).addr)
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have ⟨hTile,hHead⟩ : 256 * coord.1 < p.qLength batch ∧ coord.2 < p.heads :=
    assignedCoordinates_valid hp hLo hHi
  obtain ⟨s,_,hs,_,hPositive,_⟩ := hp.scales
  have hScale : valFloat .f32 (b32 p.scaleLog2Bits) = .ok (s : ℝ) := by
    have hBound := (hp.values (12,p.scaleLog2Bits) (by simp [Params.scalarWords])).1
    exact valFloat_b32 (by change p.scaleLog2Bits < 2^32 at hBound; omega) hs
  have hsPos : 0 < (s : ℝ) := by exact_mod_cast hPositive
  have hAt : At c.cursor.ready (lsePc 0) (packed::F) := c.cursor.checkpoint
  obtain ⟨v0,u0,hSize0,hU0,hLocal0⟩ := finalLseOfDenominatorLocal (l := l) (g := g)
    0 words.firstSum words.firstMaximum words.firstValid hAt
    (holds_lookup hAt.2.2.2.2 (by rfl)) (holds_lookup hAt.2.2.2.2 (by rfl))
    (holds_lookup hAt.2.2.2.2 (by rfl)) (holds_lookup hAt.2.2.2.2 (by rfl))
    hScale hsPos (lseFresh 0 rfl)
  have hU0' : At u0 9065
      ([(1635,b32 (p.qLength batch)),(5967,b32 (256*coord.1)),(1613,b32 (rowOf l g)),
        packed,(1655,v0)] ++ F) := by
    refine hU0.mono ⟨holds_lookup hU0.2.2.2.2 (by rfl),holds_lookup hU0.2.2.2.2 (by rfl),
      ?_,hU0.2.2.2.2.2.1,hU0.2.2.2.2.1,hU0.2.2.2.2.2.2⟩
    have hr := holds_lookup hU0.2.2.2.2
      (show ((lseOutReg 0,v0)::packed::F).lookup 1613 = some
        (b32 (rowOf l (warpLane l g (laneOf l g)))) from rfl)
    simpa only [hSelf] using hr
  obtain ⟨_,hW0,hTest0,hGuard0⟩ := prepareFirstLseTail hp hb hTile v0 hU0'
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨_,d0,_,_⟩ := finishLseTailOfMaximal hp hMax hg hw 0 hb hHead v0 hSize0
    (localCursor c.cursor hW0 (hLocal0.trans hGuard0)) hTest0
  let H := [(7077,b32 (p.qLength batch-256*coord.1)),(1613,b32 (rowOf l g)),
    (7491,b64 (p.lseLoc (p.qOffset batch+256*coord.1+rowOf l g) coord.2).addr)] ++ F
  have hFresh (rv : Nat × Value) (hm : rv ∈ H) : rv.1 ≠ 742 := by
    intro he
    have hMem := List.mem_map_of_mem (f := Prod.fst) hm
    rw [he] at hMem
    exact (of_decide_eq_true rfl : 742 ∉ H.map Prod.fst) hMem
  obtain ⟨_,hPredicate,hA⟩ := secondLsePredicate (l := l) (g := g) words.sum d0.checkpoint
    (holds_lookup d0.checkpoint.2.2.2.2 (by rfl)) hFresh
  have hA' := hA.mono hA.2.2.2.2.2
  obtain ⟨v1,u1,hSize1,hU1,hLocal1⟩ := finalLseOfDenominatorLocal (l := l) (g := g)
    1 words.sum words.maximum words.valid hA'
    (holds_lookup hA'.2.2.2.2 (by rfl)) (holds_lookup hA'.2.2.2.2 (by rfl))
    (holds_lookup hA'.2.2.2.2 (by rfl)) hA.2.2.2.2.1 hScale hsPos (lseFresh 1 rfl)
  have hU1' : At u1 9079
      ([(7077,b32 (p.qLength batch-256*coord.1)),(1613,b32 (rowOf l g)),
        (7491,b64 (p.lseLoc (p.qOffset batch+256*coord.1+rowOf l g) coord.2).addr),
        (1656,v1)] ++ F) :=
    hU1.mono ⟨hU1.2.2.2.2.2.1,hU1.2.2.2.2.2.2.1,hU1.2.2.2.2.2.2.2.1,
      hU1.2.2.2.2.1,hU1.2.2.2.2.2.2.2.2⟩
  obtain ⟨_,hW1,hTest1,hGuard1⟩ := prepareSecondLseTail hp hb hTile v1 hU1'
    (by set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨_,d1,_,_⟩ := finishLseTailOfMaximal hp hMax hg hw 1 hb hHead v1 hSize1
    (localCursor d0 hW1 ((hPredicate.trans hLocal1).trans hGuard1)) hTest1
  exact ⟨⟨c,d1⟩⟩

end PTX.Kernels.TmlFa4Fwd.Correction
