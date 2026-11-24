-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.Thread.EpilogueScanProgress
import Kernels.TmlFa4Fwd.Proof.EpilogueProgram
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Lemmas.Step.ProtectedReadProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof Prologue EventFrame

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

private theorem consumeEndpointOfMaximal {g pos batch : Nat} (hg : g < l.threads) (slot : Fin 2)
    (hIndex : batch + slot.val ≤ p.batch) (hProtect : DrainCuQProtected p X) {before t u : TState}
    {ending : Option TState}
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before t)
    (he : EStep kernel [] l g t (endpointEvent p batch slot) (some u))
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some before))
    (hTail : Run kernel Assumptions.all l g before ((X.tr g).drop pos) ending) (hPos : 0 < pos)
    (hBound : pos ≤ (X.tr g).length) (hRelease : pos = (X.tr g).length → Step.Released l X g) :
    X.get (g,pos) = some (endpointEvent p batch slot) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos+1)) ending := by
  let value := b32 (p.qOffset (batch + slot.val))
  let a := endpointAccess p (batch + slot.val)
  have hPc := estep_source_pc he
  change 2953 + slot.val = t.pc at hPc
  have hSlot := slot.isLt
  obtain ⟨tm,hOut,hFire⟩ := he
  change Fires t.pc tm ⟨2953+slot.val,.rd a (value.toBytes.map some)⟩ (some u) at hFire
  obtain ⟨k,rfl⟩ := fires_read_tmpl hFire
  obtain ⟨bytes,_,hKind,hU⟩ := hFire
  have hBytes := (Kind.rd.inj (congrArg Event.kind hKind)).2
  change value.toBytes.map some = bytes at hBytes
  subst bytes
  obtain rfl := Option.some.inj hU
  have hModel : out kernel Assumptions.all l g t = out kernel [] l g t :=
    epilogue_out_all_eq_nil (.inl ⟨by omega,by omega⟩)
  have hn : Next kernel Assumptions.all l g before t (.read a k) :=
    ⟨hLocal,hModel.trans hOut⟩
  obtain ⟨hGet,hNew,hRest⟩ := Step.protected_read_of_maximal hMax hg (a := a) (value := value) rfl
    (hp.cuQ _ hIndex) (hProtect _ hIndex) hn hPrefix hTail hPos hBound hRelease
    (Assumptions.wf_snoc_initial hMax.1)
  refine ⟨?_,hNew,hRest⟩
  change X.get (g,pos) = some ⟨2953+slot.val,.rd a (value.toBytes.map some)⟩
  rwa [← hPc] at hGet

/-- The two protected endpoint reads of the selected output tile are forced by maximality. -/
theorem SchedulerWarpReached.enterWritebackOfMaximal {g cta first batch shuffles votes : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2899
      (fun lane => tileCoordinateFacts p cta first batch lane (F lane)) shuffles votes ends)
    (hFirst : first ≤ batch) (hGroup : batch < first+31) (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ cta) (hHi : cta < tilePrefix p (batch+1) * p.heads)
    (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ schedulerFrameRegs)
    (hStartup : ∀ lane < 32, schedulerStartupFrame p l (warpLane l g lane) ⊆ F lane)
    (hProtect : DrainCuQProtected p X) :
    Nonempty (SchedulerWarpReached l X g 2958
      (fun lane => outputReadyFacts p l batch (assignedCoordinates p batch cta).2
        (assignedCoordinates p batch cta).1 lane (F lane)) shuffles votes ends) := by
  let _ : Nonempty TState := ⟨cur.state 0⟩
  let thread := warpLane l g
  let pos := fun lane => cur.pos lane + 2
  let facts := fun lane => outputReadyFacts p l batch (assignedCoordinates p batch cta).2
    (assignedCoordinates p batch cta).1 lane (F lane)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : ∃ before state,
      At state 2958 (facts lane) ∧
      X.get (thread lane,cur.pos lane) = some (endpointEvent p batch 0) ∧
      X.get (thread lane,cur.pos lane+1) = some (endpointEvent p batch 1) ∧
      Run kernel Assumptions.all l (thread lane) {} ((X.tr (thread lane)).take (pos lane))
        (some before) ∧
      Run kernel Assumptions.all l (thread lane) before
        ((X.tr (thread lane)).drop (pos lane)) (ends lane) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) before state := by
    have hSame := Step.sameWarp_lane hBlock hg hl
    obtain ⟨t,u,v,w,hLocal,hRead₀,hRead₁,_,hLast,hw⟩ :=
      selectedEndpointPath hp hFirst hGroup hBatch hLo hHi hl hSame.2 (hF lane hl)
        (hStartup lane hl) (cur.checkpoint lane hl) (cur.localSteps lane hl)
    obtain ⟨e₀,hPrefix₀,hTail₀⟩ := consumeEndpointOfMaximal hp hMax hSame.1.1.2.1 0
      (by change batch+0 ≤ p.batch; omega) hProtect hLocal hRead₀
      (cur.recorded lane hl) (cur.continuation lane hl) (cur.positive lane hl)
      (cur.bounded lane hl) (cur.released lane hl)
    obtain ⟨e₁,hPrefix₁,hTail₁⟩ := consumeEndpointOfMaximal hp hMax hSame.1.1.2.1 1
      (by change batch+1 ≤ p.batch; omega) hProtect .refl hRead₁ hPrefix₀ hTail₀
      (Nat.succ_pos _) (len_of_get e₀) (releasedIfLast e₀ (by intro h; cases h))
    exact ⟨v,w,hw,e₀,e₁,hPrefix₁,hTail₁,hLast⟩
  choose! before state hAt he hf hRecorded hRun hLocal using hLane
  have countAfter (test : Event → Bool) (hOrdinary : ∀ n : Fin 2,
      test (endpointEvent p batch n) = false) (lane n : Nat)
      (hCount : ((X.tr (thread lane)).take (cur.pos lane)).countP test = n)
      (hl : lane < 32) : ((X.tr (thread lane)).take (pos lane)).countP test = n := by
    change ((X.tr (thread lane)).take ((cur.pos lane+1)+1)).countP test = n
    rw [List.take_add_one,show (X.tr (thread lane))[cur.pos lane+1]? = _ from hf lane hl,
      List.countP_append,List.take_add_one,show (X.tr (thread lane))[cur.pos lane]? = _
        from he lane hl]
    simp [hOrdinary,hCount]
  have hOrd : WarpOrdinals l X g pos shuffles votes :=
    ⟨fun lane hl => countAfter _ (fun _ => rfl) lane _ (cur.ordinals.shfl lane hl) hl,
      fun lane hl => countAfter _ (fun _ => rfl) lane _ (cur.ordinals.vote lane hl) hl⟩
  exact ⟨⟨⟨pos,before,state,hOrd,hRun,hLocal,hAt⟩,fun _ _ => by simp [pos],
    fun lane hl => len_of_get (hf lane hl),
    fun lane hl => releasedIfLast (hf lane hl) (by intro h; cases h),hRecorded⟩⟩

/-- A scheduled output warp reaches the first output-ready acquire for its assigned tile. -/
theorem selectedOutputReadyOfMaximal {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 13)
    (hCuQ : DrainCuQProtected p X) (hActive : g / l.block < tilePrefix p p.batch * p.heads) :
    ∃ batch < p.batch, tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      ∃ shuffles ends, Nonempty (SchedulerWarpReached l X g 2958
        (fun lane => outputReadyFacts p l batch (assignedCoordinates p batch (g / l.block)).2
          (assignedCoordinates p batch (g / l.block)).1 lane
          (schedulerStartupFrame p l (warpLane l g lane))) shuffles 1 ends) := by
  obtain ⟨first,_,hLo,hHi,_,ends,⟨seed⟩⟩ := selectedOutputBallotOfMaximal hp hMax hg hw hCuQ hActive
  have hFrame := fun lane (_ : lane < 32) => schedulerStartupFramed p l (warpLane l g lane)
  obtain ⟨batch,hFirst,hGroup,hBatch,hStart,hStop,⟨cur⟩⟩ :=
    seed.chooseTileOfMaximal hp hMax hg hLo hHi hFrame
  exact ⟨batch,hBatch,hStart,hStop,_,ends,
    cur.enterWritebackOfMaximal hp hMax hg hFirst hGroup hBatch hStart hStop hFrame
      (fun _ _ _ hm => hm) hCuQ⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
