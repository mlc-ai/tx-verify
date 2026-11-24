-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRecurringCopyProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderStackHistory
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue Prologue

/-- Live packet vectors preserve register facts, collective counts and saved lane-private words. -/
theorem packetPairWarpOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g stage shuffles votes : Nat} (hg : g < l.threads)
    (site : Fin 6) (group : Fin 16) (hStage : stage+packetStageShift site < 3)
    (src bytes : Nat → Nat) (hSrc : ∀ lane < 32, src lane < 2^64)
    (hAlign : ∀ lane < 32, src lane%16 = 0) (hSize : ∀ lane < 32, bytes lane ≤ 16)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (packetPairPc site group) (fun lane =>
      let t := warpLane l g lane
      packetCopyFacts l site stage (t%l.block) (src lane) (bytes lane) group ++ F lane)
      shuffles votes ends) :
    ∃ done : SchedulerWarpReached l X g (packetPairPc site group+2) F shuffles votes ends,
      done.pos = (fun lane => cur.pos lane+2) ∧
      ∀ lane < 32,
        let t := warpLane l g lane
        (∀ upper : Bool, X.Copy (t,cur.pos lane+if upper then 1 else 0)
          (packetCopySpec l t site stage (t%l.block) (src lane) (bytes lane) group upper)) ∧
        ∀ {pc : Nat} {cell : Acc} {data : List Byte},
          PrimingCellValue X t (cur.pos lane) pc cell data →
          PrimingCellValue X t (done.pos lane) pc cell data := by
  classical
  let threads := warpLane l g
  let stop := fun lane => cur.pos lane+2
  let spec (lane : Nat) (upper : Bool) := packetCopySpec l (threads lane) site stage
    (threads lane%l.block) (src lane) (bytes lane) group upper
  let es : Nat → List Event := fun lane =>
    [⟨packetPairPc site group,.copy (spec lane false)⟩,
      ⟨packetPairPc site group+1,.copy (spec lane true)⟩]
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : ∃ u,
      (X.tr (threads lane)).drop (cur.pos lane) =
        es lane ++ (X.tr (threads lane)).drop (stop lane) ∧
      At u (packetPairPc site group+2) (F lane) ∧
      Run kernel Assumptions.all l (threads lane) {} ((X.tr (threads lane)).take (stop lane))
        (some u) ∧
      Run kernel Assumptions.all l (threads lane) u ((X.tr (threads lane)).drop (stop lane))
        (ends lane) ∧
      stop lane ≤ (X.tr (threads lane)).length ∧
      (stop lane = (X.tr (threads lane)).length → Step.Released l X (threads lane)) ∧
      ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (threads lane) (cur.pos lane) pc cell data →
        PrimingCellValue X (threads lane) (stop lane) pc cell data := by
    have hThread := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
    have hs := cur.checkpoint lane hl
    obtain ⟨hLo,hHi,hPast,hTail⟩ := packetPairOfMaximal hp hMax hThread site group hStage
      (hSrc lane hl) (hAlign lane hl) (hSize lane hl)
      (hs.mono ((holds_append ..).mp hs.2.2.2.2).1)
      (cur.localSteps lane hl) (cur.recorded lane hl) (cur.continuation lane hl)
      (cur.positive lane hl) (cur.bounded lane hl) (cur.released lane hl)
    have hStop : stop lane = cur.pos lane+1+1 := rfl
    refine ⟨_,?_,?_,hPast,hTail,?_,?_,?_⟩
    · change (X.tr (threads lane))[cur.pos lane]? =
        some ⟨packetPairPc site group,.copy (spec lane false)⟩ at hLo
      change (X.tr (threads lane))[cur.pos lane+1]? =
        some ⟨packetPairPc site group+1,.copy (spec lane true)⟩ at hHi
      have lo := List.getElem?_eq_some_iff.mp hLo
      have hi := List.getElem?_eq_some_iff.mp hHi
      rw [List.drop_eq_getElem_cons lo.1,lo.2,List.drop_eq_getElem_cons hi.1,hi.2,hStop]
      rfl
    · exact hs.next.next.mono ((holds_append ..).mp hs.2.2.2.2).2
    · rw [hStop]; exact len_of_get hHi
    · rw [hStop]; exact releasedIfLast hHi (by intro he; cases he)
    · intro pc cell data he
      exact (he.step hMax.1 hLo (by intro _ _ h; cases h)).step hMax.1 hHi
        (by intro _ _ h; cases h)
  let _ : Inhabited TState := ⟨{}⟩
  choose! u hTrace hAt hPast hTail hBound hRelease hPreserve using hLane
  have hOrd := cur.ordinals.advance es (fun lane hl => ⟨_,hTrace lane hl⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨⟨⟨stop,u,u,hOrd,hTail,fun _ _ => .refl,hAt⟩,
    fun lane hl => (cur.positive lane hl).trans_le (Nat.le_add_right _ _),
    hBound,hRelease,hPast⟩,rfl,fun lane hl => ⟨?_,hPreserve lane hl⟩⟩
  intro upper
  refine ⟨packetPlanePc site group upper,?_⟩
  change (X.tr (threads lane))[cur.pos lane+(if upper then 1 else 0)]? = _
  rw [← List.getElem?_drop,hTrace lane hl]
  cases upper <;> rfl

end PTX.Kernels.TmlFa4Fwd.Loader
