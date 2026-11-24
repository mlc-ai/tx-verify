-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderKeyPointerBroadcast
import Kernels.TmlFa4Fwd.Proof.LoaderCopies
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.CpAsyncIssueProgress
import Lemmas.Step.DrainInOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- The actual maximal lane issues both planes of the decoded K pair. -/
theorem kCopyPairOfMaximal (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g pos stage lane src bytes : Nat} (hg : g < l.threads) (hStage : stage < 3) (hSrc : src < 2^64)
    (hAlign : src%16 = 0) (hBytes : bytes ≤ 16) (group : Fin 16) {s t : TState}
    {ending : Option TState} (ht : At t (kCopyPc group) (kCopyFacts l stage lane src bytes group))
    (hSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some s))
    (hTail : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending) (hPos : 0 < pos)
    (hBound : pos ≤ (X.tr g).length) (hRelease : pos = (X.tr g).length → Step.Released l X g) :
    X.get (g,pos) = some ⟨kCopyPc group,.copy (kCopySpec l g stage lane src bytes group false)⟩ ∧
    X.get (g,pos+1) = some
      ⟨kCopyPc group+1,.copy (kCopySpec l g stage lane src bytes group true)⟩ ∧
    Run kernel Assumptions.all l g {} ((X.tr g).take (pos+2)) (some (next (next t))) ∧
    Run kernel Assumptions.all l g (next (next t)) ((X.tr g).drop (pos+2)) ending := by
  let lo := kCopySpec l g stage lane src bytes group false
  let hi := kCopySpec l g stage lane src bytes group true
  have hn₀ : Next kernel Assumptions.all l g s t (.copy lo (next t)) :=
    ⟨hSteps,kCopyTemplate hp hStage hSrc hAlign hBytes group false ht⟩
  obtain ⟨he₀,hPast,hRest⟩ := Step.cp_async_issue_of_maximal hMax hg hn₀
    (fun _ _ => Iff.rfl) (.inl ⟨lo,rfl,rfl⟩) hPrefix hTail hPos hBound hRelease
    (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl))
  have hn₁ : Next kernel Assumptions.all l g (next t) (next t) (.copy hi (next (next t))) :=
    ⟨.refl,kCopyTemplate hp hStage hSrc hAlign hBytes group true ht.next⟩
  obtain ⟨he₁,hDone,hRemain⟩ := Step.cp_async_issue_of_maximal hMax hg hn₁
    (fun _ _ => Iff.rfl) (.inl ⟨hi,rfl,rfl⟩) hPast hRest (by omega)
    (len_of_get he₀) (releasedIfLast he₀ (by intro h; cases h))
    (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl))
  simp only [show (next t).pc = kCopyPc group+1 from ht.next.1] at he₁
  exact ⟨ht.1 ▸ he₀,he₁,hDone,hRemain⟩

/-- Each lane records both planes of the first K copy pair with the exact paged source. -/
theorem primingKeyFirstPairOfMaximal (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch tile warp shuffles votes : Nat} (hg : g < l.threads) (bases : Nat → Nat)
    (hBase : ∀ lane < 32, bases lane < 2^64 ∧ bases lane%16 = 0) {ends : Nat → Option TState}
    (after : PrimingKeyBroadcastReady p l X g batch tile warp shuffles votes bases ends) :
    ∃ _out : SchedulerWarpReached l X g 552 (primingKPacketFrame p l batch tile warp bases)
        shuffles votes ends,
      ∀ lane < 32, ∀ upper : Bool,
        let tid := 32*warp+lane
        let src := (bases (pointerBroadcastLane lane)+2*kvCopyColumn tid false)%2^64
        let bytes := kvCopySize (p.kLength batch) tile tid 0
        X.Copy (warpLane l g lane,after.pos lane+(if upper then 1 else 0))
          (firstKCopySpec l (warpLane l g lane) 0 tid src bytes upper) := by
  classical
  let F := primingKSourceInputs p l batch tile warp bases
  let tid := fun lane => 32 * warp + lane
  let src := fun lane => (bases (pointerBroadcastLane lane) +
    2 * kvCopyColumn (tid lane) false) % 2 ^ 64
  let bytes := fun lane => kvCopySize (p.kLength batch) tile (tid lane) 0
  let events : Nat → List Event := fun lane => [
    ⟨550, .copy (firstKCopySpec l (warpLane l g lane) 0 (tid lane) (src lane) (bytes lane) false)⟩,
    ⟨551, .copy (firstKCopySpec l (warpLane l g lane) 0 (tid lane) (src lane) (bytes lane) true)⟩]
  have hLane (lane : Nat) (hl : lane < 32) : ∃ u,
      (X.tr (warpLane l g lane)).drop (after.pos lane) =
        events lane ++ (X.tr (warpLane l g lane)).drop (after.pos lane + 2) ∧
      Run kernel Assumptions.all l (warpLane l g lane) {}
        ((X.tr (warpLane l g lane)).take (after.pos lane+2)) (some u) ∧
      Run kernel Assumptions.all l (warpLane l g lane) u
        ((X.tr (warpLane l g lane)).drop (after.pos lane+2)) (ends lane) ∧
      At u 552 (primingKPacketFrame p l batch tile warp bases lane) ∧
      after.pos lane+2 ≤ (X.tr (warpLane l g lane)).length ∧
      (after.pos lane+2 = (X.tr (warpLane l g lane)).length →
        Step.Released l X (warpLane l g lane)) := by
    let sender := pointerBroadcastLane lane
    have hSender : sender < 32 := by dsimp [sender, pointerBroadcastLane]; omega
    obtain ⟨hAddress, hAlign⟩ := hBase sender hSender
    let live := decide (kvCopyRow tile (tid lane) 0 < p.kLength batch)
    have ht := after.checkpoint lane hl
    have hInput : At (after.state lane) 546
        [(1855, b32 (bases sender % 2 ^ 32)), (1856, b32 (bases sender / 2 ^ 32)),
         (1082, b32 (kvCopyColumn (tid lane) false)), (124, .pred live),
         (1083, b32 (kvCopyAddress l.sharedBase 0 (tid lane) 0 false))] := by
      apply ht.mono
      exact ⟨holds_lookup ht.2.2.2.2 rfl, holds_lookup ht.2.2.2.2 rfl,
        holds_lookup ht.2.2.2.2 rfl, holds_lookup ht.2.2.2.2 rfl,
        holds_lookup ht.2.2.2.2 rfl, trivial⟩
    obtain ⟨u, hu, hU⟩ := prepareFirstKPairWithColumn l (warpLane l g lane) live hAddress
      (after.state lane) hInput
    have hBytes : bytes lane = (if live then 16 else 0) := by simp [bytes, kvCopySize, live]
    have hAt : At u 550 (firstKCopyFacts l 0 (tid lane) (src lane) (bytes lane)) := by
      rw [hBytes]
      exact hU.mono hU.2.2.2.2.2
    obtain ⟨huA, hKeep⟩ := loaderLinear (regs := (F lane).map Prod.fst)
      (by decide) (by decide) hInput.1
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hu
    have hSrcAlign : src lane % 16 = 0 := by
      dsimp only [src]
      rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat) ^ 64 by decide)]
      simp [kvCopyColumn, Nat.add_mod, hAlign, sender]
      omega
    have hBlock : l.block%32 = 0 := by rw [hp.block]
    have hActor := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
    obtain ⟨hLo,hHi,hPast,hTail⟩ := kCopyPairOfMaximal hp hMax (g := warpLane l g lane)
      hActor (by decide) (Nat.mod_lt _ (by decide)) hSrcAlign (kvCopySize_le ..) 0 hAt
      ((after.localSteps lane hl).trans (run_rtg huA)) (after.recorded lane hl)
      (after.continuation lane hl) (after.positive lane hl) (after.bounded lane hl)
      (after.released lane hl)
    have hHolds : Holds (after.state lane).regs (F lane) := ht.2.2.2.2.2.2
    have hFrame := holdsSchedulerFrame hHolds hKeep (fun _ hm => List.mem_map_of_mem hm)
    have hStop : after.pos lane+2 = after.pos lane+1+1 := by omega
    refine ⟨next (next u),?_,hPast,hTail,hU.next.next.mono ⟨hU.2.2.2.2.1,hFrame⟩,
      ?_,?_⟩
    · have hL := List.getElem?_eq_some_iff.mp hLo
      have hH := List.getElem?_eq_some_iff.mp hHi
      rw [List.drop_eq_getElem_cons hL.1,hL.2,List.drop_eq_getElem_cons hH.1,hH.2,hStop]
      rfl
    · rw [hStop]; exact len_of_get hHi
    · rw [hStop]; exact releasedIfLast hHi (by intro h; cases h)


  let _ : Nonempty TState := ⟨after.state 0⟩
  choose! u hTrace hPast hRun hAt hBound hRelease using hLane
  have hCounts := after.ordinals.advance events (fun lane hl => ⟨_, hTrace lane hl⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨⟨⟨fun lane => after.pos lane+2,u,u,hCounts,hRun,fun _ _ => .refl,hAt⟩,
    fun lane hl => (after.positive lane hl).trans_le (Nat.le_add_right _ _),
    hBound,hRelease,hPast⟩,?_⟩
  intro lane hl upper
  refine ⟨550+(if upper then 1 else 0),?_⟩
  change (X.tr (warpLane l g lane))[after.pos lane+(if upper then 1 else 0)]? = _
  rw [← List.getElem?_drop,hTrace lane hl]
  cases upper <;> rfl


end PTX.Kernels.TmlFa4Fwd.Loader
