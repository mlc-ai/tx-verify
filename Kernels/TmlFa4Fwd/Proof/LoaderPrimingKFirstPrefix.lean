-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingPrefixCoordinates
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInputOrder
import Lemmas.Flow.ElectMask
import Lemmas.Flow.NotShfl
import Lemmas.Flow.NotClc

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue Epilogue

noncomputable section

private def endsOrShuffles (op : Op) : Bool :=
  match op with
  | .ret | .exit => true
  | _ => op.isShfl

theorem firstKPeerAfterMetadata {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m)
    {g batch shuffles votes lane j : Nat} (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 381 (fun lane =>
      loaderActiveLaneFacts p l g batch lane ++ primingKActiveAbi p l (warpIndex l g))
      shuffles votes ends)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e) (hi : cur.pos lane ≤ j)
    (hKind : Execution.isShfl e = true ∨ e.kind = .exit) : 543 < e.pc := by
  let thread := warpLane l g lane
  have hGet : ((X.tr thread).drop (cur.pos lane))[j - cur.pos lane]? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hi]
    exact he
  have hMem := List.mem_of_getElem? hGet
  have hr := (cur.continuation lane hl).after_local_nonempty (cur.localSteps lane hl)
    (by intro h; rw [h] at hMem; cases hMem)
  obtain ⟨visits, hWalk⟩ := Mma.walkFromRun hr
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hWarp : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hw
  have ht := cur.checkpoint lane hl
  have hRegs : Holds (cur.state lane).regs
      [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] := by
    rw [hWarp]
    exact ⟨holds_lookup ht.2.2.2.2 rfl, holds_lookup ht.2.2.2.2 rfl, trivial⟩
  have hBranches : ∀ branch, ((kernel.code.drop 381).take (1901 - 381)).all
      (fun ins => loaderPipelineCutOp 381 1901 branch [2535, 1062] ins.op) = true := by
    intro branch
    set_option maxRecDepth 100000 in kernel_rfl
  have hLower := (Epilogue.loaderWalkEventRange warp (by decide) (by rw [ht.1]; decide)
    (ringShapeOfAt ht) hRegs hBranches hWalk e hMem).1
  obtain ⟨t, stop, hStep⟩ := hr.estep hMem
  have hPc := estep_source_pc hStep
  obtain ⟨tmpl, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨fault, rfl⟩ | ⟨ins, hCode, rfl⟩
  · obtain ⟨rfl, _⟩ := hFire
    cases hKind <;> contradiction
  have hOp : endsOrShuffles ins.op = true := by
    rcases hKind with hShfl | hExit
    · have hs := fires_shfl_op hFire hShfl
      cases hInsn : ins.op <;>
        first | rfl | simpa only [endsOrShuffles, hInsn, Op.isShfl] using hs
    · obtain he | he := fires_exit_op hFire hExit <;> rw [he] <;> rfl
  by_contra! hSmall
  have hGetCode : ((kernel.code.drop 381).take (544 - 381))[e.pc - 381]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLower, hPc]
    exact hCode
  have hAudit : ((kernel.code.drop 381).take (544 - 381)).all
      (fun ins => !(endsOrShuffles ins.op)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAudit ins (List.mem_of_getElem? hGetCode)
  rw [hOp] at h
  cases h

private structure FirstKShuffles (l : Launch) (X : Execution) (g index ordinal base : Nat)
    (F : List (Nat × Value)) (ending : Option TState) where
  low : Value
  high : Value
  lowChecked : Bool
  highChecked : Bool
  state : TState
  first : X.get (g, index) =
    some ⟨544, .shfl .idx (b32 (base % 2 ^ 32)) 0 6175 low lowChecked⟩
  second : X.get (g, index + 1) =
    some ⟨545, .shfl .idx (b32 (base / 2 ^ 32)) 0 6175 high highChecked⟩
  firstOrdinal : X.ShflK (g, index) ordinal
  secondOrdinal : X.ShflK (g, index + 1) (ordinal + 1)
  checkpoint : At state 546 ((1855, low) :: (1856, high) :: F)
  continuation : Run kernel Assumptions.all l g state ((X.tr g).drop (index + 2)) ending

/-- The two unguarded pointer shuffles consume exactly their available records. -/
private theorem firstKTwoShuffles {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch tile warp lane index ordinal : Nat} {bases : Nat → Nat}
    {s : TState} {ending : Option TState}
    (hs : At s 544 (primingKSourceInputs p l batch tile warp bases lane))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hOrd : ((X.tr g).take index).countP Execution.isShfl = ordinal)
    (hFirst : (X.tr g).drop index ≠ [])
    (hSecond : ∀ recv ok,
      X.get (g, index) = some ⟨544, .shfl .idx (b32 (bases lane % 2 ^ 32)) 0 6175 recv ok⟩ →
      Run kernel Assumptions.all l g (next (setReg s 1855 recv))
        ((X.tr g).drop (index + 1)) ending →
      (X.tr g).drop (index + 1) ≠ []) :
    Nonempty (FirstKShuffles l X g index ordinal (bases lane)
      (primingKSourceInputs p l batch tile warp bases lane) ending) := by
  let F := primingKSourceInputs p l batch tile warp bases lane
  let t0 := fun v (_ : Bool) => next (setReg s 1855 v)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hn : Next kernel Assumptions.all l g s s
      (.shfl .idx (b32 (bases lane % 2 ^ 32)) 0 6175 t0) :=
    ⟨.refl, primingKShuffleTemplate hBlock 0 hs hs.2.2.2.2.1⟩
  obtain ⟨recv, ok, hGet, hRank, hSuffix⟩ := hn.shuffle_at_nonempty hr hFirst hOrd
  rw [hs.1] at hGet
  have hFresh0 : ∀ pair ∈ F, pair.1 ≠ 1855 := by
    simp [F, primingKSourceInputs, primingKSourceFrame]
  have hFresh1 : ∀ pair ∈ (1855, recv) :: F, pair.1 ≠ 1856 := by
    simp [F, primingKSourceInputs, primingKSourceFrame]
  have ht : At (t0 recv ok) 545 ((1855, recv) :: F) := hs.set hFresh0
  let t1 := fun v (_ : Bool) => next (setReg (t0 recv ok) 1856 v)
  have hn1 : Next kernel Assumptions.all l g (t0 recv ok) (t0 recv ok)
      (.shfl .idx (b32 (bases lane / 2 ^ 32)) 0 6175 t1) :=
    ⟨.refl, primingKShuffleTemplate hBlock 1 ht ht.2.2.2.2.2.2.1⟩
  have hOrd' := (Flow.countP_take_succ hGet rfl).trans (congrArg (· + 1) hOrd)
  obtain ⟨high, good, hHigh, hHighRank, hTail⟩ := hn1.shuffle_at_nonempty hSuffix
    (hSecond recv ok hGet hSuffix) hOrd'
  rw [ht.1] at hHigh
  have ha := ht.set (v := high) hFresh1
  exact ⟨⟨recv, high, ok, good, t1 high good, hGet, hHigh, hRank, hHighRank,
    ha.mono ⟨ha.2.2.2.2.2.1, ha.2.2.2.2.1, ha.2.2.2.2.2.2⟩, hTail⟩⟩

private theorem traceAfter {X : Execution} {g i j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hle : i ≤ j) : (X.tr g).drop i ≠ [] := by
  intro h
  exact Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp he).1
    ((List.drop_eq_nil_iff.mp h).trans hle)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g src j : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hSrc : src < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
include hp hX hg hw hSrc writes

private theorem firstKShuffleOrigins (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    {target : Event} (he : X.get (warpLane l g src, j) = some target) (hPc : 545 < target.pc) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let coords := assignedCoordinates p batch (g / l.block)
      let head := coords.2 / 6
      let tile := Mma.trips p batch coords.1 - 1
      let warp := warpIndex l g
      let t := warpLane l g src
      let base := primingKRowPointer p batch head
        (primingLaneRow tile (32 * warp + pointerBroadcastLane src))
      let bases := fun lane =>
        primingKRowPointer p batch head (primingLaneRow tile (32 * warp + lane))
      ∃ index state ending highSent highOk,
        X.get (t, index + 1) = some
          ⟨545, .shfl .idx (b32 (bases src / 2 ^ 32)) 0 6175 highSent highOk⟩ ∧
        At state 546 ([(1855, b32 (base % 2 ^ 32)), (1856, b32 (base / 2 ^ 32))] ++
          primingKSourceInputs p l batch tile warp bases src) ∧
        Run kernel Assumptions.all l t state ((X.tr t).drop (index + 2)) ending := by
  obtain ⟨batch, hIn, hLo, hHi, _, index, state, ending, hs, hr, hStill, hOrd⟩ :=
    loaderPrimingKPointerOfActiveEvent hp hX hg hw hSrc writes hCTA he
      (bound := 545) (by decide) hPc
  obtain ⟨recv⟩ := firstKTwoShuffles hp hs hr hOrd (hStill.nonempty hr)
    (fun _ _ h0 hTail => (hStill.advance h0 (by decide : 544 ≤ 545)).nonempty hTail)
  let lane := pointerBroadcastLane src
  let thread := warpLane l g
  have hl : lane < 32 := by unfold lane pointerBroadcastLane; omega
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hWarp := Step.sameWarp_trans
    (sameWarp_symm (Step.sameWarp_lane hBlock hg hSrc).1) (Step.sameWarp_lane hBlock hg hl).1
  obtain ⟨otherBatch, otherIn, hlo, hhi, _, cur, hFollows⟩ :=
    loaderPrimingEntryOfActiveEvent hp hX hg hw hSrc (hp.cuQ_protected writes)
      hCTA he (by omega)
  obtain ⟨chosen, _, unique⟩ := tileBatch_existsUnique p hCTA
  have hb : batch = chosen := unique batch ⟨hIn, hLo, hHi⟩
  have hSame : otherBatch = batch := by
    have hOther := unique otherBatch ⟨otherIn, hlo, hhi⟩
    exact hOther.trans hb.symm
  subst otherBatch
  let rank := primingSearchShuffleCount batch
  have hEarly (partner : Nat) (hPeer : X.ShflK (thread lane, partner) (rank + 1)) :
      cur.pos lane ≤ partner := by
    by_contra h
    have hMono := Flow.countP_take_mono Execution.isShfl (X.tr (thread lane))
      (show partner ≤ cur.pos lane by omega)
    have hL : ((X.tr (thread lane)).take partner).countP Execution.isShfl = rank + 1 := hPeer.2
    have hR : ((X.tr (thread lane)).take (cur.pos lane)).countP Execution.isShfl = rank :=
      cur.ordinals.shfl lane hl
    rw [hL, hR] at hMono
    omega
  have hPeer : ∃ k e, X.get (thread lane, k) = some e ∧
      (X.ShflK (thread lane, k) (rank + 1) ∨ e.kind = .exit) ∧ 543 < e.pc := by
    rcases Step.shfl_lane_of_ready hX recv.second recv.secondOrdinal hWarp with
      ⟨k, hShfl⟩ | ⟨k, pc, hExit, _⟩
    · obtain ⟨⟨pc, mode, input, select, clamp, result, ok, hEv⟩, hCount⟩ := hShfl
      let ev : Event := ⟨pc, .shfl mode input select clamp result ok⟩
      have hOrdinal : X.ShflK (thread lane, k) (rank + 1) :=
        ⟨⟨_, _, _, _, _, _, _, hEv⟩, hCount⟩
      exact ⟨k, ev, hEv, .inl hOrdinal,
        firstKPeerAfterMetadata hp hw hl cur hEv (hEarly k hOrdinal) (.inl rfl)⟩
    · have hBefore : cur.pos lane ≤ k := by
        by_contra h
        exact hFollows.noExit lane hl k (by omega) pc hExit
      exact ⟨k, ⟨pc, .exit⟩, hExit, .inr rfl,
        firstKPeerAfterMetadata hp hw hl cur hExit hBefore (.inr rfl)⟩
  obtain ⟨k, ev, hk, hClass, hLate⟩ := hPeer
  obtain ⟨b, hBin, hBlo, hBhi, _, senderIndex, senderState, senderEnding, hSenderAt, hSenderRun,
    hSenderDemand, hSenderOrdinal⟩ :=
    loaderPrimingKPointerOfActiveEvent hp hX hg hw hl writes hCTA hk (by decide) hLate
  have hEq : b = batch := (unique b ⟨hBin, hBlo, hBhi⟩).trans hb.symm
  subst b
  have hThread : thread lane < l.threads := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
  obtain ⟨sent⟩ := firstKTwoShuffles hp hSenderAt hSenderRun hSenderOrdinal
    (hSenderDemand.nonempty hSenderRun) (fun _ _ hLow _ => by
      have hNext : senderIndex + 1 ≤ k := by
        rcases hClass with hPeerK | hExit
        · by_contra h
          have hm := Flow.countP_take_mono Execution.isShfl (X.tr (thread lane))
            (show k ≤ senderIndex by omega)
          have hCount : ((X.tr (thread lane)).take k).countP Execution.isShfl = rank + 1 := hPeerK.2
          rw [hCount, hSenderOrdinal] at hm
          exact (Nat.not_succ_le_self rank) hm
        · by_contra h
          obtain ⟨pc, kind⟩ := ev
          change kind = .exit at hExit
          subst kind
          exact noExitThroughContinuingEvent hX hThread hLow (by intro h; cases h)
            (by omega) pc hk
      exact traceAfter hk hNext)
  have hLane : laneOf l (thread src) = src := (Step.sameWarp_lane hBlock hg hSrc).2
  have hSource : (shflSource .idx src 0 6175).1 = lane :=
    congrArg Prod.fst (kv_shuffle_source ⟨src, hSrc⟩ 0)
  have hFrom : thread src - laneOf l (thread src) +
      (shflSource .idx (laneOf l (thread src)) 0 6175).1 = thread lane := by
    rw [hLane, hSource]
    unfold thread warpLane
    omega
  have hLoWord := (Flow.shfl_source_value hX recv.first recv.firstOrdinal
    (by rw [hFrom]; exact sent.first) (by rw [hFrom]; exact sent.firstOrdinal)
    (by rw [hFrom]; exact ShflK.not_exited hX hThread sent.firstOrdinal)).1
  have hHiWord := (Flow.shfl_source_value hX recv.second recv.secondOrdinal
    (by rw [hFrom]; exact sent.second) (by rw [hFrom]; exact sent.secondOrdinal)
    (by rw [hFrom]; exact ShflK.not_exited hX hThread sent.secondOrdinal)).1
  have hReady := recv.checkpoint
  rw [hLoWord, hHiWord] at hReady
  exact ⟨batch, hIn, hLo, hHi, index, recv.state, ending, recv.high, recv.highChecked,
    recv.second, hReady, recv.continuation⟩

/-- An already issued first K vector of any active CTA uses its actual sender's
launch page. The peer words are observed even when the issuer's trace stops at the copy. -/
theorem actualFirstKCopySourceInPrefix (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (upper : Bool) {spec : AsyncCopy.Spec}
    (he : X.get (warpLane l g src, j) = some ⟨550 + if upper then 1 else 0, .copy spec⟩) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let coords := assignedCoordinates p batch (g / l.block)
      let head := coords.2 / 6
      let tile := Mma.trips p batch coords.1 - 1
      let tid := 32 * warpIndex l g + src
      let row := kvCopyRow tile tid 0
      head < p.kvHeads ∧
      spec.src.size = (if row < p.kLength batch then 16 else 0) ∧
      spec.src.loc = p.kLayout.loc (primingScratchPage p batch row)
        head (row % 16) (kvCopyColumn tid upper) := by
  have hPc : 545 < 550 + if upper then 1 else 0 := by omega
  obtain ⟨batch, hIn, hLo, hHi, index, state, ending, hi, ok, hHigh, hAt, hRun⟩ :=
    firstKShuffleOrigins hp hX hg hw hSrc writes hCTA he hPc
  let coords := assignedCoordinates p batch (g / l.block)
  let head := coords.2 / 6
  let tile := Mma.trips p batch coords.1 - 1
  let warp := warpIndex l g
  let thread := warpLane l g src
  let tid := 32 * warp + src
  let row := kvCopyRow tile tid 0
  let base := primingKRowPointer p batch head row
  let live := decide (row < p.kLength batch)
  let address := (base + 2 * kvCopyColumn tid false) % 2 ^ 64
  let bytes := if live then 16 else 0
  have hw' : warpIndex l g = warpIndex l thread :=
    (Step.sameWarp_lane (by rw [hp.block]) hg hSrc).1.2
  have hLoader : 14 ≤ warpIndex l thread := hw' ▸ hw
  have hBefore : index + 2 ≤ j := by
    by_contra! hAfter
    have hAudit : ∀ branch, ((kernel.code.drop 546).take (1901 - 546)).all
        (fun ins => loaderPipelineCutOp 546 1901 branch [2535, 1062] ins.op) = true := by
      intro branch
      set_option maxRecDepth 100000 in kernel_rfl
    have hEarly := Thread.Loader.eventBeforeClosedCut hp hX hLoader (cut := 546)
      (by decide) hAudit he hHigh (by omega) (show 173 < 545 by decide)
      (show 545 < 546 by decide)
    change 550 + (if upper then 1 else 0) < 546 at hEarly
    omega
  have hb := hIn
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : head < p.kvHeads := by unfold head coords; unfold Params.heads at hHead; omega
  have hPage := primingScratchPageBound hp (row := row) hb
  have hRow : primingLaneRow tile (32 * warp + pointerBroadcastLane src) = row :=
    recurringFirstPointerRow tile warp src
  rw [hRow] at hAt
  obtain ⟨hEq, hFit, hAlign⟩ := sourceScratchPayload_live hp 0 hPage
    (Nat.mod_lt row (by decide)) hh
  rw [hEq] at hFit hAlign
  have hArg : At state 546
      [(1855, b32 (base % 2 ^ 32)), (1856, b32 (base / 2 ^ 32)),
       (1082, b32 (kvCopyColumn tid false)), (124, .pred live),
       (1083, b32 (kvCopyAddress l.sharedBase 0 tid 0 false))] := by
    apply hAt.mono
    exact ⟨holds_lookup hAt.2.2.2.2 rfl, holds_lookup hAt.2.2.2.2 rfl,
      holds_lookup hAt.2.2.2.2 rfl, holds_lookup hAt.2.2.2.2 rfl,
      holds_lookup hAt.2.2.2.2 rfl, trivial⟩
  obtain ⟨u, hu, hU⟩ := prepareFirstKPair l thread (stage := 0) (base := base) live hFit state hArg
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hArg.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hMore := traceAfter he hBefore
  have hUrun := hRun.after_local_nonempty (run_rtg huA) hMore
  have hAddress : address < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hAlignS : address % 16 = 0 := by
    dsimp only [address]
    rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat) ^ 64 by decide)]
    have hCol : 2 * kvCopyColumn tid false % 16 = 0 := by
      change 2 * (8 * (tid % 8)) % 16 = 0
      omega
    rw [Nat.add_mod, show base % 16 = 0 from hAlign, hCol]
  have hBytes : bytes ≤ 16 := by unfold bytes; split <;> decide
  obtain ⟨hLow, hTail⟩ := kCopyPrefixObserved hp (by decide : 0 < 3) hAddress hAlignS
    hBytes 0 false hU hUrun hMore
  have hIssued : ∃ k, X.get (thread, k) = some
      ⟨550 + if upper then 1 else 0,
        .copy (firstKCopySpec l thread 0 tid address bytes upper)⟩ := by
    cases upper
    · exact ⟨_, hLow⟩
    · have hLater : index + 2 + 1 ≤ j := by
        by_contra h
        have heq : index + 2 = j := by omega
        rw [heq] at hLow
        have hBad := congrArg Event.pc (Option.some.inj (he.symm.trans hLow))
        change 551 = 550 at hBad
        contradiction
      obtain ⟨hHighIssue, _⟩ := kCopyPrefixObserved hp (by decide : 0 < 3) hAddress hAlignS
        hBytes 0 true hU.next hTail (traceAfter he hLater)
      exact ⟨_, hHighIssue⟩
  obtain ⟨other, ho⟩ := hIssued
  have hSite : 550 ≤ 550 + (if upper then 1 else 0) ∧
      550 + (if upper then 1 else 0) ≤ 672 := by cases upper <;> decide
  have hEqPos := Thread.Loader.uniquePrimingCopy hp hX hLoader (.inl hSite) he ho
  rw [hEqPos] at he
  have hs : spec = firstKCopySpec l thread 0 tid address bytes upper :=
    Kind.copy.inj (congrArg Event.kind (Option.some.inj (he.symm.trans ho)))
  subst spec
  refine ⟨batch, hIn, hLo, hHi, hh, ?_, primingKCopySourceLoc hp hPage hh 0 upper⟩
  change bytes = (if row < p.kLength batch then 16 else 0)
  simp [bytes, live]

end
end PTX.Kernels.TmlFa4Fwd.Loader
