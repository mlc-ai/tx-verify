-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderEntry
public import Kernels.TmlFa4Fwd.Proof.EpilogueGroupRoute
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainEntry
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue Prologue

noncomputable section

/-- The lane's cuQ contribution and the ABI retained for later page-table and tensor accesses. -/
def loaderCuQFacts (p : Params) (l : Launch) (g warp : Nat) : List (Nat × Value) :=
  [(7159, b32 (drainCuQ p (laneOf l g))), (1073, b32 (laneOf l g))] ++
    loaderEntryFacts p l g warp

variable {p : Params} {l : Launch}

private theorem loaderLaneGate {m : Mem0} (hp : Pre p l m) (g : Nat) :
    Seg kernel [] l g 3 180 [(7170, b32 p.batch)] 183
      [(1073, b32 (laneOf l g)), (61, .pred (decide (p.batch < laneOf l g))),
        (7159, b32 0)] := by
  intro t ht
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have signed {n : Nat} (hn : n < 2 ^ 31) :
      toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
    simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left hn]
  have hBatch := hp.shape.2.1
  have hLane32 : laneOf l g < 2 ^ 32 := by omega
  have hBatch32 : p.batch < 2 ^ 32 := by omega
  seg_fp ht using first
    | rfl
    | simp only [b32, truncBits_ofNat hLane32 (by decide), truncBits_ofNat hBatch32 (by decide),
        compare, Option.getD_some, signed (show laneOf l g < 2 ^ 31 by omega),
        signed hBatch, gt_iff_lt, Int.ofNat_lt]

private theorem loaderCuQAddress {m : Mem0} (hp : Pre p l m) {g : Nat} (hb : laneOf l g ≤ p.batch) :
    Seg kernel [] l g 2 184 [(1073, b32 (laneOf l g)), (7506, b64 p.cuQBase)] 186
      [(7511, b64 (p.cuQBase + 4 * laneOf l g))] := by
  intro t ht
  have hRange := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRange
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hL32 : laneOf l g < 2 ^ 32 := by omega
  have hL64 : laneOf l g < 2 ^ 64 := by omega
  have hOff : 4 * laneOf l g < 2 ^ 64 := by omega
  have hBase : p.cuQBase < 2 ^ 64 := by omega
  have hAddr : p.cuQBase + 4 * laneOf l g < 2 ^ 64 := by omega
  have h4 : (truncBits 32 (BitVec.ofInt 64 4)).toNat = 4 := rfl
  seg_fp ht using simp only [b64, kind_u_beq_s, Bool.false_eq_true, ↓reduceIte,
    truncBits_ofNat hL32 (by decide), toNat_ofNat_lt hL64, h4, Nat.mul_comm (laneOf l g),
    truncBits_ofNat hOff (by decide), truncBits_ofNat hBase (by decide),
    ← BitVec.ofNat_add, truncBits_ofNat hAddr (by decide)]

/-- Resolve the first metadata sentinel branch. -/
theorem loaderCuQGate {m : Mem0} {g warp : Nat} (hp : Pre p l m) {t : TState}
    (ht : At t 180 (loaderEntryFacts p l g warp)) :
    ∃ w, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t w ∧
      At w (if p.batch < laneOf l g then 187 else 184)
        ((7159, b32 0) :: (1073, b32 (laneOf l g)) :: loaderEntryFacts p l g warp) := by
  let lane := laneOf l g
  let carry := (1073, b32 lane) :: loaderEntryFacts p l g warp
  let regs := (loaderEntryFacts p l g warp).map Prod.fst
  obtain ⟨v, hv, hV⟩ := loaderLaneGate hp g t (ht.mono ⟨ht.2.2.2.2.1, trivial⟩)
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := regs) (by decide) (by decide) ht.1 (by
    set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hStable := holdsSchedulerFrame ht.2.2.2.2 hvFrame (fun _ h => List.mem_map_of_mem h)
  have hGateAt : At v 183 ((61, .pred (decide (p.batch < lane))) :: (7159, b32 0) :: carry) :=
    hV.mono ⟨hV.2.2.2.2.2.1, hV.2.2.2.2.2.2.1, hV.2.2.2.2.1, hStable⟩
  obtain ⟨w, hw, hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_183 _ hGateAt hGateAt.2.2.2.2.1 (by simp)
  obtain ⟨hwA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hGateAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hw
  refine ⟨w, run_rtg (run_comp hvA hwA), ?_⟩
  exact ⟨by simpa only [decide_eq_true_eq] using hW.1,
    hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.2⟩

/-- Resolve the first metadata read for a lane within the sentinel. -/
theorem loaderCuQNext {m : Mem0} {g warp : Nat} (hp : Pre p l m) (hLane : laneOf l g ≤ p.batch)
    {w : TState} (hw : At w 184 ((1073, b32 (laneOf l g)) :: loaderEntryFacts p l g warp)) :
    ∃ s, At s 186 ((1073, b32 (laneOf l g)) :: loaderEntryFacts p l g warp) ∧
      Next kernel Assumptions.all l g w s
        (.read {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4}
          (afterLoad s [7159])) := by
  let lane := laneOf l g
  let carry := (1073, b32 lane) :: loaderEntryFacts p l g warp
  let regs := (loaderEntryFacts p l g warp).map Prod.fst
  have hFrame : Holds w.regs carry := hw.2.2.2.2
  have hArg : At w 184 [(1073, b32 lane), (7506, b64 p.cuQBase)] :=
    hw.mono ⟨hFrame.1,
      holds_mem hFrame (by simp [carry, loaderEntryFacts, loaderBarrierFacts, abiFacts]), trivial⟩
  obtain ⟨s, hs, hS⟩ := loaderCuQAddress hp hLane w hArg
  obtain ⟨hsA, hsFrame⟩ := loaderLinear (regs := 1073 :: regs) (by decide) (by decide) hw.1 (by
    set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hs
  have ha := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at ha
  have hAlign := hp.alignment.2.2.2.2.2.2.2.2.1
  let acc : Acc := {loc := globalLoc (p.cuQBase + 4 * lane), size := 4}
  have hOut : out kernel Assumptions.all l g s = .ev (.read acc (afterLoad s [7159])) := by
    rw [loaderOutCore (by rw [hS.1]; decide) (by rw [hS.1]; decide)]
    rw [out_event hS.2.2.2.1 (by rw [hS.1]; exact Flow.code_186) rfl rfl]
    change Out.ev (loadTmpl [] l g s .global false 32 [7159] 7511 0) = _
    exact congrArg Out.ev (loadTmpl_global hS.2.1 hS.2.2.2.2.1 (by omega)
      (by decide) (by omega))
  have hKeep := holdsSchedulerFrame hFrame hsFrame (fun _ hx => List.mem_map_of_mem hx)
  exact ⟨s, hS.mono hKeep, run_rtg hsA, hOut⟩

/-- A participating loader lane reads its cuQ word. A lane beyond the batch sentinel reaches
the same shuffle with zero and no read. Both route results carry the actual trace suffix. -/
theorem loaderCuQReadyInPrefix {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g i warp : Nat} {t : TState}
    {ending : Option TState} (ht : At t 180 (loaderEntryFacts p l g warp))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hMore : (X.tr g).drop i ≠ [])
    (hProtected : laneOf l g ≤ p.batch → ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * laneOf l g)).at k)) :
    let lane := laneOf l g
    let word := b32 (drainCuQ p lane)
    ∃ u, At u 187 (loaderCuQFacts p l g warp) ∧
      (lane ≤ p.batch → X.get (g, i) =
        some ⟨186, .rd {loc := globalLoc (p.cuQBase + 4 * lane), size := 4}
          (word.toBytes.map some)⟩) ∧
      Run kernel Assumptions.all l g u
        ((X.tr g).drop (if lane ≤ p.batch then i + 1 else i)) ending := by
  dsimp only
  let lane := laneOf l g
  let carry := (1073, b32 lane) :: loaderEntryFacts p l g warp
  let regs := (loaderEntryFacts p l g warp).map Prod.fst
  let word := b32 (drainCuQ p lane)
  obtain ⟨w, hw, hW⟩ := loaderCuQGate hp ht
  have hRest := hRun.after_local_nonempty hw hMore
  by_cases h : lane ≤ p.batch
  · have hwPC : w.pc = 184 := by simpa [lane, Nat.not_lt_of_ge h] using hW.1
    have hwAt : At w 184 carry := ⟨hwPC, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.2⟩
    obtain ⟨s, hS, hNext⟩ := loaderCuQNext hp h hwAt
    let acc : Acc := {loc := globalLoc (p.cuQBase + 4 * lane), size := 4}
    obtain ⟨_, _, he, ⟨bs, _, rfl, hu⟩, hTail⟩ := hNext.continuing_at_nonempty (by
      rintro e ⟨_, _, _, hBad⟩
      cases hBad) hRest hMore
    obtain rfl := Option.some.inj hu
    rw [hS.1] at he
    have hRead : X.MemReads (.thread (g, i)) acc bs := .inl ⟨186, he⟩
    have hBytes : bs = word.toBytes.map some := by
      apply hX.launch_value hRead rfl (hProtected h)
      simpa [lane, word, drainCuQ, h, acc, b32, HasValue, Value.bytes] using hp.cuQ lane h
    subst bs
    have hRebuild := PTX.Proof.rebuild_scalar (v := word) (show 0 < 4 by decide) rfl
    have hState : afterLoad s [7159] (word.toBytes.map some) = next (setReg s 7159 word) := by
      rw [afterLoad_ok hS.2.1 hS.2.2.1 hRebuild]
      simp [next, setReg, hS.2.1, hS.2.2.1]
    rw [hState] at hTail
    have hFresh : ∀ x ∈ carry, x.1 ≠ 7159 := by
      intro pair hm heq
      have hh := List.mem_map_of_mem (f := Prod.fst) hm
      rw [heq] at hh
      exact (of_decide_eq_true rfl : 7159 ∉ (1073 :: regs)) hh
    exact ⟨_, hS.set (v := word) hFresh, fun _ => he, by
      simpa only [ite_eq_left (show laneOf l g ≤ p.batch from h)] using hTail⟩
  · have hwPC : w.pc = 187 := by simpa [lane, Nat.lt_of_not_ge h] using hW.1
    have hWord : word = b32 0 := by simp [word, drainCuQ, h, lane]
    have hF : Holds w.regs (loaderCuQFacts p l g warp) := by
      change Holds w.regs ((7159, word) :: carry)
      rw [hWord]
      exact hW.2.2.2.2
    exact ⟨w, ⟨hwPC, hW.2.1, hW.2.2.1, hW.2.2.2.1, hF⟩, fun hh => (h hh).elim,
      by simpa only [ite_eq_right (show ¬ laneOf l g ≤ p.batch from h)] using hRest⟩

private theorem loaderSchedulerSuffix {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {o : Option TState}
    (hs : 187 ≤ s.pc) (hr : Run kernel Assumptions.all l g s events o) :
    ∀ e ∈ events, 187 ≤ e.pc := by
  obtain ⟨_, hWalk⟩ := Mma.walkFromRun hr
  exact Thread.eventTailEvents (floor := 187) (by decide +kernel) (by decide +kernel) hWalk hs

/-- Before any metadata value has been used, an observed loader lane read accesses its
in-range launch CuQ word. -/
theorem firstCuQReadFootprint {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, j) = some ⟨186, .rd a bs⟩) :
    j = 6 ∧ laneOf l g ≤ p.batch ∧
      a = {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4} := by
  have hRole := roleBodyPcOfEvent hp hX he (by change 173 < 186; decide)
    (by change 186 ∉ registerHintSites; decide)
  have hw : 14 ≤ warpIndex l g := by
    change roleBodyPc (warpIndex l g) 186 at hRole
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · cases h
    · split_ifs at h <;> omega
  have hg := event_thread_lt hX he
  have hLen : j < (X.tr g).length := len_of_get he
  have nonempty (k : Nat) (hk : k ≤ j) : (X.tr g).drop k ≠ [] :=
    fun h => Nat.not_le_of_lt hLen ((List.drop_eq_nil_iff.mp h).trans hk)
  obtain ⟨t, o, hFive, ht, hTid, hr, _, _⟩ :=
    nonzeroCommonPrefixOfDemand hp hX hg (show 0 < warpIndex l g by omega) he
      (.inl (by change 173 < 186; decide))
  let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
  have ht' : At t 174 (loaderBarrierFacts p l g warp.val) := by
    have h := ht.2.2.2.2
    have hAbi : Holds t.regs (abiFacts p l) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    apply ht.mono
    rw [loaderBarrierFacts, holds_append]
    exact ⟨⟨h.1, h.2.1, hAbi⟩, hTid, trivial⟩
  obtain ⟨_, u, hHint, hu, hTail⟩ :=
    loaderHintObservedPrefix hp hg warp hw ht' hr (nonempty 5 hFive)
  have hSix : 6 ≤ j := by
    by_contra! h
    have hEq : j = 5 := by omega
    subst j
    rw [he] at hHint
    cases hHint
  have hMore := nonempty 6 hSix
  obtain ⟨w, hLocal, hW⟩ := loaderCuQGate hp hu
  by_cases hLane : laneOf l g ≤ p.batch
  · have hAt : At w 184
        ((1073, b32 (laneOf l g)) :: loaderEntryFacts p l g warp.val) := by
      exact ⟨by simpa [Nat.not_lt_of_ge hLane] using hW.1,
        hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.2⟩
    obtain ⟨s, hs, hNext⟩ := loaderCuQNext hp hLane hAt
    have hBefore := hTail.after_local_nonempty hLocal hMore
    obtain ⟨hPos, hAcc⟩ := hNext.uniqueScalarReadAt hs.1 hBefore hSix he
      (fun _ _ => loaderSchedulerSuffix)
    exact ⟨hPos, hLane, hAcc⟩
  · have hPc : w.pc = 187 := by simpa [Nat.lt_of_not_ge hLane] using hW.1
    have hIndexed : ((X.tr g).drop 6)[j - 6]? = some ⟨186, .rd a bs⟩ := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hSix]
      exact he
    have hEventFloor := loaderSchedulerSuffix hPc.ge (hTail.after_local_nonempty hLocal hMore)
      _ (List.mem_of_getElem? hIndexed)
    change 187 ≤ 186 at hEventFloor
    omega

/-- A terminated trace supplies the complete input of the first loader shuffle. -/
theorem loaderCuQReady {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g i warp : Nat} {t : TState}
    (ht : At t 180 (loaderEntryFacts p l g warp))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) none)
    (hProtected : laneOf l g ≤ p.batch → ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * laneOf l g)).at k)) :
    let lane := laneOf l g
    let word := b32 (drainCuQ p lane)
    ∃ u, At u 187 (loaderCuQFacts p l g warp) ∧
      (lane ≤ p.batch → X.get (g, i) =
        some ⟨186, .rd {loc := globalLoc (p.cuQBase + 4 * lane), size := 4}
          (word.toBytes.map some)⟩) ∧
      Run kernel Assumptions.all l g u
        ((X.tr g).drop (if lane ≤ p.batch then i + 1 else i)) none :=
  loaderCuQReadyInPrefix hp hX ht hRun (fun h => by rw [h] at hRun; cases hRun) hProtected

theorem loaderDownTemplate {m : Mem0} (hp : Pre p l m) {g warp : Nat} {t : TState}
    (ht : At t 187 (loaderCuQFacts p l g warp)) :
    out kernel Assumptions.all l g t = .ev (.shfl .down (b32 (drainCuQ p (laneOf l g))) 1 31
      (fun value _ => next (setReg t 1707 value))) := by
  have hv := ht.2.2.2.2.1
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  rw [loaderOutCore (by rw [ht.1]; decide) (by rw [ht.1]; decide)]
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_187) rfl rfl]
  change Out.ev (shflTmpl l g t .down 1707 none (.reg 7159) (.imm 1) (.imm 31) (.imm (-1))) = _
  simp [shflTmpl, readValue, readReg, hv, hBlock, Value.bytes, b32, readBits, pure, Except.pure]
  rfl

/-- An accepted loader warp reads its first cuQ group and consumes the same actual down
shuffle in all lanes. Optional reads preserve the warp collective ordinals. -/
theorem loaderFirstWarpCuQ {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g warp shuffles votes : Nat}
    (hg : g < l.threads)
    (cur : SchedulerWarpAt l X g 180
      (fun lane => loaderEntryFacts p l (warpLane l g lane) warp) shuffles votes)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k)) :
    Nonempty (SchedulerWarpAt l X g 188 (fun lane =>
      (1707, b32 (drainCuQ p (shflSource .down lane 1 31).1)) ::
        loaderCuQFacts p l (warpLane l g lane) warp) (shuffles + 1) votes) := by
  let _ : Nonempty TState := ⟨cur.state 0⟩
  let pos := fun lane => if lane ≤ p.batch then cur.pos lane + 1 else cur.pos lane
  let word := fun lane => b32 (drainCuQ p lane)
  let thread := warpLane l g
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (thread lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  have hRead (lane : Nat) (hl : lane < 32) :
      ∃ t, At t 187 (loaderCuQFacts p l (thread lane) warp) ∧
        (lane ≤ p.batch → X.get (thread lane, cur.pos lane) =
          some ⟨186, .rd {loc := globalLoc (p.cuQBase + 4 * lane), size := 4}
            ((word lane).toBytes.map some)⟩) ∧
        Run kernel Assumptions.all l (thread lane) t
          ((X.tr (thread lane)).drop (pos lane)) none := by
    have hr := (cur.continuation lane hl).after_local (cur.localSteps lane hl)
    obtain ⟨u, hu, he, hs⟩ := loaderCuQReady hp hX (cur.checkpoint lane hl) hr
      (fun h => hProtected (laneOf l (thread lane)) h)
    rw [hLane lane hl] at he hs
    exact ⟨u, hu, he, hs⟩
  choose! state hAt hEvent hRun using hRead
  have hOrd : WarpOrdinals l X g pos shuffles votes := by
    have keep (test : Event → Bool) (n : Nat)
        (hc : ∀ lane < 32, ((X.tr (thread lane)).take (cur.pos lane)).countP test = n)
        (hOrdinary : ∀ a bs, test ⟨186, .rd a bs⟩ = false) :
        ∀ lane < 32, ((X.tr (thread lane)).take (pos lane)).countP test = n := by
      intro lane hl
      by_cases h : lane ≤ p.batch
      · have he := hEvent lane hl h
        simp only [pos, ite_eq_left h, List.take_add_one]
        rw [show (X.tr (thread lane))[cur.pos lane]? = _ from he]
        simp [hOrdinary, hc lane hl]
      · simpa only [pos, ite_eq_right h] using hc lane hl
    exact ⟨keep _ _ cur.ordinals.shfl (fun _ _ => rfl), keep _ _ cur.ordinals.vote (fun _ _ => rfl)⟩
  let down : SchedulerWarpAt l X g 187 (fun lane => loaderCuQFacts p l (thread lane) warp)
      shuffles votes := ⟨pos, state, state, hOrd, hRun, fun _ _ => .refl, hAt⟩
  have hFresh (lane : Nat) (_ : lane < 32) (pair : Nat × Value)
      (hm : pair ∈ loaderCuQFacts p l (thread lane) warp) : pair.1 ≠ 1707 := by
    intro he
    have hm' := List.mem_map_of_mem (f := Prod.fst) hm
    rw [he] at hm'
    exact (of_decide_eq_true rfl : 1707 ∉
      [7159, 1073, 7170, 1072, 1062, 2535, 1, 7492, 7493, 7494, 7495, 1663, 1664, 7496,
        7497, 7498, 7499, 7500, 7501, 7502, 7503, 7504, 7505, 7291, 7290, 7289, 7506,
        7292, 7293, 7294, 7295, 1665, 1061]) hm'
  have hOut (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (thread lane) (state lane) =
        .ev (.shfl .down (word lane) 1 31
          (fun value _ => next (setReg (state lane) 1707 value))) := by
    simpa only [hLane lane hl] using loaderDownTemplate hp (hAt lane hl)
  exact down.consumeShuffle hp hX hg .down word (fun _ => 1) (fun _ => 31) hFresh hOut

end
end PTX.Kernels.TmlFa4Fwd.Loader
