-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueGroupRoute
public import Kernels.TmlFa4Fwd.Proof.CorrectionFallbackSites
public import Kernels.TmlFa4Fwd.Proof.CorrectionFirstRoute
import Kernels.TmlFa4Fwd.Proof.MmaScanCounter
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainEntry
import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Lemmas.Kernel.ReadValue
import Kernels.TmlFa4Fwd.Proof.InputRead
import Lemmas.Step.ProtectedReadProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction.Fallback
open PTX PTX.Proof PTX.Flow Epilogue Prologue

noncomputable section

def fallbackFrameRegs : List Nat :=
  [1062, 2535, 1063, 1064, 1065, 1066, 1067, 1068, 6495, 2390, 1069, 1070, 6497,
    1071, 1, 7492, 7493, 7494, 7495, 1663, 1664, 7496, 7497, 7498, 7499, 7500,
    7501, 7502, 7503, 7504, 7505, 7291, 7290, 7289, 7506, 7292, 7293, 7294,
    7295, 1665, 1072, 1618, 1612, 1613, 1614, 1615, 5868, 1616, 7267, 17, 7142, 7277]

/-- The stable registers used by the correction group search and tile selection. -/
def groupSchedulerFrame (p : Params) (lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  (17, .pred (decide (laneHasRequest lane p.batch))) :: (7142, b32 p.heads) :: F

/-- Scheduler group-loop state before advancing to the next group. -/
def groupSearchFacts (p : Params) (cta first lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
  [(1619, b32 (cta + 1)), (7273, b32 first), (7268, b32 limit),
    (7277, b32 p.batch), (1616, b32 lane), (1618, b32 cta)] ++ groupSchedulerFrame p lane F

/-- The verified lane contributions and prefix words needed by the selection ballot. -/
def groupChoiceFacts (p : Params) (cta first lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  [(7272, b32 (∑ j ∈ Finset.range 32, groupLaneTiles p first j)),
    (7271, b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)),
    (7274, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
    (7142, b32 p.heads), (1618, b32 cta), (7273, b32 first),
    (7270, b32 (groupLaneTiles p first lane))] ++ groupSchedulerFrame p lane F

/-- The group test can inspect the live batch count before entering selection. -/
def groupAvailableFacts (p : Params) (cta first lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  (7277, b32 p.batch) :: groupChoiceFacts p cta first lane F

def exhaustedScheduleFacts (p : Params) (F : List (Nat × Value)) : List (Nat × Value) :=
  [(7273, b32 p.batch), (7277, b32 p.batch)] ++ F

private theorem searchModel {l : Launch} {g : Nat} {t : TState}
    (hlo : 7807 ≤ t.pc) (hhi : t.pc < 7864) :
    out kernel Assumptions.all l g t = out kernel [] l g t :=
  Mma.groupScanOut .correctionSelect (by change 7807 ≤ t.pc; omega)
    (by change t.pc < 7864; omega)

private theorem searchLinear {l : Launch} {g lo n : Nat} {t u : TState}
    {R : List Nat}
    (hLo : 7807 ≤ lo) (hHi : lo + n ≤ 7864) (hpc : t.pc = lo)
    (hCode : ((kernel.code.drop lo).take n).all
      (fun i => R.all (fun r => !(writesRegs i.op).contains r)) = true)
    (hStraight : ((kernel.code.drop lo).take (n - 1)).all
      (fun i => schedulerFallsThrough i.op) = true)
    (hRun : run kernel [] l g n t = some u) :
    run kernel Assumptions.all l g n t = some u ∧
      ∀ r ∈ R, u.regs r = t.regs r :=
  ⟨schedulerLocalTransport hStraight
    (fun hlo hhi => searchModel (by omega) (by omega)) hRun (by omega) (by omega),
   fun _ hr => schedulerLocalFrame hCode hStraight hRun (by omega) (by omega) hr⟩

/-- The live ABI frame retained by the correction scheduler's fallback. -/
def fallbackFrame (p : Params) (l : Launch) (g lane : Nat) : List (Nat × Value) :=
  firstShuffleFacts p l (warpLane l g lane)

theorem fallbackFrame_mem {p : Params} {l : Launch} {g lane : Nat} :
    ∀ pair ∈ fallbackFrame p l g lane, pair.1 ∈ fallbackFrameRegs := by
  intro pair hm
  have hMap := List.mem_map_of_mem (f := Prod.fst) hm
  have hSubset : (fallbackFrame p l g lane).map Prod.fst ⊆ fallbackFrameRegs :=
    of_decide_eq_true rfl
  exact hSubset hMap

private theorem startSearchPreserving {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g shuffles votes : Nat} (hg : g < l.threads)
    (hCta : g / l.block + 1 < 2 ^ 32) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 7807 (correctionFirstRouteFacts p l g) shuffles votes ends) :
    ∃ result : SchedulerWarpAt l X g 7810
        (fun lane => groupSearchFacts p (g / l.block) 0 lane (fallbackFrame p l g lane))
        shuffles votes ends, result.pos = cur.pos ∧ result.before = cur.before := by
  apply cur.advanceLocalPreserving
  intro lane hl
  let thread := warpLane l g lane
  let cta := g / l.block
  let limit := tilePrefix p (min p.batch 31) * p.heads
  let F := fallbackFrame p l g lane
  let carry := [(7277, b32 p.batch), (1616, b32 lane), (1618, b32 cta)] ++
    groupSchedulerFrame p lane F
  have ht := cur.checkpoint lane hl
  have hR := ht.2.2.2.2
  have hAt : At (cur.state lane) 7807 [(1618, b32 cta), (7274, b32 limit)] :=
    ht.mono ⟨hR.2.2.1, hR.1, trivial⟩
  obtain ⟨u, hr, hu⟩ := enterGroupSearch l thread hCta _ hAt
  obtain ⟨hRun, hFrame⟩ := searchLinear (R := fallbackFrameRegs) (by decide) (by decide)
    hAt.1 (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hr
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane : laneOf l thread = lane := (Step.sameWarp_lane hBlock hg hl).2
  have hOld : Holds (cur.state lane).regs carry := by
    have hF : Holds (cur.state lane).regs F := hR.2.2.2.2.2.2.2.2
    have hBatch := holds_lookup hF (show F.lookup 7277 = some (b32 p.batch) by rfl)
    have hLaneReg := holds_lookup hF (show F.lookup 1616 = some (b32 (laneOf l thread)) by rfl)
    have hPred := hR.2.2.2.2.2.2.2.1
    change (cur.state lane).regs 17 =
      some (.pred (decide (laneHasRequest (laneOf l thread) p.batch))) at hPred
    rw [hLane] at hPred hLaneReg
    exact ⟨hBatch, hLaneReg, hR.2.2.1, hPred, hR.2.2.2.2.2.2.1, hF⟩
  have hRegs : ∀ pair ∈ carry, pair.1 ∈ fallbackFrameRegs := by
    intro pair hm
    simp only [carry, groupSchedulerFrame, List.cons_append, List.nil_append, List.mem_cons] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | hm
    all_goals first | exact of_decide_eq_true rfl | exact fallbackFrame_mem _ hm
  have hSaved := holdsSchedulerFrame hOld hFrame hRegs
  exact ⟨u, run_rtg hRun, hu.mono ⟨hu.2.2.2.2.1, hu.2.2.2.2.2.1, hu.2.2.2.2.2.2.1, hSaved⟩⟩

section
variable {p : Params} {l : Launch}

/-- Initialize the first 31-request fallback iteration without consuming an event. -/
theorem startSearch {m : Mem0} {X : Execution} (hp : Pre p l m) {g shuffles votes : Nat}
    (hg : g < l.threads) (hCta : g / l.block + 1 < 2 ^ 32) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 7807 (correctionFirstRouteFacts p l g) shuffles votes ends) :
    ∃ result : SchedulerWarpAt l X g 7810
        (fun lane => groupSearchFacts p (g / l.block) 0 lane (fallbackFrame p l g lane))
        shuffles votes ends, result.pos = cur.pos := by
  obtain ⟨next, hPos, _⟩ := startSearchPreserving hp hg hCta cur
  exact ⟨next, hPos⟩

private def searchCarry (p : Params) (cta first base lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  [(1619, b32 (cta + 1)), (7273, b32 first), (7268, b32 base), (7277, b32 p.batch),
    (1616, b32 lane), (1618, b32 cta)] ++ groupSchedulerFrame p lane F

private def searchCarryRegs : List Nat := [1619, 7273, 7268, 7277] ++ fallbackFrameRegs

private theorem searchCarry_mem {p : Params} {cta first base lane : Nat}
    {F : List (Nat × Value)} (hF : ∀ x ∈ F, x.1 ∈ fallbackFrameRegs) :
    ∀ x ∈ searchCarry p cta first base lane F, x.1 ∈ searchCarryRegs := by
  intro x hx
  simp only [searchCarry, groupSchedulerFrame, List.cons_append, List.nil_append,
    List.mem_cons] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hx <;>
    first | exact List.mem_append.mpr (.inr (hF x hx)) | simp [searchCarryRegs, fallbackFrameRegs]

private def groupAdvanced (p : Params) (cta first lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  [(1620, b32 (first + 31)), (695, .pred (decide (p.batch ≤ first + 31))),
    (7274, b32 (cta + 1))] ++
  searchCarry p cta (min (first + 31) p.batch)
    (tilePrefix p (min p.batch (first + 31)) * p.heads) lane F

private theorem advanceSearchGroup {m : Mem0} (hp : Pre p l m) {g cta first lane : Nat} {t : TState}
    {F : List (Nat × Value)} (hf : first < p.batch) (hF : ∀ x ∈ F, x.1 ∈ fallbackFrameRegs)
    (ht : At t 7810 (groupSearchFacts p cta first lane F)) :
    ∃ u, run kernel Assumptions.all l g 4 t = some u ∧
      At u 7814 (groupAdvanced p cta first lane F) := by
  have hReg := ht.2.2.2.2
  have hAt : At t 7810 [(7273, b32 first), (7277, b32 p.batch), (1619, b32 (cta + 1))] :=
    ht.mono ⟨hReg.2.1, hReg.2.2.2.1, hReg.1, trivial⟩
  obtain ⟨u, hr, hu⟩ := (advanceGroup_of_pre hp g hf).2.2 t hAt
  obtain ⟨hRun, hFrame⟩ := searchLinear (R := [1619, 7268, 7277] ++ fallbackFrameRegs)
    (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hr
  have hOldFrame : Holds t.regs (groupSchedulerFrame p lane F) := hReg.2.2.2.2.2.2
  have hTail := holdsSchedulerFrame hOldFrame hFrame (by
    intro x hx
    apply List.mem_append.mpr
    right
    simp only [groupSchedulerFrame, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
    · exact hF x hx)
  have hSaved : Holds u.regs (searchCarry p cta (min (first + 31) p.batch)
      (tilePrefix p (min p.batch (first + 31)) * p.heads) lane F) :=
    ⟨(hFrame 1619 (by decide)).trans hReg.1, hu.2.2.2.2.2.2.1,
      (hFrame 7268 (by decide)).trans hReg.2.2.1,
      (hFrame 7277 (by decide)).trans hReg.2.2.2.1,
      (hFrame 1616 (by decide)).trans hReg.2.2.2.2.1,
      (hFrame 1618 (by decide)).trans hReg.2.2.2.2.2.1, hTail⟩
  have hNew := hu.2.2.2.2
  exact ⟨u, hRun, hu.mono ⟨hNew.1, hNew.2.1, hNew.2.2.2.1, hSaved⟩⟩

private theorem branchSearchGroup {g cta first lane : Nat} {F : List (Nat × Value)} {t : TState}
    (ht : At t 7814 (groupAdvanced p cta first lane F)) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u (if p.batch ≤ first + 31 then 7861 else 7815) (groupAdvanced p cta first lane F) := by
  obtain ⟨u, hr, hu⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_7814 _ ht ht.2.2.2.2.2.1 (by simp)
  obtain ⟨hRun, _⟩ := searchLinear (R := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hr
  exact ⟨u, hRun, by simpa only [decide_eq_true_eq] using hu⟩

private def groupLaneFacts (p : Params) (cta first lane : Nat) (F : List (Nat × Value))
    (word : Value) : List (Nat × Value) :=
  [(1621, b32 (first + 31 + lane)), (7269, word)] ++
    searchCarry p cta (first + 31) (tilePrefix p (first + 31) * p.heads) lane F

private theorem searchLaneGate {m : Mem0} (hp : Pre p l m) {g cta first lane : Nat}
    {F : List (Nat × Value)} {t : TState} (hGroup : first + 31 < p.batch) (hl : lane < 32)
    (hF : ∀ x ∈ F, x.1 ∈ fallbackFrameRegs) (ht : At t 7815 (groupAdvanced p cta first lane F)) :
    ∃ u, run kernel Assumptions.all l g 3 t = some u ∧
      At u 7818 ((696, .pred (decide (p.batch < first + 31 + lane))) ::
        groupLaneFacts p cta first lane F (b32 0)) := by
  let carry := searchCarry p cta (first + 31) (tilePrefix p (first + 31) * p.heads) lane F
  have hInitial : Holds t.regs carry := by
    have h := ht.2.2.2.2.2.2.2
    change Holds t.regs (searchCarry p cta (min (first + 31) p.batch)
      (tilePrefix p (min p.batch (first + 31)) * p.heads) lane F) at h
    have hLE := Nat.le_of_lt hGroup
    simpa only [carry, Nat.min_eq_left hLE, Nat.min_eq_right hLE] using h
  have hIndex : first + 31 + lane < 2 ^ 31 := by
    have := hp.shape.2.2.2.2.2
    omega
  have hArgs : At t 7815 [(1620, b32 (first + 31)), (1616, b32 lane), (7277, b32 p.batch)] :=
    ht.mono ⟨ht.2.2.2.2.1, holds_mem hInitial (by simp [carry, searchCarry]),
      holds_mem hInitial (by simp [carry, searchCarry]), trivial⟩
  obtain ⟨u, hr, hu⟩ := groupLaneGate l g hIndex hp.shape.2.1 t hArgs
  obtain ⟨hRun, hFrame⟩ := searchLinear (R := searchCarryRegs)
    (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hr
  have hKeep := holdsSchedulerFrame hInitial hFrame (searchCarry_mem hF)
  have h := hu.2.2.2.2
  exact ⟨u, hRun, hu.mono ⟨h.2.1, h.1, h.2.2.1, hKeep⟩⟩

private def searchReadAcc (p : Params) (index : Nat) : Acc :=
  {loc := globalLoc (p.cuQBase + 4 * index), size := 4}

private theorem replaySearchLaneRead {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g j cta first lane : Nat} {F : List (Nat × Value)} {before t : TState} {o : Option TState}
    (hF : ∀ x ∈ F, x.1 ∈ fallbackFrameRegs) (hBase : (7506, b64 p.cuQBase) ∈ F)
    (ht : At t 7818 ((696, .pred (decide (p.batch < first + 31 + lane))) ::
      groupLaneFacts p cta first lane F (b32 0)))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before t)
    (hRun : Run kernel Assumptions.all l g before ((X.tr g).drop j) o)
    (Recorded : Nat → TState → Prop) (hRecorded : Recorded j before)
    (hConsume : let index := first + 31 + lane
      let acc := searchReadAcc p index
      let bytes := (b32 (drainCuQ p index)).toBytes.map some
      index ≤ p.batch → ∀ {a : TState}, a.pc = 7821 →
      Next kernel Assumptions.all l g before a (.read acc (afterLoad a [7269])) →
        X.get (g,j) = some ⟨7821,.rd acc bytes⟩ ∧
          Run kernel Assumptions.all l g (afterLoad a [7269] bytes) ((X.tr g).drop (j+1)) o ∧
          Recorded (j+1) (afterLoad a [7269] bytes)) :
    let index := first + 31 + lane
    let word := b32 (drainCuQ p index)
    ∃ v u, At u 7822 (groupLaneFacts p cta first lane F word) ∧
      (index ≤ p.batch → X.get (g, j) = some ⟨7821, .rd (searchReadAcc p index)
        (word.toBytes.map some)⟩) ∧
      Run kernel Assumptions.all l g v
        ((X.tr g).drop (if index ≤ p.batch then j + 1 else j)) o ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) v u ∧
      Recorded (if index ≤ p.batch then j + 1 else j) v := by
  dsimp only
  let index := first + 31 + lane
  let word := b32 (drainCuQ p index)
  let carry := searchCarry p cta (first + 31) (tilePrefix p (first + 31) * p.heads) lane F
  obtain ⟨v, hr, hv⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_7818 _ ht ht.2.2.2.2.1 (by simp)
  obtain ⟨hrA, _⟩ := searchLinear (R := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hr
  have hApproach := hLocal.trans (run_rtg hrA)
  by_cases h : index ≤ p.batch
  · have hvPC : v.pc = 7819 := by simpa [index, Nat.not_lt_of_ge h] using hv.1
    have hc : Holds v.regs carry := hv.2.2.2.2.2.2.2
    have hIndex : v.regs 1621 = some (b32 index) := hv.2.2.2.2.2.1
    have hAt : At v 7819 [(1621, b32 index), (7506, b64 p.cuQBase)] :=
      ⟨hvPC, hv.2.1, hv.2.2.1, hv.2.2.2.1, hIndex,
        holds_mem hc (by simp [carry, searchCarry, groupSchedulerFrame, hBase]), trivial⟩
    obtain ⟨a, ha, hA⟩ := groupLaneAddress hp g h v hAt
    obtain ⟨haA, hFrame⟩ := searchLinear (R := 1621 :: searchCarryRegs)
      (by decide) (by decide) hAt.1
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) ha
    let acc := searchReadAcc p index
    have hOut : out kernel Assumptions.all l g a = .ev (.read acc (afterLoad a [7269])) :=
      (searchModel (by have := hA.1; omega) (by have := hA.1; omega)).trans
        (groupLaneRead hp g a h hA)
    have hn : Next kernel Assumptions.all l g before a (.read acc (afterLoad a [7269])) :=
      ⟨hApproach.trans (run_rtg haA), hOut⟩
    obtain ⟨hGet,hTail,hPast⟩ := hConsume h hA.1 hn
    have hRead := rebuild_scalar (v := word) (show 0 < 4 by decide) rfl
    have hState : afterLoad a [7269] (word.toBytes.map some) = next (setReg a 7269 word) := by
      rw [afterLoad_ok hA.2.1 hA.2.2.1 hRead]
      simp [next, setReg, hA.2.1, hA.2.2.1]
    rw [hState] at hTail hPast
    have hKeep := holdsSchedulerFrame hc hFrame (fun pair hp' =>
      List.mem_cons_of_mem _ (searchCarry_mem hF pair hp'))
    have hAtA : At a 7821 ((1621, b32 index) :: carry) :=
      hA.mono ⟨(hFrame _ (by simp)).trans hIndex, hKeep⟩
    have hFresh : ∀ pair ∈ ((1621, b32 index) :: carry), pair.1 ≠ 7269 := by
      intro pair hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact of_decide_eq_true rfl
      · exact fun heq => (of_decide_eq_true rfl : 7269 ∉ searchCarryRegs)
          (heq ▸ searchCarry_mem hF pair hm)
    have hU := hAtA.set (v := word) hFresh
    refine ⟨next (setReg a 7269 word), next (setReg a 7269 word), hU.mono ?_,
      fun _ => hGet, ?_, .refl, ?_⟩
    · exact ⟨hU.2.2.2.2.2.1, hU.2.2.2.2.1, hU.2.2.2.2.2.2⟩
    · simpa only [ite_eq_left (show first + 31 + lane ≤ p.batch from h)] using hTail
    · simpa only [ite_eq_left (show first + 31 + lane ≤ p.batch from h)] using hPast
  · have hvPC : v.pc = 7822 := by simpa [index, Nat.lt_of_not_ge h] using hv.1
    have hWord : word = b32 0 := by simp [word, drainCuQ, h]
    have hvFacts : At v 7822 (groupLaneFacts p cta first lane F word) :=
      ⟨hvPC, hv.2.1, hv.2.2.1, hv.2.2.2.1, by simpa only [hWord] using hv.2.2.2.2.2⟩
    exact ⟨before, v, hvFacts, fun h' => (h h').elim, by
      simpa only [show ¬ first + 31 + lane ≤ p.batch from h, ite_false] using hRun, hApproach, by
        simpa only [ite_eq_right (show ¬ first + 31 + lane ≤ p.batch from h)] using hRecorded⟩

private theorem searchLaneRead {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j cta first lane : Nat}
    {F : List (Nat × Value)} {before t : TState} {o : Option TState}
    (hF : ∀ x ∈ F, x.1 ∈ fallbackFrameRegs) (hBase : (7506, b64 p.cuQBase) ∈ F)
    (ht : At t 7818 ((696, .pred (decide (p.batch < first + 31 + lane))) ::
      groupLaneFacts p cta first lane F (b32 0)))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before t)
    (hRun : Run kernel Assumptions.all l g before ((X.tr g).drop j) o)
    (hNonempty : first + 31 + lane ≤ p.batch → (X.tr g).drop j ≠ []) :
    let index := first + 31 + lane
    let word := b32 (drainCuQ p index)
    ∃ v u, At u 7822 (groupLaneFacts p cta first lane F word) ∧
      (index ≤ p.batch → X.get (g, j) = some ⟨7821, .rd (searchReadAcc p index)
        (word.toBytes.map some)⟩) ∧
      Run kernel Assumptions.all l g v
        ((X.tr g).drop (if index ≤ p.batch then j + 1 else j)) o ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) v u := by
  dsimp only
  let index := first + 31 + lane
  let acc := searchReadAcc p index
  let word := b32 (drainCuQ p index)
  obtain ⟨v,u,hu,he,hr,hs,_⟩ := replaySearchLaneRead hp hF hBase ht hLocal hRun
    (fun _ _ => True) trivial (by
      dsimp only
      intro h a hPc hn
      obtain ⟨e, u, hGet, ⟨bs, _, rfl, hu⟩, hTail⟩ := hn.continuing_at_nonempty (by
        rintro _ ⟨_, _, _, hBad⟩; cases hBad) hRun (hNonempty h)
      obtain rfl := Option.some.inj hu
      rw [hPc] at hGet
      have hBytes : bs = word.toBytes.map some := by
        change bs = (b32 (drainCuQ p index)).toBytes.map some
        rw [drainCuQ, ite_eq_left h]
        exact cuQWordReads hp hX h (g, j) bs ⟨7821, hGet⟩
      subst bs
      exact ⟨hGet,hTail,trivial⟩)
  exact ⟨v,u,hu,he,hr,hs⟩

private theorem searchLastLane {g cta first lane : Nat} {F : List (Nat × Value)} {t : TState}
    {word : Value} (hl : lane < 32) (hF : ∀ x ∈ F, x.1 ∈ fallbackFrameRegs)
    (ht : At t 7822 (groupLaneFacts p cta first lane F word)) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u 7823 ((697, .pred (decide (lane = 31))) :: groupLaneFacts p cta first lane F word) := by
  have hAt : At t 7822 [(1616, b32 lane)] := ht.mono
    ⟨holds_mem ht.2.2.2.2 (by simp [groupLaneFacts, searchCarry]), trivial⟩
  obtain ⟨u, hr, hu⟩ := groupLastLaneCheck l g hl t hAt
  obtain ⟨hRun, hFrame⟩ := searchLinear (R := [1621, 7269] ++ searchCarryRegs)
    (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hr
  have hKeep := holdsSchedulerFrame ht.2.2.2.2 hFrame (by
    intro pair hm
    simp only [groupLaneFacts, List.cons_append, List.nil_append, List.mem_cons] at hm
    rcases hm with rfl | rfl | hm
    · exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
    · exact List.mem_append.mpr (.inr (searchCarry_mem hF pair hm)))
  exact ⟨u, hRun, hu.mono ⟨hu.2.2.2.2.1, hKeep⟩⟩

private def searchGuards (lane : Nat) : List (Nat × Value) :=
  [(703, .pred (decide (16 ≤ lane))), (704, .pred (decide (8 ≤ lane))),
    (705, .pred (decide (4 ≤ lane))), (706, .pred (decide (2 ≤ lane))),
    (707, .pred (decide (lane = 0)))]

private def searchScanCarry (p : Params) (cta first lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  searchGuards lane ++ (7270, b32 (groupLaneTiles p first lane)) ::
    searchCarry p cta first (tilePrefix p first * p.heads) lane F

private def searchScanRegs : List Nat := [703, 704, 705, 706, 707, 7270] ++ searchCarryRegs

private theorem searchScan_mem {p : Params} {cta first lane : Nat} {F : List (Nat × Value)}
    (hF : ∀ x ∈ F, x.1 ∈ fallbackFrameRegs) :
    ∀ x ∈ searchScanCarry p cta first lane F, x.1 ∈ searchScanRegs := by
  intro x hx
  simp only [searchScanCarry, searchGuards, List.cons_append, List.nil_append, List.mem_cons] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | hx <;>
    first | exact of_decide_eq_true rfl | exact List.mem_append.mpr (.inr (searchCarry_mem hF x hx))

private def searchUpFacts (p : Params) (cta first lane : Nat) (F : List (Nat × Value))
    (stage : Fin 5) : List (Nat × Value) :=
  (groupScanSrc stage, b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val) lane)) ::
    searchScanCarry p cta first lane F

private theorem prepareSearchUp {m : Mem0} (hp : Pre p l m) {g cta first lane : Nat}
    {F : List (Nat × Value)} {t : TState} (hGroup : first + 31 < p.batch) (hl : lane < 32)
    (hF : ∀ x ∈ F, x.1 ∈ fallbackFrameRegs)
    (ht : At t 7824 ((5890, b32 (drainCuQ p (first + 31 + (shflSource .down lane 1 31).1))) ::
      (697, .pred (decide (lane = 31))) :: groupLaneFacts p cta first lane F
        (b32 (drainCuQ p (first + 31 + lane))))) :
    ∃ n u, run kernel Assumptions.all l g n t = some u ∧
      At u 7844 (searchUpFacts p cta (first + 31) lane F 0) := by
  let nextGroup := first + 31
  let index := nextGroup + lane
  let begin := drainCuQ p index
  let finish := drainCuQ p (nextGroup + (shflSource .down lane 1 31).1)
  let eligible := decide (index < p.batch ∧ lane < 31)
  let delta := truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin)
  let len := delta.toNat
  let carry := searchCarry p cta nextGroup (tilePrefix p nextGroup * p.heads) lane F
  obtain ⟨hBegin, hFinish, hMono, hDiff, hTiles⟩ := drainWordTiles hp nextGroup lane
  have hIndex : index < 2 ^ 31 := by
    have := hp.shape.2.2.2.2.2
    dsimp [index, nextGroup]
    omega
  have hKeepT : Holds t.regs carry := ht.2.2.2.2.2.2.2.2
  have hArgs : At t 7824 [(7269, b32 begin), (5890, b32 finish), (1621, b32 index),
      (7277, b32 p.batch), (697, .pred (decide (lane = 31)))] := ht.mono
    ⟨ht.2.2.2.2.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.2.1,
      holds_mem hKeepT (by simp [carry, searchCarry]), ht.2.2.2.2.2.1, trivial⟩
  obtain ⟨v, hg, hv⟩ := groupTileGate l g hl hIndex hp.shape.2.1 hBegin hFinish t hArgs
  obtain ⟨hgA, hgFrame⟩ := searchLinear (R := searchCarryRegs)
    (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hg
  have hKeepV := holdsSchedulerFrame hKeepT hgFrame (searchCarry_mem hF)
  have hLen (he : eligible = true) : len = finish - begin := by
    have hh : begin ≤ finish := hMono he
    dsimp [len, delta]
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show begin < 2 ^ 64 by omega) hh,
      truncBits_ofNat (show finish - begin < 2 ^ 32 by omega) (by decide),
      toNat_ofNat_lt (show finish - begin < 2 ^ 64 by omega)]
  have hTileArgs : At v 7828 [(699, .pred (!eligible)), (1622, b32 len), (7270, b32 0)] :=
    hv.mono ⟨hv.2.2.2.2.2.2.1, by simpa [b32, len, delta] using hv.2.2.2.2.1,
      hv.2.2.2.2.2.1, trivial⟩
  obtain ⟨w, hw, hW⟩ := groupTileContribution l g eligible len
    (fun he => hLen he ▸ hDiff) v hTileArgs
  obtain ⟨z, hz, hZ⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_7828 (!eligible) hTileArgs hTileArgs.2.2.2.2.1 (by simp)
  obtain ⟨hzA, hzFrame⟩ := searchLinear (R := searchCarryRegs)
    (by decide) (by decide) hv.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hz
  have hKeepZ := holdsSchedulerFrame hKeepV hzFrame (searchCarry_mem hF)
  have hLocal : ∃ n, run kernel Assumptions.all l g n v = some w ∧ Holds w.regs carry := by
    cases he : eligible with
    | false =>
      rw [ite_eq_right (show ¬ eligible = true by rw [he]; decide)] at hw
      have heq := Option.some.inj (hz.symm.trans hw)
      subst w
      exact ⟨1, hzA, hKeepZ⟩
    | true =>
      have hzPC : z.pc = 7829 := by simpa [he] using hZ.1
      have hTail : run kernel [] l g 10 z = some w := by
        rw [ite_eq_left he, show (11 : Nat) = 1 + 10 from rfl, run_add, hz, Option.bind_some] at hw
        exact hw
      obtain ⟨hwA, hwFrame⟩ := searchLinear (R := searchCarryRegs)
        (by decide) (by decide) hzPC
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl) hTail
      exact ⟨11, run_comp hzA hwA, holdsSchedulerFrame hKeepZ hwFrame (searchCarry_mem hF)⟩
  obtain ⟨n, hwA, hKeepW⟩ := hLocal
  have hValue : (if eligible then (len + 255) / 256 else 0) = groupLaneTiles p nextGroup lane := by
    by_cases he : eligible = true
    · rw [hLen he]
      exact hTiles
    · rw [ite_eq_right he]
      change (if eligible then (finish - begin + 255) / 256 else 0) =
        groupLaneTiles p nextGroup lane at hTiles
      rwa [ite_eq_right he] at hTiles
  have hWord : w.regs 7270 = some (b32 (groupLaneTiles p nextGroup lane)) :=
    congrArg (fun n => some (b32 n)) hValue ▸ hW.2.2.2.2.1
  have hGuardAt : At w 7839 [(1616, b32 lane), (7270, b32 (groupLaneTiles p nextGroup lane))] :=
    hW.mono ⟨holds_mem hKeepW (by simp [carry, searchCarry]), hWord, trivial⟩
  obtain ⟨u, hr, hu⟩ := groupScanPredicates l g hl w hGuardAt
  obtain ⟨hrA, hrFrame⟩ := searchLinear (R := searchCarryRegs)
    (by decide) (by decide) hW.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hr
  have hKeepU := holdsSchedulerFrame hKeepW hrFrame (searchCarry_mem hF)
  have hGuard := hu.2.2.2.2
  have hPart : prefixWindow (groupLaneTiles p nextGroup) (2 ^ (0 : Fin 5).val) lane =
      groupLaneTiles p nextGroup lane := prefixWindow_one _ _
  exact ⟨4 + n + 5, u, run_comp (run_comp hgA hwA) hrA, hu.mono
    ⟨hPart ▸ hGuard.2.2.2.2.2.1, hGuard.1, hGuard.2.1, hGuard.2.2.1,
      hGuard.2.2.2.1, hGuard.2.2.2.2.1, hGuard.2.2.2.2.2.1, hKeepU⟩⟩

private def searchUpResult (p : Params) (cta first lane : Nat) (F : List (Nat × Value))
    (stage : Fin 5) : List (Nat × Value) :=
  (groupScanResult stage, b32 (prefixWindow (groupLaneTiles p first) (2 * 2 ^ stage.val) lane)) ::
    searchScanCarry p cta first lane F

private theorem searchScanFresh {p : Params} {cta first lane : Nat}
    {F : List (Nat × Value)} (stage : Fin 5) (hF : ∀ x ∈ F, x.1 ∈ fallbackFrameRegs)
    {pair : Nat × Value} (hm : pair ∈ searchUpFacts p cta first lane F stage) :
    pair.1 ≠ groupScanDst stage := by
  rcases List.mem_cons.mp hm with rfl | hx
  · fin_cases stage <;> exact of_decide_eq_true rfl
  · have hn : groupScanDst stage ∉ searchScanRegs := by fin_cases stage <;> decide
    exact fun e => hn (e ▸ searchScan_mem hF pair hx)

private theorem searchScanOut {m : Mem0} (hp : Pre p l m) {g cta first lane : Nat}
    {F : List (Nat × Value)} (stage : Fin 5) {t : TState}
    (ht : At t (groupScanPc stage) (searchUpFacts p cta first lane F stage)) :
    out kernel Assumptions.all l (warpLane l g lane) t =
      .ev (.shfl .up (b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val) lane))
        (2 ^ stage.val) 0 (fun v _ => next (setReg t (groupScanDst stage) v))) := by
  have hBounds : 7810 ≤ groupScanPc stage ∧ groupScanPc stage + 3 ≤ 7864 := by
    have := stage.isLt
    simp [groupScanPc]
    omega
  exact (searchModel (by rw [ht.1]; omega) (by rw [ht.1]; omega)).trans
    (groupScanTemplate hp _ _ stage _ ht.1 ht.2.2.2.1 ht.2.2.2.2.1)

private theorem searchScanFoldLocal {m : Mem0} (hp : Pre p l m) {g cta first lane : Nat}
    {F : List (Nat × Value)} (hf : first ≤ p.batch) (stage : Fin 5) (hl : lane < 32)
    (hF : ∀ x ∈ F, x.1 ∈ fallbackFrameRegs) {t : TState}
    (ht : At t (groupScanPc stage + 1)
      ((groupScanDst stage, b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val)
        (shflSource .up lane (2 ^ stage.val) 0).1)) :: searchUpFacts p cta first lane F stage)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u (groupScanPc stage + 3) (searchUpResult p cta first lane F stage) := by
  let xs := groupLaneTiles p first
  let a := fun lane => b32 (prefixWindow xs (2 ^ stage.val) lane)
  have hBounds : 7810 ≤ groupScanPc stage ∧ groupScanPc stage + 3 ≤ 7864 := by
    have := stage.isLt
    simp [groupScanPc]
    omega
  have hCarry : Holds t.regs (searchScanCarry p cta first lane F) :=
    ht.2.2.2.2.2.2
  have hGuard : t.regs (707 - stage.val) =
      some (.pred (groupScanGuard stage lane)) := by
    apply holds_mem hCarry
    fin_cases stage <;> simp [searchScanCarry, searchGuards, groupScanGuard]
  have hAt : At t (groupScanPc stage + 1)
      [(707 - stage.val, .pred (groupScanGuard stage lane)),
        (groupScanSrc stage, a lane), (groupScanDst stage,
          a (shflSource .up lane (2 ^ stage.val) 0).1)] :=
    ht.mono ⟨hGuard, ht.2.2.2.2.2.1, ht.2.2.2.2.1, trivial⟩
  have hSource := Step.shflSource_lt .up hl (2 ^ stage.val) 0
  have hLocalBound : prefixWindow xs (2 ^ stage.val) lane +
      prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1 < 2 ^ 32 := by
    have h₁ := hp.groupWindow_signed hf hl (2 ^ stage.val)
    have h₂ := hp.groupWindow_signed hf hSource (2 ^ stage.val)
    change prefixWindow xs _ lane < 2 ^ 31 at h₁
    change prefixWindow xs _ _ < 2 ^ 31 at h₂
    omega
  obtain ⟨u, hr, hu⟩ := groupScanFold stage l (warpLane l g lane) xs hLocalBound
    t hAt
  obtain ⟨hRun, hFrame⟩ := searchLinear (R := searchScanRegs)
    (by omega) (by omega) hAt.1
    (by fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl)
    (by fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl) hr
  exact ⟨u, run_rtg hRun, hu.mono
    ⟨hu.2.2.2.2.1, holdsSchedulerFrame hCarry hFrame (searchScan_mem hF)⟩⟩

private theorem searchScanStage {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g cta first shuffles votes : Nat}
    (hg : g < l.threads) (hf : first ≤ p.batch) (stage : Fin 5) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ fallbackFrameRegs)
    (cur : SchedulerWarpAt l X g (groupScanPc stage)
      (fun lane => searchUpFacts p cta first lane (F lane) stage) shuffles votes ends)
    {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : groupScanPc stage < target.pc) :
    ∃ result : SchedulerWarpAt l X g (groupScanPc stage + 3)
        (fun lane => searchUpResult p cta first lane (F lane) stage) (shuffles + 1) votes ends,
      result.pos = (fun lane => cur.pos lane + 1) ∧
      (WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g result.pos src index target) := by
  let xs := groupLaneTiles p first
  let a := fun lane => b32 (prefixWindow xs (2 ^ stage.val) lane)
  obtain ⟨mid, hMidPos, _, hMid⟩ := cur.consumeShuffleToRecorded hp hX hg .up a
    (fun _ => 2 ^ stage.val) (fun _ => 0)
    (fun lane hl _ => searchScanFresh stage (hF lane hl))
    (fun lane hl => searchScanOut hp stage (cur.checkpoint lane hl)) hProgress hPc
  obtain ⟨result, hResult⟩ := mid.advanceLocalAt
    (fun lane hl => searchScanFoldLocal hp hf stage hl (hF lane hl) (mid.checkpoint lane hl))
  exact ⟨result, hResult.trans hMidPos, fun h => hResult.symm ▸ hMid h⟩

private theorem searchScanStageOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g cta first shuffles votes : Nat}
    (hg : g < l.threads) (hf : first ≤ p.batch) (stage : Fin 5) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ fallbackFrameRegs)
    (cur : SchedulerWarpReached l X g (groupScanPc stage)
      (fun lane => searchUpFacts p cta first lane (F lane) stage) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g (groupScanPc stage + 3)
      (fun lane => searchUpResult p cta first lane (F lane) stage) (shuffles + 1) votes ends) := by
  let xs := groupLaneTiles p first
  let a := fun lane => b32 (prefixWindow xs (2 ^ stage.val) lane)
  obtain ⟨mid⟩ := cur.consumeShuffle hp hMax hg .up a (fun _ => 2 ^ stage.val) (fun _ => 0)
    (fun lane hl _ => searchScanFresh stage (hF lane hl))
    (fun lane hl => searchScanOut hp stage (cur.checkpoint lane hl))
  exact mid.advanceLocal
    (fun lane hl => searchScanFoldLocal hp hf stage hl (hF lane hl) (mid.checkpoint lane hl))

private theorem searchReadCount {p : Params} {X : Execution} {g pos index n : Nat}
    (test : Event → Bool) (hCount : ((X.tr g).take pos).countP test = n)
    (hOrdinary : ∀ a bytes, test ⟨7821,.rd a bytes⟩ = false)
    (hRead : index ≤ p.batch → X.get (g,pos) =
      some ⟨7821,.rd (searchReadAcc p index) ((b32 (drainCuQ p index)).toBytes.map some)⟩) :
    ((X.tr g).take (if index ≤ p.batch then pos+1 else pos)).countP test = n := by
  by_cases h : index ≤ p.batch
  · simp only [ite_eq_left h, List.take_add_one]
    rw [show (X.tr g)[pos]? = _ from hRead h]
    simp [hOrdinary,hCount]
  · simpa only [ite_eq_right h] using hCount

private def searchDownFacts (p : Params) (cta first lane : Nat)
    (F : List (Nat × Value)) : List (Nat × Value) :=
  (697, .pred (decide (lane = 31))) ::
    groupLaneFacts p cta first lane F (b32 (drainCuQ p (first + 31 + lane)))

private theorem searchDownOut {m : Mem0} (hp : Pre p l m) {g cta first lane : Nat}
    {F : List (Nat × Value)} {t : TState} (ht : At t 7823 (searchDownFacts p cta first lane F)) :
    out kernel Assumptions.all l (warpLane l g lane) t =
      .ev (.shfl .down (b32 (drainCuQ p (first + 31 + lane))) 1 31
        (fun v _ => next (setReg t 5890 v))) :=
  (searchModel (by rw [ht.1]; decide) (by rw [ht.1]; decide)).trans
    (groupDownTemplate hp _ _ _ ht.1 ht.2.2.2.1 ht.2.2.2.2.2.2.1)

private theorem searchDownFresh {p : Params} {cta first lane : Nat}
    {F : List (Nat × Value)} (hF : ∀ x ∈ F, x.1 ∈ fallbackFrameRegs)
    {pair : Nat × Value} (hPair : pair ∈ searchDownFacts p cta first lane F) :
    pair.1 ≠ 5890 := by
  simp only [searchDownFacts, groupLaneFacts, List.cons_append, List.nil_append,
    List.mem_cons] at hPair
  rcases hPair with rfl | rfl | rfl | hPair
  all_goals first
    | exact of_decide_eq_true rfl
    | exact fun he => (of_decide_eq_true rfl : 5890 ∉ searchCarryRegs)
        (he ▸ searchCarry_mem hF pair hPair)

private theorem searchDownWarp {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g cta first shuffles votes : Nat}
    (hg : g < l.threads) (hGroup : first + 31 < p.batch) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ fallbackFrameRegs)
    (hBase : ∀ lane < 32, (7506, b64 p.cuQBase) ∈ F lane)
    (cur : SchedulerWarpAt l X g 7814 (fun lane => groupAdvanced p cta first lane (F lane))
      shuffles votes ends) {src targetPos : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨
      WarpFollowsEvent l X g cur.pos src targetPos target) (hPc : 7823 < target.pc) :
    ∃ result : SchedulerWarpAt l X g 7844
        (fun lane => searchUpFacts p cta (first + 31) lane (F lane) 0) (shuffles + 1) votes ends,
      result.pos = (fun lane => (if first + 31 + lane ≤ p.batch then cur.pos lane + 1
        else cur.pos lane) + 1) ∧
      (∀ lane < 32, first + 31 + lane ≤ p.batch → X.get (warpLane l g lane, cur.pos lane) =
        some ⟨7821, .rd (searchReadAcc p (first + 31 + lane))
          ((b32 (drainCuQ p (first + 31 + lane))).toBytes.map some)⟩) ∧
      (WarpFollowsEvent l X g cur.pos src targetPos target →
        WarpFollowsEvent l X g result.pos src targetPos target) := by
  let _ : Nonempty TState := ⟨cur.state 0⟩
  let index := fun lane => first + 31 + lane
  let word := fun lane => b32 (drainCuQ p (index lane))
  let pos := fun lane => if index lane ≤ p.batch then cur.pos lane + 1 else cur.pos lane
  let facts := fun lane => searchDownFacts p cta first lane (F lane)
  have hLane (lane : Nat) (hl : lane < 32)
      (hSuffix : (X.tr (warpLane l g lane)).drop (cur.pos lane) ≠ []) :
      ∃ before t, At t 7823 (facts lane) ∧
        Run kernel Assumptions.all l (warpLane l g lane) before
          ((X.tr (warpLane l g lane)).drop (pos lane)) (ends lane) ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) before t ∧
        (index lane ≤ p.batch → X.get (warpLane l g lane, cur.pos lane) =
          some ⟨7821, .rd (searchReadAcc p (index lane)) ((word lane).toBytes.map some)⟩) := by
    let thread := warpLane l g lane
    have ht := cur.checkpoint lane hl
    obtain ⟨v, hv, hV⟩ := branchSearchGroup (l := l) (g := thread) ht
    have hV' : At v 7815 (groupAdvanced p cta first lane (F lane)) := by
      simpa only [ite_eq_right (Nat.not_le.mpr hGroup)] using hV
    obtain ⟨w, hw, hW⟩ := searchLaneGate hp (g := thread) hGroup hl (hF lane hl) hV'
    have hLocal := (cur.localSteps lane hl).trans (run_rtg (run_comp hv hw))
    obtain ⟨before, u, hu, hRead, hTail, hSteps⟩ :=
      searchLaneRead hp hX (hF lane hl) (hBase lane hl) hW hLocal
        (cur.continuation lane hl) (fun _ => hSuffix)
    obtain ⟨out, hStep, hAt⟩ := searchLastLane (l := l) (g := thread) hl (hF lane hl) hu
    exact ⟨before, out, hAt, hTail, hSteps.trans (run_rtg hStep), hRead⟩
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hTemplate (lane : Nat) {t : TState} (ht : At t 7823 (facts lane)) :=
    searchDownOut hp (g := g) ht
  have hBefore (h : WarpFollowsEvent l X g cur.pos src targetPos target)
      (hRead : index src ≤ p.batch → X.get (warpLane l g src, cur.pos src) =
        some ⟨7821, .rd (searchReadAcc p (index src)) ((word src).toBytes.map some)⟩) :
      pos src ≤ targetPos := by
    by_cases hd : index src ≤ p.batch
    · simp only [pos, ite_eq_left hd]
      rcases Nat.eq_or_lt_of_le h.before with heq | hlt
      · have hGet := hRead hd
        rw [heq] at hGet
        have hEq := congrArg Event.pc (Option.some.inj (hGet.symm.trans h.get))
        change 7821 = target.pc at hEq
        omega
      · exact hlt
    · simpa only [pos, ite_eq_right hd] using h.before
  have hSuffix (lane : Nat) (hl : lane < 32) :
      (X.tr (warpLane l g lane)).drop (cur.pos lane) ≠ [] := by
    rcases hProgress with he | h
    · intro hNil
      have hr := cur.continuation lane hl
      rw [hNil, he lane hl] at hr
      cases hr
    · obtain ⟨before, t, ht, hr, hLocal, hRead⟩ := hLane src h.lane h.nonempty
      have hpast := hBefore h hRead
      have hRemain : (X.tr (warpLane l g src)).drop (pos src) ≠ [] := by
        intro hNil
        have hLen : targetPos < (X.tr (warpLane l g src)).length :=
          (List.getElem?_eq_some_iff.mp h.get).1
        exact Nat.not_le_of_lt hLen ((List.drop_eq_nil_iff.mp hNil).trans hpast)
      have hn : Next kernel Assumptions.all l (warpLane l g src) before t
          (.shfl .down (word src) 1 31 (fun x _ => next (setReg t 5890 x))) :=
        ⟨hLocal, hTemplate src ht⟩
      obtain ⟨_, _, he, hk, _⟩ := hn.shuffle_at_nonempty hr hRemain
        (searchReadCount _ (cur.ordinals.shfl src h.lane) (fun _ _ => rfl) hRead)
      exact cur.ordinals.shuffle_suffix_nonempty hX hBlock hg h.lane he hk hl (h.noExit lane hl)
  choose! before state hAt hRun hLocal hRead using
    fun lane hl => hLane lane hl (hSuffix lane hl)
  have hOrd : WarpOrdinals l X g pos shuffles votes :=
    ⟨fun lane hl => searchReadCount _ (cur.ordinals.shfl lane hl) (fun _ _ => rfl)
      (hRead lane hl),
      fun lane hl => searchReadCount _ (cur.ordinals.vote lane hl) (fun _ _ => rfl)
        (hRead lane hl)⟩
  let down : SchedulerWarpAt l X g 7823 facts shuffles votes ends :=
    ⟨pos, before, state, hOrd, hRun, hLocal, hAt⟩
  have hKeep (h : WarpFollowsEvent l X g cur.pos src targetPos target) :
      WarpFollowsEvent l X g down.pos src targetPos target := by
    apply h.after (hBefore h (hRead src h.lane))
    intro lane hl j hj₁ hj₂ pc
    by_cases ha : index lane ≤ p.batch
    · have he := hRead lane hl ha
      change j < pos lane at hj₁
      simp only [pos, ite_eq_left ha] at hj₁
      exact noExitThroughContinuingEvent hX (Step.sameWarp_lane hBlock hg hl).1.1.2.1
        he (by intro h; cases h) hj₁ pc
    · change j < pos lane at hj₁
      simp only [pos, ite_eq_right ha] at hj₁
      omega
  have hOut := fun lane hl => hTemplate lane (hAt lane hl)
  obtain ⟨after, hAfterPos, _, hAfter⟩ :=
    down.consumeShuffleToRecorded hp hX hg .down word (fun _ => 1) (fun _ => 31)
      (fun lane hl _ => searchDownFresh (hF lane hl)) hOut
      (hProgress.imp_right hKeep) hPc
  have hPrep : ∃ result : SchedulerWarpAt l X g 7844
      (fun lane => searchUpFacts p cta (first + 31) lane (F lane) 0) (shuffles + 1) votes ends,
      result.pos = after.pos := by
    apply after.advanceLocalAt
    intro lane hl
    obtain ⟨_, u, hu, hU⟩ := prepareSearchUp hp (g := warpLane l g lane) hGroup hl (hF lane hl)
      (after.checkpoint lane hl)
    exact ⟨u, run_rtg hu, hU⟩
  obtain ⟨result, hResult⟩ := hPrep
  exact ⟨result, hResult.trans hAfterPos, hRead, fun h => hResult.symm ▸ hAfter (hKeep h)⟩

private theorem searchDownOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g cta first shuffles votes : Nat}
    (hg : g < l.threads) (hGroup : first + 31 < p.batch) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ fallbackFrameRegs)
    (hBase : ∀ lane < 32, (7506,b64 p.cuQBase) ∈ F lane)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k))
    (cur : SchedulerWarpReached l X g 7814 (fun lane => groupAdvanced p cta first lane (F lane))
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7844
      (fun lane => searchUpFacts p cta (first + 31) lane (F lane) 0)
      (shuffles + 1) votes ends) := by
  let _ : Nonempty TState := ⟨cur.state 0⟩
  let index := fun lane => first + 31 + lane
  let word := fun lane => b32 (drainCuQ p (index lane))
  let pos := fun lane => if index lane ≤ p.batch then cur.pos lane + 1 else cur.pos lane
  let facts := fun lane => searchDownFacts p cta first lane (F lane)
  let thread := warpLane l g
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) :
      ∃ before t, At t 7823 (facts lane) ∧
        Run kernel Assumptions.all l (thread lane) before
          ((X.tr (thread lane)).drop (pos lane)) (ends lane) ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) before t ∧
        Run kernel Assumptions.all l (thread lane) {}
          ((X.tr (thread lane)).take (pos lane)) (some before) ∧
        (index lane ≤ p.batch → X.get (thread lane, cur.pos lane) =
          some ⟨7821, .rd (searchReadAcc p (index lane)) ((word lane).toBytes.map some)⟩) := by
    have ht := cur.checkpoint lane hl
    obtain ⟨v,hv,hV⟩ := branchSearchGroup (l := l) (g := thread lane) ht
    have hV' : At v 7815 (groupAdvanced p cta first lane (F lane)) := by
      simpa only [ite_eq_right (Nat.not_le.mpr hGroup)] using hV
    obtain ⟨w,hw,hW⟩ := searchLaneGate hp (g := thread lane) hGroup hl (hF lane hl) hV'
    have hLocal := (cur.localSteps lane hl).trans (run_rtg (run_comp hv hw))
    have hg' := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
    obtain ⟨before,u,hu,he,hRun,hSteps,hPast⟩ :=
      replaySearchLaneRead hp (hF lane hl) (hBase lane hl) hW hLocal
        (cur.continuation lane hl)
        (fun n s => Run kernel Assumptions.all l (thread lane) {}
          ((X.tr (thread lane)).take n) (some s)) (cur.recorded lane hl) (by
        dsimp only
        intro h a hSite hNext
        let acc := searchReadAcc p (index lane)
        obtain ⟨hGet,hPast,hRest⟩ :=
          Step.protected_read_of_maximal hMax hg' (show acc.size = (word lane).bytes from rfl)
            (by
              intro k hk
              change m ((globalLoc (p.cuQBase + 4 * index lane)).at k) =
                some (some ((b32 (drainCuQ p (index lane))).byteAt k))
              rw [drainCuQ, ite_eq_left h]
              exact hp.cuQ (index lane) h k hk) (hProtected (index lane) h) hNext
            (cur.recorded lane hl) (cur.continuation lane hl) (cur.positive lane hl)
            (cur.bounded lane hl) (cur.released lane hl)
            (Assumptions.wf_snoc_initial hMax.1)
        rw [hSite] at hGet
        exact ⟨hGet,hRest,hPast⟩)
    obtain ⟨u',hu',hReady⟩ := searchLastLane (l := l) (g := thread lane) hl (hF lane hl) hu
    exact ⟨before,u',hReady,hRun,hSteps.trans (run_rtg hu'),hPast,he⟩
  choose! before state hAt hRun hSteps hPast hRead using hLane
  have hOrd : WarpOrdinals l X g pos shuffles votes := by
    exact ⟨fun lane hl => searchReadCount _ (cur.ordinals.shfl lane hl) (fun _ _ => rfl)
        (hRead lane hl),
      fun lane hl => searchReadCount _ (cur.ordinals.vote lane hl) (fun _ _ => rfl)
        (hRead lane hl)⟩
  let down : SchedulerWarpReached l X g 7823 facts shuffles votes ends :=
    ⟨⟨pos,before,state,hOrd,hRun,hSteps,hAt⟩,fun lane hl => by
      have := cur.positive lane hl
      dsimp only [pos]
      split_ifs <;> omega,fun lane hl => by
      by_cases h : index lane ≤ p.batch
      · simpa only [pos, ite_eq_left h] using Nat.succ_le_of_lt (len_of_get (hRead lane hl h))
      · simpa only [pos, ite_eq_right h] using cur.bounded lane hl,fun lane hl => by
      by_cases h : index lane ≤ p.batch
      · simpa only [pos, ite_eq_left h] using
          (releasedIfLast (l := l) (hRead lane hl h) (by intro h; cases h))
      · simpa only [pos, ite_eq_right h] using cur.released lane hl,hPast⟩
  obtain ⟨after⟩ := down.consumeShuffle hp hMax hg .down word (fun _ => 1) (fun _ => 31)
    (fun lane hl _ => searchDownFresh (hF lane hl))
    (fun lane hl => searchDownOut hp (down.checkpoint lane hl))
  exact after.advanceLocal (fun lane hl => by
    obtain ⟨_, u, hu, hU⟩ := prepareSearchUp hp (g := thread lane) hGroup hl (hF lane hl)
      (after.checkpoint lane hl)
    exact ⟨u,run_rtg hu,hU⟩)

private theorem searchSigned {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

private theorem searchExhausted {X : Execution} {g cta first shuffles votes : Nat}
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState} (hStop : cta + 1 < 2 ^ 31)
    (hClip : p.batch ≤ first + 31) (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ fallbackFrameRegs)
    (cur : SchedulerWarpAt l X g 7814 (fun lane => groupAdvanced p cta first lane (F lane))
      shuffles votes ends) :
    ∃ result : SchedulerWarpAt l X g 7864 (fun lane => exhaustedScheduleFacts p (F lane))
        shuffles votes ends,
      result.pos = cur.pos ∧ result.before = cur.before := by
  apply cur.advanceLocalPreserving
  intro lane hl
  let thread := warpLane l g lane
  obtain ⟨v, hv, hV⟩ := branchSearchGroup (l := l) (g := thread) (cur.checkpoint lane hl)
  have hpv : v.pc = 7861 := by simpa only [ite_eq_left hClip] using hV.1
  have hAt : At v 7861 [(7274, b32 (cta + 1)), (1618, b32 cta)] :=
    ⟨hpv, hV.2.1, hV.2.2.1, hV.2.2.2.1, hV.2.2.2.2.2.2.1,
      holds_mem hV.2.2.2.2 (by simp [groupAdvanced, searchCarry]), trivial⟩
  have hGate : Seg kernel [] l thread 2 7861 [(7274, b32 (cta + 1)), (1618, b32 cta)] 7863
      [(708, .pred false)] := by
    intro t ht
    have hCta : cta < 2 ^ 31 := by omega
    seg_fp ht using simp only [compare, Option.getD_some,
      truncBits_ofNat (show cta + 1 < 2 ^ 32 by omega) (by decide),
      truncBits_ofNat (show cta < 2 ^ 32 by omega) (by decide),
      searchSigned hStop, searchSigned hCta, Int.ofNat_le, show ¬ cta + 1 ≤ cta by omega,
      decide_false]
  obtain ⟨w, hw, hW⟩ := hGate v hAt
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := thread)
    Flow.code_7863 false hW hW.2.2.2.2.1 (by simp)
  obtain ⟨hRun, hFrame⟩ := searchLinear (R := [7273, 7277] ++ fallbackFrameRegs)
    (by decide) (by decide) hpv
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) (run_comp hw hu)
  have hSaved : Holds v.regs (exhaustedScheduleFacts p (F lane)) := by
    exact ⟨holds_mem hV.2.2.2.2 (by simp [groupAdvanced, searchCarry, Nat.min_eq_right hClip]),
      holds_mem hV.2.2.2.2 (by simp [groupAdvanced, searchCarry]),
      hV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  have hKeep : ∀ pair ∈ exhaustedScheduleFacts p (F lane),
      pair.1 ∈ [7273, 7277] ++ fallbackFrameRegs := by
    intro pair hp
    simp only [exhaustedScheduleFacts, List.cons_append, List.nil_append, List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
    · exact List.mem_append.mpr (.inr (hF lane hl pair hp))
  exact ⟨u, run_rtg (run_comp hv hRun), hU.mono (holdsSchedulerFrame hSaved hFrame hKeep)⟩

private def searchTotalFacts (p : Params) (cta first lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  [(7272, b32 (∑ j ∈ Finset.range 32, groupLaneTiles p first j)),
    (7271, b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)),
    (7270, b32 (groupLaneTiles p first lane))] ++
    searchCarry p cta first (tilePrefix p first * p.heads) lane F

private def searchTotalSum (p : Params) (first lane : Nat) : Value :=
  b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)

private theorem searchTotalFresh {p : Params} {cta first lane : Nat}
    {F : List (Nat × Value)} (hF : ∀ x ∈ F, x.1 ∈ fallbackFrameRegs)
    {pair : Nat × Value} (hm : pair ∈ searchUpResult p cta first lane F 4) : pair.1 ≠ 7272 := by
  rcases List.mem_cons.mp hm with rfl | hx
  · exact of_decide_eq_true rfl
  · exact fun he => (of_decide_eq_true rfl : 7272 ∉ searchScanRegs)
      (he ▸ searchScan_mem hF pair hx)

private theorem searchTotalOut {m : Mem0} (hp : Pre p l m) {g cta first lane : Nat}
    {F : List (Nat × Value)} (hl : lane < 32) {t : TState}
    (ht : At t 7859 (searchUpResult p cta first lane F 4)) :
    out kernel Assumptions.all l (warpLane l g lane) t =
      .ev (.shfl .idx (searchTotalSum p first lane) 31 31
        (fun v _ => next (setReg t 7272 v))) := by
  have hPart := ht.2.2.2.2.1
  change t.regs 7271 =
    some (b32 (prefixWindow (groupLaneTiles p first) 32 lane)) at hPart
  rw [prefixWindow_warp _ hl] at hPart
  exact (searchModel (by rw [ht.1]; decide) (by rw [ht.1]; decide)).trans
    (groupTotalTemplate hp _ _ _ ht.1 ht.2.2.2.1 hPart)

private theorem searchTotalLocal {g cta first lane : Nat} {F : List (Nat × Value)} (hl : lane < 32)
    {t : TState}
    (ht : At t 7860 ((7272, searchTotalSum p first (shflSource .idx lane 31 31).1) ::
      searchUpResult p cta first lane F 4)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u 7860 (searchTotalFacts p cta first lane F) := by
  have hSrc : (shflSource .idx lane 31 31).1 = 31 := by
    rw [shflSource_idx lane (show (31 : Nat) < 32 by decide)]
  have hCount := ht.2.2.2.2.1
  rw [hSrc] at hCount
  have hPart := ht.2.2.2.2.2.1
  change t.regs 7271 =
    some (b32 (prefixWindow (groupLaneTiles p first) 32 lane)) at hPart
  rw [prefixWindow_warp _ hl] at hPart
  have hCarry : Holds t.regs (searchScanCarry p cta first lane F) :=
    ht.2.2.2.2.2.2
  have hKeep := ((holds_append ..).mp hCarry).2
  exact ⟨t, .refl, ht.mono ⟨hCount, hPart, hKeep⟩⟩

private theorem searchTotalWarp {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g cta first shuffles votes : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ fallbackFrameRegs)
    (cur : SchedulerWarpAt l X g 7859 (fun lane => searchUpResult p cta first lane (F lane) 4)
      shuffles votes ends) {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 7859 < target.pc) :
    ∃ result : SchedulerWarpAt l X g 7860
        (fun lane => searchTotalFacts p cta first lane (F lane)) (shuffles + 1) votes ends,
      result.pos = (fun lane => cur.pos lane + 1) ∧
      (∀ lane < 32, result.pos lane ≤ (X.tr (warpLane l g lane)).length) ∧
      (WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g result.pos src index target) := by
  obtain ⟨after, hAfterPos, hEvent, hAfter⟩ :=
    cur.consumeShuffleToRecorded hp hX hg .idx (searchTotalSum p first)
    (fun _ => 31) (fun _ => 31) (fun lane hl _ => searchTotalFresh (hF lane hl))
    (fun lane hl => searchTotalOut hp hl (cur.checkpoint lane hl)) hProgress hPc
  obtain ⟨result, hResult⟩ := after.advanceLocalAt
    (fun lane hl => searchTotalLocal hl (after.checkpoint lane hl))
  refine ⟨result, hResult.trans hAfterPos, ?_, fun h => hResult.symm ▸ hAfter h⟩
  intro lane hl
  obtain ⟨_, _, he⟩ := hEvent lane hl
  rw [hResult, hAfterPos]
  exact len_of_get he

private theorem searchTotalOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g cta first shuffles votes : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ fallbackFrameRegs)
    (cur : SchedulerWarpReached l X g 7859 (fun lane => searchUpResult p cta first lane (F lane) 4)
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7860
        (fun lane => searchTotalFacts p cta first lane (F lane)) (shuffles + 1) votes ends) := by
  obtain ⟨after⟩ := cur.consumeShuffle hp hMax hg .idx (searchTotalSum p first)
    (fun _ => 31) (fun _ => 31) (fun lane hl _ => searchTotalFresh (hF lane hl))
    (fun lane hl => searchTotalOut hp hl (cur.checkpoint lane hl))
  exact after.advanceLocal (fun lane hl => searchTotalLocal hl (after.checkpoint lane hl))

private def searchResultFacts (p : Params) (cta first lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
  [(7268, b32 limit), (7274, b32 limit),
    (7272, b32 (∑ j ∈ Finset.range 32, groupLaneTiles p first j)),
    (7271, b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)),
    (7270, b32 (groupLaneTiles p first lane)),
    (1619, b32 (cta + 1)), (7273, b32 first), (7277, b32 p.batch), (1616, b32 lane),
    (1618, b32 cta)] ++ groupSchedulerFrame p lane F

private theorem searchLimitLane {m : Mem0} (hp : Pre p l m) {g cta first lane : Nat}
    {F : List (Nat × Value)} {t : TState} (hf : first ≤ p.batch) (hCta : cta < 2 ^ 31)
    (hF : ∀ x ∈ F, x.1 ∈ fallbackFrameRegs) (ht : At t 7860 (searchTotalFacts p cta first lane F)) :
    let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
    ∃ u, run kernel Assumptions.all l g 4 t = some u ∧
      At u (if limit ≤ cta then 7810 else 7864) (searchResultFacts p cta first lane F) := by
  dsimp only
  let remaining := [(7272, b32 (∑ j ∈ Finset.range 32, groupLaneTiles p first j)),
    (7271, b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)),
    (7270, b32 (groupLaneTiles p first lane)),
    (1619, b32 (cta + 1)), (7273, b32 first), (7277, b32 p.batch), (1616, b32 lane),
    (1618, b32 cta)] ++ groupSchedulerFrame p lane F
  have h := ht.2.2.2.2
  have hFrame := h.2.2.2.2.2.2.2.2.2
  have hInput := (groupLimit hp g hf hCta) t (ht.mono
    ⟨h.1, hFrame.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, trivial⟩)
  obtain ⟨u, hr, hu⟩ := hInput
  let keep := [7272, 7271, 7270, 1619, 7273, 7277] ++ fallbackFrameRegs
  obtain ⟨hRun, hSave⟩ := searchLinear (R := keep)
    (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hr
  have hRemain : Holds u.regs remaining := by
    apply holdsSchedulerFrame
      (show Holds t.regs remaining from
        ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
          h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, hFrame⟩) hSave
    intro x hx
    simp only [remaining, groupSchedulerFrame, List.cons_append, List.nil_append,
      List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hx
    all_goals first | exact of_decide_eq_true rfl | exact List.mem_append.mpr (.inr (hF x hx))
  exact ⟨u, hRun, hu.mono ⟨hu.2.2.2.2.1, hu.2.2.2.2.2.1, hRemain⟩⟩

private theorem searchLimitContinue {m : Mem0} (hp : Pre p l m) {g cta first lane : Nat}
    {F : List (Nat × Value)} {t : TState} (hFirst : first ≤ p.batch) (hCta : cta < 2 ^ 31)
    (hF : ∀ pair ∈ F, pair.1 ∈ fallbackFrameRegs)
    (ht : At t 7860 (searchTotalFacts p cta first lane F))
    (hLimit : tilePrefix p (min p.batch (first + 31)) * p.heads ≤ cta) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u 7810 (groupSearchFacts p cta first lane F) := by
  let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
  obtain ⟨u, hu, hU⟩ := searchLimitLane hp (g := warpLane l g lane) hFirst hCta
    hF ht
  have hPc : u.pc = 7810 := by
    have h := hU.1
    change u.pc = (if limit ≤ cta then 7810 else 7864) at h
    rw [ite_eq_left hLimit] at h
    exact h
  have h := hU.2.2.2.2
  refine ⟨u, run_rtg hu, ⟨hPc, hU.2.1, hU.2.2.1, hU.2.2.2.1, ?_⟩⟩
  exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2⟩
end

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g cta first shuffles votes : Nat}
    (hg : g < l.threads) (hCTA : cta < l.grid) (hFirst : first < p.batch)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ fallbackFrameRegs)
    (hBase : ∀ lane < 32, (7506, b64 p.cuQBase) ∈ F lane)
    (cur : SchedulerWarpAt l X g 7810 (fun lane => groupSearchFacts p cta first lane (F lane))
      shuffles votes ends) {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
include hp hX hg hCTA hFirst hF hBase cur hProgress

/-- Run one group of the fallback scheduler in the actual trace. The exhausted group skips
the collectives. A populated group performs one down shuffle, five up shuffles and its total
broadcast before carrying to the next group or selecting this group's request. -/
theorem searchGroupToRecorded (hPc : 7859 < target.pc) :
    let Follows := fun pos => WarpFollowsEvent l X g cur.pos src index target →
      WarpFollowsEvent l X g pos src index target
    let Bounded := fun pos => ∀ lane < 32, ∀ j a bytes, cur.pos lane ≤ j → j < pos lane →
      X.get (warpLane l g lane, j) = some ⟨7821, .rd a bytes⟩ →
      ∃ i ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4 * i), size := 4}
    (p.batch ≤ first + 31 ∧
      ∃ result : SchedulerWarpAt l X g 7864 (fun lane => exhaustedScheduleFacts p (F lane))
          shuffles votes ends, Follows result.pos ∧ Bounded result.pos) ∨
    (first + 31 < p.batch ∧
      ((tilePrefix p (min p.batch (first + 31 + 31)) * p.heads ≤ cta ∧
        ∃ result : SchedulerWarpAt l X g 7810
            (fun lane => groupSearchFacts p cta (first + 31) lane (F lane))
            (shuffles + 7) votes ends, Follows result.pos ∧ Bounded result.pos) ∨
      (cta < tilePrefix p (min p.batch (first + 31 + 31)) * p.heads ∧
        ∃ result : SchedulerWarpAt l X g 7864
          (fun lane => groupAvailableFacts p cta (first + 31) lane (F lane))
          (shuffles + 7) votes ends, Follows result.pos ∧ Bounded result.pos))) := by
  dsimp only
  have hStop : cta + 1 < 2 ^ 31 := by have := hp.grid.2.2; omega
  have hAdvance : ∃ result : SchedulerWarpAt l X g 7814
      (fun lane => groupAdvanced p cta first lane (F lane)) shuffles votes ends,
      result.pos = cur.pos := by
    apply cur.advanceLocalAt
    intro lane hl
    obtain ⟨u, hu, hU⟩ := advanceSearchGroup hp (g := warpLane l g lane) hFirst (hF lane hl)
      (cur.checkpoint lane hl)
    exact ⟨u, run_rtg hu, hU⟩
  obtain ⟨advanced, ha⟩ := hAdvance
  by_cases hClip : p.batch ≤ first + 31
  · obtain ⟨result, hResult, _⟩ := searchExhausted hStop hClip hF advanced
    refine .inl ⟨hClip, result, fun h => hResult.symm ▸ ha.symm ▸ h, ?_⟩
    intro lane _ j _ _ hLo hHi _
    rw [hResult,ha] at hHi
    omega
  have hGroup := Nat.lt_of_not_ge hClip
  have hBound := Nat.le_of_lt hGroup
  have followA : WarpFollowsEvent l X g cur.pos src index target →
      WarpFollowsEvent l X g advanced.pos src index target := fun h => ha.symm ▸ h
  obtain ⟨s0, hp0, hRead, h0⟩ := searchDownWarp hp hX hg hGroup hF hBase advanced
    (hProgress.imp_right followA) (by omega)
  have follow0 := h0 ∘ followA
  obtain ⟨s1, hp1, h1⟩ := searchScanStage hp hX hg hBound 0 hF s0 (hProgress.imp_right follow0)
    (by change 7844 < target.pc; omega)
  have follow1 := h1 ∘ follow0
  obtain ⟨s2, hp2, h2⟩ := searchScanStage hp hX hg hBound 1 hF s1 (hProgress.imp_right follow1)
    (by change 7847 < target.pc; omega)
  have follow2 := h2 ∘ follow1
  obtain ⟨s3, hp3, h3⟩ := searchScanStage hp hX hg hBound 2 hF s2 (hProgress.imp_right follow2)
    (by change 7850 < target.pc; omega)
  have follow3 := h3 ∘ follow2
  obtain ⟨s4, hp4, h4⟩ := searchScanStage hp hX hg hBound 3 hF s3 (hProgress.imp_right follow3)
    (by change 7853 < target.pc; omega)
  have follow4 := h4 ∘ follow3
  obtain ⟨s5, hp5, h5⟩ := searchScanStage hp hX hg hBound 4 hF s4 (hProgress.imp_right follow4)
    (by change 7856 < target.pc; omega)
  have follow5 := h5 ∘ follow4
  obtain ⟨total, hTotalPos, hTotalLen, hTotal⟩ :=
    searchTotalWarp hp hX hg hF s5 (hProgress.imp_right follow5) hPc
  have followTotal := hTotal ∘ follow5
  have hInterval (lane : Nat) (hl : lane < 32) (j : Nat) (a : Acc)
      (bytes : List (Option Byte)) (hLo : cur.pos lane ≤ j) (hHi : j < total.pos lane)
      (he : X.get (warpLane l g lane,j) = some ⟨7821,.rd a bytes⟩) :
      ∃ i ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4 * i), size := 4} := by
    let ix := first+31+lane
    let base := advanced.pos lane
    let afterRead := if ix ≤ p.batch then base+1 else base
    have hBase : base ≤ j := by dsimp only [base]; rwa [ha]
    have hLen : total.pos lane = afterRead+7 := by
      rw [hTotalPos,hp5,hp4,hp3,hp2,hp1,hp0]
    have hKeep : ((X.tr (warpLane l g lane)).take afterRead).countP Execution.isShfl =
        shuffles := by
      apply searchReadCount _ (advanced.ordinals.shfl lane hl) (fun _ _ => rfl)
      exact hRead lane hl
    by_cases hActual : j < afterRead
    · by_cases hIndex : ix ≤ p.batch
      · have hAt : j = base := by simp [afterRead,hIndex] at hActual; omega
        have hAtEvent := hAt ▸ he
        have hAcc := (Kind.rd.inj (congrArg Event.kind (Option.some.inj
          (hAtEvent.symm.trans (hRead lane hl hIndex))))).1
        exact ⟨ix,hIndex,hAcc⟩
      · simp [afterRead,hIndex] at hActual
        omega
    have hCount := total.ordinals.shfl lane hl
    have hCounts : ((X.tr (warpLane l g lane)).take (total.pos lane)).countP Execution.isShfl =
        ((X.tr (warpLane l g lane)).take afterRead).countP Execution.isShfl +
          (total.pos lane-afterRead) := by
      change ((X.tr (warpLane l g lane)).take (total.pos lane)).countP Execution.isShfl =
        shuffles+7 at hCount
      omega
    cases getIsShuffleBetween (hTotalLen lane hl) (Nat.le_of_not_gt hActual) hHi hCounts he
  let limit := tilePrefix p (min p.batch (first + 31 + 31)) * p.heads
  refine .inr ⟨hGroup, ?_⟩
  by_cases hLimit : limit ≤ cta
  · have hLocal : ∃ result : SchedulerWarpAt l X g 7810
        (fun lane => groupSearchFacts p cta (first + 31) lane (F lane)) (shuffles + 7) votes ends,
        result.pos = total.pos := by
      apply total.advanceLocalAt
      intro lane hl
      exact searchLimitContinue hp hBound (by omega) (hF lane hl)
        (total.checkpoint lane hl) hLimit
    obtain ⟨result, hResult⟩ := hLocal
    refine .inl ⟨hLimit, result, fun h => hResult.symm ▸ followTotal h, ?_⟩
    intro lane hl j a bytes hLo hHi he
    exact hInterval lane hl j a bytes hLo (hResult ▸ hHi) he
  · have hLocal : ∃ result : SchedulerWarpAt l X g 7864
        (fun lane => groupAvailableFacts p cta (first + 31) lane (F lane))
        (shuffles + 7) votes ends,
        result.pos = total.pos := by
      apply total.advanceLocalAt
      intro lane hl
      obtain ⟨u, hu, hU⟩ := searchLimitLane hp (g := warpLane l g lane) hBound (by omega)
        (hF lane hl) (total.checkpoint lane hl)
      have hPc : u.pc = 7864 := by
        have h := hU.1
        change u.pc = (if limit ≤ cta then 7810 else 7864) at h
        simpa only [ite_eq_right hLimit] using h
      have h := hU.2.2.2.2
      refine ⟨u, run_rtg hu, ⟨hPc, hU.2.1, hU.2.2.1, hU.2.2.2.1, ?_⟩⟩
      exact ⟨h.2.2.2.2.2.2.2.1, h.2.2.1, h.2.2.2.1, h.2.1,
        h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.1,
        h.2.2.2.2.2.2.2.2.2.2⟩
    obtain ⟨result, hResult⟩ := hLocal
    refine .inr ⟨Nat.lt_of_not_ge hLimit, result, fun h => hResult.symm ▸ followTotal h, ?_⟩
    intro lane hl j a bytes hLo hHi he
    exact hInterval lane hl j a bytes hLo (hResult ▸ hHi) he


theorem searchGroupTo (hPc : 7859 < target.pc) :
    let Follows := fun pos => WarpFollowsEvent l X g cur.pos src index target →
      WarpFollowsEvent l X g pos src index target
    (p.batch ≤ first + 31 ∧
      ∃ result : SchedulerWarpAt l X g 7864 (fun lane => exhaustedScheduleFacts p (F lane))
          shuffles votes ends, Follows result.pos) ∨
    (first + 31 < p.batch ∧
      ((tilePrefix p (min p.batch (first + 31 + 31)) * p.heads ≤ cta ∧
        ∃ result : SchedulerWarpAt l X g 7810
            (fun lane => groupSearchFacts p cta (first + 31) lane (F lane))
            (shuffles + 7) votes ends, Follows result.pos) ∨
      (cta < tilePrefix p (min p.batch (first + 31 + 31)) * p.heads ∧
        ∃ result : SchedulerWarpAt l X g 7864
          (fun lane => groupAvailableFacts p cta (first + 31) lane (F lane))
          (shuffles + 7) votes ends, Follows result.pos))) := by
  rcases searchGroupToRecorded hp hX hg hCTA hFirst hF hBase cur hProgress hPc with
    ⟨hClip, u, hFollow, _⟩ | ⟨hMore, ⟨hPast, u, hFollow, _⟩ | ⟨hWithin, u, hFollow, _⟩⟩
  · exact .inl ⟨hClip,u,hFollow⟩
  · exact .inr ⟨hMore,.inl ⟨hPast,u,hFollow⟩⟩
  · exact .inr ⟨hMore,.inr ⟨hWithin,u,hFollow⟩⟩
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

private theorem advanceSearchOfMaximal {g cta first shuffles votes : Nat} (hFirst : first < p.batch)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ fallbackFrameRegs)
    (cur : SchedulerWarpReached l X g 7810 (fun lane => groupSearchFacts p cta first lane (F lane))
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7814
      (fun lane => groupAdvanced p cta first lane (F lane)) shuffles votes ends) := by
  apply cur.advanceLocal
  intro lane hl
  obtain ⟨u,hu,hU⟩ := advanceSearchGroup hp (g := warpLane l g lane) hFirst (hF lane hl)
    (cur.checkpoint lane hl)
  exact ⟨u,run_rtg hu,hU⟩

/-- When a whole request list fits in the first scheduler group, its fallback is event-free. -/
theorem shortSearchExhausted {g shuffles votes : Nat} (hg : g < l.threads) (hShort : p.batch ≤ 31)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7807 (correctionFirstRouteFacts p l g) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7864
      (fun lane => exhaustedScheduleFacts p (fallbackFrame p l g lane)) shuffles votes ends) := by
  have hCta : g/l.block < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hStop : g/l.block + 1 < 2 ^ 31 := by have := hp.grid.2.2; omega
  obtain ⟨start, hPos, hState⟩ := startSearchPreserving hp hg (by omega) cur.toSchedulerWarpAt
  have ready := cur.reframe start hPos hState
  obtain ⟨advanced⟩ := advanceSearchOfMaximal hp hp.shape.1
    (fun _ _ => fallbackFrame_mem) ready
  obtain ⟨done, hPos', hState'⟩ := searchExhausted hStop hShort
    (fun _ _ => fallbackFrame_mem) advanced.toSchedulerWarpAt
  exact ⟨advanced.reframe done hPos' hState'⟩


private theorem nextGroupTotalOfMaximal (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads) (hMore : first + 31 < p.batch)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k)) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7810
      (fun lane => groupSearchFacts p (g / l.block) first lane (fallbackFrame p l g lane))
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7860
      (fun lane => searchTotalFacts p (g/l.block) (first+31) lane (fallbackFrame p l g lane))
      (shuffles + 7) votes ends) := by
  let F := fallbackFrame p l g
  have hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ fallbackFrameRegs :=
    fun _ _ => fallbackFrame_mem
  have hBase : ∀ lane < 32, (7506,b64 p.cuQBase) ∈ F lane := by
    intro lane _
    simp [F,fallbackFrame,firstShuffleFacts,afterCreditFacts,creditFacts,entryFacts,
      nonzeroBarrierFacts,abiFacts]
  obtain ⟨advanced⟩ := advanceSearchOfMaximal hp (by omega : first < p.batch) hF cur
  obtain ⟨r0⟩ := searchDownOfMaximal hp hMax hg hMore hF hBase hProtected advanced
  obtain ⟨r1⟩ := searchScanStageOfMaximal hp hMax hg hMore.le 0 hF r0
  obtain ⟨r2⟩ := searchScanStageOfMaximal hp hMax hg hMore.le 1 hF r1
  obtain ⟨r3⟩ := searchScanStageOfMaximal hp hMax hg hMore.le 2 hF r2
  obtain ⟨r4⟩ := searchScanStageOfMaximal hp hMax hg hMore.le 3 hF r3
  obtain ⟨r5⟩ := searchScanStageOfMaximal hp hMax hg hMore.le 4 hF r4
  exact searchTotalOfMaximal hp hMax hg hF r5

private theorem continueOfMaximal (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads) (hMore : first + 31 < p.batch)
    (hPast : tilePrefix p (min p.batch (first+31+31)) * p.heads ≤ g/l.block)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k)) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7810
      (fun lane => groupSearchFacts p (g / l.block) first lane (fallbackFrame p l g lane))
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7810
      (fun lane => groupSearchFacts p (g / l.block) (first + 31) lane (fallbackFrame p l g lane))
      (shuffles + 7) votes ends) := by
  let cta := g / l.block
  have hgCta : cta < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hCta : cta < 2 ^ 31 := hgCta.trans hp.grid.2.2
  let F := fallbackFrame p l g
  have hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ fallbackFrameRegs :=
    fun _ _ => fallbackFrame_mem
  obtain ⟨total⟩ := nextGroupTotalOfMaximal hp hMax hg hMore hProtected cur
  apply total.advanceLocal
  intro lane hl
  exact searchLimitContinue hp hMore.le hCta (hF lane hl) (total.checkpoint lane hl) hPast

private theorem selectGroupOfMaximal (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads) (hMore : first + 31 < p.batch)
    (hWithin : g/l.block < tilePrefix p (min p.batch (first+31+31)) * p.heads)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k)) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7810
      (fun lane => groupSearchFacts p (g/l.block) first lane (fallbackFrame p l g lane))
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7864
      (fun lane => groupAvailableFacts p (g/l.block) (first+31) lane (fallbackFrame p l g lane))
      (shuffles + 7) votes ends) := by
  let cta := g/l.block
  have hCta : cta < 2 ^ 31 :=
    ((Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg).trans hp.grid.2.2
  let F := fallbackFrame p l g
  have hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ fallbackFrameRegs :=
    fun _ _ => fallbackFrame_mem
  obtain ⟨total⟩ := nextGroupTotalOfMaximal hp hMax hg hMore hProtected cur
  apply total.advanceLocal
  intro lane hl
  obtain ⟨u,hu,hU⟩ := searchLimitLane hp hMore.le hCta (hF lane hl) (total.checkpoint lane hl)
  have hPc : u.pc = 7864 := by
    have h := hU.1
    change u.pc = (if tilePrefix p (min p.batch (first+31+31)) * p.heads ≤ g/l.block
      then 7810 else 7864) at h
    simpa only [ite_eq_right (Nat.not_le_of_lt hWithin)] using h
  have h := hU.2.2.2.2
  refine ⟨u,run_rtg hu,⟨hPc,hU.2.1,hU.2.2.1,hU.2.2.2.1,?_⟩⟩
  exact ⟨h.2.2.2.2.2.2.2.1, h.2.2.1, h.2.2.2.1, h.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2⟩

omit hp in
/-- Active correction fallback consumes the real exchanges through its containing group. -/
theorem activeSearchOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes : Nat}
    (hg : g < l.threads) (hWork : g/l.block < tilePrefix p p.batch * p.heads)
    (hPast : tilePrefix p (min p.batch 31) * p.heads ≤ g/l.block)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k)) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7807 (correctionFirstRouteFacts p l g) shuffles votes ends) :
    ∃ first count, tilePrefix p first * p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (min p.batch (first+31)) * p.heads ∧
      Nonempty (SchedulerWarpReached l X g 7864
        (fun lane => groupAvailableFacts p (g/l.block) first lane (fallbackFrame p l g lane))
        count votes ends) := by
  let cta := g/l.block
  have hCta : cta < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hStop : cta+1 < 2 ^ 31 := by have := hp.grid.2.2; omega
  obtain ⟨start,hPos,hBefore⟩ := startSearchPreserving hp hg (by omega) cur.toSchedulerWarpAt
  let rec reached (first count : Nat) (hPast : tilePrefix p (min p.batch (first+31))*p.heads ≤ cta)
      (c : SchedulerWarpReached l X g 7810
        (fun lane => groupSearchFacts p cta first lane (fallbackFrame p l g lane))
        count votes ends) :
      ∃ selected n, tilePrefix p selected*p.heads ≤ cta ∧
        cta < tilePrefix p (min p.batch (selected+31))*p.heads ∧
        Nonempty (SchedulerWarpReached l X g 7864
          (fun lane => groupAvailableFacts p cta selected lane (fallbackFrame p l g lane))
          n votes ends) := by
    have hMore : first+31 < p.batch := by
      by_contra! h
      rw [Nat.min_eq_left h] at hPast
      exact (Nat.not_le_of_lt hWork) hPast
    by_cases hContinue : tilePrefix p (min p.batch (first+31+31))*p.heads ≤ cta
    · obtain ⟨again⟩ := continueOfMaximal hp hMax hg hMore hContinue hProtected c
      exact reached (first+31) (count+7) hContinue again
    · exact ⟨first+31,count+7,(Nat.min_eq_right hMore.le) ▸ hPast,
        Nat.lt_of_not_ge hContinue,
        selectGroupOfMaximal hp hMax hg hMore (Nat.lt_of_not_ge hContinue) hProtected c⟩
    termination_by p.batch - first
    decreasing_by omega
  exact reached 0 shuffles hPast (cur.reframe start hPos hBefore)


/-- Idle correction skips all request groups in the actual maximal execution. -/
theorem idleSearchExhaustedOfMaximal (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads)
    (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k)) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7807 (correctionFirstRouteFacts p l g) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7864
      (fun lane => exhaustedScheduleFacts p (fallbackFrame p l g lane))
      (shuffles + 7 * ((p.batch - 1) / 31)) votes ends) := by
  let cta := g / l.block
  let F := fallbackFrame p l g
  have hgCta : cta < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hStop : cta + 1 < 2 ^ 31 := by have := hp.grid.2.2; omega
  obtain ⟨start,hPos,hBefore⟩ := startSearchPreserving hp hg (by omega) cur.toSchedulerWarpAt
  let first := cur.reframe start hPos hBefore
  have reached (n : Nat) (hn : 31 * n < p.batch) :
      Nonempty (SchedulerWarpReached l X g 7810
        (fun lane => groupSearchFacts p cta (31 * n) lane (F lane))
        (shuffles + 7 * n) votes ends) := by
    induction n with
    | zero => exact ⟨first⟩
    | succ n ih =>
      obtain ⟨prev⟩ := ih (by omega)
      simpa only [show 31 * n + 31 = 31 * n.succ by omega,
        show shuffles + 7 * n + 7 = shuffles + 7 * n.succ by omega] using
        continueOfMaximal hp hMax hg (first := 31 * n) (by omega)
          ((Nat.mul_le_mul_right _ (tilePrefix_mono p (Nat.min_le_left ..))).trans hIdle)
          hProtected prev
  let n := (p.batch - 1) / 31
  have hDiv := Nat.div_add_mod (p.batch - 1) 31
  have hMod := Nat.mod_lt (p.batch - 1) (show 0 < 31 by decide)
  have hpPos := hp.shape.1
  have hFirst : 31 * n < p.batch := by dsimp [n]; omega
  have hClip : p.batch ≤ 31 * n + 31 := by dsimp [n]; omega
  obtain ⟨last⟩ := reached n hFirst
  have hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ fallbackFrameRegs :=
    fun _ _ => fallbackFrame_mem
  obtain ⟨advanced⟩ := advanceSearchOfMaximal hp hFirst hF last
  obtain ⟨done,hPos,hBefore⟩ := searchExhausted hStop hClip hF advanced.toSchedulerWarpAt
  exact ⟨advanced.reframe done hPos hBefore⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction.Fallback
