-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress

public import Kernels.TmlFa4Fwd.Proof.EpilogueGroupRoute
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuQReadBytes
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainEntry
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Lemmas.Step.ProtectedReadProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

private theorem searchModel {l : Launch} {g : Nat} {t : TState}
    (hlo : 2824 ≤ t.pc) (hhi : t.pc < 2883) :
    out kernel Assumptions.all l g t = out kernel [] l g t :=
  epilogue_out_all_eq_nil (.inl ⟨by omega, by omega⟩)

private theorem searchLinear {l : Launch} {g lo n : Nat} {t u : TState}
    {R : List Nat}
    (hLo : 2824 ≤ lo) (hHi : lo + n ≤ 2883) (hpc : t.pc = lo)
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

private def searchCarry (p : Params) (cta first base lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  [(1203, b32 (cta + 1)), (7223, b32 first), (7218, b32 base), (7228, b32 p.batch),
    (1201, b32 lane), (1072, b32 cta)] ++ groupSchedulerFrame p lane F

private def searchCarryRegs : List Nat := [1203, 7223, 7218, 7228] ++ schedulerFrameRegs

private theorem searchCarry_mem {p : Params} {cta first base lane : Nat}
    {F : List (Nat × Value)} (hF : ∀ x ∈ F, x.1 ∈ schedulerFrameRegs) :
    ∀ x ∈ searchCarry p cta first base lane F, x.1 ∈ searchCarryRegs := by
  intro x hx
  simp only [searchCarry, groupSchedulerFrame, List.cons_append, List.nil_append,
    List.mem_cons] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hx <;>
    first | exact List.mem_append.mpr (.inr (hF x hx)) | simp [searchCarryRegs, schedulerFrameRegs]

private def groupAdvanced (p : Params) (cta first lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  [(1204, b32 (first + 31)), (278, .pred (decide (p.batch ≤ first + 31))),
    (7224, b32 (cta + 1))] ++
  searchCarry p cta (min (first + 31) p.batch)
    (tilePrefix p (min p.batch (first + 31)) * p.heads) lane F

section
variable {p : Params} {l : Launch}

private theorem advanceSearchGroup {m : Mem0} (hp : Pre p l m) {g cta first lane : Nat} {t : TState}
    {F : List (Nat × Value)} (hf : first < p.batch) (hF : ∀ x ∈ F, x.1 ∈ schedulerFrameRegs)
    (ht : At t 2824 (groupSearchFacts p cta first lane F)) :
    ∃ u, run kernel Assumptions.all l g 4 t = some u ∧
      At u 2828 (groupAdvanced p cta first lane F) := by
  have hReg := ht.2.2.2.2
  have hAt : At t 2824 [(7223, b32 first), (7228, b32 p.batch), (1203, b32 (cta + 1))] :=
    ht.mono ⟨hReg.2.1, hReg.2.2.2.1, hReg.1, trivial⟩
  obtain ⟨u, hr, hu⟩ := (advanceGroup_of_pre hp g hf).2.2 t hAt
  obtain ⟨hRun, hFrame⟩ := searchLinear (R := [1203, 7218, 7228] ++ schedulerFrameRegs)
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
    ⟨(hFrame 1203 (by decide)).trans hReg.1, hu.2.2.2.2.2.2.1,
      (hFrame 7218 (by decide)).trans hReg.2.2.1,
      (hFrame 7228 (by decide)).trans hReg.2.2.2.1,
      (hFrame 1201 (by decide)).trans hReg.2.2.2.2.1,
      (hFrame 1072 (by decide)).trans hReg.2.2.2.2.2.1, hTail⟩
  have hNew := hu.2.2.2.2
  exact ⟨u, hRun, hu.mono ⟨hNew.1, hNew.2.1, hNew.2.2.2.1, hSaved⟩⟩

private theorem branchSearchGroup {g cta first lane : Nat} {F : List (Nat × Value)} {t : TState}
    (ht : At t 2828 (groupAdvanced p cta first lane F)) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u (if p.batch ≤ first + 31 then 2875 else 2829) (groupAdvanced p cta first lane F) := by
  obtain ⟨u, hr, hu⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2828 _ ht ht.2.2.2.2.2.1 (by simp)
  obtain ⟨hRun, _⟩ := searchLinear (R := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hr
  exact ⟨u, hRun, by simpa only [decide_eq_true_eq] using hu⟩

private def groupLaneFacts (p : Params) (cta first lane : Nat) (F : List (Nat × Value))
    (word : Value) : List (Nat × Value) :=
  [(1205, b32 (first + 31 + lane)), (7219, word)] ++
    searchCarry p cta (first + 31) (tilePrefix p (first + 31) * p.heads) lane F

private theorem searchLaneGate {m : Mem0} (hp : Pre p l m) {g cta first lane : Nat}
    {F : List (Nat × Value)} {t : TState} (hGroup : first + 31 < p.batch) (hl : lane < 32)
    (hF : ∀ x ∈ F, x.1 ∈ schedulerFrameRegs) (ht : At t 2829 (groupAdvanced p cta first lane F)) :
    ∃ u, run kernel Assumptions.all l g 3 t = some u ∧
      At u 2832 ((279, .pred (decide (p.batch < first + 31 + lane))) ::
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
  have hArgs : At t 2829 [(1204, b32 (first + 31)), (1201, b32 lane), (7228, b32 p.batch)] :=
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

private theorem searchLaneRead {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g j cta first lane : Nat} {F : List (Nat × Value)} {before t : TState} {o : Option TState}
    (hF : ∀ x ∈ F, x.1 ∈ schedulerFrameRegs) (hBase : (7506, b64 p.cuQBase) ∈ F)
    (ht : At t 2832 ((279, .pred (decide (p.batch < first + 31 + lane))) ::
      groupLaneFacts p cta first lane F (b32 0)))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before t)
    (hRun : Run kernel Assumptions.all l g before ((X.tr g).drop j) o)
    (hNonempty : first + 31 + lane ≤ p.batch → (X.tr g).drop j ≠ [])
    (hReads : first + 31 + lane ≤ p.batch →
      CuQWordReadsFromLaunchOnThread p X g (first + 31 + lane)) :
    let index := first + 31 + lane
    let word := b32 (drainCuQ p index)
    ∃ v u, At u 2836 (groupLaneFacts p cta first lane F word) ∧
      (index ≤ p.batch → X.get (g, j) = some ⟨2835, .rd (searchReadAcc p index)
        (word.toBytes.map some)⟩) ∧
      Run kernel Assumptions.all l g v
        ((X.tr g).drop (if index ≤ p.batch then j + 1 else j)) o ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) v u := by
  dsimp only
  let index := first + 31 + lane
  let word := b32 (drainCuQ p index)
  let carry := searchCarry p cta (first + 31) (tilePrefix p (first + 31) * p.heads) lane F
  obtain ⟨v, hr, hv⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2832 _ ht ht.2.2.2.2.1 (by simp)
  obtain ⟨hrA, _⟩ := searchLinear (R := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hr
  have hApproach := hLocal.trans (run_rtg hrA)
  by_cases h : index ≤ p.batch
  · have hvPC : v.pc = 2833 := by simpa [index, Nat.not_lt_of_ge h] using hv.1
    have hc : Holds v.regs carry := hv.2.2.2.2.2.2.2
    have hIndex : v.regs 1205 = some (b32 index) := hv.2.2.2.2.2.1
    have hAt : At v 2833 [(1205, b32 index), (7506, b64 p.cuQBase)] :=
      ⟨hvPC, hv.2.1, hv.2.2.1, hv.2.2.2.1, hIndex,
        holds_mem hc (by simp [carry, searchCarry, groupSchedulerFrame, hBase]), trivial⟩
    obtain ⟨a, ha, hA⟩ := groupLaneAddress hp g h v hAt
    obtain ⟨haA, hFrame⟩ := searchLinear (R := 1205 :: searchCarryRegs)
      (by decide) (by decide) hAt.1
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) ha
    let acc := searchReadAcc p index
    have hOut : out kernel Assumptions.all l g a = .ev (.read acc (afterLoad a [7219])) :=
      (searchModel (by have := hA.1; omega) (by have := hA.1; omega)).trans
        (groupLaneRead hp g a h hA)
    have hn : Next kernel Assumptions.all l g before a (.read acc (afterLoad a [7219])) :=
      ⟨hApproach.trans (run_rtg haA), hOut⟩
    obtain ⟨e, u, hGet, ⟨bs, _, rfl, hu⟩, hTail⟩ := hn.continuing_at_nonempty (by
      rintro _ ⟨_, _, _, hBad⟩; cases hBad) hRun (hNonempty h)
    obtain rfl := Option.some.inj hu
    rw [hA.1] at hGet
    have hBytes : bs = word.toBytes.map some := by
      simpa only [word, drainCuQ, ite_eq_left h] using hReads h j bs ⟨2835, hGet⟩
    subst bs
    have hRead := rebuild_scalar (v := word) (show 0 < 4 by decide) rfl
    have hState : afterLoad a [7219] (word.toBytes.map some) = next (setReg a 7219 word) := by
      rw [afterLoad_ok hA.2.1 hA.2.2.1 hRead]
      simp [next, setReg, hA.2.1, hA.2.2.1]
    rw [hState] at hTail
    have hKeep := holdsSchedulerFrame hc hFrame (fun pair hp' =>
      List.mem_cons_of_mem _ (searchCarry_mem hF pair hp'))
    have hAtA : At a 2835 ((1205, b32 index) :: carry) :=
      hA.mono ⟨(hFrame _ (by simp)).trans hIndex, hKeep⟩
    have hFresh : ∀ pair ∈ ((1205, b32 index) :: carry), pair.1 ≠ 7219 := by
      intro pair hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact of_decide_eq_true rfl
      · exact fun heq => (of_decide_eq_true rfl : 7219 ∉ searchCarryRegs)
          (heq ▸ searchCarry_mem hF pair hm)
    have hU := hAtA.set (v := word) hFresh
    refine ⟨next (setReg a 7219 word), next (setReg a 7219 word), hU.mono ?_,
      fun _ => hGet, ?_, .refl⟩
    · exact ⟨hU.2.2.2.2.2.1, hU.2.2.2.2.1, hU.2.2.2.2.2.2⟩
    · simpa only [ite_eq_left (show first + 31 + lane ≤ p.batch from h)] using hTail
  · have hvPC : v.pc = 2836 := by simpa [index, Nat.lt_of_not_ge h] using hv.1
    have hWord : word = b32 0 := by simp [word, drainCuQ, h]
    have hvFacts : At v 2836 (groupLaneFacts p cta first lane F word) :=
      ⟨hvPC, hv.2.1, hv.2.2.1, hv.2.2.2.1, by simpa only [hWord] using hv.2.2.2.2.2⟩
    exact ⟨before, v, hvFacts, fun h' => (h h').elim, by
      simpa only [show ¬ first + 31 + lane ≤ p.batch from h, ite_false] using hRun, hApproach⟩

private theorem searchLaneReadReached {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g j cta first lane : Nat} (hg : g < l.threads)
    {F : List (Nat × Value)} {before t : TState} {o : Option TState}
    (hF : ∀ x ∈ F, x.1 ∈ schedulerFrameRegs) (hBase : (7506, b64 p.cuQBase) ∈ F)
    (ht : At t 2832 ((279, .pred (decide (p.batch < first + 31 + lane))) ::
      groupLaneFacts p cta first lane F (b32 0)))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before t)
    (hRun : Run kernel Assumptions.all l g before ((X.tr g).drop j) o) (hPos : 0 < j)
    (hBound : j ≤ (X.tr g).length) (hReleased : j = (X.tr g).length → Step.Released l X g)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take j) (some before))
    (hProtect : DrainCuQProtected p X) :
    let index := first + 31 + lane
    let pos := if index ≤ p.batch then j + 1 else j
    ∃ v u, At u 2836 (groupLaneFacts p cta first lane F (b32 (drainCuQ p index))) ∧
      pos ≤ (X.tr g).length ∧
      (pos = (X.tr g).length → Step.Released l X g) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some v) ∧
      Run kernel Assumptions.all l g v ((X.tr g).drop pos) o ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) v u ∧
      (index ≤ p.batch → X.get (g, j) = some ⟨2835, .rd (searchReadAcc p index)
        ((b32 (drainCuQ p index)).toBytes.map some)⟩) := by
  dsimp only
  let index := first + 31 + lane
  let word := b32 (drainCuQ p index)
  let carry := searchCarry p cta (first + 31) (tilePrefix p (first + 31) * p.heads) lane F
  obtain ⟨v, hr, hv⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2832 _ ht ht.2.2.2.2.1 (by simp)
  obtain ⟨hrA, _⟩ := searchLinear (R := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hr
  have hApproach := hLocal.trans (run_rtg hrA)
  by_cases h : index ≤ p.batch
  · have hvPC : v.pc = 2833 := by simpa [index, Nat.not_lt_of_ge h] using hv.1
    have hc : Holds v.regs carry := hv.2.2.2.2.2.2.2
    have hIndex : v.regs 1205 = some (b32 index) := hv.2.2.2.2.2.1
    have hAt : At v 2833 [(1205, b32 index), (7506, b64 p.cuQBase)] :=
      ⟨hvPC, hv.2.1, hv.2.2.1, hv.2.2.2.1, hIndex,
        holds_mem hc (by simp [carry, searchCarry, groupSchedulerFrame, hBase]), trivial⟩
    obtain ⟨a, ha, hA⟩ := groupLaneAddress hp g h v hAt
    obtain ⟨haA, hFrame⟩ := searchLinear (R := 1205 :: searchCarryRegs)
      (by decide) (by decide) hAt.1
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) ha
    let acc := searchReadAcc p index
    have hOut : out kernel Assumptions.all l g a = .ev (.read acc (afterLoad a [7219])) :=
      (searchModel (by have := hA.1; omega) (by have := hA.1; omega)).trans
        (groupLaneRead hp g a h hA)
    have hn : Next kernel Assumptions.all l g before a (.read acc (afterLoad a [7219])) :=
      ⟨hApproach.trans (run_rtg haA), hOut⟩
    have hValue : word = b32 (p.qOffset index) := by simp [word, drainCuQ, h]
    have hInit : HasValue m acc.loc word := by rw [hValue]; exact hp.cuQ index h
    obtain ⟨hGet, hRecorded, hTail⟩ := Step.protected_read_of_maximal hMax hg
      (a := acc) (value := word) rfl hInit (hProtect index h) hn hPrefix hRun hPos hBound
      hReleased (Assumptions.wf_snoc_initial hMax.1)
    have hRead := rebuild_scalar (v := word) (show 0 < 4 by decide) rfl
    have hState : afterLoad a [7219] (word.toBytes.map some) = next (setReg a 7219 word) := by
      rw [afterLoad_ok hA.2.1 hA.2.2.1 hRead]
      simp [next, setReg, hA.2.1, hA.2.2.1]
    rw [hState] at hRecorded hTail
    have hKeep := holdsSchedulerFrame hc hFrame (fun pair hp' =>
      List.mem_cons_of_mem _ (searchCarry_mem hF pair hp'))
    have hAtA : At a 2835 ((1205, b32 index) :: carry) :=
      hA.mono ⟨(hFrame _ (by simp)).trans hIndex, hKeep⟩
    have hFresh : ∀ pair ∈ ((1205, b32 index) :: carry), pair.1 ≠ 7219 := by
      intro pair hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact of_decide_eq_true rfl
      · exact fun heq => (of_decide_eq_true rfl : 7219 ∉ searchCarryRegs)
          (heq ▸ searchCarry_mem hF pair hm)
    have hU := hAtA.set (v := word) hFresh
    refine ⟨next (setReg a 7219 word), next (setReg a 7219 word), hU.mono ?_,
      ?_, ?_, ?_, ?_, .refl, ?_⟩
    · exact ⟨hU.2.2.2.2.2.1, hU.2.2.2.2.1, hU.2.2.2.2.2.2⟩
    · simp only [index] at h
      simpa only [ite_eq_left h] using Nat.succ_le_of_lt (len_of_get hGet)
    · simp only [index] at h
      simpa only [ite_eq_left h] using Prologue.releasedIfLast hGet (by intro he; cases he)
    · simp only [index] at h
      simpa only [ite_eq_left h] using hRecorded
    · simp only [index] at h
      simpa only [ite_eq_left h] using hTail
    · intro _
      exact hA.1 ▸ hGet
  · have hvPC : v.pc = 2836 := by simpa [index, Nat.lt_of_not_ge h] using hv.1
    have hWord : word = b32 0 := by simp [word, drainCuQ, h]
    have hvFacts : At v 2836 (groupLaneFacts p cta first lane F word) :=
      ⟨hvPC, hv.2.1, hv.2.2.1, hv.2.2.2.1, by simpa only [hWord] using hv.2.2.2.2.2⟩
    rw [ite_eq_right (show ¬ first + 31 + lane ≤ p.batch from h)]
    exact ⟨before, v, hvFacts, hBound, hReleased, hPrefix, hRun, hApproach, fun hx => (h hx).elim⟩


private theorem searchLastLane {g cta first lane : Nat} {F : List (Nat × Value)} {t : TState}
    {word : Value} (hl : lane < 32) (hF : ∀ x ∈ F, x.1 ∈ schedulerFrameRegs)
    (ht : At t 2836 (groupLaneFacts p cta first lane F word)) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u 2837 ((280, .pred (decide (lane = 31))) :: groupLaneFacts p cta first lane F word) := by
  have hAt : At t 2836 [(1201, b32 lane)] := ht.mono
    ⟨holds_mem ht.2.2.2.2 (by simp [groupLaneFacts, searchCarry]), trivial⟩
  obtain ⟨u, hr, hu⟩ := groupLastLaneCheck l g hl t hAt
  obtain ⟨hRun, hFrame⟩ := searchLinear (R := [1205, 7219] ++ searchCarryRegs)
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
  [(286, .pred (decide (16 ≤ lane))), (287, .pred (decide (8 ≤ lane))),
    (288, .pred (decide (4 ≤ lane))), (289, .pred (decide (2 ≤ lane))),
    (290, .pred (decide (lane = 0)))]

private def searchScanCarry (p : Params) (cta first lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  searchGuards lane ++ (7220, b32 (groupLaneTiles p first lane)) ::
    searchCarry p cta first (tilePrefix p first * p.heads) lane F

private def searchScanRegs : List Nat := [286, 287, 288, 289, 290, 7220] ++ searchCarryRegs

private theorem searchScan_mem {p : Params} {cta first lane : Nat} {F : List (Nat × Value)}
    (hF : ∀ x ∈ F, x.1 ∈ schedulerFrameRegs) :
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
    (hF : ∀ x ∈ F, x.1 ∈ schedulerFrameRegs)
    (ht : At t 2838 ((2329, b32 (drainCuQ p (first + 31 + (shflSource .down lane 1 31).1))) ::
      (280, .pred (decide (lane = 31))) :: groupLaneFacts p cta first lane F
        (b32 (drainCuQ p (first + 31 + lane))))) :
    ∃ n u, run kernel Assumptions.all l g n t = some u ∧
      At u 2858 (searchUpFacts p cta (first + 31) lane F 0) := by
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
  have hArgs : At t 2838 [(7219, b32 begin), (2329, b32 finish), (1205, b32 index),
      (7228, b32 p.batch), (280, .pred (decide (lane = 31)))] := ht.mono
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
  have hTileArgs : At v 2842 [(282, .pred (!eligible)), (1206, b32 len), (7220, b32 0)] :=
    hv.mono ⟨hv.2.2.2.2.2.2.1, by simpa [b32, len, delta] using hv.2.2.2.2.1,
      hv.2.2.2.2.2.1, trivial⟩
  obtain ⟨w, hw, hW⟩ := groupTileContribution l g eligible len
    (fun he => hLen he ▸ hDiff) v hTileArgs
  obtain ⟨z, hz, hZ⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2842 (!eligible) hTileArgs hTileArgs.2.2.2.2.1 (by simp)
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
      have hzPC : z.pc = 2843 := by simpa [he] using hZ.1
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
  have hWord : w.regs 7220 = some (b32 (groupLaneTiles p nextGroup lane)) :=
    congrArg (fun n => some (b32 n)) hValue ▸ hW.2.2.2.2.1
  have hGuardAt : At w 2853 [(1201, b32 lane), (7220, b32 (groupLaneTiles p nextGroup lane))] :=
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

private theorem searchUpBounds (stage : Fin 5) :
    2824 ≤ groupScanPc stage ∧ groupScanPc stage + 3 ≤ 2883 := by
  have := stage.isLt
  simp [groupScanPc]
  omega

private theorem searchUpArgs {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g cta first shuffles votes : Nat} (stage : Fin 5) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ schedulerFrameRegs)
    (cur : SchedulerWarpAt l X g (groupScanPc stage)
      (fun lane => searchUpFacts p cta first lane (F lane) stage) shuffles votes ends) :
    (∀ lane < 32, ∀ pair ∈ searchUpFacts p cta first lane (F lane) stage,
      pair.1 ≠ groupScanDst stage) ∧
    (∀ lane < 32, out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
      .ev (.shfl .up (b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val) lane))
        (2 ^ stage.val) 0 (fun v _ => next (setReg (cur.state lane) (groupScanDst stage) v)))) := by
  let xs := groupLaneTiles p first
  let a := fun lane => b32 (prefixWindow xs (2 ^ stage.val) lane)
  have hBounds := searchUpBounds stage
  have hFresh : ∀ lane < 32, ∀ pair ∈ searchUpFacts p cta first lane (F lane) stage,
      pair.1 ≠ groupScanDst stage := by
    intro lane hl x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · fin_cases stage <;> exact of_decide_eq_true rfl
    · have hn : groupScanDst stage ∉ searchScanRegs := by fin_cases stage <;> decide
      exact fun e => hn (e ▸ searchScan_mem (hF lane hl) x hx)
  have hOut (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
        .ev (.shfl .up (a lane) (2 ^ stage.val) 0
          (fun v _ => next (setReg (cur.state lane) (groupScanDst stage) v))) := by
    have ht := cur.checkpoint lane hl
    exact (searchModel (by rw [ht.1]; omega) (by rw [ht.1]; omega)).trans
      (groupScanTemplate hp _ _ stage _ ht.1 ht.2.2.2.1 ht.2.2.2.2.1)
  exact ⟨hFresh, hOut⟩

private theorem searchUpFinish {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g cta first shuffles votes : Nat} (hf : first ≤ p.batch) (stage : Fin 5)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ schedulerFrameRegs)
    (mid : SchedulerWarpAt l X g (groupScanPc stage + 1)
      (fun lane => (groupScanDst stage,
          b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val)
            (shflSource .up lane (2 ^ stage.val) 0).1)) ::
        searchUpFacts p cta first lane (F lane) stage) shuffles votes ends) (lane : Nat)
    (hl : lane < 32) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane))
      (mid.state lane) u ∧ At u (groupScanPc stage + 3)
        (searchUpResult p cta first lane (F lane) stage) := by
  let xs := groupLaneTiles p first
  let a := fun lane => b32 (prefixWindow xs (2 ^ stage.val) lane)
  have hBounds := searchUpBounds stage
  have ht := mid.checkpoint lane hl
  have hCarry : Holds (mid.state lane).regs (searchScanCarry p cta first lane (F lane)) :=
    ht.2.2.2.2.2.2
  have hGuard : (mid.state lane).regs (290 - stage.val) =
      some (.pred (groupScanGuard stage lane)) := by
    apply holds_mem hCarry
    fin_cases stage <;> simp [searchScanCarry, searchGuards, groupScanGuard]
  have hAt : At (mid.state lane) (groupScanPc stage + 1)
      [(290 - stage.val, .pred (groupScanGuard stage lane)),
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
    (mid.state lane) hAt
  obtain ⟨hRun, hFrame⟩ := searchLinear (R := searchScanRegs)
    (by omega) (by omega) hAt.1
    (by fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl)
    (by fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl) hr
  exact ⟨u, run_rtg hRun, hu.mono
    ⟨hu.2.2.2.2.1, holdsSchedulerFrame hCarry hFrame (searchScan_mem (hF lane hl))⟩⟩

/-- CuQ lookups in this trace interval address launch words. -/
def SearchReadRange (p : Params) (l : Launch) (X : Execution) (g : Nat)
    (first last : Nat → Nat) : Prop :=
  ∀ lane < 32, ∀ j, first lane ≤ j → j < last lane → ∀ a bytes,
    X.get (warpLane l g lane,j) = some ⟨2835,.rd a bytes⟩ →
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase+4*index), size := 4}

private theorem searchReadRangeEmpty {p l X g first last} (h : last = first) :
    SearchReadRange p l X g first last := by
  subst last
  intro lane hl j hLo hHi
  omega

private theorem searchReadRangeAppend {p l X g a b c}
    (ab : SearchReadRange p l X g a b) (bc : SearchReadRange p l X g b c) :
    SearchReadRange p l X g a c := by
  intro lane hl j hLo hHi x bytes he
  by_cases hb : j < b lane
  · exact ab lane hl j hLo hb x bytes he
  · exact bc lane hl j (Nat.le_of_not_gt hb) hHi x bytes he

private theorem searchReadRangeShuffle {p l X g first last pc mode}
    {a : Nat → Value} {b c : Nat → Nat}
    (hPos : last = fun lane => first lane + 1)
    (hShuffle : ∀ lane < 32, ∃ recv ok, X.get (warpLane l g lane, first lane) =
      some ⟨pc,.shfl mode (a lane) (b lane) (c lane) recv ok⟩) :
    SearchReadRange p l X g first last := by
  subst last
  intro lane hl j hLo hHi x bytes he
  have hEq : j = first lane := by dsimp only at hHi; omega
  subst j
  obtain ⟨_,_,hEvent⟩ := hShuffle lane hl
  cases congrArg Event.kind (Option.some.inj (hEvent.symm.trans he))

private theorem searchScanStage {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g cta first shuffles votes : Nat}
    (hg : g < l.threads) (hf : first ≤ p.batch) (stage : Fin 5) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ schedulerFrameRegs)
    (cur : SchedulerWarpAt l X g (groupScanPc stage)
      (fun lane => searchUpFacts p cta first lane (F lane) stage) shuffles votes ends)
    {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : groupScanPc stage < target.pc) :
    ∃ result : SchedulerWarpAt l X g (groupScanPc stage + 3)
        (fun lane => searchUpResult p cta first lane (F lane) stage) (shuffles + 1) votes ends,
      SearchReadRange p l X g cur.pos result.pos ∧
      (WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g result.pos src index target) := by
  let a := fun lane => b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val) lane)
  obtain ⟨hFresh, hOut⟩ := searchUpArgs hp stage hF cur
  obtain ⟨mid, hPos, hShuffle, hMid⟩ := cur.consumeShuffleToRecorded hp hX hg .up a
    (fun _ => 2 ^ stage.val) (fun _ => 0) hFresh hOut hProgress hPc
  have hLocal : ∃ result : SchedulerWarpAt l X g (groupScanPc stage + 3)
      (fun lane => searchUpResult p cta first lane (F lane) stage) (shuffles + 1) votes ends,
      result.pos = mid.pos := by
    apply mid.advanceLocalAt
    intro lane hl
    exact searchUpFinish hp hf stage hF mid lane hl

  obtain ⟨result, hResult⟩ := hLocal
  exact ⟨result, hResult.symm ▸ searchReadRangeShuffle hPos hShuffle,
    fun h => hResult.symm ▸ hMid h⟩

private theorem searchScanStageReached {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g cta first shuffles votes : Nat}
    (hg : g < l.threads) (hf : first ≤ p.batch) (stage : Fin 5) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ schedulerFrameRegs)
    (cur : SchedulerWarpReached l X g (groupScanPc stage)
      (fun lane => searchUpFacts p cta first lane (F lane) stage) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g (groupScanPc stage + 3)
      (fun lane => searchUpResult p cta first lane (F lane) stage) (shuffles + 1) votes ends) := by
  let a := fun lane => b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val) lane)
  obtain ⟨hFresh, hOut⟩ := searchUpArgs hp stage hF cur.toSchedulerWarpAt
  obtain ⟨mid⟩ := cur.consumeShuffle hp hMax hg .up a (fun _ => 2 ^ stage.val) (fun _ => 0)
    hFresh hOut
  apply mid.advanceLocal
  intro lane hl
  exact searchUpFinish hp hf stage hF mid.toSchedulerWarpAt lane hl

private theorem searchDownWarp {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g cta first shuffles votes : Nat}
    (hg : g < l.threads) (hGroup : first + 31 < p.batch) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ schedulerFrameRegs)
    (hBase : ∀ lane < 32, (7506, b64 p.cuQBase) ∈ F lane)
    (hReads : CuQReadsFromLaunchInWarp p l X g)
    (cur : SchedulerWarpAt l X g 2828 (fun lane => groupAdvanced p cta first lane (F lane))
      shuffles votes ends) {src targetPos : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨
      WarpFollowsEvent l X g cur.pos src targetPos target) (hPc : 2837 < target.pc) :
    ∃ result : SchedulerWarpAt l X g 2858
        (fun lane => searchUpFacts p cta (first + 31) lane (F lane) 0) (shuffles + 1) votes ends,
      SearchReadRange p l X g cur.pos result.pos ∧
      (WarpFollowsEvent l X g cur.pos src targetPos target →
        WarpFollowsEvent l X g result.pos src targetPos target) := by
  let _ : Nonempty TState := ⟨cur.state 0⟩
  let index := fun lane => first + 31 + lane
  let word := fun lane => b32 (drainCuQ p (index lane))
  let pos := fun lane => if index lane ≤ p.batch then cur.pos lane + 1 else cur.pos lane
  let facts := fun lane => (280, .pred (decide (lane = 31))) ::
    groupLaneFacts p cta first lane (F lane) (word lane)
  have hLane (lane : Nat) (hl : lane < 32)
      (hSuffix : (X.tr (warpLane l g lane)).drop (cur.pos lane) ≠ []) :
      ∃ before t, At t 2837 (facts lane) ∧
        Run kernel Assumptions.all l (warpLane l g lane) before
          ((X.tr (warpLane l g lane)).drop (pos lane)) (ends lane) ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) before t ∧
        (index lane ≤ p.batch → X.get (warpLane l g lane, cur.pos lane) =
          some ⟨2835, .rd (searchReadAcc p (index lane)) ((word lane).toBytes.map some)⟩) := by
    let thread := warpLane l g lane
    have ht := cur.checkpoint lane hl
    obtain ⟨v, hv, hV⟩ := branchSearchGroup (l := l) (g := thread) ht
    have hV' : At v 2829 (groupAdvanced p cta first lane (F lane)) := by
      simpa only [ite_eq_right (Nat.not_le.mpr hGroup)] using hV
    obtain ⟨w, hw, hW⟩ := searchLaneGate hp (g := thread) hGroup hl (hF lane hl) hV'
    have hLocal := (cur.localSteps lane hl).trans (run_rtg (run_comp hv hw))
    obtain ⟨before, u, hu, hRead, hTail, hSteps⟩ :=
      searchLaneRead hp (hF lane hl) (hBase lane hl) hW hLocal
        (cur.continuation lane hl) (fun _ => hSuffix) (fun h => hReads lane hl (index lane) h)
    obtain ⟨out, hStep, hAt⟩ := searchLastLane (l := l) (g := thread) hl (hF lane hl) hu
    exact ⟨before, out, hAt, hTail, hSteps.trans (run_rtg hStep), hRead⟩
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hTemplate (lane : Nat) {t : TState} (ht : At t 2837 (facts lane)) :
      out kernel Assumptions.all l (warpLane l g lane) t =
        .ev (.shfl .down (word lane) 1 31 (fun v _ => next (setReg t 2329 v))) :=
    (searchModel (by rw [ht.1]; decide) (by rw [ht.1]; decide)).trans
      (groupDownTemplate hp _ _ _ ht.1 ht.2.2.2.1 ht.2.2.2.2.2.2.1)
  have hBefore (h : WarpFollowsEvent l X g cur.pos src targetPos target)
      (hRead : index src ≤ p.batch → X.get (warpLane l g src, cur.pos src) =
        some ⟨2835, .rd (searchReadAcc p (index src)) ((word src).toBytes.map some)⟩) :
      pos src ≤ targetPos := by
    by_cases hd : index src ≤ p.batch
    · simp only [pos, ite_eq_left hd]
      rcases Nat.eq_or_lt_of_le h.before with heq | hlt
      · have hGet := hRead hd
        rw [heq] at hGet
        have hEq := congrArg Event.pc (Option.some.inj (hGet.symm.trans h.get))
        change 2835 = target.pc at hEq
        omega
      · exact hlt
    · simpa only [pos, ite_eq_right hd] using h.before
  have countAfterRead (test : Event → Bool) (lane n : Nat)
      (hCount : ((X.tr (warpLane l g lane)).take (cur.pos lane)).countP test = n)
      (hOrdinary : ∀ a bs, test ⟨2835, .rd a bs⟩ = false)
      (hRead : index lane ≤ p.batch → X.get (warpLane l g lane, cur.pos lane) =
        some ⟨2835, .rd (searchReadAcc p (index lane)) ((word lane).toBytes.map some)⟩) :
      ((X.tr (warpLane l g lane)).take (pos lane)).countP test = n := by
    by_cases h : index lane ≤ p.batch
    · have he := hRead h
      simp only [pos, ite_eq_left h, List.take_add_one]
      rw [show (X.tr (warpLane l g lane))[cur.pos lane]? = _ from he]
      simp [hOrdinary, hCount]
    · simpa only [pos, ite_eq_right h] using hCount
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
          (.shfl .down (word src) 1 31 (fun x _ => next (setReg t 2329 x))) :=
        ⟨hLocal, hTemplate src ht⟩
      obtain ⟨_, _, he, hk, _⟩ := hn.shuffle_at_nonempty hr hRemain
        (countAfterRead _ src _ (cur.ordinals.shfl src h.lane) (fun _ _ => rfl) hRead)
      exact cur.ordinals.shuffle_suffix_nonempty hX hBlock hg h.lane he hk hl (h.noExit lane hl)
  choose! before state hAt hRun hLocal hRead using
    fun lane hl => hLane lane hl (hSuffix lane hl)
  have hOrd : WarpOrdinals l X g pos shuffles votes :=
    ⟨fun lane hl => countAfterRead _ lane _ (cur.ordinals.shfl lane hl) (fun _ _ => rfl)
      (hRead lane hl),
      fun lane hl => countAfterRead _ lane _ (cur.ordinals.vote lane hl) (fun _ _ => rfl)
        (hRead lane hl)⟩
  let down : SchedulerWarpAt l X g 2837 facts shuffles votes ends :=
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
  have hFresh : ∀ lane < 32, ∀ x ∈ facts lane, x.1 ≠ 2329 := by
    intro lane hl x hx
    simp only [facts, groupLaneFacts, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx
    all_goals first
      | exact of_decide_eq_true rfl
      | exact fun he => (of_decide_eq_true rfl : 2329 ∉ searchCarryRegs)
          (he ▸ searchCarry_mem (hF lane hl) x hx)
  have hOut := fun lane hl => hTemplate lane (hAt lane hl)
  obtain ⟨after, hPos, hShuffle, hAfter⟩ :=
    down.consumeShuffleToRecorded hp hX hg .down word (fun _ => 1) (fun _ => 31) hFresh hOut
      (hProgress.imp_right hKeep) hPc
  have hPrep : ∃ result : SchedulerWarpAt l X g 2858
      (fun lane => searchUpFacts p cta (first + 31) lane (F lane) 0) (shuffles + 1) votes ends,
      result.pos = after.pos := by
    apply after.advanceLocalAt
    intro lane hl
    obtain ⟨_, u, hu, hU⟩ := prepareSearchUp hp (g := warpLane l g lane) hGroup hl (hF lane hl)
      (after.checkpoint lane hl)
    exact ⟨u, run_rtg hu, hU⟩
  obtain ⟨result, hResult⟩ := hPrep
  refine ⟨result, ?_, fun h => hResult.symm ▸ hAfter (hKeep h)⟩
  rw [hResult]
  apply searchReadRangeAppend (b := down.pos) _
    (searchReadRangeShuffle hPos hShuffle)
  intro lane hl j hLo hHi a bytes he
  change j < pos lane at hHi
  by_cases hIndex : index lane ≤ p.batch
  · rw [show pos lane = cur.pos lane+1 from ite_eq_left hIndex] at hHi
    have hEq : j = cur.pos lane := by omega
    rw [hEq] at he
    have hAn := congrArg Event.kind (Option.some.inj ((hRead lane hl hIndex).symm.trans he))
    exact ⟨index lane,hIndex,(Kind.rd.inj hAn).1.symm⟩
  · rw [show pos lane = cur.pos lane from ite_eq_right hIndex] at hHi
    omega

private theorem searchDownWarpReached {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g cta first shuffles votes : Nat}
    (hg : g < l.threads) (hGroup : first + 31 < p.batch) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ schedulerFrameRegs)
    (hBase : ∀ lane < 32, (7506, b64 p.cuQBase) ∈ F lane) (hProtect : DrainCuQProtected p X)
    (cur : SchedulerWarpReached l X g 2828
      (fun lane => groupAdvanced p cta first lane (F lane)) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 2858
      (fun lane => searchUpFacts p cta (first + 31) lane (F lane) 0)
      (shuffles + 1) votes ends) := by
  let _ : Nonempty TState := ⟨cur.state 0⟩
  let index := fun lane => first + 31 + lane
  let word := fun lane => b32 (drainCuQ p (index lane))
  let pos := fun lane => if index lane ≤ p.batch then cur.pos lane + 1 else cur.pos lane
  let facts := fun lane => (280, .pred (decide (lane = 31))) ::
    groupLaneFacts p cta first lane (F lane) (word lane)
  have hLane (lane : Nat) (hl : lane < 32) :
      ∃ before t, At t 2837 (facts lane) ∧
        pos lane ≤ (X.tr (warpLane l g lane)).length ∧
        (pos lane = (X.tr (warpLane l g lane)).length → Step.Released l X (warpLane l g lane)) ∧
        Run kernel Assumptions.all l (warpLane l g lane) {} ((X.tr (warpLane l g lane)).take
          (pos lane)) (some before) ∧
        Run kernel Assumptions.all l (warpLane l g lane) before
          ((X.tr (warpLane l g lane)).drop (pos lane)) (ends lane) ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) before t ∧
        (index lane ≤ p.batch → X.get (warpLane l g lane, cur.pos lane) =
          some ⟨2835, .rd (searchReadAcc p (index lane)) ((word lane).toBytes.map some)⟩) := by
    let thread := warpLane l g lane
    have ht := cur.checkpoint lane hl
    obtain ⟨v, hv, hV⟩ := branchSearchGroup (l := l) (g := thread) ht
    have hV' : At v 2829 (groupAdvanced p cta first lane (F lane)) := by
      simpa only [ite_eq_right (Nat.not_le.mpr hGroup)] using hV
    obtain ⟨w, hw, hW⟩ := searchLaneGate hp (g := thread) hGroup hl (hF lane hl) hV'
    have hLocal := (cur.localSteps lane hl).trans (run_rtg (run_comp hv hw))
    have hThread := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.1.2.1
    obtain ⟨before, u, hu, hBound, hReleased, hRecorded, hTail, hSteps, hRead⟩ :=
      searchLaneReadReached hp hMax hThread (hF lane hl) (hBase lane hl) hW hLocal
        (cur.continuation lane hl) (cur.positive lane hl) (cur.bounded lane hl)
        (cur.released lane hl) (cur.recorded lane hl) hProtect
    obtain ⟨out, hStep, hAt⟩ := searchLastLane (l := l) (g := thread) hl (hF lane hl) hu
    exact ⟨before, out, hAt, hBound, hReleased, hRecorded, hTail,
      hSteps.trans (run_rtg hStep), hRead⟩
  have hTemplate (lane : Nat) {t : TState} (ht : At t 2837 (facts lane)) :
      out kernel Assumptions.all l (warpLane l g lane) t =
        .ev (.shfl .down (word lane) 1 31 (fun v _ => next (setReg t 2329 v))) :=
    (searchModel (by rw [ht.1]; decide) (by rw [ht.1]; decide)).trans
      (groupDownTemplate hp _ _ _ ht.1 ht.2.2.2.1 ht.2.2.2.2.2.2.1)
  have countAfterRead (test : Event → Bool) (lane n : Nat)
      (hCount : ((X.tr (warpLane l g lane)).take (cur.pos lane)).countP test = n)
      (hOrdinary : ∀ a bs, test ⟨2835, .rd a bs⟩ = false)
      (hRead : index lane ≤ p.batch → X.get (warpLane l g lane, cur.pos lane) =
        some ⟨2835, .rd (searchReadAcc p (index lane)) ((word lane).toBytes.map some)⟩) :
      ((X.tr (warpLane l g lane)).take (pos lane)).countP test = n := by
    by_cases h : index lane ≤ p.batch
    · have he := hRead h
      simp only [pos, ite_eq_left h, List.take_add_one]
      rw [show (X.tr (warpLane l g lane))[cur.pos lane]? = _ from he]
      simp [hOrdinary, hCount]
    · simpa only [pos, ite_eq_right h] using hCount
  choose! before state hAt hBound hReleased hRecorded hRun hLocal hRead using hLane
  have hOrd : WarpOrdinals l X g pos shuffles votes :=
    ⟨fun lane hl => countAfterRead _ lane _ (cur.ordinals.shfl lane hl) (fun _ _ => rfl)
      (hRead lane hl),
      fun lane hl => countAfterRead _ lane _ (cur.ordinals.vote lane hl) (fun _ _ => rfl)
        (hRead lane hl)⟩
  have hPositive (lane : Nat) (hl : lane < 32) : 0 < pos lane := by
    have hPrev := cur.positive lane hl
    simp only [pos]
    split <;> omega
  let down : SchedulerWarpReached l X g 2837 facts shuffles votes ends :=
    ⟨⟨pos, before, state, hOrd, hRun, hLocal, hAt⟩, hPositive, hBound, hReleased, hRecorded⟩
  have hFresh : ∀ lane < 32, ∀ x ∈ facts lane, x.1 ≠ 2329 := by
    intro lane hl x hx
    simp only [facts, groupLaneFacts, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx
    all_goals first
      | exact of_decide_eq_true rfl
      | exact fun he => (of_decide_eq_true rfl : 2329 ∉ searchCarryRegs)
          (he ▸ searchCarry_mem (hF lane hl) x hx)
  obtain ⟨after⟩ := down.consumeShuffle hp hMax hg .down word (fun _ => 1) (fun _ => 31)
    hFresh (fun lane hl => hTemplate lane (hAt lane hl))
  apply after.advanceLocal
  intro lane hl
  obtain ⟨_, u, hu, hU⟩ := prepareSearchUp hp (g := warpLane l g lane) hGroup hl (hF lane hl)
    (after.checkpoint lane hl)
  exact ⟨u, run_rtg hu, hU⟩

private theorem searchSigned {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

private theorem searchExhausted {X : Execution} {g cta first shuffles votes : Nat}
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState} (hStop : cta + 1 < 2 ^ 31)
    (hClip : p.batch ≤ first + 31) (hWarp : ∀ lane < 32, (1062, b32 13) ∈ F lane)
    (cur : SchedulerWarpAt l X g 2828 (fun lane => groupAdvanced p cta first lane (F lane))
      shuffles votes ends) :
    ∃ result : SchedulerWarpAt l X g 2878 (fun _ => exhaustedScheduleFacts p) shuffles votes ends,
      result.pos = cur.pos ∧ result.before = cur.before := by
  apply cur.advanceLocalPreserving
  intro lane hl
  let thread := warpLane l g lane
  obtain ⟨v, hv, hV⟩ := branchSearchGroup (l := l) (g := thread) (cur.checkpoint lane hl)
  have hpv : v.pc = 2875 := by simpa only [ite_eq_left hClip] using hV.1
  have hAt : At v 2875 [(7224, b32 (cta + 1)), (1072, b32 cta)] :=
    ⟨hpv, hV.2.1, hV.2.2.1, hV.2.2.2.1, hV.2.2.2.2.2.2.1,
      holds_mem hV.2.2.2.2 (by simp [groupAdvanced, searchCarry]), trivial⟩
  have hGate : Seg kernel [] l thread 2 2875 [(7224, b32 (cta + 1)), (1072, b32 cta)] 2877
      [(291, .pred false)] := by
    intro t ht
    have hCta : cta < 2 ^ 31 := by omega
    seg_fp ht using simp only [compare, Option.getD_some,
      truncBits_ofNat (show cta + 1 < 2 ^ 32 by omega) (by decide),
      truncBits_ofNat (show cta < 2 ^ 32 by omega) (by decide),
      searchSigned hStop, searchSigned hCta, Int.ofNat_le, show ¬ cta + 1 ≤ cta by omega,
      decide_false]
  obtain ⟨w, hw, hW⟩ := hGate v hAt
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := thread)
    Flow.code_2877 false hW hW.2.2.2.2.1 (by simp)
  obtain ⟨hRun, hFrame⟩ := searchLinear (R := [7223, 7228, 1062])
    (by decide) (by decide) hpv
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) (run_comp hw hu)
  have hSaved : Holds v.regs (exhaustedScheduleFacts p) := by
    refine ⟨?_, holds_mem hV.2.2.2.2 (by simp [groupAdvanced, searchCarry]),
      holds_mem hV.2.2.2.2
        (by simp [groupAdvanced, searchCarry, groupSchedulerFrame, hWarp lane hl]),
      trivial⟩
    exact holds_mem hV.2.2.2.2 (by simp [groupAdvanced, searchCarry, Nat.min_eq_right hClip])
  refine ⟨u, run_rtg (run_comp hv hRun), hU.mono ?_⟩
  exact ⟨(hFrame 7223 (by decide)).trans hSaved.1, (hFrame 7228 (by decide)).trans hSaved.2.1,
    (hFrame 1062 (by decide)).trans hSaved.2.2.1, trivial⟩

private def searchTotalFacts (p : Params) (cta first lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  [(7222, b32 (∑ j ∈ Finset.range 32, groupLaneTiles p first j)),
    (7221, b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)),
    (7220, b32 (groupLaneTiles p first lane))] ++
    searchCarry p cta first (tilePrefix p first * p.heads) lane F

private theorem searchTotalArgs {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g cta first shuffles votes : Nat} {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ schedulerFrameRegs)
    (cur : SchedulerWarpAt l X g 2873
      (fun lane => searchUpResult p cta first lane (F lane) 4) shuffles votes ends) :
    (∀ lane < 32, ∀ x ∈ searchUpResult p cta first lane (F lane) 4, x.1 ≠ 7222) ∧
    (∀ lane < 32, out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
      .ev (.shfl .idx (b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)) 31 31
        (fun v _ => next (setReg (cur.state lane) 7222 v)))) := by
  let a := fun lane => b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)
  have hFresh : ∀ lane < 32, ∀ x ∈ searchUpResult p cta first lane (F lane) 4, x.1 ≠ 7222 := by
    intro lane hl x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact of_decide_eq_true rfl
    · exact fun he => (of_decide_eq_true rfl : 7222 ∉ searchScanRegs)
        (he ▸ searchScan_mem (hF lane hl) x hx)
  have hOut (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
        .ev (.shfl .idx (a lane) 31 31
          (fun v _ => next (setReg (cur.state lane) 7222 v))) := by
    have ht := cur.checkpoint lane hl
    have hPart := ht.2.2.2.2.1
    change (cur.state lane).regs 7221 =
      some (b32 (prefixWindow (groupLaneTiles p first) 32 lane)) at hPart
    rw [prefixWindow_warp _ hl] at hPart
    exact (searchModel (by rw [ht.1]; decide) (by rw [ht.1]; decide)).trans
      (groupTotalTemplate hp _ _ _ ht.1 ht.2.2.2.1 hPart)
  exact ⟨hFresh, hOut⟩

private theorem searchTotalFinish {X : Execution} {g cta first shuffles votes : Nat}
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (after : SchedulerWarpAt l X g 2874
      (fun lane => (7222,
        b32 (∑ j ∈ Finset.range ((shflSource .idx lane 31 31).1 + 1), groupLaneTiles p first j)) ::
        searchUpResult p cta first lane (F lane) 4) shuffles votes ends) (lane : Nat)
    (hl : lane < 32) :
    At (after.state lane) 2874 (searchTotalFacts p cta first lane (F lane)) := by
  have ht := after.checkpoint lane hl
  have hSrc : (shflSource .idx lane 31 31).1 = 31 := by
    rw [shflSource_idx lane (show (31 : Nat) < 32 by decide)]
  have hCount := ht.2.2.2.2.1
  rw [hSrc] at hCount
  have hPart := ht.2.2.2.2.2.1
  change (after.state lane).regs 7221 =
    some (b32 (prefixWindow (groupLaneTiles p first) 32 lane)) at hPart
  rw [prefixWindow_warp _ hl] at hPart
  have hCarry : Holds (after.state lane).regs (searchScanCarry p cta first lane (F lane)) :=
    ht.2.2.2.2.2.2
  have hKeep := ((holds_append ..).mp hCarry).2
  exact ht.mono ⟨hCount, hPart, hKeep⟩

private theorem searchTotalWarp {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g cta first shuffles votes : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ schedulerFrameRegs)
    (cur : SchedulerWarpAt l X g 2873 (fun lane => searchUpResult p cta first lane (F lane) 4)
      shuffles votes ends) {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 2873 < target.pc) :
    ∃ result : SchedulerWarpAt l X g 2874
        (fun lane => searchTotalFacts p cta first lane (F lane)) (shuffles + 1) votes ends,
      SearchReadRange p l X g cur.pos result.pos ∧
      (WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g result.pos src index target) := by
  let a := fun lane => b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)
  obtain ⟨hFresh, hOut⟩ := searchTotalArgs hp hF cur
  obtain ⟨after, hPos, hShuffle, hAfter⟩ :=
    cur.consumeShuffleToRecorded hp hX hg .idx a (fun _ => 31) (fun _ => 31)
      hFresh hOut hProgress hPc
  have hLocal : ∃ result : SchedulerWarpAt l X g 2874
      (fun lane => searchTotalFacts p cta first lane (F lane)) (shuffles + 1) votes ends,
      result.pos = after.pos := by
    apply after.advanceLocalAt
    intro lane hl
    exact ⟨after.state lane, .refl, searchTotalFinish after lane hl⟩

  obtain ⟨result, hResult⟩ := hLocal
  exact ⟨result, hResult.symm ▸ searchReadRangeShuffle hPos hShuffle,
    fun h => hResult.symm ▸ hAfter h⟩

private theorem searchTotalWarpReached {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g cta first shuffles votes : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ schedulerFrameRegs)
    (cur : SchedulerWarpReached l X g 2873
      (fun lane => searchUpResult p cta first lane (F lane) 4) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 2874
      (fun lane => searchTotalFacts p cta first lane (F lane)) (shuffles + 1) votes ends) := by
  let a := fun lane => b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)
  obtain ⟨hFresh, hOut⟩ := searchTotalArgs hp hF cur.toSchedulerWarpAt
  obtain ⟨after⟩ := cur.consumeShuffle hp hMax hg .idx a (fun _ => 31) (fun _ => 31)
    hFresh hOut
  apply after.advanceLocal
  intro lane hl
  exact ⟨after.state lane, .refl, searchTotalFinish after.toSchedulerWarpAt lane hl⟩

private def searchResultFacts (p : Params) (cta first lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
  [(7218, b32 limit), (7224, b32 limit),
    (7222, b32 (∑ j ∈ Finset.range 32, groupLaneTiles p first j)),
    (7221, b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)),
    (7220, b32 (groupLaneTiles p first lane)),
    (1203, b32 (cta + 1)), (7223, b32 first), (7228, b32 p.batch), (1201, b32 lane),
    (1072, b32 cta)] ++ groupSchedulerFrame p lane F

private theorem searchLimitLane {m : Mem0} (hp : Pre p l m) {g cta first lane : Nat}
    {F : List (Nat × Value)} {t : TState} (hf : first ≤ p.batch) (hCta : cta < 2 ^ 31)
    (hF : ∀ x ∈ F, x.1 ∈ schedulerFrameRegs) (ht : At t 2874 (searchTotalFacts p cta first lane F))
    :
    let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
    ∃ u, run kernel Assumptions.all l g 4 t = some u ∧
      At u (if limit ≤ cta then 2824 else 2878) (searchResultFacts p cta first lane F) := by
  dsimp only
  let remaining := [(7222, b32 (∑ j ∈ Finset.range 32, groupLaneTiles p first j)),
    (7221, b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)),
    (7220, b32 (groupLaneTiles p first lane)),
    (1203, b32 (cta + 1)), (7223, b32 first), (7228, b32 p.batch), (1201, b32 lane),
    (1072, b32 cta)] ++ groupSchedulerFrame p lane F
  have h := ht.2.2.2.2
  have hFrame := h.2.2.2.2.2.2.2.2.2
  have hInput := (groupLimit hp g hf hCta) t (ht.mono
    ⟨h.1, hFrame.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, trivial⟩)
  obtain ⟨u, hr, hu⟩ := hInput
  let keep := [7222, 7221, 7220, 1203, 7223, 7228] ++ schedulerFrameRegs
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
end

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g cta first shuffles votes : Nat}
    (hg : g < l.threads) (hCTA : cta < l.grid) (hFirst : first < p.batch)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ schedulerFrameRegs)
    (hBase : ∀ lane < 32, (7506, b64 p.cuQBase) ∈ F lane)
    (hWarp : ∀ lane < 32, (1062, b32 13) ∈ F lane)
include hp hX hg hCTA hFirst hF hBase hWarp

/-- Run one group of the fallback scheduler in the actual trace. The exhausted group skips
the collectives. A populated group performs one down shuffle, five up shuffles and its total
broadcast before carrying to the next group or selecting this group's request. -/
theorem SchedulerWarpAt.searchGroupRecordingReads (hReads : CuQReadsFromLaunchInWarp p l X g)
    (cur : SchedulerWarpAt l X g 2824 (fun lane => groupSearchFacts p cta first lane (F lane))
      shuffles votes ends) {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 2873 < target.pc) :
    let Follows := fun pos => WarpFollowsEvent l X g cur.pos src index target →
      WarpFollowsEvent l X g pos src index target
    (p.batch ≤ first + 31 ∧
      ∃ result : SchedulerWarpAt l X g 2878 (fun _ => exhaustedScheduleFacts p)
          shuffles votes ends,
        SearchReadRange p l X g cur.pos result.pos ∧ Follows result.pos) ∨
    (first + 31 < p.batch ∧
      ((tilePrefix p (min p.batch (first + 31 + 31)) * p.heads ≤ cta ∧
        ∃ result : SchedulerWarpAt l X g 2824
            (fun lane => groupSearchFacts p cta (first + 31) lane (F lane))
            (shuffles + 7) votes ends,
          SearchReadRange p l X g cur.pos result.pos ∧ Follows result.pos) ∨
      (cta < tilePrefix p (min p.batch (first + 31 + 31)) * p.heads ∧
        ∃ result : SchedulerWarpAt l X g 2878
          (fun lane => groupAvailableFacts p cta (first + 31) lane (F lane))
          (shuffles + 7) votes ends,
          SearchReadRange p l X g cur.pos result.pos ∧ Follows result.pos))) := by
  dsimp only
  have hStop : cta + 1 < 2 ^ 31 := by have := hp.grid.2.2; omega
  have hAdvance : ∃ result : SchedulerWarpAt l X g 2828
      (fun lane => groupAdvanced p cta first lane (F lane)) shuffles votes ends,
      result.pos = cur.pos := by
    apply cur.advanceLocalAt
    intro lane hl
    obtain ⟨u, hu, hU⟩ := advanceSearchGroup hp (g := warpLane l g lane) hFirst (hF lane hl)
      (cur.checkpoint lane hl)
    exact ⟨u, run_rtg hu, hU⟩
  obtain ⟨advanced, ha⟩ := hAdvance
  by_cases hClip : p.batch ≤ first + 31
  · obtain ⟨result, hResult, _⟩ := searchExhausted hStop hClip hWarp advanced
    exact .inl ⟨hClip, result, searchReadRangeEmpty (hResult.trans ha),
      fun h => hResult.symm ▸ ha.symm ▸ h⟩
  have hGroup := Nat.lt_of_not_ge hClip
  have hBound := Nat.le_of_lt hGroup
  have followA : WarpFollowsEvent l X g cur.pos src index target →
      WarpFollowsEvent l X g advanced.pos src index target := fun h => ha.symm ▸ h
  obtain ⟨s0, reads0, h0⟩ := searchDownWarp hp hX hg hGroup hF hBase hReads advanced
    (hProgress.imp_right followA) (by omega)
  have follow0 := h0 ∘ followA
  obtain ⟨s1, reads1, h1⟩ := searchScanStage hp hX hg hBound 0 hF s0 (hProgress.imp_right follow0)
    (by change 2858 < target.pc; omega)
  have follow1 := h1 ∘ follow0
  obtain ⟨s2, reads2, h2⟩ := searchScanStage hp hX hg hBound 1 hF s1 (hProgress.imp_right follow1)
    (by change 2861 < target.pc; omega)
  have follow2 := h2 ∘ follow1
  obtain ⟨s3, reads3, h3⟩ := searchScanStage hp hX hg hBound 2 hF s2 (hProgress.imp_right follow2)
    (by change 2864 < target.pc; omega)
  have follow3 := h3 ∘ follow2
  obtain ⟨s4, reads4, h4⟩ := searchScanStage hp hX hg hBound 3 hF s3 (hProgress.imp_right follow3)
    (by change 2867 < target.pc; omega)
  have follow4 := h4 ∘ follow3
  obtain ⟨s5, reads5, h5⟩ := searchScanStage hp hX hg hBound 4 hF s4 (hProgress.imp_right follow4)
    (by change 2870 < target.pc; omega)
  have follow5 := h5 ∘ follow4
  obtain ⟨total, readsTotal, hTotal⟩ := searchTotalWarp hp hX hg hF s5
    (hProgress.imp_right follow5) hPc
  have followTotal := hTotal ∘ follow5
  have hRange : SearchReadRange p l X g cur.pos total.pos :=
    ha ▸ searchReadRangeAppend reads0 (searchReadRangeAppend reads1
      (searchReadRangeAppend reads2 (searchReadRangeAppend reads3
        (searchReadRangeAppend reads4 (searchReadRangeAppend reads5 readsTotal)))))
  let limit := tilePrefix p (min p.batch (first + 31 + 31)) * p.heads
  refine .inr ⟨hGroup, ?_⟩
  by_cases hLimit : limit ≤ cta
  · have hLocal : ∃ result : SchedulerWarpAt l X g 2824
        (fun lane => groupSearchFacts p cta (first + 31) lane (F lane)) (shuffles + 7) votes ends,
        result.pos = total.pos := by
      apply total.advanceLocalAt
      intro lane hl
      obtain ⟨u, hu, hU⟩ := searchLimitLane hp (g := warpLane l g lane) hBound (by omega)
        (hF lane hl) (total.checkpoint lane hl)
      have hPc : u.pc = 2824 := by
        have h := hU.1
        change u.pc = (if limit ≤ cta then 2824 else 2878) at h
        simpa only [ite_eq_left hLimit] using h
      have h := hU.2.2.2.2
      refine ⟨u, run_rtg hu, ⟨hPc, hU.2.1, hU.2.2.1, hU.2.2.2.1, ?_⟩⟩
      exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.1, h.2.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2⟩
    obtain ⟨result, hResult⟩ := hLocal
    exact .inl ⟨hLimit,result,hResult.symm ▸ hRange,fun h => hResult.symm ▸ followTotal h⟩
  · have hLocal : ∃ result : SchedulerWarpAt l X g 2878
        (fun lane => groupAvailableFacts p cta (first + 31) lane (F lane))
        (shuffles + 7) votes ends,
        result.pos = total.pos := by
      apply total.advanceLocalAt
      intro lane hl
      obtain ⟨u, hu, hU⟩ := searchLimitLane hp (g := warpLane l g lane) hBound (by omega)
        (hF lane hl) (total.checkpoint lane hl)
      have hPc : u.pc = 2878 := by
        have h := hU.1
        change u.pc = (if limit ≤ cta then 2824 else 2878) at h
        simpa only [ite_eq_right hLimit] using h
      have h := hU.2.2.2.2
      refine ⟨u, run_rtg hu, ⟨hPc, hU.2.1, hU.2.2.1, hU.2.2.2.1, ?_⟩⟩
      exact ⟨h.2.2.2.2.2.2.2.1, h.2.2.1, h.2.2.2.1, h.2.1,
        h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.1,
        h.2.2.2.2.2.2.2.2.2.2⟩
    obtain ⟨result, hResult⟩ := hLocal
    exact .inr ⟨Nat.lt_of_not_ge hLimit, result, hResult.symm ▸ hRange,
      fun h => hResult.symm ▸ followTotal h⟩

theorem SchedulerWarpAt.searchGroupToInWarp (hReads : CuQReadsFromLaunchInWarp p l X g)
    (cur : SchedulerWarpAt l X g 2824 (fun lane => groupSearchFacts p cta first lane (F lane))
      shuffles votes ends) {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 2873 < target.pc) :
    let Follows := fun pos => WarpFollowsEvent l X g cur.pos src index target →
      WarpFollowsEvent l X g pos src index target
    (p.batch ≤ first + 31 ∧
      ∃ result : SchedulerWarpAt l X g 2878 (fun _ => exhaustedScheduleFacts p)
          shuffles votes ends, Follows result.pos) ∨
    (first + 31 < p.batch ∧
      ((tilePrefix p (min p.batch (first + 31 + 31)) * p.heads ≤ cta ∧
        ∃ result : SchedulerWarpAt l X g 2824
            (fun lane => groupSearchFacts p cta (first + 31) lane (F lane))
            (shuffles + 7) votes ends, Follows result.pos) ∨
      (cta < tilePrefix p (min p.batch (first + 31 + 31)) * p.heads ∧
        ∃ result : SchedulerWarpAt l X g 2878
          (fun lane => groupAvailableFacts p cta (first + 31) lane (F lane))
          (shuffles + 7) votes ends, Follows result.pos))) := by
  rcases cur.searchGroupRecordingReads hp hX hg hCTA hFirst hF hBase hWarp
      hReads hProgress hPc with
    ⟨hClip,result,_,hFollow⟩ | ⟨hGroup,⟨hMore,result,_,hFollow⟩ | ⟨hDone,result,_,hFollow⟩⟩
  · exact .inl ⟨hClip,result,hFollow⟩
  · exact .inr ⟨hGroup,.inl ⟨hMore,result,hFollow⟩⟩
  · exact .inr ⟨hGroup,.inr ⟨hDone,result,hFollow⟩⟩

/-- Apply the scoped proof when every CuQ read agrees with the launch. -/
theorem SchedulerWarpAt.searchGroupTo (hReads : CuQReadsFromLaunch p X)
    (cur : SchedulerWarpAt l X g 2824 (fun lane => groupSearchFacts p cta first lane (F lane))
      shuffles votes ends) {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 2873 < target.pc) :
    let Follows := fun pos => WarpFollowsEvent l X g cur.pos src index target →
      WarpFollowsEvent l X g pos src index target
    (p.batch ≤ first + 31 ∧
      ∃ result : SchedulerWarpAt l X g 2878 (fun _ => exhaustedScheduleFacts p)
          shuffles votes ends, Follows result.pos) ∨
    (first + 31 < p.batch ∧
      ((tilePrefix p (min p.batch (first + 31 + 31)) * p.heads ≤ cta ∧
        ∃ result : SchedulerWarpAt l X g 2824
            (fun lane => groupSearchFacts p cta (first + 31) lane (F lane))
            (shuffles + 7) votes ends, Follows result.pos) ∨
      (cta < tilePrefix p (min p.batch (first + 31 + 31)) * p.heads ∧
        ∃ result : SchedulerWarpAt l X g 2878
          (fun lane => groupAvailableFacts p cta (first + 31) lane (F lane))
          (shuffles + 7) votes ends, Follows result.pos))) :=
  SchedulerWarpAt.searchGroupToInWarp hp hX hg hCTA hFirst hF hBase hWarp
    (hReads.inWarp g) cur hProgress hPc
end

/-- Run one group of the fallback scheduler in the actual trace. The exhausted group skips
the collectives. A populated group performs one down shuffle, five up shuffles and its total
broadcast before carrying to the next group or selecting this group's request. -/
theorem SchedulerWarpAt.searchGroup {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g cta first shuffles votes : Nat} (hg : g < l.threads) (hCTA : cta < l.grid)
    (hFirst : first < p.batch) {F : Nat → List (Nat × Value)}
    (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ schedulerFrameRegs)
    (hBase : ∀ lane < 32, (7506, b64 p.cuQBase) ∈ F lane)
    (hWarp : ∀ lane < 32, (1062, b32 13) ∈ F lane)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k))
    (cur : SchedulerWarpAt l X g 2824 (fun lane => groupSearchFacts p cta first lane (F lane))
      shuffles votes) :
    (p.batch ≤ first + 31 ∧
      Nonempty (SchedulerWarpAt l X g 2878 (fun _ => exhaustedScheduleFacts p) shuffles votes)) ∨
    (first + 31 < p.batch ∧
      ((tilePrefix p (min p.batch (first + 31 + 31)) * p.heads ≤ cta ∧
        Nonempty (SchedulerWarpAt l X g 2824
          (fun lane => groupSearchFacts p cta (first + 31) lane (F lane)) (shuffles + 7) votes)) ∨
      (cta < tilePrefix p (min p.batch (first + 31 + 31)) * p.heads ∧
        Nonempty (SchedulerWarpAt l X g 2878
          (fun lane => groupAvailableFacts p cta (first + 31) lane (F lane))
          (shuffles + 7) votes)))) := by
  rcases cur.searchGroupTo hp hX hg hCTA hFirst hF hBase hWarp
      (fun i hi => cuQWordReadsFromLaunchOfProtected hp hX hi (hProtected i hi))
      (src := 0) (index := 0) (target := ⟨2874, .exit⟩) (.inl (fun _ _ => rfl)) (by decide) with
    ⟨hClip, result, _⟩ | ⟨hMore, ⟨hContinue, result, _⟩ | ⟨hFound, result, _⟩⟩
  · exact .inl ⟨hClip, ⟨result⟩⟩
  · exact .inr ⟨hMore, .inl ⟨hContinue, ⟨result⟩⟩⟩
  · exact .inr ⟨hMore, .inr ⟨hFound, ⟨result⟩⟩⟩


/-- Follow every later fallback group of an idle warp through its actual recorded collectives. -/
theorem SchedulerWarpReached.idleSearchExhausted {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g cta : Nat} (hg : g < l.threads) (hCTA : cta < l.grid)
    (hIdle : tilePrefix p p.batch * p.heads ≤ cta)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ schedulerFrameRegs)
    (hBase : ∀ lane < 32, (7506, b64 p.cuQBase) ∈ F lane)
    (hWarp : ∀ lane < 32, (1062, b32 13) ∈ F lane)
    (hProtect : DrainCuQProtected p X)
    {first shuffles votes : Nat} (hFirst : first < p.batch)
    (cur : SchedulerWarpReached l X g 2824 (fun lane => groupSearchFacts p cta first lane (F lane))
      shuffles votes ends) :
    ∃ shuffles', Nonempty (SchedulerWarpReached l X g 2878 (fun _ => exhaustedScheduleFacts p)
      shuffles' votes ends) := by
  have hStop : cta + 1 < 2 ^ 31 := by have := hp.grid.2.2; omega
  obtain ⟨advanced⟩ := cur.advanceLocal
    (G := fun lane => groupAdvanced p cta first lane (F lane)) (pc' := 2828) (by
      intro lane hl
      obtain ⟨u, hu, hU⟩ := advanceSearchGroup hp (g := warpLane l g lane) hFirst (hF lane hl)
        (cur.checkpoint lane hl)
      exact ⟨u, run_rtg hu, hU⟩)
  by_cases hClip : p.batch ≤ first + 31
  · obtain ⟨done, hPos, hBefore⟩ := searchExhausted hStop hClip hWarp advanced.toSchedulerWarpAt
    exact ⟨shuffles, ⟨advanced.reframe done hPos hBefore⟩⟩
  have hGroup := Nat.lt_of_not_ge hClip
  have hLe := Nat.le_of_lt hGroup
  obtain ⟨s0⟩ := searchDownWarpReached hp hMax hg hGroup hF hBase hProtect advanced
  obtain ⟨s1⟩ := searchScanStageReached hp hMax hg hLe 0 hF s0
  obtain ⟨s2⟩ := searchScanStageReached hp hMax hg hLe 1 hF s1
  obtain ⟨s3⟩ := searchScanStageReached hp hMax hg hLe 2 hF s2
  obtain ⟨s4⟩ := searchScanStageReached hp hMax hg hLe 3 hF s3
  obtain ⟨s5⟩ := searchScanStageReached hp hMax hg hLe 4 hF s4
  obtain ⟨total⟩ := searchTotalWarpReached hp hMax hg hF s5
  have hLimit : tilePrefix p (min p.batch (first + 31 + 31)) * p.heads ≤ cta :=
    (Nat.mul_le_mul_right _ (tilePrefix_mono p (Nat.min_le_left ..))).trans hIdle
  obtain ⟨next⟩ := total.advanceLocal (pc' := 2824)
    (G := fun lane => groupSearchFacts p cta (first + 31) lane (F lane)) (by
      intro lane hl
      obtain ⟨u, hu, hU⟩ := searchLimitLane hp (g := warpLane l g lane) hLe (by omega)
        (hF lane hl) (total.checkpoint lane hl)
      have hPc : u.pc = 2824 := by simpa only [ite_eq_left hLimit] using hU.1
      have h := hU.2.2.2.2
      refine ⟨u, run_rtg hu, ⟨hPc, hU.2.1, hU.2.2.1, hU.2.2.2.1, ?_⟩⟩
      exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.1, h.2.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2⟩)
  exact idleSearchExhausted hp hMax hg hCTA hIdle hF hBase hWarp hProtect hGroup next
termination_by p.batch - first
decreasing_by omega

/-- An active output warp reaches the availability check in the group containing its CTA. -/
theorem SchedulerWarpReached.selectedSearchGroupOfMaximal
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g cta : Nat} (hg : g < l.threads) (hCTA : cta < l.grid)
    (hActive : cta < tilePrefix p p.batch * p.heads)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hF : ∀ lane < 32, ∀ x ∈ F lane, x.1 ∈ schedulerFrameRegs)
    (hBase : ∀ lane < 32, (7506,b64 p.cuQBase) ∈ F lane)
    (hProtect : DrainCuQProtected p X)
    {first shuffles votes : Nat} (hFirst : first < p.batch)
    (hPast : tilePrefix p (min p.batch (first + 31)) * p.heads ≤ cta)
    (cur : SchedulerWarpReached l X g 2824
      (fun lane => groupSearchFacts p cta first lane (F lane)) shuffles votes ends) :
    ∃ selected shuffles', selected < p.batch ∧ tilePrefix p selected * p.heads ≤ cta ∧
      cta < tilePrefix p (min p.batch (selected + 31)) * p.heads ∧
      Nonempty (SchedulerWarpReached l X g 2878
        (fun lane => groupAvailableFacts p cta selected lane (F lane)) shuffles' votes ends) := by
  have hGrid : l.grid < 2 ^ 31 := hp.grid.2.2
  have hGroup : first + 31 < p.batch := by
    by_contra! hClip
    rw [Nat.min_eq_left hClip] at hPast
    omega
  let next := first + 31
  let limit := tilePrefix p (min p.batch (next + 31)) * p.heads
  have hLow : tilePrefix p next * p.heads ≤ cta := by
    simpa only [next,Nat.min_eq_right hGroup.le] using hPast
  obtain ⟨advanced⟩ := cur.advanceLocal
    (G := fun lane => groupAdvanced p cta first lane (F lane)) (pc' := 2828) (by
      intro lane hl
      obtain ⟨u,hu,hU⟩ := advanceSearchGroup hp (g := warpLane l g lane) hFirst (hF lane hl)
        (cur.checkpoint lane hl)
      exact ⟨u,run_rtg hu,hU⟩)
  obtain ⟨s0⟩ := searchDownWarpReached hp hMax hg hGroup hF hBase hProtect advanced
  obtain ⟨s1⟩ := searchScanStageReached hp hMax hg hGroup.le 0 hF s0
  obtain ⟨s2⟩ := searchScanStageReached hp hMax hg hGroup.le 1 hF s1
  obtain ⟨s3⟩ := searchScanStageReached hp hMax hg hGroup.le 2 hF s2
  obtain ⟨s4⟩ := searchScanStageReached hp hMax hg hGroup.le 3 hF s3
  obtain ⟨s5⟩ := searchScanStageReached hp hMax hg hGroup.le 4 hF s4
  obtain ⟨total⟩ := searchTotalWarpReached hp hMax hg hF s5
  by_cases hLimit : limit ≤ cta
  · obtain ⟨nextGroup⟩ := total.advanceLocal (pc' := 2824)
      (G := fun lane => groupSearchFacts p cta next lane (F lane)) (by
        intro lane hl
        obtain ⟨u,hu,hU⟩ := searchLimitLane hp (g := warpLane l g lane) hGroup.le (by omega)
          (hF lane hl) (total.checkpoint lane hl)
        have hPc : u.pc = 2824 := by
          have h := hU.1
          change u.pc = (if limit ≤ cta then 2824 else 2878) at h
          simpa only [ite_eq_left hLimit] using h
        have h := hU.2.2.2.2
        refine ⟨u,run_rtg hu,⟨hPc,hU.2.1,hU.2.2.1,hU.2.2.2.1,?_⟩⟩
        exact ⟨h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,h.1,h.2.2.2.2.2.2.2.1,
          h.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2⟩)
    exact selectedSearchGroupOfMaximal hp hMax hg hCTA hActive hF hBase hProtect
      hGroup hLimit nextGroup
  · have hSelected := Nat.lt_of_not_ge hLimit
    refine ⟨next,shuffles+7,hGroup,hLow,hSelected,total.advanceLocal (pc' := 2878) ?_⟩
    intro lane hl
    obtain ⟨u,hu,hU⟩ := searchLimitLane hp (g := warpLane l g lane) hGroup.le (by omega)
      (hF lane hl) (total.checkpoint lane hl)
    have hPc : u.pc = 2878 := by
      have h := hU.1
      change u.pc = (if limit ≤ cta then 2824 else 2878) at h
      simpa only [ite_eq_right hLimit] using h
    have h := hU.2.2.2.2
    refine ⟨u,run_rtg hu,⟨hPc,hU.2.1,hU.2.2.1,hU.2.2.2.1,?_⟩⟩
    exact ⟨h.2.2.2.2.2.2.2.1, h.2.2.1, h.2.2.2.1, h.2.1,
      h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.2.2⟩
termination_by p.batch - first
decreasing_by omega

/-- A short batch has no later request groups after the first search. -/
theorem SchedulerWarpReached.shortSearchExhausted {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g cta shuffles votes : Nat} (hCTA : cta < l.grid)
    (hBatch : p.batch ≤ 31) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs)
    (hWarp : ∀ lane < 32, (1062,b32 13) ∈ F lane)
    (cur : SchedulerWarpReached l X g 2824 (fun lane => groupSearchFacts p cta 0 lane (F lane))
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 2878 (fun _ => exhaustedScheduleFacts p)
      shuffles votes ends) := by
  have hStop : cta + 1 < 2 ^ 31 := by have := hp.grid.2.2; omega
  obtain ⟨advanced⟩ := cur.advanceLocal
    (G := fun lane => groupAdvanced p cta 0 lane (F lane)) (pc' := 2828) (by
      intro lane hl
      obtain ⟨u,hu,hU⟩ := advanceSearchGroup hp (g := warpLane l g lane) hp.shape.1 (hF lane hl)
        (cur.checkpoint lane hl)
      exact ⟨u,run_rtg hu,hU⟩)
  obtain ⟨done,hPos,hBefore⟩ := searchExhausted hStop hBatch hWarp advanced.toSchedulerWarpAt
  exact ⟨advanced.reframe done hPos hBefore⟩


end
end PTX.Kernels.TmlFa4Fwd.Epilogue
