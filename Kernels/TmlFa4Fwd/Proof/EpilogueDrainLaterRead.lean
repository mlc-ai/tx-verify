-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainEntry
public import Kernels.TmlFa4Fwd.Proof.EpilogueLocalRun
public import Lemmas.Flow.WarpScan

public import Lemmas.Step.Released
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
import Lemmas.Step.ProtectedReadProgress
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The invariant inputs carried by each lane throughout a later group's optional read. -/
def drainLaterCommon (p : Params) (l : Launch) (g base cta : Nat) : List (Nat × Value) :=
  [(1201, b32 (laneOf l g)), (7147, b32 p.batch), (7506, b64 p.cuQBase),
   (7230, b32 base), (1072, b32 cta), (7138, b32 p.heads), (1062, b32 13)]

/-- The old group start and sentinel stop word on entry at PC 3032. -/
def drainLaterEntry (p : Params) (l : Launch) (g first base stop cta : Nat) :
    List (Nat × Value) :=
  [(7235, b32 first), (1210, b32 stop)] ++ drainLaterCommon p l g base cta

/-- The next group installs the clipped start and resets its end word to the stop value. -/
def drainLaterGroup (p : Params) (l : Launch) (g first base stop cta : Nat) :
    List (Nat × Value) :=
  [(7235, b32 first), (7236, b32 stop), (1210, b32 stop)] ++ drainLaterCommon p l g base cta

private theorem keepFacts {t u : TState} {F : List (Nat × Value)} {D : List Nat}
    (h : Holds t.regs F) (hFrame : ∀ r ∉ D, u.regs r = t.regs r)
    (hDisj : List.Disjoint (F.map Prod.fst) D) : Holds u.regs F := by
  induction F with
  | nil => trivial
  | cons a F ih =>
    obtain ⟨r, v⟩ := a
    exact ⟨(hFrame r (hDisj (by simp))).trans h.1,
      ih h.2 (fun _ hr => hDisj (by simp [hr]))⟩

private theorem laterRunOne {l : Launch} {g : Nat} {t u : TState}
    (hlo : 2768 ≤ t.pc) (hhi : t.pc ≤ 3100) (hr : run kernel [] l g 1 t = some u) :
    run kernel Assumptions.all l g 1 t = some u := by
  simpa only [run, tauStep, epilogue_out_all_eq_nil (.inl ⟨hlo, hhi⟩)] using hr

/-- The later group advances its base by 31 requests. At the batch sentinel it branches
directly to the end test. Otherwise, its per-lane index and read guard are available. -/
theorem drainLaterReadRoute {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g first base stop cta : Nat} {t : TState}
    (hNext : first + 31 + laneOf l g < 2 ^ 31)
    (ht : At t 3032 (drainLaterEntry p l g first base stop cta)) :
    (p.batch ≤ first + 31 ∧ ∃ u,
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 3083 (drainLaterGroup p l g p.batch base stop cta)) ∨
    (first + 31 < p.batch ∧ ∃ u,
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 3040 ([(1212, b32 (first + 31 + laneOf l g)),
        (318, .pred (decide (p.batch < first + 31 + laneOf l g))), (7231, b32 0)] ++
        drainLaterGroup p l g (first + 31) base stop cta)) := by
  have ha : At t 3032 [(7235, b32 first), (7147, b32 p.batch), (1210, b32 stop)] := by
    apply ht.mono
    exact ⟨holds_mem ht.2.2.2.2 (by simp [drainLaterEntry]),
      holds_mem ht.2.2.2.2 (by simp [drainLaterEntry, drainLaterCommon]),
      holds_mem ht.2.2.2.2 (by simp [drainLaterEntry]), trivial⟩
  obtain ⟨u, hu, hU⟩ := drainGroupAdvance (first := first) l g (by omega) hp.shape.2.1 t ha
  have hpc := ht.1
  obtain ⟨hu', hFrame, _, _⟩ := epilogueLinearRun (F := [1211, 317, 7235, 7236])
    (t := t) (n := 4) (by omega) (by omega) (by
      intro pc hlo hhi
      have hcases : pc = 3032 ∨ pc = 3033 ∨ pc = 3034 := by omega
      rcases hcases with rfl | rfl | rfl
      · exact ⟨_, Flow.code_3032, rfl, fun _ h => h, by simp [writesRegs]⟩
      · exact ⟨_, Flow.code_3033, rfl, fun _ h => h, by simp [writesRegs]⟩
      · exact ⟨_, Flow.code_3034, rfl, fun _ h => h, by simp [writesRegs]⟩) (by
      intro _
      rw [hpc]
      exact ⟨_, Flow.code_3035, by simp [writesRegs]⟩) ht.2.1 ht.2.2.1 hu
  let group := drainLaterGroup p l g (min (first + 31) p.batch) base stop cta
  have hKeepT : Holds t.regs ((1210, b32 stop) :: drainLaterCommon p l g base cta) :=
    (holds_append _ _ _).mp ht.2.2.2.2 |>.2 |> fun hTail =>
      ⟨ha.2.2.2.2.2.2.1, hTail⟩
  have hKeep : Holds u.regs ((1210, b32 stop) :: drainLaterCommon p l g base cta) :=
    keepFacts hKeepT hFrame (by
      change List.Disjoint [1210, 1201, 7147, 7506, 7230, 1072, 7138, 1062] [1211, 317, 7235, 7236]
      simp only [List.disjoint_left, List.mem_cons, List.not_mem_nil, or_false]
      omega)
  have hGroup : Holds u.regs group :=
    ⟨hU.2.2.2.2.2.2.1, hU.2.2.2.2.2.2.2.1, hKeep⟩
  have hArgs : At u 3036 ((1211, b32 (first + 31)) :: group) :=
    hU.mono ⟨hU.2.2.2.2.1, hGroup⟩
  obtain ⟨v, hv, hV⟩ := drainBranchRun 2 l g u _ hArgs hU.2.2.2.2.2.1
  have hupc := hU.1
  have hVsteps := (run_rtg hu').trans (run_rtg (laterRunOne (by omega) (by omega) hv))
  by_cases hClip : p.batch ≤ first + 31
  · refine .inl ⟨hClip, v, hVsteps, ?_⟩
    have hP : v.pc = 3083 := by simpa [drainBranchSite, hClip] using hV.1
    exact ⟨hP, hV.2.1, hV.2.2.1, hV.2.2.2.1,
      by simpa only [group, Nat.min_eq_right hClip] using hV.2.2.2.2.2⟩
  · have hLt := Nat.lt_of_not_ge hClip
    have hvpc : v.pc = 3037 := by simpa [drainBranchSite, hClip] using hV.1
    have hAt : At v 3037 [(1211, b32 (first + 31)), (1201, b32 (laneOf l g)),
        (7147, b32 p.batch)] :=
      ⟨hvpc, hV.2.1, hV.2.2.1, hV.2.2.2.1,
        holds_mem hV.2.2.2.2 (by simp),
        holds_mem hV.2.2.2.2 (by simp [group, drainLaterGroup, drainLaterCommon]),
        holds_mem hV.2.2.2.2 (by simp [group, drainLaterGroup, drainLaterCommon]), trivial⟩
    obtain ⟨w, hw, hW⟩ := drainLaneGate l g hNext hp.shape.2.1 v hAt
    obtain ⟨hw', hwFrame, _, _⟩ := epilogueLinearRun (F := [1212, 318, 7231])
      (t := v) (n := 3) (by omega) (by omega) (by
        intro pc hlo hhi
        have hcases : pc = 3037 ∨ pc = 3038 := by omega
        rcases hcases with rfl | rfl
        · exact ⟨_, Flow.code_3037, rfl, fun _ h => h, by simp [writesRegs]⟩
        · exact ⟨_, Flow.code_3038, rfl, fun _ h => h, by simp [writesRegs]⟩) (by
        intro _
        rw [hvpc]
        exact ⟨_, Flow.code_3039, by simp [writesRegs]⟩) hV.2.1 hV.2.2.1 hw
    have hVgroup : Holds v.regs (drainLaterGroup p l g (first + 31) base stop cta) := by
      simpa only [group, Nat.min_eq_left (Nat.le_of_lt hLt)] using hV.2.2.2.2.2
    have hWgroup := keepFacts hVgroup hwFrame (by
      change List.Disjoint
        [7235, 7236, 1210, 1201, 7147, 7506, 7230, 1072, 7138, 1062] [1212, 318, 7231]
      simp only [List.disjoint_left, List.mem_cons, List.not_mem_nil, or_false]
      omega)
    exact .inr ⟨hLt, w, hVsteps.trans (run_rtg hw'), hW.mono
      ((holds_append _ _ _).2 ⟨hW.2.2.2.2, hWgroup⟩)⟩

def laterLaneFacts (l : Launch) (g first : Nat) (word : Value) :
    List (Nat × Value) :=
  [(1212, b32 (first + laneOf l g)), (7231, word)]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem laterReadTrace (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j first base stop cta : Nat} {t : TState}
    (ht : At t 3040 ([(1212, b32 (first + laneOf l g)),
      (318, .pred (decide (p.batch < first + laneOf l g))), (7231, b32 0)] ++
      drainLaterGroup p l g first base stop cta))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none)
    (hProtected : first + laneOf l g ≤ p.batch → ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * (first + laneOf l g))).at k)) :
    let laneIndex := first + laneOf l g
    let readAcc : Acc := {loc := globalLoc (p.cuQBase + 4 * laneIndex), size := 4}
    let word := b32 (drainCuQ p laneIndex)
    let idx := if laneIndex ≤ p.batch then j + 1 else j
    ∃ u, At u 3044 (laterLaneFacts l g first word ++ drainLaterGroup p l g first base stop cta) ∧
      (laneIndex ≤ p.batch →
        X.get (g, j) = some ⟨3043, .rd readAcc (word.toBytes.map some)⟩) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop idx) none := by
  dsimp only
  let index := first + laneOf l g
  let word := b32 (drainCuQ p index)
  let F := drainLaterGroup p l g first base stop cta
  have hPred : t.regs 318 = some (.pred (decide (p.batch < index))) := by
    exact holds_mem ht.2.2.2.2 (by simp [index])
  have hAt : At t 3040 (laterLaneFacts l g first (b32 0) ++ F) := by
    apply ht.mono
    have hFacts := (holds_append _ _ _).1 ht.2.2.2.2
    exact (holds_append _ _ _).2 ⟨⟨hFacts.1.1, hFacts.1.2.2.1, trivial⟩, hFacts.2⟩
  obtain ⟨v, hr, hV⟩ := drainBranchRun 3 l g t _ hAt hPred
  have hpc := ht.1
  have hRun' := hRun.after_local (run_rtg (laterRunOne (by omega) (by omega) hr))
  by_cases hSkip : p.batch < index
  · have hvpc : v.pc = 3044 := by simpa [drainBranchSite, hSkip] using hV.1
    have hNo : ¬ index ≤ p.batch := Nat.not_le_of_lt hSkip
    have hWord : word = b32 0 := by simp [word, drainCuQ, hNo]
    refine ⟨v, ⟨hvpc, hV.2.1, hV.2.2.1, hV.2.2.2.1, ?_⟩,
      fun h => (hNo h).elim, ?_⟩
    · simpa only [← hWord] using hV.2.2.2.2
    · simpa only [show ¬ first + laneOf l g ≤ p.batch from hNo, ite_false] using hRun'
  · have hvpc : v.pc = 3041 := by simpa [drainBranchSite, hSkip] using hV.1
    have hLane : index ≤ p.batch := Nat.le_of_not_lt hSkip
    have hAddr : At v 3041 [(1212, b32 index), (7506, b64 p.cuQBase)] := by
      refine ⟨hvpc, hV.2.1, hV.2.2.1, hV.2.2.2.1, ?_⟩
      exact ⟨holds_mem hV.2.2.2.2 (by simp [laterLaneFacts, index]),
        holds_mem hV.2.2.2.2 (by simp [F, drainLaterGroup, drainLaterCommon]), trivial⟩
    obtain ⟨a, ha, hA⟩ := drainLaterAddress hp g hLane v hAddr
    obtain ⟨ha', hFrame, _, _⟩ := epilogueLinearRun (F := [7874, 7875]) (t := v) (n := 2)
      (by omega) (by omega) (by
        intro pc hlo hhi
        have heq : pc = 3041 := by omega
        subst pc
        exact ⟨_, Flow.code_3041, rfl, fun _ h => h, by simp [writesRegs]⟩) (by
        intro _
        rw [hvpc]
        exact ⟨_, Flow.code_3042, by simp [writesRegs]⟩) hV.2.1 hV.2.2.1 ha
    have hRunA := hRun'.after_local (run_rtg ha')
    let acc : Acc := {loc := globalLoc (p.cuQBase + 4 * index), size := 4}
    have hOut : out kernel Assumptions.all l g a = .ev (.read acc (afterLoad a [7231])) :=
      (epilogue_out_all_eq_nil (.inl ⟨by have := hA.1; omega, by have := hA.1; omega⟩)).trans
        (drainLaterRead hp g hLane a hA)
    have hn : Next kernel Assumptions.all l g a a (.read acc (afterLoad a [7231])) :=
      ⟨.refl, hOut⟩
    cases hSuffix : (X.tr g).drop j with
    | nil => rw [hSuffix] at hRunA; cases hRunA
    | cons e es =>
      rw [hSuffix] at hRunA
      obtain ⟨u, ⟨bs, _, hEvent, hState⟩, hTail⟩ := hn.continuing_event (by
        rintro ⟨_, _, _, hBad⟩; cases hBad) hRunA
      obtain rfl := Option.some.inj hState
      have hObs := traceHeadOfDrop hSuffix
      rw [hEvent, hA.1] at hObs
      have hMem : X.MemReads (.thread (g, j)) acc bs := .inl ⟨3043, hObs.1⟩
      have hBytes : bs = word.toBytes.map some := by
        apply hX.launch_value hMem rfl (hProtected hLane)
        simpa [word, drainCuQ, hLane, b32, HasValue, Value.bytes] using hp.cuQ index hLane
      subst bs
      have hRead := rebuild_scalar (v := word) (show 0 < 4 by decide) rfl
      have hState : afterLoad a [7231] (word.toBytes.map some) = next (setReg a 7231 word) := by
        rw [afterLoad_ok hA.2.1 hA.2.2.1 hRead]
        simp [next, setReg, hA.2.1, hA.2.2.1]
      rw [hState] at hTail
      have hKeep := keepFacts ((holds_append _ _ _).1 hV.2.2.2.2).2 hFrame (by
        change List.Disjoint
          [7235, 7236, 1210, 1201, 7147, 7506, 7230, 1072, 7138, 1062] [7874, 7875]
        simp only [List.disjoint_left, List.mem_cons, List.not_mem_nil, or_false]
        omega)
      have hIndex : a.regs 1212 = some (b32 index) :=
        (hFrame 1212 (by decide)).trans (holds_mem hV.2.2.2.2 (by simp [laterLaneFacts, index]))
      have hAtA : At a 3043 ((1212, b32 index) :: F) := hA.mono ⟨hIndex, hKeep⟩
      have hAtU := hAtA.set (r := 7231) (v := word) (by
        simp [F, drainLaterGroup, drainLaterCommon])
      refine ⟨next (setReg a 7231 word), hAtU.mono ?_, fun _ => hObs.1, ?_⟩
      · exact ⟨hAtU.2.2.2.2.2.1, hAtU.2.2.2.2.1, hAtU.2.2.2.2.2.2⟩
      · rw [ite_eq_left (show first + laneOf l g ≤ p.batch from hLane), hObs.2]
        exact hTail

/-- The protected later drain lookup is forced in a maximal trace. -/
theorem laterDrainReadOfMaximal (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g j first base stop cta shuffles votes : Nat} (hg : g < l.threads) {t before : TState}
    {ending : Option TState}
    (ht : At t 3040 ([(1212, b32 (first + laneOf l g)),
      (318, .pred (decide (p.batch < first + laneOf l g))), (7231, b32 0)] ++
      drainLaterGroup p l g first base stop cta))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before t)
    (hRun : Run kernel Assumptions.all l g before ((X.tr g).drop j) ending) (hPos : 0 < j)
    (hBound : j ≤ (X.tr g).length) (hReleased : j = (X.tr g).length → Step.Released l X g)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take j) (some before))
    (hSh : ((X.tr g).take j).countP Execution.isShfl = shuffles)
    (hVote : ((X.tr g).take j).countP isFullWarpVote = votes)
    (hProtected : ∀ idx ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * idx)).at k)) :
    let laneIndex := first + laneOf l g
    let word := b32 (drainCuQ p laneIndex)
    let idx := if laneIndex ≤ p.batch then j + 1 else j
    ∃ v u, At u 3044 (laterLaneFacts l g first word ++ drainLaterGroup p l g first base stop cta) ∧
      0 < idx ∧ idx ≤ (X.tr g).length ∧
      (idx = (X.tr g).length → Step.Released l X g) ∧
      ((X.tr g).take idx).countP Execution.isShfl = shuffles ∧
      ((X.tr g).take idx).countP isFullWarpVote = votes ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take idx) (some v) ∧
      Run kernel Assumptions.all l g v ((X.tr g).drop idx) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) v u := by
  dsimp only
  let index := first + laneOf l g
  let word := b32 (drainCuQ p index)
  let F := drainLaterGroup p l g first base stop cta
  have hPred : t.regs 318 = some (.pred (decide (p.batch < index))) := by
    exact holds_mem ht.2.2.2.2 (by simp [index])
  have hAt : At t 3040 (laterLaneFacts l g first (b32 0) ++ F) := by
    apply ht.mono
    have hFacts := (holds_append _ _ _).1 ht.2.2.2.2
    exact (holds_append _ _ _).2 ⟨⟨hFacts.1.1, hFacts.1.2.2.1, trivial⟩, hFacts.2⟩
  obtain ⟨v, hr, hV⟩ := drainBranchRun 3 l g t _ hAt hPred
  have hpc := ht.1
  have hApproach := hLocal.trans (run_rtg (laterRunOne (by omega) (by omega) hr))
  by_cases hSkip : p.batch < index
  · have hvpc : v.pc = 3044 := by simpa [drainBranchSite, hSkip] using hV.1
    have hNo : ¬ index ≤ p.batch := Nat.not_le_of_lt hSkip
    have hWord : word = b32 0 := by simp [word, drainCuQ, hNo]
    rw [ite_eq_right (show ¬ first + laneOf l g ≤ p.batch from hNo)]
    refine ⟨before,v,⟨hvpc,hV.2.1,hV.2.2.1,hV.2.2.2.1,?_⟩,hPos,hBound,
      hReleased,hSh,hVote,hPrefix,hRun,hApproach⟩
    simpa only [← hWord] using hV.2.2.2.2
  · have hvpc : v.pc = 3041 := by simpa [drainBranchSite, hSkip] using hV.1
    have hLane : index ≤ p.batch := Nat.le_of_not_lt hSkip
    have hAddr : At v 3041 [(1212, b32 index), (7506, b64 p.cuQBase)] := by
      refine ⟨hvpc, hV.2.1, hV.2.2.1, hV.2.2.2.1, ?_⟩
      exact ⟨holds_mem hV.2.2.2.2 (by simp [laterLaneFacts, index]),
        holds_mem hV.2.2.2.2 (by simp [F, drainLaterGroup, drainLaterCommon]), trivial⟩
    obtain ⟨a, ha, hA⟩ := drainLaterAddress hp g hLane v hAddr
    obtain ⟨ha', hFrame, _, _⟩ := epilogueLinearRun (F := [7874, 7875]) (t := v) (n := 2)
      (by omega) (by omega) (by
        intro pc hlo hhi
        have heq : pc = 3041 := by omega
        subst pc
        exact ⟨_, Flow.code_3041, rfl, fun _ h => h, by simp [writesRegs]⟩) (by
        intro _
        rw [hvpc]
        exact ⟨_, Flow.code_3042, by simp [writesRegs]⟩) hV.2.1 hV.2.2.1 ha
    let acc : Acc := {loc := globalLoc (p.cuQBase + 4 * index), size := 4}
    have hOut : out kernel Assumptions.all l g a = .ev (.read acc (afterLoad a [7231])) :=
      (epilogue_out_all_eq_nil (.inl ⟨by have := hA.1; omega, by have := hA.1; omega⟩)).trans
        (drainLaterRead hp g hLane a hA)
    have hn : Next kernel Assumptions.all l g before a (.read acc (afterLoad a [7231])) :=
      ⟨hApproach.trans (run_rtg ha'), hOut⟩
    have hInit : HasValue m acc.loc word := by
      have hWord : word = b32 (p.qOffset index) := by simp [word,drainCuQ,hLane]
      rw [hWord]
      exact hp.cuQ _ hLane
    obtain ⟨he,hRecorded,hTail⟩ := Step.protected_read_of_maximal hMax hg (a := acc) (value := word)
      rfl hInit (hProtected _ hLane) hn hPrefix hRun hPos hBound hReleased
      (Assumptions.wf_snoc_initial hMax.1)
    have hRead := rebuild_scalar (v := word) (show 0 < 4 by decide) rfl
    have hState : afterLoad a [7231] (word.toBytes.map some) = next (setReg a 7231 word) := by
      rw [afterLoad_ok hA.2.1 hA.2.2.1 hRead]
      simp [next, setReg, hA.2.1, hA.2.2.1]
    rw [hState] at hTail hRecorded
    have hKeep := keepFacts ((holds_append _ _ _).1 hV.2.2.2.2).2 hFrame (by
      change List.Disjoint
        [7235, 7236, 1210, 1201, 7147, 7506, 7230, 1072, 7138, 1062] [7874, 7875]
      simp only [List.disjoint_left, List.mem_cons, List.not_mem_nil, or_false]
      omega)
    have hIndex : a.regs 1212 = some (b32 index) :=
      (hFrame 1212 (by decide)).trans (holds_mem hV.2.2.2.2 (by simp [laterLaneFacts, index]))
    have hAtA : At a 3043 ((1212, b32 index) :: F) := hA.mono ⟨hIndex, hKeep⟩
    have hAtU := hAtA.set (r := 7231) (v := word) (by
      simp [F, drainLaterGroup, drainLaterCommon])
    rw [ite_eq_left (show first + laneOf l g ≤ p.batch from hLane)]
    have hTake := List.take_succ_eq_append_getElem (len_of_get he)
    rw [(List.getElem?_eq_some_iff.mp he).2] at hTake
    refine ⟨_,_,hAtU.mono ?_,Nat.succ_pos _,len_of_get he,
      Prologue.releasedIfLast he (by intro h; cases h),?_,?_,hRecorded,hTail,.refl⟩
    · exact ⟨hAtU.2.2.2.2.2.1,hAtU.2.2.2.2.1,hAtU.2.2.2.2.2.2⟩
    · rw [hTake,List.countP_append,hSh]; rfl
    · rw [hTake,List.countP_append,hVote]; rfl

/-- The source lane's actual down shuffle is in the same ordinal as this lane. -/
def DrainDownPeer (p : Params) (l : Launch) (X : Execution) (g i first : Nat) : Prop :=
  let lane := laneOf l g
  let source := (shflSource .down lane 1 31).1
  ∀ recv ok, X.get (g, i) = some ⟨3045, .shfl .down (b32 (drainCuQ p (first + lane)))
      1 31 recv ok⟩ →
    ∃ ordinal j peerRecv peerOk, X.ShflK (g, i) ordinal ∧
      X.get (g - lane + source, j) =
        some ⟨3045, .shfl .down (b32 (drainCuQ p (first + source))) 1 31 peerRecv peerOk⟩ ∧
      X.ShflK (g - lane + source, j) ordinal ∧ ¬ ShflExited X (g - lane + source) ordinal

def drainLaterWordFacts (p : Params) (l : Launch) (g first : Nat) (recv : Value) :
    List (Nat × Value) :=
  let lane := laneOf l g
  [(2422, recv), (7231, b32 (drainCuQ p (first + lane))),
   (1212, b32 (first + lane)), (319, .pred (decide (lane = 31)))]

/-- Registers after the down shuffle, before computing the lane's contribution to the scan. -/
def drainLaterWords (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  let source := (shflSource .down (laneOf l g) 1 31).1
  drainLaterWordFacts p l g first (b32 (drainCuQ p (first + source)))

/-- The later drain computes the last-lane predicate before the actual down shuffle. -/
theorem laterDrainDownLocal {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g first base stop cta : Nat} {t : TState}
    (ht : At t 3044 (laterLaneFacts l g first (b32 (drainCuQ p (first + laneOf l g))) ++
      drainLaterGroup p l g first base stop cta)) :
    let word := b32 (drainCuQ p (first + laneOf l g))
    ∃ v, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t v ∧
      At v 3045 ((319,.pred (decide (laneOf l g = 31))) ::
        (laterLaneFacts l g first word ++ drainLaterGroup p l g first base stop cta)) ∧
      out kernel Assumptions.all l g v =
        .ev (.shfl .down word 1 31 (fun value _ => next (setReg v 2422 value))) := by
  dsimp only
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hAt : At t 3044 [(1201, b32 (laneOf l g))] := ht.mono
    ⟨holds_mem ht.2.2.2.2 (by simp [drainLaterGroup, drainLaterCommon]), trivial⟩
  obtain ⟨v, hv, hV⟩ := drainLaterLastLane l g hLane t hAt
  have htpc := ht.1
  obtain ⟨hv', hFrame, _, _⟩ := epilogueLinearRun (F := [319]) (t := t) (n := 1)
    (by omega) (by omega) (by omega) (by
      intro _
      rw [htpc]
      exact ⟨_, Flow.code_3044, by simp [writesRegs]⟩) ht.2.1 ht.2.2.1 hv
  let word := b32 (drainCuQ p (first + laneOf l g))
  have hWord : v.regs 7231 = some word :=
    (hFrame 7231 (by decide)).trans (holds_mem ht.2.2.2.2 (by simp [laterLaneFacts, word]))
  have hOut : out kernel Assumptions.all l g v =
      .ev (.shfl .down word 1 31 (fun value _ => next (setReg v 2422 value))) :=
    (epilogue_out_all_eq_nil (.inl ⟨by have := hV.1; omega, by have := hV.1; omega⟩)).trans
      (drainLaterShuffle hp g v _ hV.1 hV.2.2.2.1 hWord)
  refine ⟨v,run_rtg hv',hV.mono ?_,hOut⟩
  refine ⟨hV.2.2.2.2.1,keepFacts ht.2.2.2.2 hFrame ?_⟩
  change List.Disjoint
    [1212,7231,7235,7236,1210,1201,7147,7506,7230,1072,7138,1062] [319]
  simp only [List.disjoint_left,List.mem_cons,List.not_mem_nil,or_false]
  omega

private theorem laterDownShape (hp : Pre p l m) {g i first base stop cta : Nat} {t : TState}
    (ht : At t 3044 (laterLaneFacts l g first (b32 (drainCuQ p (first + laneOf l g))) ++
      drainLaterGroup p l g first base stop cta))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    let lane := laneOf l g
    ∃ recv ok u, X.get (g, i) = some ⟨3045, .shfl .down (b32 (drainCuQ p (first + lane)))
        1 31 recv ok⟩ ∧
      At u 3046
        (drainLaterWordFacts p l g first recv ++ drainLaterGroup p l g first base stop cta) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1)) none := by
  dsimp only
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hAt : At t 3044 [(1201, b32 (laneOf l g))] := ht.mono
    ⟨holds_mem ht.2.2.2.2 (by simp [drainLaterGroup, drainLaterCommon]), trivial⟩
  obtain ⟨v, hv, hV⟩ := drainLaterLastLane l g hLane t hAt
  have htpc := ht.1
  obtain ⟨hv', hFrame, _, _⟩ := epilogueLinearRun (F := [319]) (t := t) (n := 1)
    (by omega) (by omega) (by omega) (by
      intro _
      rw [htpc]
      exact ⟨_, Flow.code_3044, by simp [writesRegs]⟩) ht.2.1 ht.2.2.1 hv
  have hRunV := hRun.after_local (run_rtg hv')
  let word := b32 (drainCuQ p (first + laneOf l g))
  have hWord : v.regs 7231 = some word :=
    (hFrame 7231 (by decide)).trans (holds_mem ht.2.2.2.2 (by simp [laterLaneFacts, word]))
  have hOut : out kernel Assumptions.all l g v =
      .ev (.shfl .down word 1 31 (fun value _ => next (setReg v 2422 value))) :=
    (epilogue_out_all_eq_nil (.inl ⟨by have := hV.1; omega, by have := hV.1; omega⟩)).trans
      (drainLaterShuffle hp g v _ hV.1 hV.2.2.2.1 hWord)
  have hn : Next kernel Assumptions.all l g v v
      (.shfl .down word 1 31 (fun value _ => next (setReg v 2422 value))) := ⟨.refl, hOut⟩
  cases hSuffix : (X.tr g).drop i with
  | nil => rw [hSuffix] at hRunV; cases hRunV
  | cons e es =>
    rw [hSuffix] at hRunV
    obtain ⟨u, ⟨recv, ok, hEvent, hState⟩, hTail⟩ := hn.continuing_event (by
      rintro ⟨_, _, _, hBad⟩; cases hBad) hRunV
    obtain rfl := Option.some.inj hState
    have hObs := traceHeadOfDrop hSuffix
    rw [hEvent, hV.1] at hObs
    refine ⟨recv, ok, next (setReg v 2422 recv), hObs.1, ?_, by rw [hObs.2]; exact hTail⟩
    have hKeep := keepFacts ht.2.2.2.2 hFrame (by
      change List.Disjoint
        [1212, 7231, 7235, 7236, 1210, 1201, 7147, 7506, 7230, 1072, 7138, 1062] [319]
      simp only [List.disjoint_left, List.mem_cons, List.not_mem_nil, or_false]
      omega)
    have hV' := hV.mono ((holds_append _ _ _).2 ⟨hV.2.2.2.2, hKeep⟩)
    have hU := hV'.set (r := 2422) (v := recv) (by
        simp [laterLaneFacts, drainLaterGroup, drainLaterCommon])
    apply hU.mono
    have hs := (holds_append _ (laterLaneFacts l g first word)
      (drainLaterGroup p l g first base stop cta)).1 hU.2.2.2.2.2.2
    exact ⟨hU.2.2.2.2.1, hs.1.2.1, hs.1.1, hU.2.2.2.2.2.1, hs.2⟩

private theorem laterDownTrace (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i first base stop cta : Nat} {t : TState}
    (ht : At t 3044 (laterLaneFacts l g first (b32 (drainCuQ p (first + laneOf l g))) ++
      drainLaterGroup p l g first base stop cta)) (hPeer : DrainDownPeer p l X g i first)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    let lane := laneOf l g
    let source := shflSource .down lane 1 31
    ∃ u, X.get (g, i) = some ⟨3045, .shfl .down (b32 (drainCuQ p (first + lane)))
        1 31 (b32 (drainCuQ p (first + source.1))) source.2⟩ ∧
      At u 3046 (drainLaterWords p l g first ++ drainLaterGroup p l g first base stop cta) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1)) none := by
  dsimp only
  obtain ⟨recv, ok, u, hObs, hAt, hr⟩ := laterDownShape hp ht hRun
  obtain ⟨ordinal, j, peerRecv, peerOk, hk, hRead, hj, hLive⟩ := hPeer recv ok hObs
  obtain ⟨hRecv, hOk⟩ := shfl_source_value hX hObs hk hRead hj hLive
  subst recv
  subst ok
  exact ⟨u, hObs, hAt, hr⟩

/-- The next group's source operands follow from each lane's own trace. Matching shuffle
ordinals can therefore be supplied independently of any received value. -/
theorem drainLaterDownOperands (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j first base stop cta : Nat} {t : TState} (hNext : first + 31 + laneOf l g < 2 ^ 31)
    (hGroup : first + 31 < p.batch) (ht : At t 3032 (drainLaterEntry p l g first base stop cta))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let laneIndex := first + 31 + laneOf l g
    let acc : Acc := {loc := globalLoc (p.cuQBase + 4 * laneIndex), size := 4}
    let word := b32 (drainCuQ p laneIndex)
    let idx := if laneIndex ≤ p.batch then j + 1 else j
    (laneIndex ≤ p.batch → ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers (acc.loc.at k)) →
    (laneIndex ≤ p.batch → X.get (g, j) = some ⟨3043, .rd acc (word.toBytes.map some)⟩) ∧
      ∃ recv ok, X.get (g, idx) = some ⟨3045, .shfl .down word 1 31 recv ok⟩ := by
  dsimp only
  intro hProtected
  rcases drainLaterReadRoute hp hNext ht with ⟨hc, _, _, _⟩ | ⟨_, u, hu, hAt⟩
  · omega
  obtain ⟨v, hv, hRead, hr⟩ := laterReadTrace hp hX hAt (hRun.after_local hu) hProtected
  obtain ⟨recv, ok, _, hObs, _, _⟩ := laterDownShape hp hv hr
  exact ⟨hRead, recv, ok, hObs⟩

/-- Connected to an actual terminal run, a later group either clips at the sentinel or reads
its participating lane's cuQ word, then receives the next lane's word in the down shuffle. -/
theorem drainLaterReadObserved (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j first base stop cta : Nat} {t : TState} (hNext : first + 31 + laneOf l g < 2 ^ 31)
    (ht : At t 3032 (drainLaterEntry p l g first base stop cta))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let nextGroup := first + 31
    let lane := laneOf l g
    let laneIndex := nextGroup + lane
    let readAcc : Acc := {loc := globalLoc (p.cuQBase + 4 * laneIndex), size := 4}
    let idx := if laneIndex ≤ p.batch then j + 1 else j
    let source := shflSource .down lane 1 31
    (laneIndex ≤ p.batch → ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers (readAcc.loc.at k)) →
    (nextGroup < p.batch → DrainDownPeer p l X g idx nextGroup) →
    (p.batch ≤ nextGroup ∧ ∃ u, At u 3083 (drainLaterGroup p l g p.batch base stop cta) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop j) none) ∨
    (nextGroup < p.batch ∧ ∃ u,
      (laneIndex ≤ p.batch →
        X.get (g, j) = some ⟨3043, .rd readAcc ((b32 (drainCuQ p laneIndex)).toBytes.map some)⟩) ∧
      X.get (g, idx) = some ⟨3045, .shfl .down (b32 (drainCuQ p laneIndex)) 1 31
        (b32 (drainCuQ p (nextGroup + source.1))) source.2⟩ ∧
      At u 3046 (drainLaterWords p l g nextGroup ++ drainLaterGroup p l g nextGroup base stop cta) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (idx + 1)) none) := by
  dsimp only
  intro hProtected hPeer
  rcases drainLaterReadRoute hp hNext ht with ⟨hc, u, hu, hAt⟩ | ⟨hc, u, hu, hAt⟩
  · exact .inl ⟨hc, u, hAt, hRun.after_local hu⟩
  obtain ⟨v, hv, hRead, hTail⟩ := laterReadTrace hp hX hAt (hRun.after_local hu) hProtected
  obtain ⟨w, hSh, hw, hEnd⟩ := laterDownTrace hp hX hv (hPeer hc) hTail
  exact .inr ⟨hc, w, hRead, hSh, hw, hEnd⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
