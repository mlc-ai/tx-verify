-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionGroupChoose
public import Kernels.TmlFa4Fwd.Proof.EpilogueGroupTileTrace
public import Lemmas.Flow.TcTmpl
import Kernels.TmlFa4Fwd.Flow.Code.Part123

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The chosen request's exclusive prefix within its group, in units of CTA work. -/
def correctionPrefixFacts (p : Params) (l : Launch) (g first batch lane : Nat) :
    List (Nat × Value) :=
  (7275, b32 (selectedGroupPrefix p first batch)) ::
    (correctionChosenFacts p l g first batch lane).filter (fun pair => pair.1 != 7275)

private theorem prefixCarry {R : Nat → Option Value} {F : List (Nat × Value)} (h : Holds R F) :
    Holds R (F.filter (fun pair => pair.1 != 7275)) := by
  induction F with
  | nil => trivial
  | cons a as ih =>
    rw [List.filter_cons]
    split
    · exact ⟨h.1, ih h.2⟩
    · exact ih h.2

private theorem correctionPrefixIdxTemplate {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g idx sum : Nat} (hIdx : idx < 32) {t : TState}
    (ht : At t 7880 [(5914, b32 idx), (7271, b32 sum)]) :
    out kernel Assumptions.all l g t = .ev (.shfl .idx (b32 sum) idx 31
      (fun value _ => next (setReg t 5915 value))) := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  rw [groupCoreOut (by rw [ht.1]; decide) (by rw [ht.1]; decide)]
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_7880) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 5915 none (.reg 7271) (.reg 5914)
    (.imm 31) (.imm (-1))) = _
  have hIndex := readBits_b32 (g := g) (L := l) ht.2.2.2.2.1 (show idx < 2 ^ 32 by omega)
  have hMask : readBits l g t 32 (.imm (-1)) = .ok 4294967295#64 := rfl
  have hClamp : readBits l g t 32 (.imm 31) = .ok 31#64 := rfl
  simp only [shflTmpl, readValue, readReg, ht.2.2.2.2.2.1, hBlock, hMask, hClamp, hIndex,
    pure, Except.pure, toNat_ofNat_lt (show idx < 2 ^ 64 by omega)]
  rfl

private theorem prefixSkipLane {p : Params} {l : Launch} {g first batch lane : Nat}
    (hEq : batch = first) {t : TState}
    (ht : At t 7878 (correctionChosenFacts p l g first batch lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u 7882 (correctionPrefixFacts p l g first batch lane) := by
  let thread := warpLane l g lane
  have hg : t.regs 711 = some (.pred true) := by
    simpa only [hEq, decide_true] using ht.2.2.2.2.2.2.1
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := thread)
    Flow.code_7878 true ht hg (by simp)
  obtain ⟨huA, _⟩ := groupLinear (regs := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  have hZero : selectedGroupPrefix p first batch = 0 := by simp [selectedGroupPrefix, hEq]
  exact ⟨u, run_rtg huA, hU.mono ⟨by simpa only [hZero] using hU.2.2.2.2.2.2.2.1,
    prefixCarry hU.2.2.2.2⟩⟩

private theorem prefixIdxLane {p : Params} {l : Launch} {g first batch lane : Nat}
    (hLess : first < batch) (hN : batch-first < 32) {t : TState}
    (ht : At t 7878 (correctionChosenFacts p l g first batch lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u 7880 ((5914,b32 (batch-first-1)) :: correctionChosenFacts p l g first batch lane) := by
  let chosen := correctionChosenFacts p l g first batch
  let idx := batch-first-1
  let thread := warpLane l g lane
  let keep := (chosen lane).map Prod.fst
  have hFlag : t.regs 711 = some (.pred false) := by
    simpa only [decide_eq_false (Nat.ne_of_gt hLess)] using ht.2.2.2.2.2.2.1
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := thread)
    Flow.code_7878 false ht hFlag (by simp)
  obtain ⟨huA, _⟩ := groupLinear (regs := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  have hStep : Seg kernel [] l thread 1 7879 [(1624, b32 (batch - first))] 7880
      [(5914, b32 idx)] := by
    intro z hz
    seg_fp hz using norm_bits [idx]
  obtain ⟨v, hv, hV⟩ := hStep _ (hU.mono ⟨hU.2.2.2.2.1, trivial⟩)
  obtain ⟨hvA, hvFrame⟩ := groupLinear (regs := keep) (by decide) (by decide) hU.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hv
  have hSaved := holdsSchedulerFrame hU.2.2.2.2 hvFrame (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨v, run_rtg (run_comp huA hvA), hV.mono ⟨hV.2.2.2.2.1, hSaved⟩⟩

private theorem prefixAfterIdxLane {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g first batch lane : Nat} (hFirst : first ≤ batch) (hLess : first < batch)
    (hGroup : batch < first+31) (hBatch : batch < p.batch) {t : TState}
    (ht : At t 7881
      ((5915,b32 (∑ j ∈ Finset.range ((shflSource .idx lane (batch-first-1) 31).1 +1),
        groupLaneTiles p first j)) ::
        (5914,b32 (batch-first-1)) :: correctionChosenFacts p l g first batch lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u 7882 (correctionPrefixFacts p l g first batch lane) := by
  let idx := batch-first-1
  let part := fun lane => ∑ j ∈ Finset.range (lane+1), groupLaneTiles p first j
  let chosen := correctionChosenFacts p l g first batch
  let frame := fun lane => (chosen lane).filter (fun pair => pair.1 != 7275)
  have hIdx : idx < 32 := by omega
  let thread := warpLane l g lane
  let keep := (frame lane).map Prod.fst
  let n := batch - first
  let count := ∑ j ∈ Finset.range n, groupLaneTiles p first j
  have hCount := ht.2.2.2.2.1
  rw [shflSource_idx lane hIdx] at hCount
  have he : idx + 1 = n := by omega
  change t.regs 5915 = some (b32 (part idx)) at hCount
  simp only [part, he] at hCount
  have hHeads := holds_lookup ht.2.2.2.2 (show
    (((5915, b32 (part (shflSource .idx lane idx 31).1)) ::
      (5914, b32 idx) :: chosen lane).lookup 7142) = some (b32 p.heads) from rfl)
  have hAt : At t 7881 [(5915, b32 count), (7142, b32 p.heads)] :=
    ht.mono ⟨hCount, hHeads, trivial⟩
  have hSum := groupTiles_eq p (hFirst.trans hBatch.le) (show n ≤ 32 by omega)
  have hn : first + min 31 n = batch := by rw [Nat.min_eq_right (by omega)]; omega
  have hSum' : tilePrefix p first + count = tilePrefix p batch := by
    rw [hn, Nat.min_eq_right hBatch.le] at hSum
    exact hSum
  have hTotal : count * p.heads ≤ tilePrefix p batch * p.heads :=
    Nat.mul_le_mul_right _ (by omega)
  have hFit := hp.prefixWork_signed hBatch.le
  have hHeadsFit := hp.heads_signed
  have hHeadsPos : 0 < p.heads := by unfold Params.heads; have := hp.shape.2.2.1; omega
  have hCountFit : count < 2 ^ 32 := by have := Nat.le_mul_of_pos_right count hHeadsPos; omega
  have hCountExact : count % 4294967296 = count := Nat.mod_eq_of_lt hCountFit
  have hHeadsExact : p.heads % 4294967296 = p.heads := Nat.mod_eq_of_lt (by omega)
  have hWorkExact : count * p.heads % 4294967296 = count * p.heads :=
    Nat.mod_eq_of_lt (by omega)
  have hWorkWiden : count * p.heads % 18446744073709551616 = count * p.heads :=
    Nat.mod_eq_of_lt (by omega)
  have hStep : Seg kernel [] l thread 1 7881 [(5915, b32 count), (7142, b32 p.heads)] 7882
      [(7275, b32 (selectedGroupPrefix p first batch))] := by
    intro z hz
    change ∃ u, run kernel [] l thread 1 z = some u ∧ At u 7882 [(7275, b32 (count
    * p.heads))]
    seg_fp hz using norm_bits [hCountExact, hHeadsExact, hWorkExact, hWorkWiden]
  obtain ⟨u, hu, hU⟩ := hStep _ hAt
  obtain ⟨huA, huFrame⟩ := groupLinear (regs := keep) (by decide) (by decide) hAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  have hCarry : Holds t.regs (frame lane) := prefixCarry ht.2.2.2.2.2.2
  have hSave := holdsSchedulerFrame hCarry huFrame (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨u, run_rtg huA, hU.mono ⟨hU.2.2.2.2.1, hSave⟩⟩

/-- The first request has zero exclusive work. Every other request uses the prior lane's
actual prefix and the decoded scale by the head count. -/
theorem correctionSelectedPrefixTo {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g first batch shuffles votes : Nat} (hg : g < l.threads)
    (hFirst : first ≤ batch) (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    {ends : Nat → Option TState} {src index : Nat} {target : Event}
    (cur : SchedulerWarpAt l X g 7878 (correctionChosenFacts p l g first batch) shuffles votes ends)
    (hProgress : (∀ lane < 32, ends lane = none) ∨
      WarpFollowsEvent l X g cur.pos src index target) (hTarget : 7880 < target.pc) :
    ∃ next : SchedulerWarpAt l X g 7882 (correctionPrefixFacts p l g first batch)
      (shuffles + if first < batch then 1 else 0) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target := by
  let idx := batch - first - 1
  let part := fun lane => ∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j
  let chosen := correctionChosenFacts p l g first batch

  have hIdx : idx < 32 := by omega
  by_cases hEq : batch = first
  · rw [ite_eq_right (by omega : ¬ first < batch), Nat.add_zero]
    obtain ⟨next, hPos⟩ := cur.advanceLocalAt (G := correctionPrefixFacts p l g first batch)
      (pc' := 7882) (fun lane hl => prefixSkipLane hEq (cur.checkpoint lane hl))
    exact ⟨next, fun h => hPos.symm ▸ h⟩
  · have hLess : first < batch := by omega
    rw [ite_eq_left hLess]
    obtain ⟨ready, hRPos⟩ : ∃ ready : SchedulerWarpAt l X g 7880
        (fun lane => (5914, b32 idx) :: chosen lane) shuffles votes ends,
        ready.pos = cur.pos := by
      apply cur.advanceLocalAt
      exact fun lane hl => prefixIdxLane hLess (by omega) (cur.checkpoint lane hl)
    have hFresh (lane : Nat) (_ : lane < 32) (pair : Nat × Value)
        (hm : pair ∈ (5914, b32 idx) :: chosen lane) : pair.1 ≠ 5915 := by
      intro he
      have hMem := List.mem_map_of_mem (f := Prod.fst) hm
      rw [he] at hMem
      exact (of_decide_eq_true rfl : 5915 ∉ 5914 :: (chosen lane).map Prod.fst) hMem
    have hOut (lane : Nat) (hl : lane < 32) :
        out kernel Assumptions.all l (warpLane l g lane) (ready.state lane) =
          .ev (.shfl .idx (b32 (part lane)) idx 31
            (fun v _ => next (setReg (ready.state lane) 5915 v))) := by
      have ht := ready.checkpoint lane hl
      have hv := holds_lookup ht.2.2.2.2 (show
        (((5914, b32 idx) :: chosen lane).lookup 7271) = some (b32 (part lane)) from rfl)
      exact correctionPrefixIdxTemplate hp hIdx (ht.mono ⟨ht.2.2.2.2.1, hv, trivial⟩)
    obtain ⟨read, hRead⟩ := ready.consumeShuffleTo hp hX hg .idx (fun lane => b32 (part lane))
      (fun _ => idx) (fun _ => 31) hFresh hOut (by rw [hRPos]; exact hProgress) hTarget
    obtain ⟨next, hNPos⟩ := read.advanceLocalAt (G := correctionPrefixFacts p l g first batch)
      (pc' := 7882) (fun lane hl =>
        prefixAfterIdxLane hp hFirst hLess hGroup hBatch (read.checkpoint lane hl))
    exact ⟨next, fun h => hNPos.symm ▸ hRead (hRPos.symm ▸ h)⟩

/-- A maximal correction warp executes the selected request's optional prefix exchange. -/
theorem correctionSelectedPrefixOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first batch shuffles votes : Nat} (hg : g < l.threads)
    (hFirst : first ≤ batch) (hGroup : batch < first+31) (hBatch : batch < p.batch)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7878 (correctionChosenFacts p l g first batch)
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7882 (correctionPrefixFacts p l g first batch)
      (shuffles+if first < batch then 1 else 0) votes ends) := by
  let idx := batch-first-1
  let part := fun lane => ∑ j ∈ Finset.range (lane+1), groupLaneTiles p first j
  let chosen := correctionChosenFacts p l g first batch
  have hIdx : idx < 32 := by omega
  by_cases hEq : batch = first
  · rw [ite_eq_right (show ¬ first < batch by omega),Nat.add_zero]
    exact cur.advanceLocal (fun lane hl => prefixSkipLane hEq (cur.checkpoint lane hl))
  · have hLess : first < batch := by omega
    rw [ite_eq_left hLess]
    obtain ⟨ready⟩ := cur.advanceLocal (G := fun lane => (5914,b32 idx) :: chosen lane)
      (fun lane hl => prefixIdxLane hLess (by omega) (cur.checkpoint lane hl))
    have hFresh (lane : Nat) (_ : lane < 32) (pair : Nat × Value)
        (hm : pair ∈ (5914, b32 idx) :: chosen lane) : pair.1 ≠ 5915 := by
      intro he
      have hMem := List.mem_map_of_mem (f := Prod.fst) hm
      rw [he] at hMem
      exact (of_decide_eq_true rfl : 5915 ∉ 5914 :: (chosen lane).map Prod.fst) hMem
    have hOut (lane : Nat) (hl : lane < 32) :
        out kernel Assumptions.all l (warpLane l g lane) (ready.state lane) =
          .ev (.shfl .idx (b32 (part lane)) idx 31
            (fun v _ => next (setReg (ready.state lane) 5915 v))) := by
      have ht := ready.checkpoint lane hl
      have hv := holds_lookup ht.2.2.2.2 (show
        (((5914, b32 idx) :: chosen lane).lookup 7271) = some (b32 (part lane)) from rfl)
      exact correctionPrefixIdxTemplate hp hIdx (ht.mono ⟨ht.2.2.2.2.1, hv, trivial⟩)
    obtain ⟨read⟩ := ready.consumeShuffle hp hMax hg .idx (fun lane => b32 (part lane))
      (fun _ => idx) (fun _ => 31) hFresh hOut
    exact read.advanceLocal (fun lane hl =>
      prefixAfterIdxLane hp hFirst hLess hGroup hBatch (read.checkpoint lane hl))

end
end PTX.Kernels.TmlFa4Fwd.Correction
