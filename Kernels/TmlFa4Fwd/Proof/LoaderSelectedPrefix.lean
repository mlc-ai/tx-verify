-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSchedule
public import Kernels.TmlFa4Fwd.Proof.EpilogueGroupTileTrace
public import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The chosen request's exclusive prefix within its group, in units of CTA work. -/
def loaderPrefixFacts (p : Params) (l : Launch) (g warp first batch lane : Nat) :
    List (Nat × Value) :=
  (7167, b32 (selectedGroupPrefix p first batch)) ::
    (loaderChosenFacts p l g warp first batch lane).filter (fun pair => pair.1 != 7167)

private theorem prefixCarry {R : Nat → Option Value} {F : List (Nat × Value)} (h : Holds R F) :
    Holds R (F.filter (fun pair => pair.1 != 7167)) := by
  induction F with
  | nil => trivial
  | cons a as ih =>
    rw [List.filter_cons]
    split
    · exact ⟨h.1, ih h.2⟩
    · exact ih h.2

variable {p : Params} {l : Launch}

/-- The previous-lane prefix is broadcast by the checked shuffle. -/
theorem loaderPrefixIdxTemplate {m : Mem0} (hp : Pre p l m) {g idx sum : Nat} (hIdx : idx < 32)
    {t : TState} (ht : At t 304 [(1752, b32 idx), (7163, b32 sum)]) :
    out kernel Assumptions.all l g t = .ev (.shfl .idx (b32 sum) idx 31
      (fun value _ => next (setReg t 1753 value))) := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  rw [loaderOutCore (by rw [ht.1]; decide) (by rw [ht.1]; decide)]
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_304) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 1753 none (.reg 7163) (.reg 1752)
    (.imm 31) (.imm (-1))) = _
  have hIndex := readBits_b32 (g := g) (L := l) ht.2.2.2.2.1 (show idx < 2 ^ 32 by omega)
  have hMask : readBits l g t 32 (.imm (-1)) = .ok 4294967295#64 := rfl
  have hClamp : readBits l g t 32 (.imm 31) = .ok 31#64 := rfl
  simp only [shflTmpl, readValue, readReg, ht.2.2.2.2.2.1, hBlock, hMask, hClamp, hIndex,
    pure, Except.pure, toNat_ofNat_lt (show idx < 2 ^ 64 by omega)]
  rfl

/-- A selected first request has no preceding prefix to broadcast. -/
theorem loaderSelectedPrefixZeroLocal {g warp first batch : Nat} {t : TState} (lane : Nat)
    (hEq : batch = first) (ht : At t 302 (loaderChosenFacts p l g warp first batch lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u 306 (loaderPrefixFacts p l g warp first batch lane) := by
  let thread := warpLane l g lane
  have hg : t.regs 90 = some (.pred true) := by
    simpa only [hEq, decide_true] using ht.2.2.2.2.2.2.1
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := thread)
    Flow.code_302 true ht hg (by simp)
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  have hZero : selectedGroupPrefix p first batch = 0 := by simp [selectedGroupPrefix, hEq]
  exact ⟨u, run_rtg huA, hU.mono ⟨by simpa only [hZero] using hU.2.2.2.2.2.2.2.1,
    prefixCarry hU.2.2.2.2⟩⟩

/-- A nonfirst request prepares the previous lane index for the exclusive prefix broadcast. -/
theorem loaderSelectedPrefixIdxLocal {g warp first batch : Nat} (hFirst : first ≤ batch)
    (hGroup : batch < first + 31) (hEq : batch ≠ first) {t : TState} (lane : Nat)
    (ht : At t 302 (loaderChosenFacts p l g warp first batch lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u 304 ((1752,b32 (batch-first-1)) :: loaderChosenFacts p l g warp first batch lane) := by
  let idx := batch-first-1
  let chosen := loaderChosenFacts p l g warp first batch
  let thread := warpLane l g lane
  let keep := (chosen lane).map Prod.fst
  have hFlag : t.regs 90 = some (.pred false) := by
    simpa only [decide_eq_false hEq] using ht.2.2.2.2.2.2.1
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := thread)
    Flow.code_302 false ht hFlag (by simp)
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  have hStep : Seg kernel [] l thread 1 303 [(1080, b32 (batch - first))] 304
      [(1752, b32 idx)] := by
    have hN : batch - first < 32 := by omega
    intro z hz
    seg_fp hz using norm_bits [idx]
  obtain ⟨v, hv, hV⟩ := hStep _ (hU.mono ⟨hU.2.2.2.2.1, trivial⟩)
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := keep) (by decide) (by decide) hU.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hv
  have hSaved := holdsSchedulerFrame hU.2.2.2.2 hvFrame (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨v, run_rtg (run_comp huA hvA), hV.mono ⟨hV.2.2.2.2.1, hSaved⟩⟩

/-- The returned prefix shuffle mask gives the selected request's preceding work. -/
theorem loaderSelectedPrefixReturnLocal {m : Mem0} (hp : Pre p l m) {g warp first batch : Nat}
    (hFirst : first ≤ batch) (hGroup : batch < first+31) (hBatch : batch < p.batch)
    (hLess : first < batch) {t : TState} (lane : Nat)
    (ht : At t 305 ((1753,b32 (∑ j ∈ Finset.range
      ((shflSource .idx lane (batch-first-1) 31).1 + 1), groupLaneTiles p first j)) ::
        (1752,b32 (batch-first-1)) :: loaderChosenFacts p l g warp first batch lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u 306 (loaderPrefixFacts p l g warp first batch lane) := by
  let idx := batch-first-1
  let part := fun lane => ∑ j ∈ Finset.range (lane+1), groupLaneTiles p first j
  let chosen := loaderChosenFacts p l g warp first batch
  let frame := fun lane => (chosen lane).filter (fun pair => pair.1 != 7167)
  have hIdx : idx < 32 := by omega
  let thread := warpLane l g lane
  let keep := (frame lane).map Prod.fst
  let n := batch - first
  let count := ∑ j ∈ Finset.range n, groupLaneTiles p first j
  have hCount := ht.2.2.2.2.1
  rw [shflSource_idx lane hIdx] at hCount
  have he : idx + 1 = n := by omega
  change t.regs 1753 = some (b32 (part idx)) at hCount
  simp only [part, he] at hCount
  have hHeads := holds_lookup ht.2.2.2.2 (show
    (((1753, b32 (part (shflSource .idx lane idx 31).1)) ::
      (1752, b32 idx) :: chosen lane).lookup 7136) = some (b32 p.heads) from rfl)
  have hAt : At t 305 [(1753, b32 count), (7136, b32 p.heads)] :=
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
  have hStep : Seg kernel [] l thread 1 305 [(1753, b32 count), (7136, b32 p.heads)] 306
      [(7167, b32 (selectedGroupPrefix p first batch))] := by
    intro z hz
    change ∃ u, run kernel [] l thread 1 z = some u ∧ At u 306 [(7167, b32 (count * p.heads))]
    seg_fp hz using norm_bits [hCountExact, hHeadsExact, hWorkExact, hWorkWiden]
  obtain ⟨u, hu, hU⟩ := hStep _ hAt
  obtain ⟨huA, huFrame⟩ := loaderLinear (regs := keep) (by decide) (by decide) hAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  have hCarry : Holds t.regs (frame lane) := prefixCarry ht.2.2.2.2.2.2
  have hSave := holdsSchedulerFrame hCarry huFrame (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨u, run_rtg huA, hU.mono ⟨hU.2.2.2.2.1, hSave⟩⟩

/-- The first request has zero exclusive work. Every other request uses the prior lane's
actual prefix and the decoded scale by the head count. -/
theorem loaderSelectedPrefixTo {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g warp first batch shuffles votes : Nat}
    (hg : g < l.threads) (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 302 (loaderChosenFacts p l g warp first batch) shuffles votes ends)
    {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 304 < target.pc) :
    ∃ next : SchedulerWarpAt l X g 306 (loaderPrefixFacts p l g warp first batch)
      (shuffles + if first < batch then 1 else 0) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target := by
  let idx := batch - first - 1
  let part := fun lane => ∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j
  let chosen := loaderChosenFacts p l g warp first batch
  have hIdx : idx < 32 := by omega
  by_cases hEq : batch = first
  · rw [ite_eq_right (by omega : ¬ first < batch), Nat.add_zero]
    obtain ⟨localReady, hPos⟩ := cur.advanceLocalAt
      (pc' := 306) (G := loaderPrefixFacts p l g warp first batch) (fun lane hl =>
        loaderSelectedPrefixZeroLocal lane hEq (cur.checkpoint lane hl))
    exact ⟨localReady, fun h => hPos.symm ▸ h⟩
  · have hLess : first < batch := by omega
    rw [ite_eq_left hLess]
    obtain ⟨ready, hReadyPos⟩ := cur.advanceLocalAt (pc' := 304)
      (G := fun lane => (1752, b32 idx) :: chosen lane) (fun lane hl =>
        loaderSelectedPrefixIdxLocal hFirst hGroup hEq lane (cur.checkpoint lane hl))
    have hFresh (lane : Nat) (_ : lane < 32) (pair : Nat × Value)
        (hm : pair ∈ (1752, b32 idx) :: chosen lane) : pair.1 ≠ 1753 := by
      intro he
      have hMem := List.mem_map_of_mem (f := Prod.fst) hm
      rw [he] at hMem
      exact (of_decide_eq_true rfl : 1753 ∉ 1752 :: (chosen lane).map Prod.fst) hMem
    have hOut (lane : Nat) (hl : lane < 32) :
        out kernel Assumptions.all l (warpLane l g lane) (ready.state lane) =
          .ev (.shfl .idx (b32 (part lane)) idx 31
            (fun v _ => next (setReg (ready.state lane) 1753 v))) := by
      have ht := ready.checkpoint lane hl
      have hv := holds_lookup ht.2.2.2.2 (show
        (((1752, b32 idx) :: chosen lane).lookup 7163) = some (b32 (part lane)) from rfl)
      exact loaderPrefixIdxTemplate hp hIdx (ht.mono ⟨ht.2.2.2.2.1, hv, trivial⟩)
    have hBefore : WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g ready.pos src index target := fun h => hReadyPos.symm ▸ h
    obtain ⟨read, hAdvance⟩ := ready.consumeShuffleTo hp hX hg .idx (fun lane => b32 (part lane))
      (fun _ => idx) (fun _ => 31) hFresh hOut (hProgress.imp_right hBefore) hPc
    obtain ⟨result, hPos⟩ := read.advanceLocalAt
      (pc' := 306) (G := loaderPrefixFacts p l g warp first batch) (fun lane hl =>
        loaderSelectedPrefixReturnLocal hp hFirst hGroup hBatch hLess lane
          (read.checkpoint lane hl))
    exact ⟨result, fun h => hPos.symm ▸ hAdvance (hBefore h)⟩

/-- The verified selected prefix on a terminated trace. -/
theorem loaderSelectedPrefix {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g warp first batch shuffles votes : Nat}
    (hg : g < l.threads) (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch)
    (cur : SchedulerWarpAt l X g 302 (loaderChosenFacts p l g warp first batch) shuffles votes) :
    Nonempty (SchedulerWarpAt l X g 306 (loaderPrefixFacts p l g warp first batch)
      (shuffles + if first < batch then 1 else 0) votes) := by
  obtain ⟨next, _⟩ := loaderSelectedPrefixTo hp hX hg hFirst hGroup hBatch cur
    (src := 0) (index := 0) (target := ⟨305, .exit⟩) (.inl (fun _ _ => rfl)) (by decide)
  exact ⟨next⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
