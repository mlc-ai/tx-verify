-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueGroupBallotTrace
public import Kernels.TmlFa4Fwd.Proof.SchedulerGroupPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- Stable mathematical inputs which survive the two indexed shuffles. -/
def groupOffsetFrame (p : Params) (cta first batch lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  [(1208, b32 (batch - first)), (7220, b32 (groupLaneTiles p first lane)),
    (1207, b32 (tilePrefix p first * p.heads)), (1072, b32 cta), (7228, b32 batch)] ++
    groupSchedulerFrame p lane F

/-- The exclusive scan prefix is in the register used by tile decomposition. -/
def groupOffsetFacts (p : Params) (cta first batch lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  (7225, b32 (selectedGroupPrefix p first batch)) :: groupOffsetFrame p cta first batch lane F

private def groupBallotRegs : List Nat :=
  [1208, 7228, 294, 7225, 1207, 7223, 7220, 7221, 1072, 268, 7138] ++ schedulerFrameRegs

private theorem groupBallotFacts_regs {p : Params} {cta first batch lane : Nat}
    {F : List (Nat × Value)} (hF : ∀ pair ∈ F, pair.1 ∈ schedulerFrameRegs) :
    ∀ pair ∈ groupBallotFacts p cta first batch lane F, pair.1 ∈ groupBallotRegs := by
  intro pair hm
  simp only [groupBallotFacts, ballotCarry, groupSchedulerFrame, List.cons_append, List.nil_append,
    List.mem_cons] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hm
  all_goals first
    | exact List.mem_append.mpr (.inr (hF pair hm))
    | simp [groupBallotRegs, schedulerFrameRegs]

private theorem groupOffsetFrame_regs {p : Params} {cta first batch lane : Nat}
    {F : List (Nat × Value)} (hF : ∀ pair ∈ F, pair.1 ∈ schedulerFrameRegs) :
    ∀ pair ∈ groupOffsetFrame p cta first batch lane F, pair.1 ≠ 7225 := by
  intro pair hm
  simp only [groupOffsetFrame, groupSchedulerFrame, List.cons_append, List.nil_append,
    List.mem_cons] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hm
  all_goals first
    | exact fun eq => (of_decide_eq_true rfl : 7225 ∉ schedulerFrameRegs) (eq ▸ hF pair hm)
    | exact of_decide_eq_true rfl

private theorem groupOffsetFrame_from_ballot {p : Params} {cta first batch lane : Nat}
    {F : List (Nat × Value)} {r : Nat → Option Value}
    (h : Holds r (groupBallotFacts p cta first batch lane F)) :
    Holds r (groupOffsetFrame p cta first batch lane F) := by
  exact ⟨h.1, h.2.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.1,
    h.2.2.2.2.2.2.2.2.2⟩

private theorem groupTileModel {l : Launch} {g : Nat} {s : TState}
    (hLo : 2892 ≤ s.pc) (hHi : s.pc < 2959) :
    out kernel Assumptions.all l g s = out kernel [] l g s :=
  epilogue_out_all_eq_nil (.inl ⟨by omega, by omega⟩)

private theorem branchTransport {l : Launch} {g pc : Nat} {t u : TState}
    (hPc : t.pc = pc) (hLo : 2892 ≤ pc) (hHi : pc < 2959)
    (hRun : run kernel [] l g 1 t = some u) :
    run kernel Assumptions.all l g 1 t = some u :=
  schedulerLocalTransport (lo := pc) (len := 1) rfl
    (fun hlo hhi => groupTileModel (by omega) (by omega)) hRun (by rw [hPc]) (by rw [hPc])

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Use the zero relative index or the actual preceding lane's shuffle to establish the
selected batch's exclusive prefix. -/
theorem SchedulerWarpAt.selectPrefixTo (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g cta first batch shuffles votes : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 2892 (fun lane => groupBallotFacts p cta first batch lane (F lane))
      shuffles votes ends) (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs)
    {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 2894 < target.pc) :
    ∃ result : SchedulerWarpAt l X g 2896
        (fun lane => groupOffsetFacts p cta first batch lane (F lane))
        (shuffles + if first < batch then 1 else 0) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g result.pos src index target := by
  by_cases hEq : batch = first
  · rw [ite_eq_right (by omega : ¬ first < batch), Nat.add_zero]
    have hLocal : ∃ result : SchedulerWarpAt l X g 2896
        (fun lane => groupOffsetFacts p cta first batch lane (F lane)) shuffles votes ends,
        result.pos = cur.pos := by
      apply cur.advanceLocalAt
      intro lane hl
      have ht := cur.checkpoint lane hl
      have hZero : (294, .pred true) ∈ groupBallotFacts p cta first batch lane (F lane) := by
        simp [groupBallotFacts, hEq]
      obtain ⟨u, hu, hU⟩ := selectFirstRequest l (warpLane l g lane) ht hZero
      have hVal : selectedGroupPrefix p first batch = 0 := by simp [selectedGroupPrefix, hEq]
      have hFacts : At u 2896 (groupOffsetFacts p cta first batch lane (F lane)) :=
        hU.mono ⟨by simpa only [hVal] using hU.2.2.2.2.2.2.2.1,
          groupOffsetFrame_from_ballot hU.2.2.2.2⟩
      exact ⟨u, run_rtg (branchTransport ht.1 (by decide) (by decide) hu), hFacts⟩
    obtain ⟨result, hr⟩ := hLocal
    exact ⟨result, fun h => hr.symm ▸ h⟩
  · have hLT : first < batch := by omega
    rw [ite_eq_left hLT]
    let n := batch - first
    let range := fun lane => groupBallotFacts p cta first batch lane (F lane)
    let idx := fun lane => (2353, b32 (n - 1)) :: range lane
    let a := fun lane => b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)
    let thread := warpLane l g
    have hBlock : l.block % 32 = 0 := by rw [hp.block]
    have hIndex : n - 1 < 32 := by omega
    have hAdvance : ∃ point : SchedulerWarpAt l X g 2894 idx shuffles votes ends,
        point.pos = cur.pos := by
      apply cur.advanceLocalAt
      intro lane hl
      have ht := cur.checkpoint lane hl
      have hPred : (294, .pred false) ∈ range lane := by simp [range, groupBallotFacts, hEq]
      have hFresh : ∀ pair ∈ range lane, pair.1 ≠ 2353 := by
        intro pair hm eq
        exact (of_decide_eq_true rfl : 2353 ∉ groupBallotRegs)
          (eq ▸ groupBallotFacts_regs (hF lane hl) pair hm)
      obtain ⟨u, hu, hU⟩ := selectPreviousLane l (thread lane) (n := n) (by omega) (by omega)
        ht hPred (by simp [n, groupBallotFacts]) hFresh
      obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := thread lane)
        Flow.code_2892 false ht (holds_mem ht.2.2.2.2 hPred) (by simp)
      have hTail : run kernel [] l (thread lane) 1 v = some u := by
        rw [show (2 : Nat) = 1 + 1 from rfl, run_add, hv, Option.bind_some] at hu
        exact hu
      have hFirstStep := branchTransport ht.1 (by decide) (by decide) hv
      have hSecondStep := branchTransport hV.1 (by decide) (by decide) hTail
      exact ⟨u, run_rtg (run_comp hFirstStep hSecondStep), hU⟩
    obtain ⟨atIndex, hIdx⟩ := hAdvance
    have hFree : ∀ lane < 32, ∀ pair ∈ idx lane, pair.1 ≠ 2354 := by
      intro lane hl pair hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact of_decide_eq_true rfl
      · intro eq
        exact (of_decide_eq_true rfl : 2354 ∉ groupBallotRegs)
          (eq ▸ groupBallotFacts_regs (hF lane hl) pair hm)
    have hNext (lane : Nat) (hl : lane < 32) :
        out kernel Assumptions.all l (thread lane) (atIndex.state lane) =
          .ev (.shfl .idx (a lane) (n - 1) 31
            (fun v _ => next (setReg (atIndex.state lane) 2354 v))) := by
      have ht := atIndex.checkpoint lane hl
      have hIndexReg := ht.2.2.2.2.1
      have hSrc : (atIndex.state lane).regs 7221 = some (a lane) :=
        holds_mem ht.2.2.2.2
          (by simp [idx, range, groupBallotFacts, ballotCarry, a])
      exact (groupTileModel (by rw [ht.1]; decide) (by rw [ht.1]; decide)).trans
        (previousPrefixTemplate hp (thread lane) _ _ _ hIndex ht.1 ht.2.2.2.1 hIndexReg hSrc)
    obtain ⟨atPrefix, hAfter⟩ := atIndex.consumeShuffleTo hp hX hg .idx a
      (fun _ => n - 1) (fun _ => 31) hFree hNext
      (hProgress.imp_right (fun h => hIdx.symm ▸ h)) hPc
    have hLocal : ∃ result : SchedulerWarpAt l X g 2896
        (fun lane => groupOffsetFacts p cta first batch lane (F lane)) (shuffles + 1) votes ends,
        result.pos = atPrefix.pos := by
      apply atPrefix.advanceLocalAt
      intro lane hl
      have ht := atPrefix.checkpoint lane hl
      let frame := groupOffsetFrame p cta first batch lane (F lane)
      let sum := ∑ j ∈ Finset.range n, groupLaneTiles p first j
      have hRecv : a (shflSource .idx lane (n - 1) 31).1 = b32 sum := by
        rw [shflSource_idx lane hIndex]
        simp only [a, sum, show n - 1 + 1 = n by omega]
      have hAt : At (atPrefix.state lane) 2895 ((2354, b32 sum) :: frame) :=
        ht.mono ⟨hRecv ▸ ht.2.2.2.2.1, groupOffsetFrame_from_ballot ht.2.2.2.2.2.2⟩
      obtain ⟨u, hu, hU⟩ := selectPreviousWork hp (thread lane) hFirst hGroup hBatch
        (groupOffsetFrame_regs (hF lane hl)) (by simp [groupOffsetFrame, groupSchedulerFrame])
        hAt
      exact ⟨u, run_rtg (branchTransport hAt.1 (by decide) (by decide) hu), hU⟩

    obtain ⟨result, hResult⟩ := hLocal
    exact ⟨result, fun h => hResult.symm ▸ hAfter (hIdx.symm ▸ h)⟩

/-- Use the zero relative index or the actual preceding lane's shuffle to establish the
selected batch's exclusive prefix. -/
theorem SchedulerWarpAt.selectPrefix (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g cta first batch shuffles votes : Nat} (hg : g < l.threads) {F : Nat → List (Nat × Value)}
    (cur : SchedulerWarpAt l X g 2892 (fun lane => groupBallotFacts p cta first batch lane (F lane))
      shuffles votes) (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs) :
    Nonempty (SchedulerWarpAt l X g 2896
      (fun lane => groupOffsetFacts p cta first batch lane (F lane))
      (shuffles + if first < batch then 1 else 0) votes) := by
  obtain ⟨result, _⟩ := cur.selectPrefixTo hp hX hg hFirst hGroup hBatch hF
    (src := 0) (index := 0) (target := ⟨2895, .exit⟩) (.inl (fun _ _ => rfl)) (by decide)
  exact ⟨result⟩

/-- All inputs of the decoded request-local coordinate calculation. -/
def tileCoordinateFacts (p : Params) (cta first batch lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  [(1207, b32 (tilePrefix p first * p.heads)),
    (7225, b32 (selectedGroupPrefix p first batch)), (1072, b32 cta),
    (2355, b32 (requestTiles p batch)), (7138, b32 p.heads), (7155, b32 800),
    (7146, b32 p.batch), (7228, b32 batch)] ++ groupSchedulerFrame p lane F

private theorem parameterStraight :
    ((kernel.code.drop 2896).take 1).all (fun ins => schedulerFallsThrough ins.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

private theorem groupOffsetRegs {p : Params} {cta first batch lane : Nat}
    {F : List (Nat × Value)} (hF : ∀ pair ∈ F, pair.1 ∈ schedulerFrameRegs) :
    ∀ pair ∈ groupOffsetFacts p cta first batch lane F, pair.1 ≠ 7155 ∧
      pair.1 ≠ 7146 ∧ pair.1 ≠ 2355 := by
  intro pair hm
  simp only [groupOffsetFacts, groupOffsetFrame, groupSchedulerFrame, List.cons_append,
    List.nil_append, List.mem_cons] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hm
  all_goals first
    | exact of_decide_eq_true rfl
    | have h := hF pair hm
      simp only [schedulerFrameRegs, List.mem_cons, List.not_mem_nil, or_false] at h
      omega

/-- The actual selected-lane exchange and parameter loads supply the request's tile count. -/
theorem SchedulerWarpAt.selectTileCountTo (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g cta first batch shuffles votes : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 2896 (fun lane => groupOffsetFacts p cta first batch lane (F lane))
      shuffles votes ends) (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs)
    {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 2898 < target.pc) :
    ∃ result : SchedulerWarpAt l X g 2899
        (fun lane => tileCoordinateFacts p cta first batch lane (F lane))
        (shuffles + 1) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g result.pos src index target := by
  let n := batch - first
  let params := fun lane => (7146, b32 p.batch) :: (7155, b32 800) ::
    groupOffsetFacts p cta first batch lane (F lane)
  let a := fun lane => b32 (groupLaneTiles p first lane)
  let thread := warpLane l g
  have hn : n < 32 := by omega
  have hParams : ∃ point : SchedulerWarpAt l X g 2898 params shuffles votes ends,
      point.pos = cur.pos := by
    apply cur.advanceLocalAt
    intro lane hl
    have ht := cur.checkpoint lane hl
    obtain ⟨u, hu, hU⟩ := selectionParameters hp (thread lane) ht
      (fun pair hm => ⟨(groupOffsetRegs (hF lane hl) pair hm).1,
        (groupOffsetRegs (hF lane hl) pair hm).2.1⟩)
    have hActual := schedulerLocalTransport (A := Assumptions.all) (lo := 2896) (len := 2)
      parameterStraight (fun hlo hhi => groupTileModel (by omega) (by omega)) hu
      (by rw [ht.1]) (by rw [ht.1])
    exact ⟨u, run_rtg hActual, hU⟩
  obtain ⟨atParams, hPos⟩ := hParams
  have hFresh : ∀ lane < 32, ∀ pair ∈ params lane, pair.1 ≠ 2355 := by
    intro lane hl pair hm
    simp only [params, List.mem_cons] at hm
    rcases hm with rfl | rfl | hm
    · exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
    · exact (groupOffsetRegs (hF lane hl) pair hm).2.2
  have hNext (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (thread lane) (atParams.state lane) =
        .ev (.shfl .idx (a lane) n 31 (fun v _ => next (setReg (atParams.state lane) 2355 v))) := by
    have ht := atParams.checkpoint lane hl
    have hRelative := holds_mem ht.2.2.2.2
      (by simp [params, groupOffsetFacts, groupOffsetFrame, n] : (1208, b32 n) ∈ params lane)
    have hTile := holds_mem ht.2.2.2.2
      (by simp [params, groupOffsetFacts, groupOffsetFrame, a] : (7220, a lane) ∈ params lane)
    exact (groupTileModel (by rw [ht.1]; decide) (by rw [ht.1]; decide)).trans
      (selectedRequestTiles hp (thread lane) _ _ _ hn ht.1 ht.2.2.2.1 hRelative hTile)
  obtain ⟨atCount, hAfter⟩ := atParams.consumeShuffleTo hp hX hg .idx a (fun _ => n) (fun _ => 31)
    hFresh hNext (hProgress.imp_right (fun h => hPos.symm ▸ h)) hPc
  have hLocal : ∃ result : SchedulerWarpAt l X g 2899
      (fun lane => tileCoordinateFacts p cta first batch lane (F lane))
      (shuffles + 1) votes ends, result.pos = atCount.pos := by
    apply atCount.advanceLocalAt
    intro lane hl
    have ht := atCount.checkpoint lane hl
    have hSelected : a (shflSource .idx lane n 31).1 = b32 (requestTiles p batch) := by
      rw [shflSource_idx lane hn]
      simp [a, n, groupLaneTiles, Nat.add_sub_of_le hFirst, hBatch,
        show batch - first < 31 by omega]
    have hArgs := ht.2.2.2.2
    have hData := hArgs.2.2.2
    have hFrame := hData.2.2.2.2.2.2
    exact ⟨atCount.state lane, .refl, ht.mono ⟨hData.2.2.2.1, hData.1, hData.2.2.2.2.1,
      hSelected ▸ hArgs.1, hFrame.2.1, hArgs.2.2.1, hArgs.2.1, hData.2.2.2.2.2.1, hFrame⟩⟩

  obtain ⟨result, hr⟩ := hLocal
  exact ⟨result, fun h => hr.symm ▸ hAfter (hPos.symm ▸ h)⟩

/-- The actual selected-lane exchange and parameter loads supply the request's tile count. -/
theorem SchedulerWarpAt.selectTileCount (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g cta first batch shuffles votes : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)}
    (cur : SchedulerWarpAt l X g 2896 (fun lane => groupOffsetFacts p cta first batch lane (F lane))
      shuffles votes) (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs) :
    Nonempty (SchedulerWarpAt l X g 2899
      (fun lane => tileCoordinateFacts p cta first batch lane (F lane)) (shuffles + 1) votes) := by
  obtain ⟨result, _⟩ := cur.selectTileCountTo hp hX hg hFirst hGroup hBatch hF
    (src := 0) (index := 0) (target := ⟨2899, .exit⟩) (.inl (fun _ _ => rfl)) (by decide)
  exact ⟨result⟩

/-- A successful cutoff identifies the unique selected request and the actual coordinate cursor. -/
theorem SchedulerWarpAt.chooseTile (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g cta first shuffles votes : Nat} (hg : g < l.threads) {F : Nat → List (Nat × Value)}
    (cur : SchedulerWarpAt l X g 2883 (fun lane => groupChoiceFacts p cta first lane (F lane))
      shuffles votes) (hLow : tilePrefix p first * p.heads ≤ cta)
    (hHigh : cta < tilePrefix p (min p.batch (first + 31)) * p.heads)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs) :
    ∃ batch, first ≤ batch ∧ batch < first + 31 ∧ batch < p.batch ∧
      tilePrefix p batch * p.heads ≤ cta ∧ cta < tilePrefix p (batch + 1) * p.heads ∧
      Nonempty (SchedulerWarpAt l X g 2899
        (fun lane => tileCoordinateFacts p cta first batch lane (F lane))
        ((shuffles + if first < batch then 1 else 0) + 1) (votes + 1)) := by
  obtain ⟨batch, ⟨hFirst, hGroup, hBatch, hLo, hHi⟩, _⟩ :=
    groupContains_request p hLow hHigh
  obtain ⟨atVote⟩ := cur.selectBallot hp hX hg hFirst hGroup hBatch hLo hHi hF
  obtain ⟨atPrefix⟩ := atVote.selectPrefix hp hX hg hFirst hGroup hBatch hF
  exact ⟨batch, hFirst, hGroup, hBatch, hLo, hHi,
    atPrefix.selectTileCount hp hX hg hFirst hGroup hBatch hF⟩

/-- A successful cutoff identifies the unique selected request and the actual coordinate cursor. -/
theorem SchedulerWarpAt.chooseTileTo (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g cta first shuffles votes : Nat} (hg : g < l.threads) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 2883 (fun lane => groupChoiceFacts p cta first lane (F lane))
      shuffles votes ends) (hLow : tilePrefix p first * p.heads ≤ cta)
    (hHigh : cta < tilePrefix p (min p.batch (first + 31)) * p.heads)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs) {src index : Nat}
    {target : Event} (hFollow : WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 2898 < target.pc) :
    ∃ batch, first ≤ batch ∧ batch < first + 31 ∧ batch < p.batch ∧
      tilePrefix p batch * p.heads ≤ cta ∧ cta < tilePrefix p (batch + 1) * p.heads ∧
      ∃ result : SchedulerWarpAt l X g 2899
          (fun lane => tileCoordinateFacts p cta first batch lane (F lane))
          ((shuffles + if first < batch then 1 else 0) + 1) (votes + 1) ends,
        WarpFollowsEvent l X g result.pos src index target := by
  obtain ⟨batch, ⟨hFirst, hGroup, hBatch, hLo, hHi⟩, _⟩ :=
    groupContains_request p hLow hHigh
  obtain ⟨atVote, hv⟩ := cur.selectBallotTo hp hX hg hFirst hGroup hBatch hLo hHi hF
    (.inr hFollow) (by omega)
  have hVoted := hv hFollow
  obtain ⟨atPrefix, hs⟩ :=
    atVote.selectPrefixTo hp hX hg hFirst hGroup hBatch hF (.inr hVoted) (by omega)
  have hPref := hs hVoted
  obtain ⟨result, ht⟩ :=
    atPrefix.selectTileCountTo hp hX hg hFirst hGroup hBatch hF (.inr hPref) hPc
  exact ⟨batch, hFirst, hGroup, hBatch, hLo, hHi, result, ht hPref⟩

/-- The maximal execution supplies the preceding selected lane when the group offset needs it. -/
theorem SchedulerWarpReached.selectPrefixOfMaximal (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g cta first batch shuffles votes : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2892
      (fun lane => groupBallotFacts p cta first batch lane (F lane))
      shuffles votes ends) (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs)
    : Nonempty (SchedulerWarpReached l X g 2896
        (fun lane => groupOffsetFacts p cta first batch lane (F lane))
        (shuffles + if first < batch then 1 else 0) votes ends) := by
  by_cases hEq : batch = first
  · rw [ite_eq_right (by omega : ¬ first < batch), Nat.add_zero]
    apply cur.advanceLocal
    intro lane hl
    have ht := cur.checkpoint lane hl
    have hZero : (294, .pred true) ∈ groupBallotFacts p cta first batch lane (F lane) := by
      simp [groupBallotFacts, hEq]
    obtain ⟨u, hu, hU⟩ := selectFirstRequest l (warpLane l g lane) ht hZero
    have hVal : selectedGroupPrefix p first batch = 0 := by simp [selectedGroupPrefix, hEq]
    have hFacts : At u 2896 (groupOffsetFacts p cta first batch lane (F lane)) :=
      hU.mono ⟨by simpa only [hVal] using hU.2.2.2.2.2.2.2.1,
        groupOffsetFrame_from_ballot hU.2.2.2.2⟩
    exact ⟨u, run_rtg (branchTransport ht.1 (by decide) (by decide) hu), hFacts⟩
  · have hLT : first < batch := by omega
    rw [ite_eq_left hLT]
    let n := batch - first
    let range := fun lane => groupBallotFacts p cta first batch lane (F lane)
    let idx := fun lane => (2353, b32 (n - 1)) :: range lane
    let a := fun lane => b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)
    let thread := warpLane l g
    have hIndex : n - 1 < 32 := by omega
    obtain ⟨atIndex⟩ := cur.advanceLocal (pc' := 2894) (G := idx) (by
      intro lane hl
      have ht := cur.checkpoint lane hl
      have hPred : (294, .pred false) ∈ range lane := by simp [range, groupBallotFacts, hEq]
      have hFresh : ∀ pair ∈ range lane, pair.1 ≠ 2353 := by
        intro pair hm eq
        exact (of_decide_eq_true rfl : 2353 ∉ groupBallotRegs)
          (eq ▸ groupBallotFacts_regs (hF lane hl) pair hm)
      obtain ⟨u, hu, hU⟩ := selectPreviousLane l (thread lane) (n := n) (by omega) (by omega)
        ht hPred (by simp [n, groupBallotFacts]) hFresh
      obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := thread lane)
        Flow.code_2892 false ht (holds_mem ht.2.2.2.2 hPred) (by simp)
      have hTail : run kernel [] l (thread lane) 1 v = some u := by
        rw [show (2 : Nat) = 1 + 1 from rfl, run_add, hv, Option.bind_some] at hu
        exact hu
      have hFirstStep := branchTransport ht.1 (by decide) (by decide) hv
      have hSecondStep := branchTransport hV.1 (by decide) (by decide) hTail
      exact ⟨u, run_rtg (run_comp hFirstStep hSecondStep), hU⟩)
    have hFree : ∀ lane < 32, ∀ pair ∈ idx lane, pair.1 ≠ 2354 := by
      intro lane hl pair hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact of_decide_eq_true rfl
      · intro eq
        exact (of_decide_eq_true rfl : 2354 ∉ groupBallotRegs)
          (eq ▸ groupBallotFacts_regs (hF lane hl) pair hm)
    have hNext (lane : Nat) (hl : lane < 32) :
        out kernel Assumptions.all l (thread lane) (atIndex.state lane) =
          .ev (.shfl .idx (a lane) (n - 1) 31
            (fun v _ => next (setReg (atIndex.state lane) 2354 v))) := by
      have ht := atIndex.checkpoint lane hl
      have hIndexReg := ht.2.2.2.2.1
      have hSrc : (atIndex.state lane).regs 7221 = some (a lane) :=
        holds_mem ht.2.2.2.2
          (by simp [idx, range, groupBallotFacts, ballotCarry, a])
      exact (groupTileModel (by rw [ht.1]; decide) (by rw [ht.1]; decide)).trans
        (previousPrefixTemplate hp (thread lane) _ _ _ hIndex ht.1 ht.2.2.2.1 hIndexReg hSrc)
    obtain ⟨atPrefix⟩ := atIndex.consumeShuffle hp hMax hg .idx a
      (fun _ => n - 1) (fun _ => 31) hFree hNext
    apply atPrefix.advanceLocal
    intro lane hl
    have ht := atPrefix.checkpoint lane hl
    let frame := groupOffsetFrame p cta first batch lane (F lane)
    let sum := ∑ j ∈ Finset.range n, groupLaneTiles p first j
    have hRecv : a (shflSource .idx lane (n - 1) 31).1 = b32 sum := by
      rw [shflSource_idx lane hIndex]
      simp only [a, sum, show n - 1 + 1 = n by omega]
    have hAt : At (atPrefix.state lane) 2895 ((2354, b32 sum) :: frame) :=
      ht.mono ⟨hRecv ▸ ht.2.2.2.2.1, groupOffsetFrame_from_ballot ht.2.2.2.2.2.2⟩
    obtain ⟨u, hu, hU⟩ := selectPreviousWork hp (thread lane) hFirst hGroup hBatch
      (groupOffsetFrame_regs (hF lane hl)) (by simp [groupOffsetFrame, groupSchedulerFrame])
      hAt
    exact ⟨u, run_rtg (branchTransport hAt.1 (by decide) (by decide) hu), hU⟩

/-- The selected tile count shuffle records the request's exact count in every lane. -/
theorem SchedulerWarpReached.selectTileCountOfMaximal (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g cta first batch shuffles votes : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2896
      (fun lane => groupOffsetFacts p cta first batch lane (F lane))
      shuffles votes ends) (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs)
    : Nonempty (SchedulerWarpReached l X g 2899
        (fun lane => tileCoordinateFacts p cta first batch lane (F lane))
        (shuffles + 1) votes ends) := by
  let n := batch - first
  let params := fun lane => (7146, b32 p.batch) :: (7155, b32 800) ::
    groupOffsetFacts p cta first batch lane (F lane)
  let a := fun lane => b32 (groupLaneTiles p first lane)
  let thread := warpLane l g
  have hn : n < 32 := by omega
  obtain ⟨atParams⟩ := cur.advanceLocal (pc' := 2898) (G := params) (by
    intro lane hl
    have ht := cur.checkpoint lane hl
    obtain ⟨u, hu, hU⟩ := selectionParameters hp (thread lane) ht
      (fun pair hm => ⟨(groupOffsetRegs (hF lane hl) pair hm).1,
        (groupOffsetRegs (hF lane hl) pair hm).2.1⟩)
    have hActual := schedulerLocalTransport (A := Assumptions.all) (lo := 2896) (len := 2)
      parameterStraight (fun hlo hhi => groupTileModel (by omega) (by omega)) hu
      (by rw [ht.1]) (by rw [ht.1])
    exact ⟨u, run_rtg hActual, hU⟩)
  have hFresh : ∀ lane < 32, ∀ pair ∈ params lane, pair.1 ≠ 2355 := by
    intro lane hl pair hm
    simp only [params, List.mem_cons] at hm
    rcases hm with rfl | rfl | hm
    · exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
    · exact (groupOffsetRegs (hF lane hl) pair hm).2.2
  have hNext (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (thread lane) (atParams.state lane) =
        .ev (.shfl .idx (a lane) n 31 (fun v _ => next (setReg (atParams.state lane) 2355 v))) := by
    have ht := atParams.checkpoint lane hl
    have hRelative := holds_mem ht.2.2.2.2
      (by simp [params, groupOffsetFacts, groupOffsetFrame, n] : (1208, b32 n) ∈ params lane)
    have hTile := holds_mem ht.2.2.2.2
      (by simp [params, groupOffsetFacts, groupOffsetFrame, a] : (7220, a lane) ∈ params lane)
    exact (groupTileModel (by rw [ht.1]; decide) (by rw [ht.1]; decide)).trans
      (selectedRequestTiles hp (thread lane) _ _ _ hn ht.1 ht.2.2.2.1 hRelative hTile)
  obtain ⟨atCount⟩ := atParams.consumeShuffle hp hMax hg .idx a (fun _ => n) (fun _ => 31)
    hFresh hNext
  apply atCount.advanceLocal
  intro lane hl
  have ht := atCount.checkpoint lane hl
  have hSelected : a (shflSource .idx lane n 31).1 = b32 (requestTiles p batch) := by
    rw [shflSource_idx lane hn]
    simp [a, n, groupLaneTiles, Nat.add_sub_of_le hFirst, hBatch,
      show batch - first < 31 by omega]
  have hArgs := ht.2.2.2.2
  have hData := hArgs.2.2.2
  have hFrame := hData.2.2.2.2.2.2
  exact ⟨atCount.state lane, .refl, ht.mono ⟨hData.2.2.2.1, hData.1, hData.2.2.2.2.1,
    hSelected ▸ hArgs.1, hFrame.2.1, hArgs.2.2.1, hArgs.2.1, hData.2.2.2.2.2.1, hFrame⟩⟩

/-- An active interval reaches the exact output tile and head via maximal scheduler steps. -/
theorem SchedulerWarpReached.chooseTileOfMaximal (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g cta first shuffles votes : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2883 (fun lane => groupChoiceFacts p cta first lane (F lane))
      shuffles votes ends) (hLow : tilePrefix p first * p.heads ≤ cta)
    (hHigh : cta < tilePrefix p (min p.batch (first + 31)) * p.heads)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs) :
    ∃ batch, first ≤ batch ∧ batch < first + 31 ∧ batch < p.batch ∧
      tilePrefix p batch * p.heads ≤ cta ∧ cta < tilePrefix p (batch + 1) * p.heads ∧
      Nonempty (SchedulerWarpReached l X g 2899
        (fun lane => tileCoordinateFacts p cta first batch lane (F lane))
        ((shuffles + if first < batch then 1 else 0) + 1) (votes + 1) ends) := by
  obtain ⟨batch,⟨hFirst,hGroup,hBatch,hLo,hHi⟩,_⟩ := groupContains_request p hLow hHigh
  obtain ⟨vote⟩ := cur.selectBallotOfMaximal hp hMax hg hFirst hGroup hBatch hLo hHi hF
  obtain ⟨atPrefix⟩ := vote.selectPrefixOfMaximal hp hMax hg hFirst hGroup hBatch hF
  exact ⟨batch,hFirst,hGroup,hBatch,hLo,hHi,
    atPrefix.selectTileCountOfMaximal hp hMax hg hFirst hGroup hBatch hF⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
