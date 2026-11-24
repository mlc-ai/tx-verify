-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputVisits
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierCount
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputPublication

@[expose] public section

/-! # From an output tensor byte to its ordered staging write -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputReadOrder

open PTX Wg0

private instance : Fact kernel.NoBarArrive := ⟨by unfold Kernel.NoBarArrive; decide +kernel⟩

private theorem stage_group (j : Fin 4) (w : Fin 2) :
    stageGroup (planeAdd j.val + 2 * w.val) = j.val := by
  fin_cases j <;> fin_cases w <;> decide

private theorem writerOfSlot {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) (hg : g < L.threads) (hw : warpOf L g < 2)
    (j : Fin 4) (s : Result.OutputSlot) :
    let c := tmaX j.val (warpOf L g) + s.1.val
    ∃ (writer : Nat) (k : Fin 8) (sub pos : Fin 4),
      SameCta L writer g ∧ wgOf L writer = 0 ∧ head L writer = s.2.1.val ∧
      (shLoc L writer (stageWrite L writer j.val k.val sub.val)).at pos.val =
        shLoc L g (stageOff s.2.1.val c + s.2.2.val) := by
  let w : Fin 2 := ⟨warpOf L g, hw⟩
  let c := tmaX j.val w.val + s.1.val
  let warp := 2 * stageHalf (c / 64) + s.2.1.val / 32
  let thread := 32 * warp + s.2.1.val % 32
  let writer := ctaOf L g * L.block + thread
  have hx := s.1.isLt
  have hh := s.2.1.isLt
  have hbyte := s.2.2.isLt
  have hc : c < 512 := Result.outputColumn_lt j hw hx
  have hplane : c / 64 = planeAdd j.val + 2 * w.val := by unfold c tmaX; omega
  have hgroup : stageGroup (c / 64) = j.val := by
    rw [hplane]
    exact stage_group j w
  have hhalfBound : stageHalf (c / 64) < 2 := by unfold stageHalf; omega
  have hthread : thread < 128 := by unfold thread warp; omega
  have hlocal : thread < L.block := by rw [hpre.block]; omega
  have hcta : ctaOf L writer = ctaOf L g := by
    change (ctaOf L g * L.block + thread) / L.block = _
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt hlocal),
      Nat.div_eq_of_lt hlocal, Nat.zero_add]
  have htid : tidOf L writer = thread := by
    rw [tidOf_eq hpre]
    unfold writer
    rw [hpre.block]
    omega
  have hg' : writer < L.threads := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hlocal
  have hwg : wgOf L writer = 0 := by unfold wgOf; rw [htid]; omega
  have hhead : head L writer = s.2.1.val := by
    unfold head
    rw [htid]
    unfold thread warp
    omega
  have hhalf : half L writer = stageHalf (c / 64) := by
    unfold half warpOf
    rw [htid]
    unfold thread warp
    omega
  let k : Fin 8 := ⟨(c % 64) / 8, by omega⟩
  let sub : Fin 4 := ⟨(c % 8) / 2, by omega⟩
  let pos : Fin 4 := ⟨2 * ((c % 8) % 2) + s.2.2.val, by omega⟩
  refine ⟨writer, k, sub, pos, ⟨hg', hg, hcta⟩, hwg, hhead, ?_⟩
  have hloc := stageOff_eq_stageWrite hc hhalf hhead
  rw [hgroup] at hloc
  change (shLoc L writer (stageWrite L writer j.val k.val sub.val)).at pos.val =
    shLoc L g (stageOff s.2.1.val c + s.2.2.val)
  simp only [Loc.at, hloc, shLoc, hcta, k, sub, pos, Nat.add_assoc]

private theorem barrier_event {X : Execution} {g i : Nat} {e : Event}
    (he : X.get (g, i) = some e) (hk : e.kind = .bar 9 (some 128) .sync) :
    ∃ site, X.IsBarrier (g, i) 9 (some 128) site := by
  obtain ⟨site, _⟩ := e
  cases hk
  exact ⟨site, he⟩

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat} {address : Nat}
    {sp : TensorStore.Spec} {d : D} {j : Fin 4}

/-- Every byte read by an actual output tile has an actual staging write ordered before that
read through the writer's proxy fence and the passed tile barrier of the issuing lane. -/
theorem of_prefix_issue (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.TensorStoreIssue (g, i) address sp)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hj : d.site = .tmaStore j)
    (s : Result.OutputSlot) :
    let l := shLoc L g (stageOff s.2.1.val (tmaX j.val (warpOf L g) + s.1.val) + s.2.2.val)
    ∃ (writer b : Nat) (d' : D) (a : Acc) (k : Fin 8) (sub pos : Fin 4),
      Frame.stateAt (Machine.code P L) X writer b = some (some (.wg0 d')) ∧
      d'.site = .oStage j k ∧ d'.sub = sub.val ∧ head L writer = s.2.1.val ∧
      X.Writes (writer, b) a (stagePair P L writer d' (4 * k.val + sub.val)).toBytes ∧
      a.loc.at pos.val = l ∧ a.Covers l ∧
      modelCausality L X l (.thread (writer, b)) (.async (g, i)
        (.read (.store s.1.val s.2.1.val s.2.2.val))) := by
  obtain ⟨issueSite, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  have hlen : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hw := Wg0OutputControl.outputWarp hX (hs g hg) he hd hj
  obtain ⟨writer, k, sub, pos, hcta, hwg, hhead, hgeom⟩ := writerOfSlot hpre hg hw j s
  obtain ⟨bIssue, ei, di, hbi, hei, hki, hsi, hji⟩ :=
    Wg0OutputControl.barrierBeforeIssue hpre hX (hs g hg) hlen hd hj
  obtain ⟨si, hib⟩ := barrier_event hei hki
  have hrow : blocksOf P L writer = blocksOf P L g := by
    have hc : ctaOf L writer = ctaOf L g := hcta.2.2
    simp only [blocksOf, eOf, ctaidY, hc]
  have hoi := Wg0BarrierCount.epiOrdinal hpre hX (hs g hg) hei hsi hji
  have hPassed : bIssue + 1 < (X.tr g).length := by omega
  have hMember : (writer % L.block) / 32 ∈ OutputPublication.stagingWarps := by
    have hWarp : warpOf L writer < 4 := by unfold wgOf at hwg; unfold warpOf; omega
    simpa only [OutputPublication.stagingWarps, Finset.mem_range, warpOf, tidOf_eq hpre,
      hpre.block] using hWarp
  have hExit (hex : ∃ n tag, X.get (writer, n) = some ⟨tag, .exit⟩) :
      ∃ wb wt, X.IsBarrier (writer, wb) 9 (some 128) wt ∧
        ((X.tr writer).take wb).countP (Execution.isBarId 9) =
          ((X.tr g).take bIssue).countP (Execution.isBarId 9) := by
    obtain ⟨ex, tag, he⟩ := hex
    have hDone := Wg0OutputVisits.doneAtExit hX (hs writer hcta.1) ht hwg he rfl
    obtain ⟨b, _, dw, ew, hsw, hjw, hew, hkw⟩ :=
      Wg0OutputVisits.barrierBeforeDone hpre hX hcta.1 (hs writer hcta.1) hwg hDone j
    obtain ⟨wt, hb⟩ := barrier_event hew hkw
    have how := Wg0BarrierCount.epiOrdinal hpre hX (hs writer hcta.1) hew hsw hjw
    exact ⟨b, wt, hb, how.trans (by rw [hrow, ← hoi])⟩
  obtain ⟨bWriter, sw, hwb, hord⟩ := (OutputPublication.sources hpre hX hs ht).member_arrival
    hX (OutputPublication.shape hpre) hib hPassed hcta.2.2 hMember hExit
  obtain ⟨dw, hsw, hjw⟩ := Wg0BarrierCount.epiSite_of_ordinal hpre hX (hs writer hcta.1)
    ht hwb rfl (by rw [hord, hoi, hrow])
  have hbw : bWriter < (X.tr writer).length := PTX.len_of_get hwb
  obtain ⟨fence, hfb, hf, b, hbf, e, ds, a, hwrite, hst, hjw, hsub, hkind, ha, hsize⟩ :=
    Wg0OutputVisits.stagedBeforeBarrier hpre hX hcta.1 (hs writer hcta.1) hwg hbw hsw hjw k sub
  let l := shLoc L g (stageOff s.2.1.val (tmaX j.val (warpOf L g) + s.1.val) + s.2.2.val)
  have hloc : a.loc.at pos.val = l := by rw [ha]; exact hgeom
  have hcovers : a.Covers l := by
    rw [← hloc]
    refine ⟨rfl, rfl, by simp [Loc.at], ?_⟩
    simp only [Loc.at, hsize]
    have hp := pos.isLt
    omega
  have hwrites : X.Writes (writer, b) a
      (stagePair P L writer ds (4 * k.val + sub.val)).toBytes := by
    obtain ⟨tag, _⟩ := e
    cases hkind
    exact ⟨tag, hwrite⟩
  have hproxy : ProxyBefore L X (writer, b) (g, i) l :=
    OutputPublication.proxyBefore hpre hX hs ht hcta ⟨rfl, hcta.2.2.symm⟩
      hf hwb hib hord hbf (by omega) (by omega) hlen
  obtain ⟨_, hread, _⟩ := Wg0OutputTrace.tileFootprint hpre hX (hs g hg)
    ⟨issueSite, he⟩ hd hj hw s
  refine ⟨writer, b, ds, a, k, sub, pos, hst, hjw, hsub, hhead, hwrites, hloc, hcovers, ?_⟩
  refine ⟨⟨⟨l, 1, false, false, .cta, 0, false⟩, false, ?_, ?_⟩, .inl hproxy⟩
  · exact ⟨rfl, sp, address, ⟨issueSite, he⟩, hread, rfl⟩
  · exact ⟨rfl, rfl, Nat.le_refl _, by change l.addr < l.addr + 1; omega⟩

/-- Every byte read by an actual output tile has an actual staging write ordered before that
read through the writer's proxy fence and the matching tile barrier. -/
theorem of_issue (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (_hcomplete : Complete L X) (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hi : X.TensorStoreIssue (g, i) address sp)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hj : d.site = .tmaStore j)
    (s : Result.OutputSlot) :
    let l := shLoc L g (stageOff s.2.1.val (tmaX j.val (warpOf L g) + s.1.val) + s.2.2.val)
    ∃ (writer b : Nat) (d' : D) (a : Acc) (k : Fin 8) (sub pos : Fin 4),
      Frame.stateAt (Machine.code P L) X writer b = some (some (.wg0 d')) ∧
      d'.site = .oStage j k ∧ d'.sub = sub.val ∧ head L writer = s.2.1.val ∧
      X.Writes (writer, b) a (stagePair P L writer d' (4 * k.val + sub.val)).toBytes ∧
      a.loc.at pos.val = l ∧ a.Covers l ∧
      modelCausality L X l (.thread (writer, b)) (.async (g, i)
        (.read (.store s.1.val s.2.1.val s.2.2.val))) :=
  of_prefix_issue hpre hX hs ht hi hd hj s

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputReadOrder
