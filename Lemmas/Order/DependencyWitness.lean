-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Dependency
public import Core.Assembly.Execution
public import Core.Sync.Aligned
public import Core.Sync.CtaBarrierExecution
public import Core.Sync.ClusterBarrierExecution
public import Core.Sync.WarpBarrier
public import Lemmas.CtaBarrier.CtaBarrierGeneration

@[expose] public section

/-! # Synchronisation edges as dependency witnesses

Bridges from a synchronisation edge of the execution layer to the dependency layer of DEP-ORDER
(`Need`, `Needs`, `Witness`): the arrival of a CTA barrier generation (`CtaBarCounted`), an arrival
of a cluster barrier phase (`ClusterCounted`) and the event of a lane of a `bar.warp.sync` instance
fill a need of the return that waits for them, and so, with `Witness.of_need`, are witnesses of
that return (`DepStep.of_witness`). The corollaries give the `Witness L X (.thread e) f` form that
`Lemmas/Order/GuardOrder.lean` needs, and `ctaBarDone_of_returned` reads the release that a
returned `bar.sync` waits for off `DependencyOk.ready`.

Two adjustments to the requested statements:

* `bar.warp.sync` has no `MaskWait`: Core has no class `Kind → Option (WarpPart Q V)` for it
  (`KindNeeds` gives its needs directly from `X.WarpBar`), and `MaskWait` pairs the events of one
  instance *ordinal* of the lanes of a mask, which a `WarpBarEdge` (one mask and instance label of
  two lanes of one warp) does not fix. `warpBarNeed_of_lane` states the membership that `KindNeeds`
  gives instead, and `Witness.of_warpBarEdge` turns it into a witness.
* `CtaBarCounted` also asks that the arrival's record not follow the record completing the
  generation. `CtaBarrier` relates records only through their generation numbers, so
  `CtaBarCounted.of_arrival` derives that order from the monotonicity of the resource generation
  (`CtaBarrier.run_generation_mono`); it also needs both events in the same CTA (the third clause of
  `SameCta`), which neither `CtaBarArrivalK` nor `CtaBarK` states.
-/

namespace PTX
noncomputable section
variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- A `bar.sync` with a later event in its thread has returned, so the readiness of DEP-ORDER
fills the release condition among its needs: some instance of its CTA has completed (`CtaBarK`,
`CtaBarDone`). -/
theorem ctaBarDone_of_ready (hready : ∀ e, Returned X e → Ready L X e) {e : EvId} {id : Nat}
    {count : Option Nat} {pc : Nat} (hbar : X.IsBarrier e id count pc)
    (hlt : e.2 + 1 < (X.tr e.1).length) :
    ∃ key, CtaBarK L X e key ∧ CtaBarDone L X (e.1 / L.block) key := by
  have hb : X.get e = some ⟨pc, .bar id count .sync⟩ := hbar
  have hret : Returned X e := by
    simp [Returned, hb, Kind.resume, hlt]
  have hmem : Need.cond (∃ key, CtaBarK L X e key ∧ CtaBarDone L X (e.1 / L.block) key) ∈
      Needs L X e := by
    simp only [Needs, hb, KindNeeds, ctaBarNeeds]
    exact List.mem_append_right _ List.mem_cons_self
  exact hready e hret _ hmem

/-- A `bar.sync` with a later event in its thread has returned, so DEP-ORDER fills the release
condition among its needs: some instance of its CTA has completed (`CtaBarK`, `CtaBarDone`). -/
theorem ctaBarDone_of_returned (hX : Consistent L K A mem0 X) {e : EvId} {id : Nat}
    {count : Option Nat} {pc : Nat} (hbar : X.IsBarrier e id count pc)
    (hlt : e.2 + 1 < (X.tr e.1).length) :
    ∃ key, CtaBarK L X e key ∧ CtaBarDone L X (e.1 / L.block) key :=
  ctaBarDone_of_ready hX.dependency.ready hbar hlt

/-- An arrival `e` of generation `key` of a CTA barrier is counted by the release that the
`bar.sync` `f` of the same generation and of the same CTA waits for (`CtaBarCounted`). -/
theorem CtaBarCounted.of_arrival {e f : EvId} {key ic : Nat}
    (hf : CtaBarK L X f key)
    (hc : CtaBarrier.CompletesAt L.block (X.barriers (f.1 / L.block)) ic (key % 16) (key / 16))
    (he : CtaBarArrivalK L X e key) (hcta : e.1 / L.block = f.1 / L.block) :
    CtaBarCounted L X f e := by
  obtain ⟨-, -, i, s, w, n, lanes, g, hi, hat, hmem, hgen, -⟩ := he
  have hcomp := hc
  obtain ⟨rc, sc, tc, hrc, hatc, hperfc, -, hgentc⟩ := hcomp
  rw [hcta] at hi hat
  unfold CtaBarrier.At at hat hatc
  -- the state after the completing record is reached at index `ic + 1`
  have hat1 : CtaBarrier.run L.block {} (List.take (ic + 1) (X.barriers (f.1 / L.block))) =
      Except.ok tc := by
    rw [List.take_succ_eq_append_getElem (List.getElem?_eq_some_iff.mp hrc).1,
      (List.getElem?_eq_some_iff.mp hrc).2, CtaBarrier.run_append, hatc]
    simp only [CtaBarrier.run, hperfc, Except.bind]
  -- the resource generation never decreases (`run_generation_mono`), so the arrival's record
  -- cannot follow the record that completes its own generation
  have hle : i ≤ ic := by
    by_contra hcon
    have hlt : ic < i := Nat.lt_of_not_le hcon
    have hsplit : List.take i (X.barriers (f.1 / L.block)) =
        List.take (ic + 1) (X.barriers (f.1 / L.block)) ++
          List.drop (ic + 1) (List.take i (X.barriers (f.1 / L.block))) := by
      conv_lhs =>
        rw [← List.take_append_drop (ic + 1) (List.take i (X.barriers (f.1 / L.block)))]
      rw [List.take_take, Nat.min_eq_left (by omega)]
    have hrest : CtaBarrier.run L.block tc
        (List.drop (ic + 1) (List.take i (X.barriers (f.1 / L.block)))) = Except.ok s := by
      rw [hsplit, CtaBarrier.run_append, hat1] at hat
      simpa only [Except.bind] using hat
    have hmono := CtaBarrier.run_generation_mono hrest (key % 16)
    rw [hgentc, hgen] at hmono
    omega
  refine ⟨key, ic, hf, hc, i, CtaBarrier.Record.arrival (key % 16) w n lanes, hi, ?_, hle, ?_⟩
  · exact List.mem_map.mpr ⟨(g, e), hmem, rfl⟩
  · exact .inl ⟨w, n, lanes, s, rfl, hat, hgen⟩

/-- The arrival `e` of a generation released by the `bar.sync` `f` is a witness of `f`'s return:
its record is a need of `f` (`ctaBarCounted_witnessed`). -/
theorem Witness.of_ctaBarCounted {e f : EvId} {key ic : Nat}
    (hf : CtaBarK L X f key)
    (hc : CtaBarrier.CompletesAt L.block (X.barriers (f.1 / L.block)) ic (key % 16) (key / 16))
    (he : CtaBarArrivalK L X e key) (hcta : e.1 / L.block = f.1 / L.block) :
    Witness L X (.thread e) f := by
  have harr := he
  obtain ⟨-, ⟨count, pc, hmode⟩, i, s, w, n, lanes, g, hi, -, hmem, -, -⟩ := he
  obtain ⟨mode, hget⟩ := hmode
  obtain ⟨cnt, pc', hbar⟩ := hf.2.1
  have hy : e ∈ (X.barriers (f.1 / L.block)).flatMap CtaBarrier.Record.refs := by
    rw [hcta] at hi
    exact List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hi, List.mem_map.mpr ⟨(g, e), hmem, rfl⟩⟩
  exact Witness.of_need L (ctaBarCounted_witnessed L X f e hbar hy
    (CtaBarCounted.of_arrival hf hc harr hcta)) ⟨_, hget⟩ rfl

/-- An arrival `e` of the phase that the cluster wait `f` observes is counted by the completion of
that phase (`ClusterCounted`); `ClusterBarrier.Synchronizes` names a release arrival of the phase
of a wait. -/
theorem clusterCounted_of_synchronizes {e f : EvId}
    (h : ClusterBarrier.Synchronizes L.block
      (L.clusterSizeAt (L.clusterOfCta (f.1 / L.block)))
      (X.clusters (L.clusterOfCta (f.1 / L.block))) e f) :
    ClusterCounted L X f e := by
  obtain ⟨phase, harrival, hwait⟩ := h
  exact .inl ⟨phase, true, hwait, harrival⟩

/-- An arrival of the phase that a cluster wait observes is a witness of the wait's return: every
arrival of the phase is a need of a waiting `barrier.cluster.wait` (`clusterNeeds`). -/
theorem Witness.of_clusterCounted {e f : EvId} {pc : Nat} {aligned : Bool}
    (hf : X.get f = some ⟨pc, .cluster (.wait aligned)⟩)
    (h : ClusterBarrier.Synchronizes L.block
      (L.clusterSizeAt (L.clusterOfCta (f.1 / L.block)))
      (X.clusters (L.clusterOfCta (f.1 / L.block))) e f)
    (hpres : X.RefPresent (.thread e)) : Witness L X (.thread e) f := by
  classical
  have hcounted := clusterCounted_of_synchronizes (L := L) (X := X) h
  obtain ⟨-, ⟨i, s, t, cta, warp, lanes, g, hi, -, hmem, -, -⟩, -⟩ := h
  have hy : e ∈ (X.clusters (L.clusterOfCta (f.1 / L.block))).flatMap
      ClusterBarrier.Record.refs :=
    List.mem_flatMap.mpr
      ⟨_, List.mem_of_getElem? hi, List.mem_map.mpr ⟨(g, e), hmem, rfl⟩⟩
  have hneed : Need.node (· = .thread e) ∈ Needs L X f := by
    simp only [Needs, hf, KindNeeds, clusterNeeds, needsIf, List.mem_append, List.mem_flatMap]
    exact .inr ⟨e, List.mem_flatMap.mp hy, by simp [hcounted]⟩
  exact Witness.of_need L hneed hpres rfl

/-- Every lane `l` of the member mask of a `bar.warp.sync` event `e` names a need of `e`'s return:
its event with the same mask and instance label, or its exit (`KindNeeds`). -/
theorem warpBarNeed_of_lane {e : EvId} {pc mask inst : Nat}
    (he : X.get e = some ⟨pc, .warpBar mask inst⟩) {l : Nat} (hl : l < 32)
    (hm : mask.testBit l = true) :
    Need.node (fun x => ∃ k, x = .thread (warpLane L e.1 l, k) ∧
      X.WarpBar (warpLane L e.1 l, k) mask inst) ∈ Needs L X e := by
  simp only [Needs, he, KindNeeds, List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨l, ⟨hl, hm⟩, rfl⟩

/-- A `bar.warp.sync` event `i` is a witness of the return of another event `j` of its instance
(`WarpBarEdge`), because every lane of the mask is a member of it (`WarpBarOk`). -/
theorem Witness.of_warpBarEdge {i j : EvId} (hok : WarpBarOk L X) (h : WarpBarEdge L X i j) :
    Witness L X (.thread i) j := by
  obtain ⟨hsw, mask, inst, ⟨pci, hi⟩, ⟨pcj, hj⟩⟩ := h
  obtain ⟨hl, hm⟩ := (hok.1 i mask inst ⟨pci, hi⟩).2
  -- the lane of `i` in the warp of `j` is `i` itself
  have hsym : SameWarp L j.1 i.1 :=
    ⟨⟨hsw.1.2.1, hsw.1.1, hsw.1.2.2.symm⟩, hsw.2.symm⟩
  have hlane : i = (warpLane L j.1 (laneOf L i.1), i.2) :=
    Prod.ext (sameWarp_lane L hsym) rfl
  refine Witness.of_need L (warpBarNeed_of_lane (X := X) (e := j) hj hl hm)
    ⟨_, hi⟩ ⟨i.2, congrArg AsyncCopy.Ref.thread hlane, ?_⟩
  exact hlane ▸ ⟨pci, hi⟩

/-- The counter update a successful poll observed fills a need of the poll's return: the poll's
needs are the counter updates of the phase it observed (`pollNeeds`, DEP-ORDER), whatever its
acquire flag and scope. -/
theorem Witness.of_mbarObserved {x : AsyncCopy.Ref} {w : EvId}
    (h : MbarObserved X x (.thread w)) : Witness L X x w := by
  obtain ⟨hx, j, m, acq, ws, hj, hu, -⟩ := id h
  cases hj
  obtain ⟨⟨pc, par, hwb⟩, hb⟩ := hu
  obtain ⟨i, _, r, _, _, hri, hrid, -⟩ := hb
  refine ⟨(· = r.id), ?_, hx, hrid.symm⟩
  rw [show Needs L X w = pollNeeds X w m by simp only [Needs, hwb, KindNeeds, ite_true]]
  refine List.mem_flatMap.mpr ⟨r, List.mem_of_getElem? hri, ?_⟩
  rw [hrid]
  simp only [needsIf, h, ite_true]
  exact List.mem_singleton.mpr rfl

/-- **A witness of a successful poll is a counter update it observed**: the poll's needs are
the counter updates of the phase it observed (`pollNeeds`). -/
theorem Witness.mbarObserved {x : AsyncCopy.Ref} {w : EvId} (h : Witness L X x w) {pc p : Nat}
    {m : Loc} {acq : Bool} {sc : MbarScope} (hw : X.get w = some ⟨pc, .wait m p true acq sc⟩) :
    MbarObserved X x (.thread w) := by
  obtain ⟨fills, hn, -, hf⟩ := h
  rw [show Needs L X w = pollNeeds X w m by simp only [Needs, hw, KindNeeds, ite_true]] at hn
  obtain ⟨r, -, hr⟩ := List.mem_flatMap.mp hn
  by_cases ho : MbarObserved X r.id (.thread w)
  · simp only [needsIf, ho, ite_true, List.mem_singleton, Need.node.injEq] at hr
    subst hr
    rw [hf]
    exact ho
  · simp [needsIf, ho] at hr

end
end PTX
