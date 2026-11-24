-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.IpTmCount
public import Kernels.InklingRelDecode.Proof.Interface.ExitFacts
public import Kernels.InklingRelDecode.Proof.Interface.Reach
public import Kernels.InklingRelDecode.Proof.Interface.ShapeTrace
public import Kernels.InklingRelDecode.Proof.Interface.FootClass
public import Kernels.InklingRelDecode.Proof.Interface.LockBar0
public import Lemmas.Tmem.PairProtocol

@[expose] public section

/-!
# The paired Tensor Memory operations of every thread

The thread layer's classification of the `tcgen05` resource events of an execution
(`Tmem1Ops`, the development notes, "Protocol `Tmem`"), from the measure of the abstract states of
`Thread/IpTmCount.lean`:

* `res_event_state`: a resource event fires from the common start's allocation, the common start's
  permit relinquishment (`DStart.Site.alloc`, `relinq`, of a thread of warp 0) or the epilogue's
  deallocation (`Epi.Site.dealloc`, of a thread whose guard `%p3` holds), with the request the
  site's shape gives and the group `.one`;
* `tmops_inv`: along a thread, the number of its earlier paired operations is `tCnt` of the
  state: 0, 1, 2 and 3 at the sites of the common start, the prologue, the softmax region and the
  epilogue, and 0 for every thread outside warp 0;
* `res_event`: the n-th paired operation of a thread has the shape `n` of warp 0;
* `exit_ops`: a thread of warp 0 has made three paired operations before its exit.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.IpTm Tmem.Pair

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The paired operations a thread has made before the event of a state: the default partition's
`dCnt`, none for a worker. -/
def tCnt (L : Launch) (g : Nat) : TSt → Nat
  | .d s => dCnt L g s
  | .w _ => 0

/-- The states that fire a paired Tensor Memory operation of a thread of warp 0. -/
def ResState : DComp.St → Prop
  | .dstart d => d.site = .alloc ∨ d.site = .relinq
  | .epi d => d.site = .dealloc
  | _ => False

theorem dInc_eq_one {s : DComp.St} (h : ResState s) : dInc s = 1 := by
  cases s with
  | dstart d => rcases h with h | h <;> simp [dInc, h]
  | epi d =>
    have h' : d.site = .dealloc := h
    simp [dInc, h']
  | pro d => exact h.elim
  | sm d => exact h.elim

theorem dInc_eq_zero {s : DComp.St} (h : ¬ ResState s) : dInc s = 0 := by
  cases s with
  | dstart d =>
    simp only [ResState, not_or] at h
    obtain ⟨site, tm⟩ := d
    cases site <;> simp_all [dInc]
  | epi d => simp_all [dInc, ResState]
  | pro d => rfl
  | sm d => rfl

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- **A resource event fires from the allocation, the relinquishment or the deallocation**, in
the machine of a thread of warp 0 whose guard holds. -/
theorem res_event_state {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request}
    (he : X.get (g, k) = some ⟨pc, .tc (.resource grp dst act)⟩) :
    g % L.block < 32 ∧
      ((∃ tm, St Q L X g k = some (some (.d (.dstart ⟨.alloc, tm⟩))) ∧ grp = .one ∧
          act = .alloc 512) ∨
       (∃ tm, St Q L X g k = some (some (.d (.dstart ⟨.relinq, tm⟩))) ∧ grp = .one ∧
          act = .relinquish) ∨
       (∃ d : Epi.D, St Q L X g k = some (some (.d (.epi d))) ∧ d.site = .dealloc ∧
          grp = .one ∧ act = .dealloc d.pr.tm 512)) := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hne : ∀ pc' f, (⟨pc, .tc (.resource grp dst act)⟩ : Event) ≠ ⟨pc', .ub f⟩ := by
    intro pc' f h
    simp only [Event.mk.injEq] at h
    cases h.2
  obtain ⟨s, hσ⟩ := Frame.event_state hf.sound hX hf.tracked he hne
  obtain ⟨t, ins, o, -, hinv, hc, hfire⟩ := Frame.fired_site hf.sound hX he hσ
  have hop : tmemOp ins.op = true := fires_resource_op hfire rfl
  have hpc : TSt.pc s ∈ resPcs := OpPcsFast.mem kernel_res_pcs hc hop
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hSh := ProA.sharedOk_of_pre hpre
  have hreach := hf.reach hg hσ
  cases s with
  | w s => exact absurd hpc (worker_notRes s)
  | d s =>
    obtain ⟨hdef, hI⟩ := hinv
    have hxs : ¬ ExitState (.d s) := by
      intro hx
      cases s with
      | epi d =>
        have h1 : d.site = .exit := hx
        have h2 : d.site.pc ∈ resPcs := hpc
        rw [h1] at h2
        revert h2
        decide +kernel
      | _ => exact hx
    obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ hxs
    cases s with
    | dstart d =>
      obtain ⟨hI1, -⟩ := hI
      have hs : d.site ∈ ([.alloc, .allocWr, .relinq] : List DStart.Site) :=
        dstart_res_pc d.site hpc
      have hshape := DStart.shape_of_pre hpre (fired_dstart hF)
      obtain ⟨site, tm⟩ := d
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl
      · refine ⟨hI1.lane0 (.inl rfl), .inl ⟨tm, hσ, ?_, ?_⟩⟩
        · simp only [DStart.Shape] at hshape
          simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hshape
          exact hshape.2.1
        · simp only [DStart.Shape] at hshape
          simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hshape
          exact hshape.2.2.2
      · exfalso
        simp only [DStart.Shape] at hshape
        obtain ⟨col, -, hshape⟩ := hshape
        simp only [Event.mk.injEq] at hshape
        cases hshape.2
      · refine ⟨hI1.lane0 (.inr (.inr rfl)), .inr (.inl ⟨tm, hσ, ?_, ?_⟩)⟩
        · simp only [DStart.Shape] at hshape
          simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hshape
          exact hshape.2.1
        · simp only [DStart.Shape] at hshape
          simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hshape
          exact hshape.2.2.2
    | pro d => exact absurd hpc (fun h => by simpa using pro_res_pc d.site h)
    | sm d => exact absurd hpc (fun h => by simpa using sm_res_pc d.site h)
    | epi d =>
      have hs : d.site = .dealloc := by simpa using epi_res_pc d.site hpc
      have hshape := Epi.shape_dealloc (fired_epi hF) hs
      have hp3 : d.pr.p3 = true := hI.1.dealloc hs
      have hmeans : d.pr.p3 = decide (g % L.block < 32) := hreach.2.p3
      refine ⟨by rw [hp3] at hmeans; simpa using hmeans.symm, .inr (.inr ⟨d, hσ, hs, ?_⟩)⟩
      simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hshape
      obtain ⟨-, h2, -, h4⟩ := hshape
      exact ⟨h2, h4⟩

/-- **The allocation, the relinquishment and the deallocation fire resource events.** -/
theorem res_state_event {g k : Nat} {e : Event} {d : DComp.St} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d d))) (hr : ResState d)
    : isTmemOp e = true := by
  have hxs : ¬ ExitState (.d d) := by
    intro hx
    cases d with
    | epi d =>
      have h1 : d.site = .exit := hx
      have h2 : d.site = .dealloc := hr
      rw [h1] at h2
      cases h2
    | _ => exact hx
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ hxs
  cases d with
  | dstart d =>
    have hshape := DStart.shape_of_pre hpre (fired_dstart hF)
    obtain ⟨site, tm⟩ := d
    rcases hr with h | h <;> simp only at h <;> subst h <;> simp only [DStart.Shape] at hshape <;>
      subst hshape <;> rfl
  | pro d => exact hr.elim
  | sm d => exact hr.elim
  | epi d =>
    have hshape := Epi.shape_dealloc (fired_epi hF) hr
    subst hshape
    rfl

/-- **A paired operation is fired from a resource state of a thread of warp 0.** -/
theorem res_state_of {g k : Nat} {e : Event} {s : TSt} (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some s)) (hop : isTmemOp e = true)
    : g % L.block < 32 ∧ ∃ d, s = .d d ∧ ResState d := by
  obtain ⟨pc, grp, dst, act, rfl⟩ := tmemOp_resource hop
  obtain ⟨hl, h⟩ := res_event_state hpre hX hf he
  refine ⟨hl, ?_⟩
  rcases h with ⟨tm, h, -⟩ | ⟨tm, h, -⟩ | ⟨d, h, hs, -⟩
  · rw [hσ] at h
    obtain rfl := Option.some.inj (Option.some.inj h)
    exact ⟨_, rfl, .inl rfl⟩
  · rw [hσ] at h
    obtain rfl := Option.some.inj (Option.some.inj h)
    exact ⟨_, rfl, .inr rfl⟩
  · rw [hσ] at h
    obtain rfl := Option.some.inj (Option.some.inj h)
    exact ⟨_, rfl, hs⟩

omit hpre hX hf in
theorem countP_tmem_succ {es : List Event} {k : Nat} {e : Event} (he : es[k]? = some e) :
    tmemOps (es.take (k + 1)) = tmemOps (es.take k) + (if isTmemOp e = true then 1 else 0) := by
  rw [List.take_add_one, he]
  simp [tmemOps, List.countP_append]

/-- **The measure of paired operations along a thread**: before the event of a state, a thread has
made `tCnt` paired Tensor Memory operations. -/
theorem tmops_inv {g : Nat} (hg : g < L.threads) :
    ∀ k s, k ≤ (X.tr g).length → St Q L X g k = some (some s) →
      tmemOps ((X.tr g).take k) = tCnt L g s := by
  intro k
  induction k with
  | zero =>
    intro s _ hs
    have hs : Frame.stateAt (code L Q) X g 0 = some (some s) := hs
    rw [Frame.stateAt_zero] at hs
    have hs' : s = (threadCode L g Q).init := (Option.some.inj (Option.some.inj hs)).symm
    subst hs'
    simp only [List.take_zero, tmemOps, List.countP_nil]
    show 0 = tCnt L g (if g % L.block < 128 then .d (DComp.code L g Q).init
      else .w (WComp.code L g Q).init)
    split_ifs with hd
    · show 0 = dCnt L g (.dstart (DStart.D.start L g))
      by_cases hl : g % L.block < 32
      · simp [dCnt, hl, DStart.D.start, dBase]
      · simp [dCnt, hl]
    · rfl
  | succ k ih =>
    intro s' hk hs'
    have hs' : Frame.stateAt (code L Q) X g (k + 1) = some (some s') := hs'
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [Frame.stateAt_succ he] at hs'
    cases hσ : Frame.stateAt (code L Q) X g k with
    | none => rw [hσ] at hs'; simp at hs'
    | some o =>
      cases o with
      | none => rw [hσ] at hs'; simp [Flow.Code.toMachine] at hs'
      | some s =>
        rw [hσ] at hs'
        simp only [Option.bind_some] at hs'
        have hn : (threadCode L g Q).next s e = some (some s') := hs'
        have ih' := ih s (by omega) hσ
        have hget : X.get (g, k) = some e := he
        rw [countP_tmem_succ he, ih']
        by_cases hop : isTmemOp e = true
        · obtain ⟨hl, d, rfl, hr⟩ := res_state_of hpre hX hf hget hσ hop
          obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some (show (DComp.next L g Q d e).map
            (Option.map TSt.d) = some (some s') from hn)
          have hreach := hf.reach hg hσ
          have hp : ∀ d', d = .epi d' → d'.pr.p3 = true := by
            rintro d' rfl
            have := hreach.2.p3
            rw [this]
            simpa using hl
          have := IpTm.dBase_next hl hp ha
          simp only [tCnt, dCnt, hl, ↓reduceIte, hop]
          rw [this, dInc_eq_one hr]
        · have hop' : isTmemOp e = false := by simpa using hop
          rw [hop']
          cases s with
          | w s0 =>
            obtain ⟨a, -, rfl⟩ := map_map_eq_some_some (show (WComp.next L g s0 e).map
              (Option.map TSt.w) = some (some s') from hn)
            rfl
          | d d =>
            obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some (show (DComp.next L g Q d e).map
              (Option.map TSt.d) = some (some s') from hn)
            by_cases hl : g % L.block < 32
            · have hreach := hf.reach hg hσ
              have hp : ∀ d', d = .epi d' → d'.pr.p3 = true := by
                rintro d' rfl
                have := hreach.2.p3
                rw [this]
                simpa using hl
              have := IpTm.dBase_next hl hp ha
              have hnr : ¬ ResState d := fun hr => by
                have := res_state_event hpre hX hf hg hget hσ hr
                rw [hop'] at this
                cases this
              simp only [tCnt, dCnt, hl, ↓reduceIte]
              rw [this, dInc_eq_zero hnr]
              simp
            · simp [tCnt, dCnt, hl]

omit hpre hX hf in
theorem ev_le {g k : Nat} {e : Event} (he : X.get (g, k) = some e) : k ≤ (X.tr g).length := by
  have := (List.getElem?_eq_some_iff.mp he).1
  simp only at this
  omega

/-- **A resource event is warp 0's, in group one, and its thread's n-th has the shape n**: the
allocation of 512 columns, the relinquishment, the deallocation of 512 columns. -/
theorem res_event {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request}
    (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .tc (.resource grp dst act)⟩) :
    g % L.block / 32 = 0 ∧ grp = .one ∧ TmemShape (tmemOps ((X.tr g).take k)) act := by
  have hk : k ≤ (X.tr g).length := (ev_le he)
  obtain ⟨hl, h⟩ := res_event_state hpre hX hf he
  have h0 : g % L.block / 32 = 0 := by omega
  refine ⟨h0, ?_⟩
  rcases h with ⟨tm, hσ, hgrp, hact⟩ | ⟨tm, hσ, hgrp, hact⟩ | ⟨d, hσ, hs, hgrp, hact⟩
  · refine ⟨hgrp, ?_⟩
    rw [tmops_inv hpre hX hf hg k _ hk hσ]
    simp [tCnt, dCnt, hl, dBase, TmemShape, hact]
  · refine ⟨hgrp, ?_⟩
    rw [tmops_inv hpre hX hf hg k _ hk hσ]
    simp [tCnt, dCnt, hl, dBase, TmemShape, hact]
  · refine ⟨hgrp, ?_⟩
    rw [tmops_inv hpre hX hf hg k _ hk hσ]
    simp [tCnt, dCnt, hl, dBase, TmemShape, hact, hs]

/-- **A thread of warp 0 has made its three paired operations before it exits.** -/
theorem exit_ops {g k pc : Nat} (hg : g < L.threads) (hw : g % L.block / 32 = 0)
    (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    tmemOps ((X.tr g).take k) = 3 := by
  have hk : k ≤ (X.tr g).length := (ev_le he)
  have hl : g % L.block < 32 := by omega
  rcases exit_event_state hX hf.sound hf.tracked he with ⟨d, hσ, hs⟩ | ⟨x, hσ, -⟩
  · rw [tmops_inv hpre hX hf hg k _ hk hσ]
    simp [tCnt, dCnt, hl, dBase, hs]
  · exfalso
    exact (cls_inv (X := X) (Q := Q) k _ hk hσ).mpr (by omega)

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
