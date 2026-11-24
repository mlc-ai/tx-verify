-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Progress.Async
public import Lemmas.Step.ReadSource
public import Lemmas.Step.TcLoad

@[expose] public section

/-! # `tc_gemm` progress: a released pending thread steps

A released pending thread performs its site's template (`ThreadFacts.fire`), each a counted
extension of the safe maximal execution (`released_steps`):

* the allocation, the load's wait and the deallocation are warp-collective `tcgen05` events
  (`Descent.coll_steps`); the MMA, the commit and the `tcgen05` fences are issued by one lane
  (`Step.tc_counted_extension`); the load returns in each slot the last value written to its
  cell, a word of the MMA's result (`wrote_word`, `layoutInjective`,
  `Step.tc_load_counted_extension`);
* the address store writes the column of the recorded allocation (`alloc_col`), as the allocator's
  result rule requires; the row stores and the exit are plain events
  (`Step.plain_counted_extension`), and a store of a word that is not four bytes is undefined
  behaviour (`Descent.ub_steps`);
* the initializations and the arrival carry their checked records (`Descent.object_steps`), the
  proxy fence is quiet (`Descent.quiet_steps`), the copies are issued
  (`Step.issue_counted_extension`), the barriers arrived at (`Descent.bar_steps`) and the address
  read from a source (`Step.read_source_counted_extension`);
* a poll of `bar0` finds the phase completed (`bar0_done`); a poll of `bar1` does once thread 0
  has committed (`bar1_done`), and before that thread 0 is pending at an earlier time;
* a stopped machine performs its undefined behaviour (`Descent.dead_steps`). -/

namespace PTX.Kernels.TcGemm.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}

/-- A thread whose machine has left its initial site has events. -/
theorem ne_nil_of_site {g : Nat} {d : ThreadD}
    (hσ : stateAt L A B D X g (X.tr g).length = some (some d)) (h1 : d.site ≠ .alloc)
    (h2 : d.site ≠ .bar0 false) : X.tr g ≠ [] := by
  intro h0
  have hz : stateAt L A B D X g 0 = some (some (code L A B D g).init) := Frame.stateAt_zero
  rw [h0, List.length_nil, hz] at hσ
  obtain rfl := Option.some.inj (Option.some.inj hσ)
  simp only [code] at h1 h2
  split at h1 <;> simp_all

section
variable (hW : Wit A B D L.sharedBase X P m u)
include hW

/-- The MMA's layout is injective. -/
theorem layoutInjective : TcMma.LayoutInjective X := by
  intro i d s acc mask hi row col row' col' cell h h'
  obtain ⟨-, -, rfl, -, rfl⟩ := hW.mmaIssue hi
  obtain ⟨rfl, -, -, -⟩ := mma_writeCell_inv h
  obtain ⟨he, -, -, -⟩ := mma_writeCell_inv h'
  simp only [TcMma.Cell.mk.injEq, true_and] at he
  omega

/-- **Every value written to a Tensor Memory cell is a word**: the MMA's result. -/
theorem wrote_word (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
    {s : EvId} {cell : TcMma.Cell} {v : Value} (hw : TcMma.Wrote L [] X s cell v) :
    v.bytes = 4 := by
  rcases hw with hr | ⟨_, _, _, _, ⟨_, hst⟩, -⟩ | ⟨_, _, _, _, _, _, _, ⟨_, hcp⟩, -⟩ |
    ⟨_, _, ⟨⟨_, ⟨_, hsh⟩, -⟩, -⟩, -⟩
  · cases hr with
    | overwrite issue position reads arith =>
      have hm : hd 0 + 2 + (P 0).n0 < m 0 := by
        obtain ⟨pc, he⟩ := issue
        obtain ⟨g, j⟩ := s
        obtain ⟨-, hj, rfl, rfl, -⟩ := hW.mma he
        exact hj
      obtain ⟨rfl, rfl, rfl, -, rfl⟩ := hW.mmaIssue issue
      obtain ⟨rfl, -, -, -⟩ := mma_writeCell_inv position
      rw [result_value hpre hX hW hm (.overwrite issue position reads arith)]
      rfl
    | accumulate issue => exact absurd (hW.mmaIssue issue).2.2.2.1 (by simp)
    | accumulateStored issue => exact absurd (hW.mmaIssue issue).2.2.2.1 (by simp)
  · obtain ⟨_, _⟩ := s
    exact (hW.no_tst hst).elim
  · obtain ⟨_, _⟩ := s
    exact (hW.no_cp hcp).elim
  · obtain ⟨_, _⟩ := s
    exact (hW.no_shift hsh).elim

/-- A thread whose last event is its allocation is at the address store or the first barrier. -/
theorem last_not_alloc {g : Nat} {d : ThreadD}
    (hσ : stateAt L A B D X g (X.tr g).length = some (some d)) (h1 : d.site ≠ .allocSt)
    (h2 : d.site ≠ .bar0 false) {pc : Nat} {grp : CtaGroup} {dst : Option Loc} {n : Nat}
    (hget : X.get (g, (X.tr g).length - 1) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩) :
    False := by
  obtain ⟨d', n', rfl, rfl, -⟩ | ⟨_, _, -, -, h⟩ := hW.resource hget
  swap; · cases h
  obtain ⟨-, hj, h32, hj0, -, -⟩ := hW.talloc hget
  have hl := len_of_get hget
  simp only at hl
  rw [show (X.tr g).length - 1 = 0 by omega] at hget
  rw [show (X.tr g).length = 0 + 1 by omega] at hσ
  have h := Frame.stateAt_succ (C := code L A B D) (X := X) (g := g) (k := 0) hget
  rw [Frame.stateAt_zero] at h
  change stateAt L A B D X g (0 + 1) = _ at h
  rw [hσ] at h
  simp only [code, h32, ↓reduceIte, Option.bind_some] at h
  have h' : some (some d) = next g { site := .alloc, c := 0, vals := [] }
      ⟨pc, .tc (.resource .one (some d') (.alloc n))⟩ := h
  simp only [next, Option.some.injEq] at h'
  rw [h'] at h1 h2
  split at h1 <;> simp_all

/-- The allocation of a thread of warp 0 whose last event it is, once its return is ready, is
recorded at a column that leaves room for its 32 columns. -/
theorem alloc_col (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X) {g : Nat}
    (hr : Tmem.Pair.ReturnReady L X (g, 0)) :
    ∃ col, allocReq L.sharedBase col ∈ X.tmemHistory 0 ∧ col + 32 ≤ 512 := by
  obtain ⟨cta, r, hr', ⟨lane, hl⟩⟩ := hr.1
  obtain ⟨rfl, ⟨col, rfl⟩ | rfl⟩ := rec_shape hpre hX hW hr'
  · exact ⟨col, hr', base_room hpre hX hW hr'⟩
  · simp only [deallocReq, Tmem.Pair.WarpRequest.event, Prod.mk.injEq] at hl
    omega

end

section
variable (hpre : Pre L A B D a b mem0) (ht : ThreadFacts L A B D X)
  (hsafe : ¬ Unsafe L kernel [] mem0 X) (hmax : Maximal L kernel [] mem0 X)
  (hW : Wit A B D L.sharedBase X P m u)
include hpre ht hsafe hmax hW

/-- **A released pending thread of a safe maximal execution steps.** -/
theorem released_steps (hC : ∀ g < L.threads, (code L A B D g).Sound) {g : Nat}
    (hp : Frame.Pending L X g) (hrel : Step.Released L X g) :
    Descent.Steps L kernel [] mem0 (Descent.Obl L) (rank L A B D) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hT := threads_eq hpre
  have hg128 : g < 128 := by omega
  have hub : ¬ HasUb X := fun h => hsafe (.inl h)
  have hst := strong_ordered hpre hX hW
  have hsg := syncGuarded hW hpre hX
  have hnr : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false :=
    fun _ _ _ _ he => no_release hW he
  have hnrmw : ∀ e pc a o n, X.get e = some ⟨pc, .rmw a o n⟩ → a.release = false :=
    fun ⟨_, _⟩ _ _ _ _ he => (hW.no_rmw he).elim
  have hnf : ∀ e sem s, ¬ X.ThreadFence e sem s := fun ⟨_, _⟩ _ _ ⟨_, h⟩ => hW.no_threadFence h
  have hsn : ∀ {ev : Event}, (∀ a bs, ev.kind ≠ .wr a bs) → (∀ a o n, ev.kind ≠ .rmw a o n) →
      (∀ sem s, ev.kind ≠ .fence sem s) → (∀ pc m q acq sc, ev ≠ ⟨pc, .wait m q true acq sc⟩) →
      SyncGuarded L kernel (X.snoc g ev (fun _ => none)) := fun h1 h2 h3 h4 =>
    hsg.snoc hnr hnrmw hnf h1 h2 h3 fun _ _ _ _ _ h => (h4 _ _ _ _ _ h).elim
  have hlen := len_eq hpre hX hW hg128
  cases hσ : stateAt L A B D X g (X.tr g).length with
  | none => exact Descent.dead_steps wfFree hmax hub hC hp hσ hrel
  | some σ =>
    cases σ with
    | none => exact absurd hσ (ht.tracked g _ hg)
    | some d =>
      obtain ⟨t, hrun⟩ := Frame.run_some hX hub hp
      obtain ⟨t1, m', hl, hpc, -, hout, hm⟩ := ht.fire hg hσ hrun
      have hJ := ht.along hg le_rfl hσ
      rw [List.take_length] at hJ
      have hne := ne_nil_of_site hσ
      have htime := timeOf_of hσ
      obtain ⟨site, c, vals⟩ := d
      cases site with
      | alloc =>
        obtain ⟨u, rfl⟩ := hm
        exact Descent.coll_steps wfFree hX hg (.inr (launched hW g)) hrel hrun hl (u := some u)
          ⟨_, hout, rfl, rfl⟩ rfl (hX.tmemPairResult.snoc_not_wr nofun) (hX.tcRead_snoc_tc nofun)
      | allocSt =>
        obtain ⟨u, rfl⟩ := hm
        obtain ⟨rfl, htr⟩ := hJ
        have hget : X.get (0, 0) = some (allocE L.sharedBase) := by
          change (X.tr 0)[0]? = _
          rw [htr]
          rfl
        have hlen1 : (X.tr 0).length = 1 := by rw [htr]; rfl
        have hget1 : X.get (0, (X.tr 0).length - 1) = some (allocE L.sharedBase) := by
          rw [hlen1]; exact hget
        have hrr := Tmem.Pair.ReturnReady.of_ready hget1 (hrel.ready _ _ hget1 rfl)
        rw [hlen1] at hrr
        obtain ⟨col, hcol, hroom⟩ := alloc_col hW hpre hX hrr
        let e : Event := ⟨t1.pc, .wr { loc := tslot L.sharedBase, size := 4 }
          (Value.bits 32 (BitVec.ofNat 64 col)).toBytes⟩
        have hres : Tmem.Pair.ResultOk L (X.snoc 0 e (fun _ => none)) := by
          apply hX.tmemPairResult.snoc
          intro pc a' bs he _ pc' grp dst n hget' cta x base hx hwi hwa
          simp only [e, Event.mk.injEq, Kind.wr.injEq] at he
          obtain ⟨-, -, rfl⟩ := he
          obtain ⟨rfl, ⟨c', rfl⟩ | rfl⟩ := rec_shape hpre hX hW hx
          · simp only [allocReq, Tmem.Action.alloc.injEq] at hwa
            rw [← hwa.2, alloc_unique hpre hX hW hx hcol]
          · simp [deallocReq] at hwa
        exact .inl (Step.plain_counted_extension hX hg (.inr (launched hW 0)) hrel hrun hl
          (o := some u) (e := e) ⟨_, hout, col, by omega, rfl, rfl⟩ rfl (by simp [e, Kind.isTma])
          (fun _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
          (fun _ _ _ h => by cases h) rfl hres (fun _ ha => by cases ha))
      | init0 =>
        obtain ⟨u, rfl⟩ := hm
        refine Descent.object_steps wfFree hX hsafe hst hsg hnr hnrmw hnf hg (.inr (launched hW g))
          hrel hrun hl hout (k := .mbInit (bar0 L.sharedBase) 1) ⟨rfl, rfl⟩ (.inr ⟨_, _, rfl⟩)
          (mb := bar0 L.sharedBase) (act := .init 1) (fun _ _ h => by cases h) fun l' => ?_
        by_cases h : l' = bar0 L.sharedBase
        · subst h
          simp [objectAction, snoc_get_new]
        · simp [objectAction, snoc_get_new, h, Ne.symm h]
      | init1 =>
        obtain ⟨u, rfl⟩ := hm
        refine Descent.object_steps wfFree hX hsafe hst hsg hnr hnrmw hnf hg (.inr (launched hW g))
          hrel hrun hl hout (k := .mbInit (bar1 L.sharedBase) 1) ⟨rfl, rfl⟩ (.inr ⟨_, _, rfl⟩)
          (mb := bar1 L.sharedBase) (act := .init 1) (fun _ _ h => by cases h) fun l' => ?_
        by_cases h : l' = bar1 L.sharedBase
        · subst h
          simp [objectAction, snoc_get_new]
        · simp [objectAction, snoc_get_new, h, Ne.symm h]
      | fence =>
        obtain ⟨u, rfl⟩ := hm
        exact Descent.quiet_steps wfFree hX hsafe hst hsg hnr hnrmw hnf hg (.inr (launched hW g))
          hrel hrun hl hout ⟨rfl, rfl⟩ (.inl ⟨_, _, rfl⟩)
      | arrive =>
        obtain ⟨u, rfl⟩ := hm
        refine Descent.object_steps wfFree hX hsafe hst hsg hnr hnrmw hnf hg (.inr (launched hW g))
          hrel hrun hl hout (k := .arrive (bar0 L.sharedBase) 4352) ⟨rfl, rfl⟩
          (.inl ⟨_, _, _, _, _, rfl⟩) (mb := bar0 L.sharedBase) (act := .arrive 1 4352)
          (fun _ _ h => by cases h) fun l' => ?_
        by_cases h : l' = bar0 L.sharedBase
        · subst h
          simp [objectAction, snoc_get_new]
        · simp [objectAction, snoc_get_new, h, Ne.symm h]
      | bulkA =>
        obtain ⟨u, rfl⟩ := hm
        exact .inl (Step.issue_counted_extension hX (noMixed_of_safe hsafe)
          (noRace_of_safe hsafe) hst hg (hne nofun nofun) hrel hrun hl (o := some u)
          ⟨_, hout, rfl, rfl⟩ (.inr (.inr ⟨_, rfl⟩)) (fun _ ha => by cases ha)
          (hsn nofun nofun nofun nofun))
      | bulkB =>
        obtain ⟨u, rfl⟩ := hm
        exact .inl (Step.issue_counted_extension hX (noMixed_of_safe hsafe)
          (noRace_of_safe hsafe) hst hg (hne nofun nofun) hrel hrun hl (o := some u)
          ⟨_, hout, rfl, rfl⟩ (.inr (.inr ⟨_, rfl⟩)) (fun _ ha => by cases ha)
          (hsn nofun nofun nofun nofun))
      | bar0 z =>
        obtain ⟨u, rfl⟩ := hm
        exact Descent.bar_steps wfFree hX hg (.inr (launched hW g)) hrel hrun hl (u := some u)
          ⟨_, hout, rfl, rfl⟩
      | bar1 =>
        obtain ⟨u, rfl⟩ := hm
        exact Descent.bar_steps wfFree hX hg (.inr (launched hW g)) hrel hrun hl (u := some u)
          ⟨_, hout, rfl, rfl⟩
      | load z =>
        obtain ⟨k, rfl⟩ := hm
        exact .inl (Step.read_source_counted_extension hX hg (hne nofun nofun) hrel hrun hl hout
          (fun _ _ _ _ ha => by cases ha) hsg)
      | wait0 =>
        obtain ⟨rfl, col, bs, n, -, -, -, hpre'⟩ := hJ
        have h7 : 7 < m 0 := by
          rw [← hlen, hpre']
          simp [headE]
        obtain ⟨before, hstate, hph⟩ := bar0_done hpre hmax hW h7
        refine Descent.mbar_wait_steps wfFree hub hmax hp hrel (hne nofun nofun)
          (m := bar0 L.sharedBase) (pcw := Flow.mbarWait_0) (par := 0) (Q := fun _ => True)
          (fun t' hrun' ok => ?_) hstate fun _ _ h _ => (hph h).elim
        obtain ⟨t1', m'', hl', hpc', -, hout', k', rfl⟩ := ht.fire hg hσ hrun'
        exact ⟨t1', k' ok, .cta, hl', ⟨_, hout', ok, by rw [hpc']; rfl, rfl⟩, fun _ => trivial⟩
      | wait1 =>
        by_cases hc : hd 0 + 3 + (P 0).n0 < m 0
        · obtain ⟨before, hstate, hph⟩ := bar1_done hpre hmax hW hc
          refine Descent.mbar_wait_steps wfFree hub hmax hp hrel (hne nofun nofun)
            (m := bar1 L.sharedBase) (pcw := Flow.mbarWait_1) (par := 0) (Q := fun _ => True)
            (fun t' hrun' ok => ?_) hstate fun _ _ h _ => (hph h).elim
          obtain ⟨t1', m'', hl', hpc', -, hout', k', rfl⟩ := ht.fire hg hσ hrun'
          exact ⟨t1', k' ok, .cta, hl', ⟨_, hout', ok, by rw [hpc']; rfl, rfl⟩, fun _ => trivial⟩
        · -- thread 0 has not committed: it is pending, earlier
          have h13 := time_le_13 hpre ht hW (by omega)
          have := ldIdx_eq (g := 0) (P 0)
          have := tl_zero (P 0)
          refine .inr ⟨X, .thread 0, hmax, pending_of hpre hX hW (by decide) (by omega), ?_⟩
          simp only [rank, htime, Site.time]
          omega
      | mma =>
        obtain ⟨u, rfl⟩ := hm
        exact .inl (Step.tc_counted_extension hX (noMixed_of_safe hsafe) (noRace_of_safe hsafe)
          hst hg (hne nofun nofun) hrel hrun hl (o := some u) ⟨_, hout, rfl, rfl⟩ rfl
          (fun _ ha => by cases ha) (hsn nofun nofun nofun nofun))
      | commit =>
        obtain ⟨u, rfl⟩ := hm
        exact .inl (Step.tc_counted_extension hX (noMixed_of_safe hsafe) (noRace_of_safe hsafe)
          hst hg (hne nofun nofun) hrel hrun hl (o := some u) ⟨_, hout, rfl, rfl⟩ rfl
          (fun _ ha => by cases ha) (hsn nofun nofun nofun nofun))
      | fence1 =>
        obtain ⟨u, rfl⟩ := hm
        exact .inl (Step.tc_counted_extension hX (noMixed_of_safe hsafe) (noRace_of_safe hsafe)
          hst hg (hne nofun nofun) hrel hrun hl (o := some u) ⟨_, hout, rfl, rfl⟩ rfl
          (fun _ ha => by cases ha) (hsn nofun nofun nofun nofun))
      | fenceB =>
        obtain ⟨u, rfl⟩ := hm
        exact .inl (Step.tc_counted_extension hX (noMixed_of_safe hsafe) (noRace_of_safe hsafe)
          hst hg (hne nofun nofun) hrel hrun hl (o := some u) ⟨_, hout, rfl, rfl⟩ rfl
          (fun _ ha => by cases ha) (hsn nofun nofun nofun nofun))
      | fence2 =>
        obtain ⟨u, rfl⟩ := hm
        exact .inl (Step.tc_counted_extension hX (noMixed_of_safe hsafe) (noRace_of_safe hsafe)
          hst hg (hne nofun nofun) hrel hrun hl (o := some u) ⟨_, hout, rfl, rfl⟩ rfl
          (fun _ ha => by cases ha) (hsn nofun nofun nofun nofun))
      | ld =>
        obtain ⟨k, rfl⟩ := hm
        refine .inl (Step.tc_load_counted_extension hX hg (hne nofun nofun) hrel hrun hl
          (o := some (k (Step.loadVals L [] X g .s32x32b (taddr g c) 8)))
          ⟨_, hout, _, Step.loadVals_length, rfl, rfl⟩ ?_ (fun _ ha => by cases ha))
        intro j v hj hv
        rw [Step.loadVals_length] at hj
        refine ⟨Step.loadVals_spec hX hsg (layoutInjective hW) hj hv, ?_⟩
        obtain ⟨s, hs, -⟩ := hv
        exact wrote_word hW hpre hX hs
      | waitLd =>
        obtain ⟨u, rfl⟩ := hm
        exact Descent.coll_steps wfFree hX hg (.inr (launched hW g)) hrel hrun hl (u := some u)
          ⟨_, hout, rfl, rfl⟩ rfl (hX.tmemPairResult.snoc_not_wr nofun) (hX.tcRead_snoc_tc nofun)
      | dealloc =>
        obtain ⟨u, rfl⟩ := hm
        exact Descent.coll_steps wfFree hX hg (.inr (launched hW g)) hrel hrun hl (u := some u)
          ⟨_, hout, rfl, rfl⟩ rfl (hX.tmemPairResult.snoc_not_wr nofun) (hX.tcRead_snoc_tc nofun)
      | st j =>
        rcases hm with ⟨-, u, rfl⟩ | ⟨-, f, rfl⟩
        · have hres : Tmem.Pair.ResultOk L (X.snoc g ⟨t1.pc, .wr (stAcc D g j)
              (stBytes (word vals j))⟩ (fun _ => none)) := by
            refine hX.tmemPairResult.snoc_last fun pc grp dst n hget => ?_
            exact (last_not_alloc hW hσ nofun nofun hget).elim
          exact .inl (Step.plain_counted_extension hX hg (.inr (launched hW g)) hrel hrun hl
            (o := some u) (e := ⟨t1.pc, .wr (stAcc D g j) (stBytes (word vals j))⟩)
            ⟨_, hout, rfl, rfl⟩ rfl (by simp [Kind.isTma, stAcc]) (fun _ _ _ _ _ _ h => by cases h)
            (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl hres
            (fun _ ha => by cases ha))
        · exact Descent.ub_steps wfFree hX hg (hne nofun nofun) hrel hrun hl hout
      | exit =>
        subst hm
        exact .inl (Step.plain_counted_extension hX hg (.inr (launched hW g)) hrel hrun hl
          (o := none) (e := ⟨t1.pc, .exit⟩) ⟨_, hout, rfl, rfl⟩ trivial rfl nofun nofun nofun rfl
          (hX.tmemPairResult.snoc_not_wr nofun) (fun _ ha => by cases ha))

end

end

end PTX.Kernels.TcGemm.Proof
