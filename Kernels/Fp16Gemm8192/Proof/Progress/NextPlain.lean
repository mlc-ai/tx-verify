-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.NextFire
public import Kernels.Fp16Gemm8192.Proof.Progress.TmemLanes
public import Kernels.Fp16Gemm8192.Proof.Progress.WarpWaitsLane
public import Lemmas.Order.GuardSnoc
public import Lemmas.Flow.Alloc
public import Kernels.Fp16Gemm8192.Proof.MemoryFacts

@[expose] public section

/-! # Progress at a plain event or the exit

A released pending thread whose next event is plain performs it: a fence, a CLC response query
and a bulk commit use no mbarrier object and no Tensor Core (`Descent.quiet_steps`, in the safe
execution); a store without release semantics, the allocation's store of its address
(at the column of the recorded allocation, 0) and the exit are outside the asynchronous
instructions (`Step.plain_counted_extension`).
Undefined behaviour in their place is performed as well (`Descent.ub_steps`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The kernel's exempt conflicting pairs are ordered: every conflicting pair is. -/
theorem strongOrdered (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    StrongOrdered L X :=
  (Memory.conflicts_ordered hpre hX).strongOrdered

open PTX.EventFrame PTX.Flow in
/-- A template that is an allocation's address store comes from the allocation instruction. -/
theorem allocOp_of_store {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {dst : Loc} {u : TState} (h : eventTmpl A L g t op = .tcAllocStore dst u) :
    allocOp op = true := by
  have hop : writeOp op = true := by
    cases hq : writeOp op
    · exfalso
      have := eventTmpl_notWrite (A := A) (L := L) (g := g) (t := t) hq
      rw [h] at this
      exact this
    · rfl
  cases op <;> simp only [writeOp, Bool.false_eq_true] at hop
  case mem a =>
    have hm := memTmpl_isMem (A := A) (L := L) (g := g) (t := t) (a := a)
    simp only [eventTmpl] at h
    rw [h] at hm
    exact hm.elim
  case matrix i =>
    exfalso
    simp only [eventTmpl] at h
    unfold matrixTmpl at h
    split at h
    · split at h
      · unfold matrixMoveTmpl at h
        dsimp only at h
        split at h
        · split at h
          · split at h <;> cases h
          · split at h <;> cases h
        · split at h
          · split at h <;> cases h
          · cases h
      all_goals first | cases h | (split at h <;> cases h)
    · cases h
  all_goals rfl

open PTX.EventFrame PTX.Flow in
/-- A pending allocation's address store is at the allocation instruction. -/
theorem out_tcAllocStore {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {dst : Loc}
    {u : TState} (h : out kernel A L g t = .ev (.tcAllocStore dst u)) :
    ∃ ins, kernel.code[t.pc]? = some ins ∧ allocOp ins.op = true := by
  unfold out at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i ins hc
      refine ⟨ins, hc, ?_⟩
      split at h
      · cases h
      · cases h
      · split at h
        · split at h <;> cases h
        · exact allocOp_of_store (Out.ev.inj h)

/-- No atomic of the kernel releases: it issues none. -/
theorem rmw_no_release (ht : ThreadFacts L X) (hX : Consistent L kernel Prod mem0 X) :
    ∀ e pc a o n, X.get e = some ⟨pc, .rmw a o n⟩ → a.release = false :=
  fun _ _ _ _ _ h => (Safety.no_rmw hX ht h).elim

/-- The kernel issues no thread fence. -/
theorem no_fence (ht : ThreadFacts L X) (hX : Consistent L kernel Prod mem0 X) :
    ∀ e sem s, ¬ X.ThreadFence e sem s :=
  fun _ _ _ h => Safety.no_threadFence hX ht h

/-- **A released pending thread at a plain event steps.** -/
theorem plain_next_steps (hpre : Pre P L mem0) (ht : ThreadFacts L X)
    (hsg : SyncGuarded L kernel X) (hsafe : ¬ Unsafe L kernel Prod mem0 X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hk : nextKind d = .plain)
    (hrel : Step.Released L X g) {obligation : Descent.Obligation} :
    Descent.Steps L kernel Prod mem0 (Descent.Obl L) (rank L) X obligation := by
  have hX := hmax.1
  have hg := hp.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide)
  have hub : ¬ HasUb X := fun h => hsafe (.inl h)
  obtain ⟨t, t1, m, hrun, hl, hat, hout, hm⟩ := next_fire ht hX hub hp hσ
  rw [hk] at hm
  -- a thread whose last event is an allocation is at the allocation's address store
  have hprev : ∀ pc grp dst n, X.get (g, (X.tr g).length - 1) =
      some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ →
      ∃ p : Prologue.D, d = .inl p ∧ p.site = .allocWrite := by
    intro pc grp dst n hget
    obtain ⟨-, -, -, hsh, d', hd', hafter⟩ :=
      ht.tmem_event hg (fun _ _ _ he => hub ⟨_, _, _, he⟩) hget
    have h0 : tmemOps ((X.tr g).take ((X.tr g).length - 1)) = 0 := by
      have := lt_of_tmemShape hsh
      generalize tmemOps ((X.tr g).take ((X.tr g).length - 1)) = k at hsh this
      interval_cases k <;> simp_all [TmemShape]
    have hlen : (X.tr g).length - 1 + 1 = (X.tr g).length := by
      have := len_of_get hget
      simp only at this
      omega
    rw [hlen, hσ] at hd'
    obtain rfl := Option.some.inj (Option.some.inj hd').symm
    rw [h0] at hafter
    obtain ⟨p, rfl, hs | hs⟩ := hafter
    · exact ⟨p, rfl, hs⟩
    · simp [nextKind, prologueKind, hs] at hk
  rcases hm with ⟨f, rfl⟩ | ⟨fk, fo, u, rfl⟩ | ⟨u, rfl⟩ | ⟨q, r, u, rfl⟩ | ⟨a, bs, u, rfl, hr⟩ |
    ⟨dst, u, rfl⟩ | ⟨u, rfl⟩
  · exact Descent.ub_steps prod_wfFree hX hg hne hrel hrun hl hout
  · exact Descent.quiet_steps prod_wfFree hX hsafe (strongOrdered hpre hX) hsg
      ht.no_release (rmw_no_release ht hX) (no_fence ht hX) hg (.inl hne) hrel hrun hl hout
      ⟨rfl, rfl⟩ (.inl ⟨_, _, rfl⟩)
  · exact Descent.quiet_steps prod_wfFree hX hsafe (strongOrdered hpre hX) hsg
      ht.no_release (rmw_no_release ht hX) (no_fence ht hX) hg (.inl hne) hrel hrun hl hout
      ⟨rfl, rfl⟩ (.inr (.inl rfl))
  · exact Descent.quiet_steps prod_wfFree hX hsafe (strongOrdered hpre hX) hsg
      ht.no_release (rmw_no_release ht hX) (no_fence ht hX) hg (.inl hne) hrel hrun hl hout
      ⟨rfl, rfl⟩
      (.inr (.inr (.inl ⟨q, r, rfl⟩)))
  · -- an ordinary store: the thread is not at an allocation's address store
    have hnot : ∀ pc grp dst n, X.get (g, (X.tr g).length - 1) =
        some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ → False := by
      intro pc grp dst n hget
      obtain ⟨p, rfl, hs⟩ := hprev pc grp dst n hget
      have hpc : t1.pc = Flow.tmemAlloc_0 := by
        have := hat.1
        dsimp only at this
        rw [this, hs]
        rfl
      have hsub : t1.sub ≠ 0 := by
        have := hat.2.1
        dsimp only at this
        simp [this, Prologue.sub, hs]
      rw [PTX.Proof.out_event hat.2.2.2.1
        (by rw [hpc]; exact Flow.code_tmemAlloc_0) rfl rfl] at hout
      rcases Flow.eventTmpl_alloc_store (A := Prod) (L := L) (g := g)
          (group := .two) (base := 90) (off := 0) (nc := .reg 91) hsub with ⟨f, hf⟩ |
            ⟨dst', u', hf⟩ <;>
        rw [hf] at hout <;> cases hout
    have hres : Tmem.Pair.ResultOk L (X.snoc g ⟨t1.pc, .wr a bs⟩ (fun _ => none)) :=
      hX.tmemPairResult.snoc_last fun pc grp dst n hget => (hnot pc grp dst n hget).elim
    exact .inl (Step.plain_counted_extension hX hg (.inl hne) hrel hrun hl (o := some u)
      (e := ⟨t1.pc, .wr a bs⟩) ⟨_, hout, rfl, rfl⟩ hr (by simp [Kind.isTma, hr])
      (fun _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl
      hres (prod_wf _))
  · -- the allocation's address store, of the recorded allocation's column 0
    -- the thread is at the prologue's allocation write: the allocation instruction at a plain site
    obtain ⟨ins, hc, ha⟩ := out_tcAllocStore hout
    obtain ⟨p, rfl, hsite⟩ := alloc_site (L := L) (g := g) (by rw [← hat.1]; exact hc) ha
    have hsite : p.site = .allocWrite := by
      rcases hsite with h | h
      · simp [nextKind, prologueKind, h] at hk
      · exact h
    let e : Event := ⟨t1.pc, .wr { loc := dst, size := 4 }
      (Value.bits 32 (BitVec.ofNat 64 0)).toBytes⟩
    have hres : Tmem.Pair.ResultOk L (X.snoc g e (fun _ => none)) := by
      apply hX.tmemPairResult.snoc
      intro pc a bs he _ pc' grp dst' n hget key x base hx hwi hwa
      simp only [e, Event.mk.injEq, Kind.wr.injEq] at he
      obtain ⟨-, -, rfl⟩ := he
      rw [(Tmem.Pair.alloc_zero hX (ht.warpOps hpre) hx n base hwa).2]
    exact .inl (Step.plain_counted_extension hX hg (.inl hne) hrel hrun hl (o := some u)
      (e := e) ⟨_, hout, 0, by decide, rfl, rfl⟩ rfl (by simp [e, Kind.isTma])
      (fun _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl
      hres (prod_wf _))
  · exact Descent.quiet_steps prod_wfFree hX hsafe (strongOrdered hpre hX) hsg
      ht.no_release (rmw_no_release ht hX) (no_fence ht hX) hg (.inl hne) hrel hrun hl hout
      ⟨rfl, rfl⟩
      (.inr (.inr (.inr rfl)))

/-- **A released pending thread at its exit steps**: it exits. -/
theorem exit_next_steps (ht : ThreadFacts L X) (hub : ¬ HasUb X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hk : nextKind d = .exit)
    (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide)
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire ht hX hub hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | rfl
  · exact Descent.ub_steps prod_wfFree hX hg hne hrel hrun hl hout
  · exact .inl (Step.plain_counted_extension hX hg (.inl hne) hrel hrun hl (o := none)
      (e := ⟨t1.pc, .exit⟩) ⟨_, hout, rfl, rfl⟩ trivial rfl
      (fun _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl
      (hX.tmemPairResult.snoc_not_wr nofun) (prod_wf _))

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
