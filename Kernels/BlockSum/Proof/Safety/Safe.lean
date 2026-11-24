-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.BlockSum.Proof.Values
public import Lemmas.Kernel.PlainSafety
public import Kernels.BlockSum.Proof.NoBarArrive

@[expose] public section

/-! # No consistent execution is unsafe

Without asynchronous instructions only the branches of `Unsafe` the threads' own events decide
remain (`Execution.NoTma.not_unsafe`). A thread performs undefined behaviour only after a read
whose bytes the code cannot use, and every read returns the launch content or a cell's input
(`no_ub`). Every access is allocated (`no_unalloc`). The only conflicting accesses are a
thread's shared store and the read of its cell by thread 0 of the CTA, which the barrier orders
(`conflicts_ordered`). Every barrier arrival is the aligned whole-CTA barrier `0` as a thread's
third event, and no thread exits before it (`no_barMismatch`). -/

namespace PTX.Kernels.BlockSum.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B : Nat} {x : Nat → ℝ} {mem0 : Mem0} {X : Execution}

/-- Adding a real to any extended real is defined. -/
theorem addEReal_coe_ne_none (x : EReal) (r : ℝ) : Assumption.addEReal x (r : EReal) ≠ none := by
  unfold Assumption.addEReal
  split
  · next hc =>
    rcases hc with ⟨-, hy⟩ | ⟨-, hy⟩
    · exact absurd hy (EReal.coe_ne_bot r)
    · exact absurd hy (EReal.coe_ne_top r)
  · simp

/-- **No undefined behaviour.** -/
theorem no_ub (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) : ¬ HasUb X := by
  rintro ⟨⟨g, k⟩, pc, f, he⟩
  have hg := Frame.lt_of_get hX he
  have hk := len_of_get he
  simp only at hk
  obtain ⟨j, d, e, hj, hσj, hej, hbad⟩ := ht.dead hg hk.le (ht.ub hg he)
  have hev := ht.event hg hej hσj
  have hidx := ht.index hg (len_of_get hej).le hσj
  rcases hbad with hx | ⟨pc', a, bs, rfl, hb⟩
  · simp only [SiteEvent, hx] at hev
    rw [hev] at hej
    have := Execution.exit_last hX hg hej
    omega
  · rcases hb with ⟨hs, hb⟩ | ⟨hs, hb⟩
    · simp only [SiteEvent, hs] at hev
      obtain ⟨bs', hev⟩ := hev
      simp only [Event.mk.injEq, Kind.rd.injEq] at hev
      obtain ⟨rfl, rfl, rfl⟩ := hev
      simp only [D.idx, hs] at hidx
      subst hidx
      exact hb _ (by rw [input_read hpre hX ht hej]; exact rebuild_bytesOf _) rfl
    · simp only [SiteEvent, hs] at hev
      obtain ⟨bs', hev⟩ := hev
      simp only [Event.mk.injEq, Kind.rd.injEq] at hev
      obtain ⟨rfl, rfl, rfl⟩ := hev
      simp only [D.idx, hs] at hidx
      have hi := ((ht.inv hg hσj).sum hs).1
      rw [shared_read hpre hX ht hi hidx hej, readVal_bytesOf] at hb
      exact absurd (hb _ rfl) (addEReal_coe_ne_none _ _)

theorem input_alloc (hpre : Pre L A B x mem0) {g : Nat} (hg : g < L.threads) {l : Loc}
    (hc : Acc.Covers { loc := gl (A + 4 * g), size := 4 } l) : mem0 l ≠ none := by
  obtain ⟨sp, c, addr⟩ := l
  obtain ⟨rfl, rfl, hlo, hhi⟩ := hc
  have h := hpre.input g hg (addr - (A + 4 * g)) (by dsimp [gl] at hlo hhi; omega)
  rw [show A + 4 * g + (addr - (A + 4 * g)) = addr by dsimp [gl] at hlo; omega] at h
  change mem0 (gl addr) ≠ none
  rw [h]; simp

theorem shared_alloc (hpre : Pre L A B x mem0) {g i : Nat} (hg : g < L.threads) (hi : i < 256)
    {l : Loc} (hc : Acc.Covers { loc := sh (g / 256) (L.sharedBase + 4 * i), size := 4 } l) :
    mem0 l ≠ none := by
  obtain ⟨sp, c, addr⟩ := l
  obtain ⟨rfl, rfl, hlo, hhi⟩ := hc
  have hc : g / 256 < L.grid := by simp only [Launch.threads, hpre.block] at hg; omega
  have h := hpre.shared (g / 256) hc (addr - L.sharedBase) (by dsimp [sh] at hlo hhi; omega)
  rw [show L.sharedBase + (addr - L.sharedBase) = addr by dsimp [sh] at hlo; omega] at h
  change mem0 (sh (g / 256) addr) ≠ none
  rw [h]; simp

theorem output_alloc (hpre : Pre L A B x mem0) {g : Nat} (hg : g < L.threads) {l : Loc}
    (hc : Acc.Covers { loc := gl (B + 4 * (g / 256)), size := 4 } l) : mem0 l ≠ none := by
  obtain ⟨sp, c, addr⟩ := l
  obtain ⟨rfl, rfl, hlo, hhi⟩ := hc
  have hc : g / 256 < L.grid := by simp only [Launch.threads, hpre.block] at hg; omega
  have h := hpre.output (addr - B) (by dsimp [gl] at hlo hhi; omega)
  rwa [show B + (addr - B) = addr by dsimp [gl] at hlo; omega] at h

/-- **Every access is allocated.** -/
theorem no_unalloc (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) : ¬ Unalloc mem0 X := by
  rintro (⟨e, a, l, htouch, hc, hn⟩ | ⟨e, m, l, hu, hc, hn⟩)
  · obtain ⟨⟨g, k⟩, rfl, hacc⟩ :=
      Execution.NoTma.memTouches_thread (noTma_of_consistent noTma hX) htouch
    rcases hacc with ⟨bs, pc, hr⟩ | ⟨bs, hnc⟩ | ⟨bs, pc, hw⟩ | ⟨old, new, hrmw⟩
    · have hg := Frame.lt_of_get hX hr
      rcases read_cases hpre hX ht hr with ⟨-, -, rfl⟩ | ⟨-, i, hi, -, -, rfl⟩
      · exact input_alloc hpre hg hc hn
      · exact shared_alloc hpre hg hi hc hn
    · exact no_nc hpre hX ht hnc
    · have hg := Frame.lt_of_get hX hw
      rcases write_cases hpre hX ht hw with ⟨-, rfl, -⟩ | ⟨-, -, rfl, -⟩
      · exact shared_alloc hpre hg (Nat.mod_lt _ (by decide)) hc hn
      · exact output_alloc hpre hg hc hn
    · exact absurd hrmw (no_rmw hpre hX)
  · exact absurd hu (noTma_of_consistent noTma hX).not_usesMbar

/-- A write of a footprint that a read accesses happens before it: it is a thread's shared store
read by thread 0 of its CTA after the barrier. -/
theorem write_before_read (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {w r : EvId} {a : Acc} {bs : List Byte}
    {cs : List (Option Byte)} (hw : X.Writes w a bs)
        (hr : X.Reads r a cs) : baseCausality L X w r := by
  obtain ⟨⟨gw, kw⟩, pcw⟩ := (⟨w, 0⟩ : EvId × Nat)
  obtain ⟨pw, hw⟩ := hw
  obtain ⟨pr, hr⟩ := hr
  obtain ⟨gw, kw⟩ := w
  obtain ⟨gr, kr⟩ := r
  have hgw := Frame.lt_of_get hX hw
  have hgr := Frame.lt_of_get hX hr
  rcases write_cases hpre hX ht hw with ⟨hk1, rfl, -⟩ | ⟨-, -, rfl, -⟩ <;>
    rcases read_cases hpre hX ht hr with ⟨-, -, ha⟩ | ⟨-, i, hi, hk, -, ha⟩
  · cases ha
  · simp only [Acc.mk.injEq, sh, Loc.mk.injEq, true_and] at ha
    subst hk1
    exact (shared_sync hpre hX ht gr gw kr _ _ _ hgw ha.1.1 hr (by omega)).2
  · exfalso
    have hd := hpre.disjoint
    have hcw : gw / 256 < L.grid := by simp only [Launch.threads, hpre.block] at hgw; omega
    have haddr := congrArg (fun a : Acc => a.loc.addr) ha
    simp only [gl] at haddr
    simp only [Launch.threads, hpre.block] at hgr hd
    omega
  · cases ha

/-- **Conflicting accesses are ordered.** -/
theorem conflicts_ordered (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) : ConflictsOrdered L X fun _ => True := by
  intro e f a b l ⟨hne, we, wf, he, hf, hw, hov⟩ _ _ _
  have hn := noTma_of_consistent noTma hX
  obtain ⟨e, rfl, he⟩ := Execution.NoTma.intent_thread hn he
  obtain ⟨f, rfl, hf⟩ := Execution.NoTma.intent_thread hn hf
  have hab := overlapping_access_eq hpre hX ht he hf hov
  subst hab
  rcases he with ⟨bs, hre, rfl⟩ | ⟨bs, hwe, rfl⟩ | ⟨old, new, hrmw⟩ <;>
    rcases hf with ⟨cs, hrf, rfl⟩ | ⟨cs, hwf, rfl⟩ | ⟨old', new', hrmw'⟩
  · simp at hw
  · exact .inr (.inl (write_before_read hpre hX ht hwf hre))
  · exact absurd hrmw' (no_rmw hpre hX)
  · exact .inl (.inl (write_before_read hpre hX ht hwe hrf))
  · exact absurd (congrArg AsyncCopy.Ref.thread (writes_unique hpre hX ht hwe hwf)) hne
  · exact absurd hrmw' (no_rmw hpre hX)
  · exact absurd hrmw (no_rmw hpre hX)
  · exact absurd hrmw (no_rmw hpre hX)
  · exact absurd hrmw (no_rmw hpre hX)

/-- No barrier precedes a thread's barrier arrival. -/
theorem countP_bar_take_two (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) (g : Nat) : ((X.tr g).take 2).countP Execution.isBar = 0 := by
  rw [List.countP_eq_zero]
  intro ev hm hbar
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
  have hj2 : j < 2 := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take, ite_eq_left hj2] at hj
  obtain ⟨pc, kd⟩ := ev
  cases kd <;> simp [Execution.isBar] at hbar
  rename_i id cnt mode
  cases mode
  case arrive => exact (hX.noBarArrive Fact.out (g, j) _ _ _ hj).elim
  have := (bar_cases hpre hX ht (show X.IsBarrier (g, j) id cnt pc from hj)).1
  omega

/-- Every barrier arrival is the aligned whole-CTA barrier. -/
theorem bars_aligned (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) : ∀ g ev, ev ∈ X.tr g → ∀ id count, ev.kind = .bar id count →
      count = none ∧ kernel.alignedAt ev.pc = true := by
  intro g ev hm id count hk
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
  obtain ⟨pc, kd⟩ := ev
  simp only at hk
  subst hk
  obtain ⟨-, -, hc, hpc⟩ := bar_cases hpre hX ht (show X.IsBarrier (g, j) id count pc from hj)
  refine ⟨hc, ?_⟩
  simp only [hpc]
  decide +kernel

/-- **Every event's kind**: a read, a write, a barrier, the exit or a fault. -/
theorem kinds (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {e : EvId} {ev : Event} (he : X.get e = some ev) :
    (∃ pc a bs, ev = ⟨pc, .rd a bs⟩) ∨ (∃ pc a bs, ev = ⟨pc, .wr a bs⟩) ∨
      (∃ pc id cnt, ev = ⟨pc, .bar id cnt⟩) ∨ (∃ pc, ev = ⟨pc, .exit⟩) ∨
      (∃ pc f, ev = ⟨pc, .ub f⟩) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨g, k⟩ := e
  rcases Frame.fired (fun g' hg' => sound hpre hg') hX he with ⟨σ, o, hσ, -⟩ | ⟨-, pc, f, h⟩
  · cases σ with
    | none => exact absurd hσ (ht.tracked g k hg)
    | some d =>
      have hev := ht.event hg he hσ
      obtain ⟨s, v, i, acc, sm⟩ := d
      cases s <;> simp only [SiteEvent] at hev
      · obtain ⟨bs, h⟩ := hev
        exact .inl ⟨_, _, bs, h⟩
      · exact .inr (.inl ⟨_, _, _, hev⟩)
      · exact .inr (.inr (.inl ⟨_, _, _, hev⟩))
      · obtain ⟨bs, h⟩ := hev
        exact .inl ⟨_, _, bs, h⟩
      · exact .inr (.inl ⟨_, _, _, hev⟩)
      · exact .inr (.inr (.inr (.inl ⟨_, hev⟩)))
  · exact .inr (.inr (.inr (.inr ⟨pc, f, h⟩)))

/-- **A barrier event is a `bar.sync`**: the kernel has no `bar.arrive`. -/
theorem bar_mode_sync (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {e : EvId} {pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get e = some ⟨pc, .bar id cnt mode⟩) : mode = .sync := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨g, k⟩ := e
  rcases Frame.fired (fun g' hg' => sound hpre hg') hX he with ⟨σ, o, hσ, -⟩ | ⟨-, pc', f, h⟩
  · cases σ with
    | none => exact absurd hσ (ht.tracked g k hg)
    | some d =>
      have hev := ht.event hg he hσ
      obtain ⟨s, v, i, acc, sm⟩ := d
      cases s <;> simp only [SiteEvent] at hev
      · obtain ⟨bs, h⟩ := hev
        cases h
      · cases hev
      · simp only [Event.mk.injEq, Kind.bar.injEq] at hev
        exact hev.2.2.2
      · obtain ⟨bs, h⟩ := hev
        cases h
      · cases hev
      · cases hev
  · cases h

/-- **The barrier instruction is a thread's third event**, barrier `0`, no thread count. -/
theorem bar_fixed (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {e : EvId} {pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get e = some ⟨pc, .bar id cnt mode⟩) :
    e.2 = 2 ∧ id = 0 ∧ cnt = none ∧ pc = Flow.bar_0 := by
  have hm := bar_mode_sync hpre hX ht he
  subst hm
  exact bar_cases hpre hX ht he

/-- No event of the kernel is of the aligned classes other than the barrier: it is a read, a
write, a barrier, the exit or a fault. -/
theorem not_member (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {e : EvId} {ev : Event} (he : X.get e = some ev) :
    ∀ c : AlignedClass, c ≠ .bar → c.member ev = false ∧ c.exitMember kernel ev = false := by
  intro c hc
  have hk := kinds hpre hX ht he
  rcases hk with ⟨p, a, bs, rfl⟩ | ⟨p, a, bs, rfl⟩ | ⟨p, id, cnt, rfl⟩ | ⟨p, rfl⟩ |
    ⟨p, f, rfl⟩ <;>
    cases c with
    | bar => exact absurd rfl hc
    | tc | cluster | setMaxReg | matrix =>
      simp [AlignedClass.member, AlignedClass.exitMember, isTcColl, isCluster, isMatrix,
        SetMaxNReg.isRequest]

/-- **No aligned instruction diverges or is left by an exit**: the kernel's only whole-CTA
barrier is one `bar.sync` at one position, which every thread reaches before its exit. -/
theorem no_alignedMismatch (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) : ¬ AlignedMismatch L kernel X := by
  rintro ⟨c, hdiv | hex⟩
  · by_cases hbar : c = .bar
    · subst hbar
      rw [AlignedClass.divergent_bar_iff] at hdiv
      obtain ⟨g, h, i, j, id, id', count, count', mode, mode', pc, pc', -, he, hf, -, -, hne⟩ :=
        hdiv
      rw [(bar_fixed hpre hX ht he).2.2.2, (bar_fixed hpre hX ht hf).2.2.2] at hne
      exact hne rfl
    · obtain ⟨_, _, _, _, _, _, _, he, _, hme, -, -, -⟩ := hdiv
      rw [(not_member hpre hX ht he c hbar).1] at hme
      cases hme
  · by_cases hbar : c = .bar
    · subst hbar
      rw [AlignedClass.exited_bar_iff] at hex
      obtain ⟨e, f, k, -, ⟨ev, he, hev⟩, hk, hs⟩ := hex
      obtain ⟨pc, id, mode, rfl, -⟩ := Kernel.isAlignedCtaBar_iff hev
      cases mode
      case arrive => exact (hX.noBarArrive Fact.out _ _ _ _ he).elim
      obtain ⟨h2, rfl, -, rfl⟩ := bar_cases hpre hX ht (show X.IsBarrier e id none pc from he)
      rw [h2, Execution.countP_isAlignedCtaBar (fun ev hm =>
        bars_aligned hpre hX ht e.1 ev (List.mem_of_mem_take hm))
        (fun ev hm => hX.noBarArrive_tr Fact.out e.1 ev (List.mem_of_mem_take hm)),
        countP_bar_take_two hpre hX ht e.1] at hk
      obtain rfl : k = 0 := by omega
      obtain ⟨pcx, hx⟩ := hs.1
      obtain ⟨f1, f2⟩ := f
      have hb := bar_of_exit hpre hX ht hx
      exact Execution.not_exitedShort_of_barK X (bars_aligned hpre hX ht)
        (hX.noBarArrive_tr Fact.out) ⟨⟨0, Flow.bar_0, hb⟩, countP_bar_take_two hpre hX ht f1⟩ hs
    · obtain ⟨_, _, _, -, he, hme, -, -⟩ := hex
      rw [(not_member hpre hX ht he c hbar).2] at hme
      cases hme

/-- **Barriers are matched.** -/
theorem no_barMismatch (hpre : Pre L A B x mem0)
    (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) : ¬ BarMismatch L X := by
  rintro (⟨g, h, i, j, id, id', count, count', pc, pc', -, hb1, hb2, -, hbad⟩ |
    ⟨g, h, i, j, id, id', count, count', mode', pc, pc', -, he, -, -, hbad⟩)
  · obtain ⟨-, rfl, rfl, -⟩ := bar_cases hpre hX ht hb1
    obtain ⟨-, rfl, rfl, -⟩ := bar_cases hpre hX ht hb2
    simp at hbad
  · exact absurd (bar_mode_sync hpre hX ht he) (by simp)

/-- **No consistent execution is unsafe.** -/
theorem safe (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) : ¬ Unsafe L kernel Prod mem0 X := by
  refine (noTma_of_consistent noTma hX).not_unsafe hX (no_ub hpre hX ht)
    (no_unalloc hpre hX ht) (conflicts_ordered hpre hX ht) (no_barMismatch hpre hX ht)
    (not_ctaBarFault hX fun e f id cnt cnt' pc pc' _ h1 h2 => ?_) ?_
    (no_alignedMismatch hpre hX ht) (not_warpDivergent (K := kernel) (by decide +kernel)) ?_
  · obtain ⟨e1, e2⟩ := e
    obtain ⟨f1, f2⟩ := f
    exact (bar_cases hpre hX ht h1).2.2.1.trans (bar_cases hpre hX ht h2).2.2.1.symm
  · rintro ⟨a, ha, hu⟩
    obtain rfl := List.mem_singleton.mp ha
    exact hu
  · intro e a w ha hs
    rcases access_shape hpre hX ht ha with ⟨p, rfl, -⟩ | ⟨p, rfl, -⟩
    · cases hs
    · simp [hpre.block]

end
end PTX.Kernels.BlockSum.Proof
