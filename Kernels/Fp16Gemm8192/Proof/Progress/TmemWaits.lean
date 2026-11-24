-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.TmemBlock
public import Lemmas.Step.Issue
public import Lemmas.Tmem.TmemResourceReady

@[expose] public section

/-! # Progress at the paired Tensor Memory operations

The class of the paired Tensor Memory operations (`tcgen05.alloc`, `relinquish_alloc_permit`,
`dealloc`, `cta_group::2`): an operation is covered when the two CTAs' allocators performed the
two requests of its pair and they are paired (`Tmem.Pair.Covered`). A thread returns from an
operation only once its CTA's allocator has performed its request, and, if its return waits for
the operation (`Tmem.Pair.MustWait`, always so for the allocation), once it is covered
(`Tmem.Pair.ReturnReady`). A thread whose last event is an operation that waits and is not
covered is pending (`pending_of_mustWait`): the return is the last event of its thread
(`Step.pending_is_last`).

A thread whose last event cannot return yet (`TmemWait`) is uncovered, since a covered event is
performed. In a safe maximal execution it steps (`tmem_wait_steps`): a ready step of its pair (a
CTA's allocator performing a request, or a pairing) is recorded by a counted extension
(`tmem_ready_steps`, from `Step.entry_counted` and `Step.pairing_counted`), and
otherwise a lane of the pair that has made no more operations is pending and earlier in the rank
table (`pair_dichotomy`, `time_lt_of_tmem`). The record of a performed operation holds the events
of all lanes of its warp, so an operation that is not ready cannot return yet
(`ReturnReady.ready`, `not_ready_tmem`). An open obligation of the pair (`.tmem`)
passes the same way to a pending lane, which ranks below a pending pair (`tmem_steps`). A released
pending thread at an operation's site issues it, or its undefined behaviour (`tmem_next_steps`, from
`Step.tccoll_counted_extension`); an allocation's result is column 0, since its CTA's history
is empty while its warp has not allocated. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Tmem.Pair Classical

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A thread whose last event is a paired Tensor Memory operation that cannot return yet: its
CTA's allocator has not performed it, or it waits for its operation and no completion covers it. -/
def TmemWait (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ pc group dst action, X.get (g, (X.tr g).length - 1) =
      some ⟨pc, .tc (.resource group dst action)⟩ ∧ ¬ Ready L X (g, (X.tr g).length - 1)

/-- An allocation-management last event that is not ready cannot return yet. -/
theorem not_ready_tmem {g pc : Nat} {group : CtaGroup}
    {dst : Option Loc} {action : Tmem.Request}
    (hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .tc (.resource group dst action)⟩)
    (hnr : ¬ Ready L X (g, (X.tr g).length - 1)) : TmemWait L X g :=
  ⟨pc, group, dst, action, hlast, hnr⟩

/-- **A ready step steps**: recording a ready request or pairing is a counted extension of the
execution. -/
theorem tmem_ready_steps (hmax : Maximal L kernel Prod mem0 X)
    (hR : (∃ c r, Step.EntryReady L X c r) ∨ ∃ q, Step.PairingReady L X q)
      {o : Descent.Obligation} :
    Descent.Steps L kernel Prod mem0 (Descent.Obl L) (rank L) X o := by
  rcases hR with ⟨c, r, hR⟩ | ⟨q, hR⟩
  · obtain ⟨Y, hY, hle, hsize, -⟩ := Step.entry_counted hmax.1 hR
      (fun a ha => prod_wfFree a ha _)
    exact .inl ⟨Y, hY, hle, hsize⟩
  · obtain ⟨Y, hY, hle, hsize, -⟩ := Step.pairing_counted hmax.1 hR
      (fun a ha => prod_wfFree a ha _)
    exact .inl ⟨Y, hY, hle, hsize⟩

/-- A safe execution has no undefined behaviour. -/
theorem noUb_of_safe (hsafe : ¬ Unsafe L kernel Prod mem0 X) : ¬ HasUb X :=
  fun h => hsafe (by unfold Unsafe; exact .inl h)

/-- A safe execution has no aligned-instruction mismatch. -/
theorem noAligned_of_safe (hsafe : ¬ Unsafe L kernel Prod mem0 X) :
    ¬ AlignedMismatch L kernel X :=
  fun h => hsafe (by simp [Unsafe, h])

/-- **Progress at a paired Tensor Memory operation.** A thread whose last event is an uncovered
operation that its return waits for steps: a ready step of its pair is recorded by a
counted extension; otherwise a lane of the pair that has made no more operations is pending and
earlier in the rank table. -/
theorem tmem_wait_steps (hpre : Pre P L mem0) (ht : ThreadFacts L X)
    (hsafe : ¬ Unsafe L kernel Prod mem0 X) (hmax : Maximal L kernel Prod mem0 X) {g : Nat}
    (hw : TmemWait L X g) (hnr : ¬ ReturnReady L X (g, (X.tr g).length - 1)) :
    Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hub := noUb_of_safe hsafe
  obtain ⟨pc, group, dst, action, hlast, _⟩ := hw
  have hnc : ¬ Covered L X (g, (X.tr g).length - 1) :=
    fun hc => hnr ⟨hc.performed hX.tmemPair, fun _ => hc⟩
  have hg : g < L.threads := Frame.lt_of_get hX hlast
  rcases pair_dichotomy hpre ht hX hub (noAligned_of_safe hsafe) hg hlast hnc with
    hR | ⟨h, hp, hh0, hle⟩
  · exact tmem_ready_steps hmax hR
  · refine .inr ⟨X, .thread h, hmax, hp, ?_⟩
    have hlen : 0 < (X.tr g).length := by
      have : (X.tr g).length - 1 < (X.tr g).length := len_of_get hlast
      omega
    have hrel : ¬ Step.Released L X g :=
      fun hr => hnr (ReturnReady.of_ready hlast (hr.ready pc _ hlast rfl))
    obtain ⟨-, -, -, hsh, d, hσ, ha⟩ := ht.tmem_event hg (noUb_of hub g) hlast
    rw [Nat.sub_add_cancel hlen] at hσ
    have hlt := time_lt_of_tmem ht hub hp.1 hh0 hσ ha (lt_of_tmemShape hsh) hle
    have h1 := rank_thread_le (L := L) (X := X) (g := h)
    have h2 : rank L X (.thread g) = threadTime L X g + 1 := by simp [rank, hrel]
    omega

/-- **An open obligation of the pair passes to a pending thread**: an uncovered operation has a
ready step, or a pending lane of its pair, which ranks below a pending pair. -/
theorem tmem_steps (hpre : Pre P L mem0) (ht : ThreadFacts L X)
    (hsafe : ¬ Unsafe L kernel Prod mem0 X) (hmax : Maximal L kernel Prod mem0 X)
    (ho : Descent.Obl L X .tmem) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X .tmem := by
  have hX := hmax.1
  simp only [Descent.Obl, Drained, not_forall] at ho
  obtain ⟨i, pc, group, dst, action, hget, hn⟩ := ho
  rcases pair_dichotomy hpre ht hX (noUb_of_safe hsafe) (noAligned_of_safe hsafe)
      (Frame.lt_of_get hX hget) hget hn with hR | ⟨h, hp, -, -⟩
  · exact tmem_ready_steps hmax hR
  · exact .inr ⟨X, .thread h, hmax, hp, rank_thread_lt_tmem hp.1⟩

/-- **Progress at a paired Tensor Memory site.** A pending thread whose next event is a paired
Tensor Memory operation, and whose last event is released, issues it (an allocation names only
its column count) or its undefined behaviour: a counted extension. -/
theorem tmem_next_steps (ht : ThreadFacts L X)
    (hmax : Maximal L kernel Prod mem0 X) (hub : ¬ HasUb X) {g : Nat} (hp : Frame.Pending L X g)
    {d : ThreadD} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hat : d.AtTmem)
    (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  obtain ⟨t, hrun⟩ := Frame.run_some hX hub hp
  have hne : X.tr g ≠ [] := by
    intro h0
    have h0' : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inl ⟨.shfl, 0⟩)) := by
      rw [h0]
      rfl
    rw [h0'] at hσ
    cases hσ
    simp [ThreadD.AtTmem] at hat
  obtain ⟨t1, m, hl, hout, htm⟩ := ht.tmem_fire hg hσ hat hrun
  have hasm : ∀ e : Event, ∀ a ∈ Prod, a.wf L mem0 (X.snoc g e (fun _ => none)) :=
    fun e a ha => prod_wfFree a ha _
  cases m
  case ub f =>
    exact .inl (Step.plain_counted_extension hX hg (.inl hne) hrel hrun hl
      (o := none) (e := ⟨t1.pc, .ub f⟩) ⟨_, hout, by simp [Fires]⟩ trivial rfl nofun nofun nofun rfl
      (hX.tmemPairResult.snoc_not_wr nofun) (hasm _))
  case tc k u =>
    cases k
    case resource grp dst act =>
      obtain rfl := htm
      exact .inl (Step.tccoll_counted_extension hX hg (.inl hne) hrel hrun hl
        (o := some u) (pc := t1.pc) (k := .resource .two dst act)
        ⟨_, hout, by simp [Fires]⟩ rfl (hX.tmemPairResult.snoc_not_wr nofun)
        (hX.tcRead_snoc_tc nofun) (hasm _))
    all_goals simp [Flow.TmemTmpl] at htm
  all_goals simp [Flow.TmemTmpl] at htm

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
