-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface

@[expose] public section

/-! # The source and resource branches of `Unsafe`, from the interface

* The kernel's `tcgen05` instructions use one CTA group (`tc_group_uniform`, a fact of the
  program text).
* The kernel's two assumptions declare no execution undefined (`no_assumption_ub`).
* No register request is unsafe (`no_reg_unsafe`): every thread issues one request, its warp's
  (`ThreadFacts.reg_event`), as its first, so it has no previous request whose count its
  direction must agree with.
* The lanes of a warp make the same request (`no_setMaxReg_divergent`).
* No thread exits short of its warpgroup's register request (`no_setMaxReg_exited`): a thread
  exits only after its own request (`reg_ops`, `exit_event_state`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The kernel's `tcgen05` instructions agree on their CTA group. -/
theorem tc_group_uniform : kernel.TcGroupUniform := kernel_groupUniform

/-- The kernel's assumptions declare no execution undefined. -/
theorem no_assumption_ub : ¬ ∃ a ∈ Prod, a.ub L mem0 X := by
  simp [Assumptions.idealArith, Assumption.idealReal, Assumptions.clusterMbar,
    Assumption.clusterScopeMbarAt, Assumptions.pollAgree, Assumption.pollAgreeAt]

/-- The previous request count over a prefix without requests is the start. -/
theorem fold_no_req (start : Option Nat) :
    ∀ l : List Event, regOps l = 0 → l.foldl (fun old ev => match ev.kind with
      | .setMaxReg _ n _ => some n | _ => old) start = start
  | [], _ => rfl
  | e :: l, h => by
    rw [regOps, List.countP_cons] at h
    have hl : regOps l = 0 := by unfold regOps; omega
    have he : isSetMaxReg e = false := by
      cases hh : isSetMaxReg e
      · rfl
      · rw [hh] at h; simp at h
    obtain ⟨pc, k⟩ := e
    rw [List.foldl_cons]
    cases k <;> first | (simp [isSetMaxReg] at he; done) | exact fold_no_req start l hl

/-- A state in an exit stage has issued its register request. -/
theorem regOps_of_exit {d : ThreadD} (h : d.exitOff ≠ none) : d.regOps = 1 := by
  cases d with
  | inl p => exact absurd rfl h
  | inr r =>
    cases r with
    | cons c =>
      simp only [ThreadD.exitOff] at h
      simp only [ThreadD.regOps]
      split_ifs with hs
      · simp [Consumer.exitOff, hs] at h
      · rfl
    | _ => rfl

/-- **No register request is unsafe.** -/
theorem no_reg_unsafe (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : ¬ SetMaxNReg.Unsafe L X := by
  rintro ⟨e, pc, inc, n, inst, hreq, hu⟩
  have hg := Frame.lt_of_get hX hreq
  obtain ⟨hrq, hops, -⟩ := ht.reg_event hg hreq
  have hord : ∀ f : EvId, SetMaxNReg.ordinal X f = regOps ((X.tr f.1).take f.2) := fun _ => rfl
  have hblock := hpre.block
  rcases hu with ⟨m, hm, -⟩ | hgrp | ⟨f, pc', inc', n', inst', hsg, hreq', hof, hne⟩ |
      ⟨hpos, -⟩
  · have hp : SetMaxNReg.prior X e = none := fold_no_req _ _ hops
    rw [hp] at hm
    cases hm
  · rw [hblock] at hgrp
    omega
  · obtain ⟨hrq', -, -⟩ := ht.reg_event (Frame.lt_of_get hX hreq') hreq'
    obtain ⟨-, hwg⟩ := hsg
    rw [hblock] at hwg hrq hrq'
    have hw : (e.1 % 384 / 32 < 8 ↔ f.1 % 384 / 32 < 8) := by omega
    unfold regRequest at hrq hrq'
    by_cases h8 : e.1 % 384 / 32 < 8
    · simp only [h8, hw.mp h8, ↓reduceIte, Prod.mk.injEq] at hrq hrq'
      obtain ⟨rfl, rfl, rfl⟩ := hrq; obtain ⟨rfl, rfl, rfl⟩ := hrq'
      simp at hne
    · have h8' : ¬ f.1 % 384 / 32 < 8 := fun h' => h8 (hw.mpr h')
      simp only [h8, h8', ↓reduceIte, Prod.mk.injEq] at hrq hrq'
      obtain ⟨rfl, rfl, rfl⟩ := hrq; obtain ⟨rfl, rfl, rfl⟩ := hrq'
      simp at hne
  · rw [hord, hops] at hpos
    exact absurd hpos (by decide)

/-- **The lanes of a warp make the same register request**: the request's position is its
warp's (`ThreadFacts.reg_event`). -/
theorem no_setMaxReg_divergent (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    ¬ AlignedClass.setMaxReg.Divergent L kernel X := by
  intro hd
  obtain ⟨e, f, pc, pc', inc, inc', n, n', inst, inst', hw, he, hf, -, hne⟩ :=
    (AlignedClass.divergent_setMaxReg_iff L).mp hd
  obtain ⟨g, i⟩ := e
  obtain ⟨h, j⟩ := f
  obtain ⟨hrq, -⟩ := ht.reg_event (Frame.lt_of_get hX he) he
  obtain ⟨hrq', -⟩ := ht.reg_event (Frame.lt_of_get hX hf) hf
  have hwarp : g % L.block / 32 = h % L.block / 32 := hw.2
  rw [hwarp, ← hrq'] at hrq
  exact hne (congrArg Prod.fst hrq)

/-- **No thread exits short of its warpgroup's register request**: a thread exits only after its
own request, the first event of every thread. -/
theorem no_setMaxReg_exited (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    ¬ AlignedClass.setMaxReg.Exited L kernel X := by
  intro hx
  obtain ⟨e, pc, inc, n, inst, hreq, h, j, pc', hh, -, hex, hle⟩ :=
    AlignedClass.exited_setMaxReg_old L hx
  have hg := Frame.lt_of_get hX hreq
  obtain ⟨-, hops, -⟩ := ht.reg_event hg hreq
  have hord : ∀ f : EvId, SetMaxNReg.ordinal X f = regOps ((X.tr f.1).take f.2) := fun _ => rfl
  obtain ⟨d, hσ, hoff⟩ := ht.exit_event_state hh hex
  have h1 := ht.reg_ops hh hσ
  rw [regOps_of_exit hoff] at h1
  rw [hord, hord, h1, hops] at hle
  exact absurd hle (by decide)

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
