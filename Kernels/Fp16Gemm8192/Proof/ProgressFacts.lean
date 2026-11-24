-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.Assembly
public import Kernels.Fp16Gemm8192.Proof.MmaFullFacts
public import Kernels.Fp16Gemm8192.Proof.AsyncFacts
public import Kernels.Fp16Gemm8192.Proof.ConsAccBlocked
public import Kernels.Fp16Gemm8192.Proof.ClcBlockedFacts
public import Kernels.Fp16Gemm8192.Proof.AckBlockedFacts
public import Kernels.Fp16Gemm8192.Proof.Region.Accessors
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Blocker
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Commits
public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.AccWitness
public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Values
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaExact
public import Kernels.Fp16Gemm8192.Proof.Thread.PrologueIndex
public import Kernels.Fp16Gemm8192.Proof.Protocol.OutputRing.Sources
public import Kernels.Fp16Gemm8192.Proof.Protocol.Exit.Order
public import Kernels.Fp16Gemm8192.Proof.GuardFacts

@[expose] public section

/-! # ProgressGoal from the safety goal

This file sits at the top of the proof tree, outside the layer order (as `MmaFullFacts.lean` does):
it instantiates the progress assembly's `Progress.ClassFacts` with the thread facts, the protocol
exports and the blocker lemmas, and two static facts of the machines (`cons_clc_init`,
`live_after`). Then `progress_goal` needs only the safety goal. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **A consumer at its CLC response wait finds its CTA's response barrier initialized.** Its
last event was fired from a role state: the prologue enters the consumers at their register
request (`Prologue.next_cons`), not at the response wait. -/
theorem cons_clc_init (hpre : Pre P L mem0) {Y : Execution}
    (hY : Consistent L kernel Prod mem0 Y) {g : Nat} {c : Consumer.D} (hg : g < L.threads)
    (hub : ¬ HasUb Y) (hσ : Frame.stateAt (code L) Y g (Y.tr g).length =
      some (some (.inr (.cons c))))
    (hs : c.site = .clcWait) :
    ∃ pc, Y.get (g / L.block * L.block, (⟨.clc, 0, true⟩ : Bar).initIndex) =
      some ⟨pc, .mbInit (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (⟨.clc, 0, true⟩ : Bar).count⟩ :=
        by
  have ht := threadFacts hpre hY
  have hne := Progress.trace_ne_nil_of_role hσ
  have hl : 0 < (Y.tr g).length := List.length_pos_of_ne_nil hne
  obtain ⟨e, he⟩ : ∃ e, (Y.tr g)[(Y.tr g).length - 1]? = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hget : Y.get (g, (Y.tr g).length - 1) = some e := he
  obtain ⟨d0, hd0⟩ := Frame.state_of_noUb ht.sound hY ht.tracked hub hget
  have hsucc := Frame.stateAt_succ (C := code L) he
  rw [Nat.sub_add_cancel hl, hd0, hσ] at hsucc
  rcases d0 with p | r
  · have hn : Prologue.next L g p e = some (some (.inr (.cons c))) := hsucc.symm
    have := Prologue.next_cons hn
    subst this
    simp [Prologue.consStart] at hs
  · have hb : L.block = 384 := hpre.block
    have hgrid : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul (by omega)).mpr hg
    obtain ⟨pc, hi, -⟩ := ht.ring_initialized (b := ⟨.clc, 0, true⟩) hg hget hd0
      (by simp [Bar.Valid, Ring.slots]) hgrid rfl
    exact ⟨pc, hi⟩

/-- **The machine does not stop after a cluster operation, a named barrier arrival or a bulk-group
wait**: every cluster site, named barrier site and drain site has a successor state. -/
theorem live_after (hpre : Pre P L mem0) {Y : Execution} (hY : Consistent L kernel Prod mem0 Y)
    {g : Nat} (hg : g < L.threads) (hub : ¬ HasUb Y) (hl : 0 < (Y.tr g).length)
    (hk : (∃ pc op, Y.get (g, (Y.tr g).length - 1) = some ⟨pc, .cluster op⟩) ∨
      (∃ pc id cnt, Y.get (g, (Y.tr g).length - 1) = some ⟨pc, .bar id cnt⟩) ∨
      ∃ pc m n, Y.get (g, (Y.tr g).length - 1) = some ⟨pc, .bulkWait m n⟩) :
    Frame.stateAt (code L) Y g (Y.tr g).length ≠ none := by
  have ht := threadFacts hpre hY
  obtain ⟨e, he⟩ : ∃ e, (Y.tr g)[(Y.tr g).length - 1]? = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hget : Y.get (g, (Y.tr g).length - 1) = some e := he
  obtain ⟨d0, hd0⟩ := Frame.state_of_noUb ht.sound hY ht.tracked hub hget
  have hsucc := Frame.stateAt_succ (C := code L) he
  rw [Nat.sub_add_cancel hl, hd0] at hsucc
  rw [hsucc]
  show (code L g).next d0 e ≠ none
  rcases hk with ⟨pc, op, hc⟩ | ⟨pc, id, cnt, hc⟩ | ⟨pc, m, n, hc⟩
  · rw [hget] at hc
    cases hc
    have hat := (((ht.cl_ops hg hd0).2 _ hget).1 rfl).2
    rcases d0 with ⟨s, w, col⟩ | (⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩) <;>
      simp only [ThreadD.AtCluster] at hat <;>
      rcases hat with rfl | rfl <;>
      simp [code, Prologue.next, Loader.next, Mma.next, Scheduler.next, Consumer.next] <;>
      split_ifs <;> simp
  · rw [hget] at hc
    cases hc
    obtain ⟨c0, rfl⟩ := ht.bar_role hg hget hd0 rfl
    rcases (ht.cons_out hg hget hd0).2.2.2.2.1 id cnt rfl with
      ⟨hs, -⟩ | ⟨⟨k, hs | hs⟩, -⟩ <;>
      simp [code, Consumer.next, hs] <;> split_ifs <;> simp
  · rw [hget] at hc
    cases hc
    obtain ⟨c0, rfl⟩ := ht.bulk_role hg hget hd0 rfl
    rcases (ht.cons_out hg hget hd0).2.2.2.1 m n rfl with
      ⟨k, hs, -⟩ | ⟨hs, -⟩ <;>
      simp [code, Consumer.next, hs]

/-- **The proved classes' facts**, from the safety goal. -/
theorem class_facts (hpre : Pre P L mem0) (hs : SafeGoal kernel Prod L mem0) :
    Progress.ClassFacts L mem0 := by
  have hub : ∀ Y : Execution, Consistent L kernel Prod mem0 Y → ¬ HasUb Y :=
    fun Y hY => Progress.noUb_of_safe (hs.2 Y hY)
  have hub' : ∀ Y : Execution, Consistent L kernel Prod mem0 Y → ∀ g k pc f,
      Y.get (g, k) ≠ some ⟨pc, .ub f⟩ := fun Y hY g k pc f h => hub Y hY ⟨(g, k), pc, f, h⟩
  have hagree : ∀ Y, Consistent L kernel Prod mem0 Y → AllResponsesAgree L Y :=
    fun Y hY => ClcRing.allResponsesAgree hpre hY (threadFacts hpre hY)
      (Region.responseWriters hpre hY (threadFacts hpre hY))
  exact {
    safe := hs.2
    thread := fun _ hY => threadFacts hpre hY
    guard := fun _ hY => sync_guarded hpre hY
    agree := hagree
    clusterAll := fun _ hY => clusterExitAll hpre hY (threadFacts hpre hY)
    words := fun _ hY => TmemRing.tmemWords hY (threadFacts hpre hY)
    loader := {
      ub := hub
      thread := fun _ hY => threadFacts hpre hY
      blocked := fun _ hY => InputRing.inputBlocked hpre hY (threadFacts hpre hY)
      agree := hagree
      commits := fun _ hY => InputRing.commitsCounted hY (threadFacts hpre hY) }
    drain := {
      ub := hub
      thread := fun _ hY => threadFacts hpre hY
      blocked := fun _ hY => InputRing.drainBlocked hpre hY (threadFacts hpre hY)
      agree := hagree
      commits := fun _ hY => InputRing.commitsCounted hY (threadFacts hpre hY) }
    mmaObl := mma_obl hpre
    tensorObl := tensor_obl hpre
    store := {
      ub := hub
      thread := fun _ hY => threadFacts hpre hY
      sources := fun _ hY => OutputRing.outputSources hpre hY (threadFacts hpre hY)
        (hagree _ hY)
        (Region.stagingAccessors hpre hY (threadFacts hpre hY)) (hub' _ hY) }
    mmaFull := mma_full_facts_proved hpre hub
    acc := {
      ub := hub
      thread := fun _ hY => threadFacts hpre hY
      witness := fun _ hY => accEmptyWitness hpre hY (threadFacts hpre hY) (hub _ hY)
        (hagree _ hY) (mma_working_claims (threadFacts hpre hY)) }
    consAcc := cons_acc_blocked_proved hpre (fun _ hY => threadFacts hpre hY) hub'
    clc := clc_wait_facts_of hpre hub (ack_blocked_all hpre hub) (ack_rank_all hpre hub)
    consClcInit := fun _ _ _ hY hg hσ hs' => cons_clc_init hpre hY hg (hub _ hY) hσ hs'
    live := fun _ _ hY hg hl hk => live_after hpre hY hg (hub _ hY) hl hk }

/-- **ProgressGoal.** Every maximal execution is complete, given the safety goal. -/
theorem progress_goal (hpre : Pre P L mem0)
    (hs : SafeGoal kernel Prod L mem0) : ProgressGoal kernel Prod L mem0 :=
  Progress.progress_of_classes (class_facts hpre hs) hpre

end

end PTX.Kernels.Fp16Gemm8192.Proof
