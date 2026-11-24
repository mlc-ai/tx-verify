-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsOrigin
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCluster
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressNext
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsFire
public import Lemmas.Flow.NotRegister

@[expose] public section

/-! # The cluster barrier's waits and the register requests' time (`ClusterWaitFacts`)

* **Positions.** The kernel's only cluster arrival is at `clusterArrive_0` and its only cluster
  wait at `clusterWait_0` (`kernel_clArrive_pcs`, `kernel_clWait_pcs`); an event is at its
  instruction's position (`fires_source_pc`), which gives `arrive_pc` and `wait_pc`.
* **Liveness.** A cluster-barrier operation fires at the prologue's arrival or wait site
  (`cluster_state`); the arrival continues at the wait, the wait at the role of the warp, whose
  start state exists for every role (`Role.start`), so the machine is at a state after it
  (`live`).
* **Times.** Every role state but the register request is later than the requests' time
  (`regT_lt_role`), and the request is at it (`regT_le_role`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A cluster arrival instruction. -/
def clArriveOp : Op → Bool
  | .cluster (.arrive ..) => true
  | _ => false

/-- A cluster wait instruction. -/
def clWaitOp : Op → Bool
  | .cluster (.wait ..) => true
  | _ => false

theorem kernel_clArrive_pcs : OpPcsFast kernel.code clArriveOp [Flow.clusterArrive_0] = true := by
  decide +kernel

theorem kernel_clWait_pcs : OpPcsFast kernel.code clWaitOp [Flow.clusterWait_0] = true := by
  decide +kernel

/-- **Every cluster-barrier arrival is at `clusterArrive_0`.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.ClusterWaitFacts_arrive_pc (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (ht : Frame.Tracked (code L) X) :
    ∀ {g k pc : Nat} {rel al : Bool}, g < L.threads →
      X.get (g, k) = some ⟨pc, .cluster (.arrive rel al)⟩ → pc = Flow.clusterArrive_0 := by
  intro g k pc rel al _ he
  obtain ⟨d, t, ins, o, -, -, -, -, hc, hf⟩ :=
    event_origin hpre hX ht (J := fun _ _ _ => True) (fun g _ => trueJ_run L g) he nofun
  have hop := fires_cluster_op hf rfl
  have hpc := OpPcsFast.mem kernel_clArrive_pcs hc (by rw [hop]; rfl)
  rw [List.mem_singleton] at hpc
  rw [← hpc]
  exact EventFrame.fires_source_pc hf

/-- **Every cluster-barrier wait is at `clusterWait_0`.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.ClusterWaitFacts_wait_pc (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (ht : Frame.Tracked (code L) X) :
    ∀ {g k pc : Nat} {al : Bool}, g < L.threads →
      X.get (g, k) = some ⟨pc, .cluster (.wait al)⟩ → pc = Flow.clusterWait_0 := by
  intro g k pc al _ he
  obtain ⟨d, t, ins, o, -, -, -, -, hc, hf⟩ :=
    event_origin hpre hX ht (J := fun _ _ _ => True) (fun g _ => trueJ_run L g) he nofun
  have hop := fires_cluster_op hf rfl
  have hpc := OpPcsFast.mem kernel_clWait_pcs hc (by rw [hop]; rfl)
  rw [List.mem_singleton] at hpc
  rw [← hpc]
  exact EventFrame.fires_source_pc hf

/-- **After a cluster-barrier operation the machine is at a state.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.ClusterWaitFacts_live (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (ht : Frame.Tracked (code L) X) :
    ∀ {g k pc : Nat} {op : ClusterOp}, g < L.threads →
      X.get (g, k) = some ⟨pc, .cluster op⟩ → ∃ d, St L X g (k + 1) = some (some d) := by
  intro g k pc op _ he
  obtain ⟨p, hσ, hs⟩ := cluster_state hpre hX ht he
  have hst : St L X g (k + 1) =
      (Prologue.next L g p ⟨pc, .cluster op⟩).map (Option.bind · (handoff L g)) := by
    unfold St
    rw [Frame.stateAt_succ he, hσ]
    rfl
  obtain ⟨s⟩ := p
  simp only at hs
  rcases hs with rfl | rfl
  · exact ⟨_, by rw [hst]; rfl⟩
  · rw [hst]
    simp only [Prologue.next, Option.map_some, Option.bind_some, handoff]
    generalize RoleKind.ofWarp (warpOf L g) = rk
    cases rk <;> exact ⟨_, rfl⟩

/-- Unfold the time tables' coordinates to numerals and slot arithmetic. -/
macro "time_unfold" : tactic => `(tactic| simp only [Progress.Time.loaderUse,
  Progress.Time.mmaAt, Progress.Time.mmaTail, Progress.Time.storeAt, Progress.Time.slotTime,
  Progress.Time.tailTime, Progress.Time.regT, Progress.Time.base, Progress.Time.span,
  Progress.Time.bandL, Progress.Time.bandM, Progress.Time.bandS, Progress.Time.bandC,
  Progress.Time.bandST, Progress.Time.idleExitT, Progress.Time.allocT,
  Progress.Time.allocWriteT, Progress.Time.bar0T, Progress.Time.ldBaseT, Progress.Time.shflQT,
  Progress.Time.freeT] at *)

/-- **Every role state but the register request is later than the requests' time.** -/
theorem regT_lt_role (L : Launch) (g : Nat) (r : Role) (h : nextKind (.inr r) ≠ .reg) :
    Progress.Time.regT < stateTime L g (.inr r) := by
  cases r with
  | idle s =>
    obtain ⟨s⟩ := s
    cases s <;> simp_all [nextKind, idleKind, stateTime, Progress.Time.idle,
      Progress.Time.idleExitT, Progress.Time.regT]
  | loader d =>
    simp only [stateTime, Progress.Time.loader]
    cases hs : d.site <;> simp [nextKind, loaderKind, hs] at h ⊢ <;> time_unfold <;> omega
  | mma d =>
    simp only [stateTime, Progress.Time.mma]
    cases hs : d.site <;> simp [nextKind, mmaKind, hs] at h ⊢ <;> time_unfold <;>
      (try split) <;> (try split) <;> omega
  | store d =>
    simp only [stateTime, Progress.Time.store]
    cases hs : d.site <;> simp [nextKind, storeKind, hs] at h ⊢ <;> time_unfold <;> omega
  | softmax d =>
    simp only [stateTime, Progress.Time.softmax]
    cases hs : d.site <;> simp [nextKind, softmaxKind, hs] at h ⊢
    all_goals (try split)
    all_goals time_unfold
    all_goals (first | omega | simp_all)
  | corr d =>
    simp only [stateTime, Progress.Time.correction]
    cases hs : d.site <;> simp [nextKind, corrKind, hs] at h ⊢
    all_goals (try split)
    all_goals time_unfold
    all_goals (first | omega | simp_all)

/-- A site of the register-request kind is a role's register request. -/
theorem reg_site (r : Role) (h : nextKind (.inr r) = .reg) :
    (∃ s : Idle.D, r = .idle s ∧ s.site = .setMaxReg) ∨
    (∃ d : Loader.D, r = .loader d ∧ d.site = .setMaxReg) ∨
    (∃ d : Mma.D, r = .mma d ∧ d.site = .setMaxReg) ∨
    (∃ d : Store.D, r = .store d ∧ d.site = .setMaxReg) ∨
    (∃ d : Softmax.D, r = .softmax d ∧ d.site = .setMaxReg) ∨
    (∃ d : Correction.D, r = .corr d ∧ d.site = .setMaxReg) := by
  cases r with
  | idle s => obtain ⟨s⟩ := s; cases s <;> simp_all [nextKind, idleKind]
  | loader d => cases hs : d.site <;> simp_all [nextKind, loaderKind]
  | mma d => cases hs : d.site <;> simp_all [nextKind, mmaKind]
  | store d => cases hs : d.site <;> simp_all [nextKind, storeKind]
  | softmax d => cases hs : d.site <;> simp_all [nextKind, softmaxKind]
  | corr d => cases hs : d.site <;> simp_all [nextKind, corrKind]

/-- **After a register request the thread is at a state later than the requests' time.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.RegWaitFacts_after (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (ht : Frame.Tracked (code L) X) :
    ∀ {g k pc n inst : Nat} {inc : Bool}, g < L.threads →
      X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩ →
      ∃ d, St L X g (k + 1) = some (some d) ∧ Progress.Time.regT < stateTime L g d := by
  intro g k pc n inst inc hg he
  obtain ⟨d, t, ins, u, hσ, -, hat, -, hc, hf⟩ :=
    event_cont hpre hX ht (J := fun _ _ _ => True) (fun g _ => trueJ_run L g) he
      (by rintro (⟨f, hf⟩ | hf) <;> cases hf)
  have hop := fires_setMaxReg_op hf rfl
  have hk := site_kindOp d hc
  rw [hop] at hk
  have hreg : nextKind d = .reg := by
    generalize nextKind d = k at hk
    cases k <;> simp_all [kindOp]
  have hst : St L X g (k + 1) = (code L g).next d ⟨pc, .setMaxReg inc n inst⟩ := by
    unfold St
    rw [Frame.stateAt_succ he, hσ]
    rfl
  rcases d with p | r
  · obtain ⟨s⟩ := p
    cases s <;> simp [nextKind, prologueKind] at hreg
  rcases reg_site r hreg with ⟨s, rfl, hs⟩ | ⟨d, rfl, hs⟩ | ⟨d, rfl, hs⟩ |
      ⟨d, rfl, hs⟩ |
      ⟨d, rfl, hs⟩ | ⟨d, rfl, hs⟩
  · refine ⟨_, by rw [hst]; simp [Idle.next, hs]; rfl, ?_⟩
    exact regT_lt_role L g _ (by simp [nextKind, idleKind])
  · refine ⟨_, by rw [hst]; simp [Loader.next, hs]; rfl, ?_⟩
    exact regT_lt_role L g _ (by split <;> simp [nextKind, loaderKind])
  · refine ⟨_, by rw [hst]; simp [Mma.next, hs]; rfl, ?_⟩
    exact regT_lt_role L g _ (by simp [nextKind, mmaKind])
  · refine ⟨_, by rw [hst]; simp [Store.next, hs]; rfl, ?_⟩
    exact regT_lt_role L g _ (by split <;> simp [nextKind, storeKind])
  · refine ⟨_, by rw [hst]; simp [Softmax.next, hs]; rfl, ?_⟩
    exact regT_lt_role L g _ (by simp [nextKind, softmaxKind])
  · refine ⟨_, by rw [hst]; simp [Correction.next, hs]; rfl, ?_⟩
    exact regT_lt_role L g _ (by simp [nextKind, corrKind])

/-- A register request event. -/
def isReg (e : Event) : Bool := match e.kind with
  | .setMaxReg .. => true
  | _ => false

/-- A register request instruction with an invalid count. -/
def badRegOp : Op → Bool
  | .setMaxReg _ n => !SetMaxNReg.validCount n
  | _ => false

theorem kernel_regs_valid : OpPcsFast kernel.code badRegOp [] = true := by
  decide +kernel

/-- **A role state past its register request follows the request.** -/
theorem reg_made (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) {g : Nat}
    (hg : g < L.threads) :
    ∀ j r, Frame.stateAt (code L) X g j = some (some (.inr r)) → nextKind (.inr r) ≠ .reg →
      ∃ x ∈ (X.tr g).take j, isReg x = true := by
  have htr := Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg
  have h := Code.run_inv (sound hpre hg) htr
    (fun d es => ∀ r, d = .inr r → nextKind (.inr r) ≠ .reg → ∃ x ∈ es, isReg x = true)
    (fun r h => by cases h) ?_
  · exact fun j r hσ hk => h j _ hσ r rfl hk
  intro d d' pre e t ins o hJ hat _ hc hf hn r hr hk
  subst hr
  rcases d with p | r0
  · change (Prologue.next L g p e).map (Option.bind · (handoff L g)) = some (some (.inr r)) at hn
    cases hx : Prologue.next L g p e with
    | none => rw [hx] at hn; cases hn
    | some x =>
      rw [hx] at hn
      cases x with
      | none => cases hn
      | some x =>
        cases x with
        | inl p' => simp [handoff] at hn
        | inr rk =>
          simp only [Option.map_some, Option.bind_some, handoff] at hn
          exfalso
          cases rk <;> simp only [Role.start, Option.map_some, Option.some.injEq,
            Sum.inr.injEq] at hn <;> subst hn <;>
            simp [nextKind, idleKind, loaderKind, mmaKind, storeKind, softmaxKind, corrKind,
              Idle.start, Softmax.start] at hk
  · by_cases hk0 : nextKind (.inr r0) = .reg
    · refine ⟨e, List.mem_append_right _ (List.mem_singleton_self e), ?_⟩
      have hkop := site_kindOp (L := L) (g := g) (.inr r0) hc
      rw [hk0] at hkop
      generalize hop : ins.op = op at hkop hf
      cases op <;> simp only [kindOp, Bool.false_eq_true] at hkop
      rename_i inc n
      have hv : SetMaxNReg.validCount n = true := by
        by_contra hne
        have := OpPcsFast.mem kernel_regs_valid hc (by rw [hop]; simpa [badRegOp] using hne)
        simp at this
      obtain ⟨inst, rfl⟩ := fires_of_setMaxReg_op hv hf
      rfl
    · obtain ⟨x, hx, hr⟩ := hJ r0 rfl hk0
      exact ⟨x, List.mem_append_left _ hx, hr⟩

theorem prologue_time_lt (s : Prologue.Site) : Progress.Time.prologue s < Progress.Time.regT := by
  cases s <;> site_decide

theorem reg_time (L : Launch) (g : Nat) (r : Role) (h : nextKind (.inr r) = .reg) :
    stateTime L g (.inr r) = Progress.Time.regT := by
  rcases reg_site r h with ⟨s, rfl, hs⟩ | ⟨d, rfl, hs⟩ | ⟨d, rfl, hs⟩ |
      ⟨d, rfl, hs⟩ |
      ⟨d, rfl, hs⟩ | ⟨d, rfl, hs⟩ <;>
    simp [stateTime, Progress.Time.idle, Progress.Time.loader, Progress.Time.mma,
      Progress.Time.store, Progress.Time.softmax, Progress.Time.correction, hs]

/-- **A thread that has made no register request is no later than the requests' time.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.RegWaitFacts_before (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (_ht : Frame.Tracked (code L) X) :
    ∀ {g : Nat}, g < L.threads →
      (∀ j pc inc n inst, X.get (g, j) ≠ some ⟨pc, .setMaxReg inc n inst⟩) →
      endTime L X g ≤ Progress.Time.regT := by
  intro g hg hno
  have noreg : ∀ j, ∀ x ∈ (X.tr g).take j, isReg x = false := by
    intro j x hx
    obtain ⟨i, -, hget⟩ := get_of_mem_take hx
    obtain ⟨pc, k⟩ := x
    cases k <;> simp only [isReg]
    exact absurd hget (hno i pc _ _ _)
  -- the time of a state the thread reaches without a register request
  have timeOf : ∀ j d, Frame.stateAt (code L) X g j = some (some d) →
      stateTime L g d ≤ Progress.Time.regT ∧
        ((∃ p, d = .inl p) ∨ nextKind d = .reg) := by
    intro j d hσ
    rcases d with p | r
    · exact ⟨(prologue_time_lt p.site).le, .inl ⟨p, rfl⟩⟩
    · by_cases hk : nextKind (.inr r) = .reg
      · exact ⟨(reg_time L g r hk).le, .inr hk⟩
      · obtain ⟨x, hx, hr⟩ := reg_made hpre hX hg j r hσ hk
        rw [noreg j x hx] at hr
        cases hr
  unfold Sched.threadTime; dsimp only [timed]
  split
  · rename_i d hσ
    exact (timeOf _ d hσ).1
  · exact Nat.zero_le _
  · rename_i hσ
    split
    · rename_i d hσ'
      -- the last event fired at `d` and stopped the machine
      have hlen : 0 < (X.tr g).length := by
        by_contra h0
        have hl : (X.tr g).length = 0 := by omega
        have h1 : Frame.stateAt (code L) X g (X.tr g).length = some (some (code L g).init) := by
          rw [hl]
          exact Frame.stateAt_zero
        rw [h1] at hσ
        cases hσ
      obtain ⟨hle, hk⟩ := timeOf _ d hσ'
      rcases hk with ⟨p, rfl⟩ | hk
      · have := prologue_time_lt p.site
        simp only [stateTime]
        omega
      · exfalso
        -- the last event is a register request
        have hj : (X.tr g).length - 1 < (X.tr g).length := by omega
        obtain ⟨e, he⟩ : ∃ e, X.get (g, (X.tr g).length - 1) = some e :=
          ⟨_, List.getElem?_eq_getElem hj⟩
        obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
          Frame.fired_site (C := code L) (fun _ hg => sound hpre hg) hX he hσ'
        have hkop := site_kindOp (L := L) (g := g) d hc
        rw [hk] at hkop
        generalize hop : ins.op = op at hkop hf
        cases op <;> simp only [kindOp, Bool.false_eq_true] at hkop
        rename_i inc n
        have hv : SetMaxNReg.validCount n = true := by
          by_contra hne
          have := OpPcsFast.mem kernel_regs_valid hc (by rw [hop]; simpa [badRegOp] using hne)
          simp at this
        obtain ⟨inst, rfl⟩ := fires_of_setMaxReg_op hv hf
        exact hno _ _ _ _ _ he
    · exact Nat.zero_le _

/-- No role step returns to the role's register request (per role: its successor function never
yields its `setMaxReg` site). -/
def NoRegReentry (L : Launch) : Prop :=
  ∀ {g : Nat} {r r' : Role} {e : Event}, (code L g).next (.inr r) e = some (some (.inr r')) →
    nextKind (.inr r') ≠ .reg

/-- **A thread at a register request has made none, and its last event is a cluster-barrier
operation.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.NextFacts_reg_entry (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (hnr : NoRegReentry L) :
    ∀ {g : Nat} {d : ThreadD}, g < L.threads →
      Frame.stateAt (code L) X g (X.tr g).length = some (some d) → nextKind d = .reg →
      (∃ pc op, X.get (g, (X.tr g).length - 1) = some ⟨pc, .cluster op⟩) ∧
        ∀ j pc inc n inst, X.get (g, j) ≠ some ⟨pc, .setMaxReg inc n inst⟩ := by
  intro g d hg hσ hk
  have htr := Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg
  have hJ := Code.run_inv (sound hpre hg) htr
    (fun d es => (∀ p, d = .inl p → ∀ x ∈ es, Prologue.ProKind x.kind) ∧
      (∀ r, d = .inr r → nextKind (.inr r) = .reg →
        (∀ x ∈ es, isReg x = false) ∧
          ∃ x op, es.getLast? = some x ∧ x.kind = .cluster op))
    ⟨fun _ _ x hx => (List.not_mem_nil hx).elim, fun r h => (Sum.inl_ne_inr h).elim⟩ ?_
  · obtain ⟨-, h2⟩ := hJ (X.tr g).length d (by rw [← Frame.stateAt]; exact hσ)
    rw [List.take_length] at h2
    rcases d with p | r
    · obtain ⟨s⟩ := p
      cases s <;> simp [nextKind, prologueKind] at hk
    obtain ⟨hno, x, op, hl, hx⟩ := h2 r rfl hk
    refine ⟨⟨x.pc, op, ?_⟩, fun j pc inc n inst he => ?_⟩
    · rw [← hx]
      change (X.tr g)[(X.tr g).length - 1]? = some x
      rw [← List.getLast?_eq_getElem?]
      exact hl
    · have hx' := hno _ (List.mem_of_getElem? he)
      simp [isReg] at hx'
  intro d d' pre e t ins o hJ hat _ hc hf hn
  obtain ⟨hJ1, hJ2⟩ := hJ
  rcases d with p | r
  · change (Prologue.next L g p e).map (Option.bind · (handoff L g)) = some (some d') at hn
    have hat' : At t p.site.pc (Prologue.facts L g p) :=
      ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩
    cases hx : Prologue.next L g p e with
    | none => rw [hx] at hn; cases hn
    | some x =>
      rw [hx] at hn
      cases x with
      | none => cases hn
      | some x =>
        have hev : Prologue.EvOk L g p.site e.kind := by
          rcases Prologue.event_cases hpre hat' hc hf with h | ⟨-, h⟩
          · exact h
          · exact absurd hx (h x)
        have hall : ∀ y ∈ pre ++ [e], Prologue.ProKind y.kind := by
          intro y hy
          rcases List.mem_append.mp hy with hy | hy
          · exact hJ1 p rfl y hy
          · rw [List.mem_singleton.mp hy]; exact hev.proKind
        cases x with
        | inl p' =>
          simp only [Option.map_some, Option.bind_some, handoff, Option.some.injEq] at hn
          subst hn
          exact ⟨fun _ _ => hall, fun r h => (Sum.inl_ne_inr h).elim⟩
        | inr rk =>
          have hs : p.site = .clWait := by
            obtain ⟨s⟩ := p
            cases s <;> simp only [Prologue.next] at hx
            all_goals (repeat' split at hx) <;> simp_all
          refine ⟨fun p' h => ?_, fun r _ _ => ?_⟩
          · simp only [Option.map_some, Option.bind_some, handoff] at hn
            subst h
            cases rk <;> simp [Role.start] at hn
          · rw [hs] at hev
            obtain ⟨op, hop⟩ := hev
            refine ⟨fun y hy => ?_, e, op, by simp, hop⟩
            have hk := hall y hy
            obtain ⟨pc, k⟩ := y
            cases k <;> simp only [Prologue.ProKind] at hk <;> rfl
  · obtain ⟨r', rfl, -⟩ := code_next_inr hn
    refine ⟨fun p h => (Sum.inl_ne_inr h.symm).elim, fun r'' h hk => ?_⟩
    cases h
    exact absurd hk (hnr hn)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
