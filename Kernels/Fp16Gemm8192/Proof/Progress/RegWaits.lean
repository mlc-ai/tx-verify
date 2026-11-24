-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.PassThread
public import Lemmas.Step.SetMaxNReg
public import Lemmas.Step.RegIssue

@[expose] public section

/-! # Progress at the register request

The class of the register request (`setmaxnreg`): a thread whose last event is a request whose
warp is incomplete (`RegWait`, DEP-SETMAXNREG-RENDEZVOUS). A lane of the request's warp has made no
request (`unissued_of_not_same`): it is pending, and earlier in the rank table, since the states
before a request are early and the states after it are late (`regEarly`, `regLate`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX Classical

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The ordinal of a request is the requests before it in its thread. -/
theorem ordinal_eq (e : EvId) : SetMaxNReg.ordinal X e = regOps ((X.tr e.1).take e.2) := rfl

/-- A thread with a request event has made a request. -/
theorem regOps_ne_of_get {g k pc : Nat} {inc : Bool} {n inst : Nat}
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) : regOps (X.tr g) ≠ 0 := by
  have he' : (X.tr g)[k]? = some ⟨pc, .setMaxReg inc n inst⟩ := he
  have hmem : (⟨pc, .setMaxReg inc n inst⟩ : Event) ∈ X.tr g := List.mem_of_getElem? he'
  have : 0 < regOps (X.tr g) := List.countP_pos_iff.mpr ⟨_, hmem, rfl⟩
  exact Nat.pos_iff_ne_zero.mp this

/-- A thread that has made a request has a request event. -/
theorem exists_request_of_regOps {es : List Event} (h : regOps es ≠ 0) :
    ∃ (j pc : Nat) (inc : Bool) (n inst : Nat), es[j]? =
      some (⟨pc, .setMaxReg inc n inst⟩ : Event) := by
  have hpos : 0 < es.countP isSetMaxReg := Nat.pos_of_ne_zero h
  obtain ⟨a, ha, hsm⟩ := List.countP_pos_iff.mp hpos
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ha
  obtain ⟨pc, k⟩ := a
  cases k <;> simp [isSetMaxReg] at hsm
  exact ⟨j, pc, _, _, _, hj⟩

/-- **A lane with no matching request has made no request.** A thread of the request's warp
whose events match none of it has no request: its request would be the warp's, and its first. -/
theorem unissued_of_not_same (ht : ThreadFacts L X) {e : EvId} {pc n inst : Nat} {inc : Bool}
    (he : SetMaxNReg.Request X e pc inc n inst) (hge : e.1 < L.threads) {h : Nat}
    (hh : h < L.threads) (hw : SameWarp L e.1 h)
    (hno : ∀ j, ¬ SetMaxNReg.SameRequest L X e (h, j)) : regOps (X.tr h) = 0 := by
  by_contra hne
  obtain ⟨j, pc', inc', n', inst', hj⟩ := exists_request_of_regOps hne
  have hj' : X.get (h, j) = some ⟨pc', .setMaxReg inc' n' inst'⟩ := hj
  obtain ⟨hs1, hord1, -⟩ := ht.reg_event hge he
  obtain ⟨hs2, hord2, -⟩ := ht.reg_event hh hj'
  rw [← hw.2] at hs2
  have hs : (pc, inc, n) = (pc', inc', n') := hs1.trans hs2.symm
  simp only [Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl, rfl⟩ := hs
  exact hno j ⟨hw, by rw [ordinal_eq, ordinal_eq]; simp only [hord1, hord2], pc, inc, n, inst,
    inst',
    he, hj'⟩

/-- A state in the exit stage has made its request. -/
theorem regOps_ne_of_exitOff {d : ThreadD} (h : d.exitOff ≠ none) : d.regOps ≠ 0 := by
  rcases d with ⟨site, w'⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w', q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
  · exact absurd rfl h
  · simp [ThreadD.regOps]
  · simp [ThreadD.regOps]
  · simp [ThreadD.regOps]
  · have hs : site ≠ .setMaxReg := by
      intro hs
      simp [ThreadD.exitOff, Consumer.exitOff, hs] at h
    simp [ThreadD.regOps, hs]

/-- A thread with no request is no exit, by its state and the requests of its prefix. -/
theorem unissued_not_exit (ht : ThreadFacts L X) {h : Nat} (hh : h < L.threads)
    (hu : regOps (X.tr h) = 0) : ∀ pc, (X.tr h).getLast? ≠ some ⟨pc, .exit⟩ := by
  intro pc hl
  have hne : X.tr h ≠ [] := by
    intro h0
    rw [h0] at hl
    cases hl
  have hget : X.get (h, (X.tr h).length - 1) = some ⟨pc, .exit⟩ := by
    change (X.tr h)[(X.tr h).length - 1]? = _
    rw [← List.getLast?_eq_getElem?]
    exact hl
  obtain ⟨d, hσ, hx⟩ := ht.exit_event_state hh hget
  have h1 := ht.reg_ops hh hσ
  have h2 := regOps_ne_of_exitOff (d := d) hx
  have h3 : regOps ((X.tr h).take ((X.tr h).length - 1)) ≤ regOps (X.tr h) :=
    (List.take_sublist _ _).countP_le
  omega

/-- An unissued thread of the cluster of a started thread is pending. -/
theorem pending_unissued (ht : ThreadFacts L X) (hX : Consistent L kernel Prod mem0 X)
    {g h : Nat} (hg : g < L.threads) (hne : X.tr g ≠ []) (hh : h < L.threads)
    (hc : L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block))
    (hu : regOps (X.tr h) = 0) : Frame.Pending L X h :=
  ⟨hh, not_canceled_of_peer hX hg hne hc, unissued_not_exit ht hh hu⟩

/-- **An unissued thread is earlier than an issued one.** A thread with no request is early in the
rank table, and a thread with one is late, when the warps' bounds are ordered. -/
theorem threadTime_lt_of_reg (ht : ThreadFacts L X) {g h : Nat} (hg : g < L.threads)
    (hh : h < L.threads) {dg : ThreadD}
    (hσg : Frame.stateAt (code L) X g (X.tr g).length = some (some dg)) (hgi : regOps (X.tr g) ≠ 0)
    (hhu : regOps (X.tr h) = 0)
    (hlt : regEarly (h % L.block / 32) < regLate (g % L.block / 32)) :
    threadTime L X h < threadTime L X g := by
  have hsg := (ht.reg_stage hg hσg).2 hgi
  have hbase : 1 ≤ exitBase L X := by simp only [exitBase]; omega
  -- the early thread `h`
  have hh1 : threadTime L X h < exitBase L X ∧
      threadTime L X h ≤ regEarly (h % L.block / 32) := by
    cases hσh : Frame.stateAt (code L) X h (X.tr h).length with
    | none => simp only [threadTime, hσh]; omega
    | some σ =>
      cases σ with
      | none => exact absurd hσh (ht.tracked h _ hh)
      | some dh =>
        obtain ⟨hex, hv⟩ := (ht.reg_stage hh hσh).1 hhu
        have h1 := threadTime_lt_exitBase (X := X) hh hσh hex
        rw [threadTime_of hσh hex] at h1 ⊢
        exact ⟨h1, hv⟩
  rcases hsg with hsome | hge
  · obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hsome
    rw [threadTime_exit hσg ho]
    omega
  · cases hx : dg.exitOff with
    | none =>
      rw [threadTime_of hσg hx]
      omega
    | some o =>
      rw [threadTime_exit hσg hx]
      omega

/-- A thread of the warp of `g` in a given lane. -/
theorem warp_mate (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) {lane : Nat}
    (hl : lane < 32) : ∃ h, h < L.threads ∧ SameWarp L g h ∧ laneOf L h = lane := by
  have hb := hpre.block
  refine ⟨g / L.block * L.block + g % L.block / 32 * 32 + lane, ?_, ?_, ?_⟩
  all_goals simp only [Launch.threads, SameWarp, SameCta, laneOf, hb] at hg ⊢
  · omega
  · refine ⟨⟨hg, ?_, ?_⟩, ?_⟩ <;> omega
  · omega

/-- A thread whose last event is a register request that is not ready: some lane of its warp has
no matching request (DEP-SETMAXNREG-RENDEZVOUS). -/
def RegWait (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ pc inc n inst, X.get (g, (X.tr g).length - 1) = some ⟨pc, .setMaxReg inc n inst⟩ ∧
    ¬ Ready L X (g, (X.tr g).length - 1)

/-- A thread that waits for a request passes to an unissued thread of its cluster that is earlier
in the rank table. -/
theorem steps_of_unissued (ht : ThreadFacts L X) (hmax : Maximal L kernel Prod mem0 X) {g h : Nat}
    (hg : g < L.threads) (hne : X.tr g ≠ []) {dg : ThreadD}
    (hσg : Frame.stateAt (code L) X g (X.tr g).length = some (some dg)) (hgi : regOps (X.tr g) ≠ 0)
    (hh : h < L.threads) (hc : L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block))
    (hu : regOps (X.tr h) = 0) (hrel : ¬ Step.Released L X g)
    (hlt : regEarly (h % L.block / 32) < regLate (g % L.block / 32)) :
    Descent.Steps L kernel Prod mem0 (Descent.Obl L) (rank L) X (.thread g) := by
  refine .inr ⟨X, .thread h, hmax, pending_unissued ht hmax.1 hg hne hh hc hu, ?_⟩
  have h1 := rank_thread_le (L := L) (X := X) (g := h)
  have h2 : rank L X (.thread g) = threadTime L X g + 1 := by simp [rank, hrel]
  have := threadTime_lt_of_reg ht hg hh hσg hgi hu hlt
  omega

/-- **Progress at a register request.** A pending thread whose last event is a register request
whose warp is incomplete steps: a thread of the warp that has made no request is pending and
earlier in the rank table. -/
theorem reg_wait_steps (hpre : Pre P L mem0) (ht : ThreadFacts L X)
    (hsafe : ¬ Unsafe L kernel Prod mem0 X) (hmax : Maximal L kernel Prod mem0 X) {g : Nat}
    (hp : Frame.Pending L X g) (hw : RegWait L X g) : Descent.Steps L kernel Prod mem0
      (Descent.Obl L) (rank L) X (.thread g) := by
  obtain ⟨pc, inc, n, inst, hlast, hm⟩ := hw
  have hg := hp.1
  have hlen : 0 < (X.tr g).length := by
    have : (X.tr g).length - 1 < (X.tr g).length := len_of_get hlast
    omega
  have hne : X.tr g ≠ [] := List.ne_nil_of_length_pos hlen
  have hrel : ¬ Step.Released L X g := fun hr => hm (hr.ready pc _ hlast rfl)
  obtain ⟨-, -, dg, hσ'⟩ := ht.reg_event hg hlast
  have hσg : Frame.stateAt (code L) X g (X.tr g).length = some (some dg) := by
    rwa [Nat.sub_add_cancel hlen] at hσ'
  have hgi := regOps_ne_of_get hlast
  obtain ⟨lane, hl, hmiss⟩ := Step.missing_member_lane hsafe hlast hm
  obtain ⟨h, hh, hwh, hlane⟩ := warp_mate hpre hg hl
  have hu := unissued_of_not_same ht hlast hg hh hwh (hmiss h hh hwh hlane).1
  refine steps_of_unissued ht hmax hg hne hσg hgi hh (by rw [hwh.1.2.2]) hu hrel ?_
  rw [← hwh.2]
  simp only [regEarly, regLate]
  split <;> omega

/-- **Progress at the register request site.** A pending thread whose next event is its register
request, and whose last event (the prologue's cluster wait) is released, issues it: a counted
extension. -/
theorem reg_next_steps (ht : ThreadFacts L X) (hmax : Maximal L kernel Prod mem0 X)
    (hub : ¬ HasUb X) {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hat : d.AtSetMaxReg)
    (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  obtain ⟨t, hrun⟩ := Frame.run_some hX hub hp
  obtain ⟨t1, u, hl, he⟩ := ht.reg_fire hg hσ hat hrun
  obtain ⟨pc, hprev⟩ := ht.reg_prev hg hσ hat
  have hne : X.tr g ≠ [] := by
    have : (X.tr g).length - 1 < (X.tr g).length := len_of_get hprev
    exact List.ne_nil_of_length_pos (by omega)
  have hops : regOps (X.tr g) = 0 := by
    have := ht.reg_ops hg hσ
    rw [List.take_length] at this
    rw [this]
    rcases d with ⟨site, w⟩ | (l | m | s | c)
    · change site = .setMaxReg at hat
      simp [ThreadD.regOps, hat]
    · exact hat.elim
    · exact hat.elim
    · exact hat.elim
    · change c.site = .setMaxReg at hat
      simp [ThreadD.regOps, hat]
  have hno : ∀ j pc' inc' n' inst', ¬ SetMaxNReg.Request X (g, j) pc' inc' n' inst' :=
    fun j pc' inc' n' inst' hr => regOps_ne_of_get hr hops
  obtain ⟨Y, hY, hle, hsize⟩ := Step.reg_issue_counted_extension hX hg hprev hrel.ready hno hrun hl
    (he 0) (fun a ha => prod_wfFree a ha _)
  exact .inl ⟨Y, hY, hle, hsize⟩

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
