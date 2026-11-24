-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ClusterCount
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleWarp
public import Kernels.Fp16Gemm8192.Proof.Thread.Tracked

@[expose] public section

/-! # A thread's register request in an execution

The request of a thread is the first and only one of its trace (`regOps`), it is the request of
its warp, and its time in the rank table is early before it and late after it (`regEarly`,
`regLate`). The counts are the run invariant of `ClusterCount.lean` (`ClInv`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- Before its request a state is early in the rank table: it is outside the exit stage, and at
most at the consumer's first site (a consumer state), or the prologue's. -/
theorem regStage_le {es : List Event} {d : ThreadD} {w : Nat}
    (hrole : ∀ c, d = .inr (.cons c) → w < 8) (h0 : d.regOps = 0) :
    d.exitOff = none ∧ d.vtime L g es ≤ regEarly w := by
  rcases d with ⟨site, w'⟩ | (l | m | s | c)
  · refine ⟨rfl, ?_⟩
    cases site <;> simp [ThreadD.regOps, ThreadD.vtime, Prologue.Site.vtime, regEarly] at h0 ⊢ <;>
      (try (rename_i i; have := i.isLt)) <;> first | omega | (split_ifs <;> omega)
  · simp [ThreadD.regOps] at h0
  · simp [ThreadD.regOps] at h0
  · simp [ThreadD.regOps] at h0
  · have hs : c.site = .setMaxReg := by
      by_contra h
      simp [ThreadD.regOps, h] at h0
    have hw := hrole c rfl
    simp [ThreadD.exitOff, Consumer.exitOff, ThreadD.vtime, Consumer.vtime, hs, regEarly, hw]

/-- After its request a state is late in the rank table: in the exit stage, or at least at its
warp's first site after it. -/
theorem regStage_ge {es : List Event} {d : ThreadD} {w : Nat}
    (hrole : ∀ r, d = .inr r → roleWarp w r)
    (hel : ∀ p : Prologue.D, d = .inl p → p.site = .roleElect → 8 ≤ w)
    (h1 : d.regOps ≠ 0) :
    d.exitOff.isSome ∨ regLate w ≤ d.vtime L g es := by
  rcases d with ⟨site, w'⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w', q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
  · have hs : site = .roleElect := by
      by_contra h
      simp [ThreadD.regOps, h] at h1
    subst hs
    have := hel _ rfl rfl
    right
    simp only [ThreadD.vtime, Prologue.Site.vtime, regLate]
    split <;> omega
  · have hw := hrole _ rfl
    simp only [roleWarp] at hw
    subst hw
    cases site <;> simp [ThreadD.exitOff, Loader.exitOff, ThreadD.vtime, Loader.vtime, ringAt,
      blockAt, blockSpan, regLate] <;> omega
  · have hw := hrole _ rfl
    simp only [roleWarp] at hw
    have h8 : 8 ≤ w := by omega
    cases site <;> simp [ThreadD.exitOff, Mma.exitOff, ThreadD.vtime, Mma.vtime, ringAt,
      blockAt, blockSpan, regLate, show ¬ w < 8 by omega] <;> omega
  · have hw := hrole _ rfl
    simp only [roleWarp] at hw
    have h8 : 8 ≤ w := by omega
    cases site <;> simp [ThreadD.exitOff, Scheduler.exitOff, ThreadD.vtime, Scheduler.vtime,
      blockAt, blockSpan, regLate, show ¬ w < 8 by omega] <;> omega
  · have hw := hrole _ rfl
    simp only [roleWarp] at hw
    have hs : site ≠ .setMaxReg := by
      intro h
      simp [ThreadD.regOps, h] at h1
    cases site <;> simp_all [ThreadD.exitOff, Consumer.exitOff, ThreadD.vtime, Consumer.vtime,
      blockAt, blockSpan, regLate] <;> omega

/-- **A thread's register requests at a prefix of its trace count its state's.** -/
theorem reg_ops_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {k : Nat} {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g k = some (some d)) : regOps ((X.tr g).take k) = d.regOps :=
  reg_ops_facts hpre hX hg hσ

/-- **A thread's register request is its warp's and its first**, and its state after it exists. -/
theorem reg_event_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {k pc : Nat} {inc : Bool}
    {n inst : Nat} (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) :
    (pc, inc, n) = regRequest (g % L.block / 32) ∧ regOps ((X.tr g).take k) = 0 ∧
      ∃ d, Frame.stateAt (code L) X g (k + 1) = some (some d) := by
  have hlen : k < (X.tr g).length := len_of_get he
  have he' : (X.tr g)[k]? = some ⟨pc, .setMaxReg inc n inst⟩ := he
  obtain ⟨σ, hσ⟩ : ∃ σ, Frame.stateAt (code L) X g k = some σ := by
    rcases (Frame.trace (fun _ => sound hpre) hX hg).fired he with ⟨τ, -, ha, -⟩ | ⟨-, hub⟩
    · exact ⟨τ, ha⟩
    · obtain ⟨pc', f, h⟩ := hub
      cases h
  obtain ⟨d, rfl⟩ : ∃ d, σ = some d := by
    cases σ with
    | none => exact absurd hσ (tracked hpre hX g k hg)
    | some d => exact ⟨d, rfl⟩
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hat := reg_site hc hfire (e := ⟨pc, .setMaxReg inc n inst⟩) rfl
  obtain ⟨inst', hev⟩ := reg_fire hat hc hfire
  simp only [Event.mk.injEq, Kind.setMaxReg.injEq] at hev
  obtain ⟨hpc, hinc, hn, -⟩ := hev
  have hops := reg_ops_fact hpre hX hg hσ
  have hk : k ≤ (X.tr g).length := hlen.le
  rcases d with ⟨site, w⟩ | (l | m | s | c)
  · change site = .setMaxReg at hat
    subst hat
    obtain ⟨hki, hw, hcanon⟩ := (onPath_all hpre hX hg k hk).1 _ hσ
    have h4 : w / 4 = 2 := hcanon.2.2.2.1 rfl
    have hpos : 0 < k := by
      have := Prologue.fenceIdx_pos L g w
      rw [hki]
      simp only [Prologue.index]
      omega
    have hww : w = g % L.block / 32 := hw hpos
    refine ⟨?_, by simpa [ThreadD.regOps] using hops, ?_⟩
    · rw [← hww]
      simp only [ThreadD.regRequest] at hpc hinc hn
      subst hpc hinc hn
      simp [regRequest, show ¬ w < 8 by omega]
    · rw [stateAt_succ_inl he' hσ]
      simp only [Prologue.next]
      split_ifs <;> first | exact ⟨_, rfl⟩ | (exfalso; omega)
  · exact hat.elim
  · exact hat.elim
  · exact hat.elim
  · change c.site = .setMaxReg at hat
    have hrw := role_warp hpre hX hg k hk _ hσ
    simp only [roleWarp, Prologue.warpOf] at hrw
    refine ⟨?_, by simpa [ThreadD.regOps, hat] using hops, ?_⟩
    · simp only [ThreadD.regRequest] at hpc hinc hn
      subst hpc hinc hn
      simp [regRequest, hrw]
    · let c' : Consumer.D := { c with site := .clcWait, m := Loader.claimM (g / L.block),
                                      n := Loader.claimN (g / L.block), cp := 0, ap := 0 }
      have hc' : Consumer.next L g c ⟨pc, .setMaxReg inc n inst⟩ = some (some c') := by
        simp [c', Consumer.next, hat]
      refine ⟨.inr (.cons c'), ?_⟩
      rw [Frame.stateAt_succ he', hσ]
      simp [Flow.Code.toMachine, code, hc']

/-- **A thread's time in the rank table is early before its request and late after it.** -/
theorem reg_stage_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) :
    (regOps (X.tr g) = 0 → d.exitOff = none ∧
      d.vtime L g (X.tr g) ≤ regEarly (g % L.block / 32)) ∧
    (regOps (X.tr g) ≠ 0 → d.exitOff.isSome ∨
      regLate (g % L.block / 32) ≤ d.vtime L g (X.tr g)) := by
  have hops : regOps (X.tr g) = d.regOps := by
    have := reg_ops_fact hpre hX hg hσ
    rwa [List.take_length] at this
  have hrole : ∀ r, d = .inr r → roleWarp (g % L.block / 32) r := by
    rintro r rfl
    exact role_warp hpre hX hg _ le_rfl r hσ
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · refine regStage_le (fun c hc => ?_) (hops ▸ h0)
    have := hrole _ hc
    simpa [roleWarp] using this
  · refine regStage_ge hrole (fun p hp hs => ?_) (hops ▸ h1)
    subst hp
    obtain ⟨hk, hw, hcanon⟩ := (onPath_all hpre hX hg _ le_rfl).1 p hσ
    have h11 := hcanon.2.2.2.2 hs
    have hpos : 0 < (X.tr g).length := by
      have := Prologue.fenceIdx_pos L g p.w
      rw [hk]
      simp only [Prologue.index, hs]
      omega
    have := hw hpos
    simp only [Prologue.warpOf] at this
    omega

/-- A state at its request site is at the request's instruction. -/
theorem reg_site_code {d : ThreadD} (hat : d.AtSetMaxReg) :
    (code L g).pc d = d.regRequest.1 ∧
      kernel.code[d.regRequest.1]? = some ⟨none, .setMaxReg d.regRequest.2.1 d.regRequest.2.2⟩ := by
  rcases d with ⟨site, w⟩ | (l | m | s | c)
  · change site = .setMaxReg at hat
    subst hat
    exact ⟨rfl, Flow.code_setMaxReg_0⟩
  · exact hat.elim
  · exact hat.elim
  · exact hat.elim
  · change c.site = .setMaxReg at hat
    exact ⟨by show c.site.pc = Flow.setMaxReg_1; rw [hat]; rfl, Flow.code_setMaxReg_1⟩

/-- **A thread at its register request can issue it.** -/
theorem reg_fire_fact (hpre : Pre P L mem0) (hg : g < L.threads) {es : List Event} {d : ThreadD}
    {t : TState}
    (hσ : (code L g).toMachine.after (some (code L g).init) es = some (some d))
    (hat : d.AtSetMaxReg) (hr : Run kernel Prod L g {} es (some t)) :
    ∃ t1 u, Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧ ∀ inst,
      EStep kernel Prod L g t1
        ⟨d.regRequest.1, .setMaxReg d.regRequest.2.1 d.regRequest.2.2 inst⟩ (some u) := by
  obtain ⟨t1, hl, hgood⟩ := Code.end_site (sound hpre hg) hr hσ
  have hout := Code.site_out (sound hpre hg) hgood
  obtain ⟨hpc, hc⟩ := reg_site_code (L := L) (g := g) hat
  have htpc : t1.pc = d.regRequest.1 := hgood.1.1.trans hpc
  rw [Code.tmpl, hpc, hc] at hout
  dsimp only at hout
  refine ⟨t1, next t1, hl, fun inst => ⟨_, hout, ?_⟩⟩
  rw [htpc]
  rcases d with ⟨site, w⟩ | (l | m | s | c)
  · change site = .setMaxReg at hat
    subst hat
    simp [eventTmpl, SetMaxNReg.tmpl, SetMaxNReg.validCount, Fires, ThreadD.regRequest]
  · exact hat.elim
  · exact hat.elim
  · exact hat.elim
  · simp [eventTmpl, SetMaxNReg.tmpl, SetMaxNReg.validCount, Fires, ThreadD.regRequest]

/-- Only the prologue's cluster wait leads to a request site. -/
theorem Prologue.next_wait_of_atSetMaxReg {p : Prologue.D} {e : Event} {d' : ThreadD}
    (hn : Prologue.next L g p e = some (some d')) (hat : d'.AtSetMaxReg) : p.site = .wait := by
  obtain ⟨site, w⟩ := p
  cases site
  case wait => rfl
  all_goals
    simp only [Prologue.next] at hn
    repeat' split at hn
  all_goals first
    | (cases hn; done)
    | (cases hn; simp_all [ThreadD.AtSetMaxReg, Prologue.afterInits, Prologue.afterElect]; done)
    | (cases hn; simp only [ThreadD.AtSetMaxReg, Prologue.afterInits, Prologue.afterElect] at hat
       split_ifs at hat)

/-- **A thread at its request site has just made its cluster wait.** -/
theorem reg_prev_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hat : d.AtSetMaxReg) :
    ∃ pc, X.get (g, (X.tr g).length - 1) = some ⟨pc, .cluster (.wait true)⟩ := by
  have hlen : 0 < (X.tr g).length := by
    by_contra h0
    have h0' : (X.tr g).length = 0 := by omega
    rw [h0', stateAt_zero] at hσ
    cases hσ
    exact absurd hat (by simp [ThreadD.AtSetMaxReg])
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[(X.tr g).length - 1]? = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hget : X.get (g, (X.tr g).length - 1) = some e := he
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hk1 := Frame.stateAt_succ (C := code L) (X := X) (g := g) he
  rw [Nat.sub_add_cancel hlen, hσ] at hk1
  cases hσk : Frame.stateAt (code L) X g ((X.tr g).length - 1) with
  | none => rw [hσk] at hk1; simp at hk1
  | some σ =>
    cases σ with
    | none => exact absurd hσk (tracked hpre hX g _ hg)
    | some dk =>
      rcases dk with p | r
      · have hn := stateAt_succ_inl he hσk
        rw [Nat.sub_add_cancel hlen, hσ] at hn
        have hw := Prologue.next_wait_of_atSetMaxReg hn.symm hat
        obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX hget hσk
        obtain ⟨site, w⟩ := p
        change site = .wait at hw
        subst hw
        change kernel.code[Flow.clusterWait_0]? = some ins at hc
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_0)
        simp only [eventTmpl, Fires] at hfire
        exact ⟨_, by rw [hget, hfire.1]⟩
      · rw [hσk] at hk1
        have hn : (code L g).next (.inr r) e = some (some d) := hk1.symm
        cases r with
        | loader l =>
          obtain ⟨l', -, rfl⟩ := next_of_loader hn
          exact hat.elim
        | mma m =>
          obtain ⟨m', -, rfl⟩ := next_of_mma hn
          exact hat.elim
        | sched s =>
          obtain ⟨s', -, rfl⟩ := next_of_sched hn
          exact hat.elim
        | cons c =>
          obtain ⟨c', hn', rfl⟩ := next_of_cons hn
          exact (Consumer.next_site_ne hn' hat).elim

end
end PTX.Kernels.Fp16Gemm8192.Proof
