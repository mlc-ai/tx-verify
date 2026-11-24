-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.TcCollDefs
public import Kernels.Fp16Gemm8192.Proof.Thread.TmemAt
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerTcFact
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerBars
public import Kernels.Fp16Gemm8192.Proof.Thread.AccExit
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoadWords
public import Kernels.Fp16Gemm8192.Proof.Thread.UbCons
public import Lemmas.Flow.TcLdTmpl

@[expose] public section

/-! # A consumer warp's warp-collective `tcgen05` events, at each event

At a consumer's state, the conjuncts of its run invariants count its collective events: its paired
operations by its state (`tmem_ops_at`), its data events thirty-two per accumulator release plus
its position in the tile (`Consumer.TcTile`), its accumulator releases its successful response
polls less its open task (`ClcPollInv`); every non-claiming response read is after its latest
poll (`Consumer.ReadInv`), and in its exit stage it has read one (`ConsInv`). So a collective
event is at a position of its warp's sequence that its count before it, with the thread's response
polls, determines (`tc_coll_fact`), and a consumer's exit follows all of its collective events
(`tc_exit_fact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}

/-- A warp-collective event is a Tensor Memory data event or a paired operation. -/
theorem isTcColl_cases {e : Event} (h : isTcColl e = true) :
    isTcData e = true ∨ isTmemOp e = true := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp [isTcColl] at h
  rename_i kd
  cases kd <;> simp_all [isTcData, isTmemOp]

/-- The counts at a consumer's state, from its run invariants. -/
theorem cons_counts (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {c : Consumer.D} (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.cons c)))) :
    g % L.block / 32 < 8 ∧
      tmemOps ((X.tr g).take k) =
        ThreadD.tmemOps (decide (g % L.block / 32 = 0)) (.inr (.cons c)) ∧
      dataOps ((X.tr g).take k) =
        32 * arrivals (Consumer.accEmpty L g (Consumer.accIdx L g)) ((X.tr g).take k) + c.tcPos ∧
      respPolls L g ((X.tr g).take k) =
        arrivals (Consumer.accEmpty L g (Consumer.accIdx L g)) ((X.tr g).take k) +
          Consumer.tileOpen c ∧
      NcLast L g ((X.tr g).take k) ∧ (c.doomed → NcRead L g ((X.tr g).take k)) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hw := role_warp hpre hX hg k hk.le _ hσ
  simp only [roleWarp] at hw
  have hops := (tmem_ops_at hpre hX hg hk hσ).1
  have hI := consInv hpre hg htr k _ hσ
  have hT : Consumer.TcTile L g c ((X.tr g).take k) := hI.2.2.2.2.2.2.1
  have hP := (clcPoll_inv hpre hg htr k _ hσ).2.1
  have hR : Consumer.ReadInv L g c ((X.tr g).take k) := Consumer.readInv_of hpre hX hg hσ
  have hlast : NcLast L g ((X.tr g).take k) := by
    rintro j rr ⟨pc, p, acq, sc, pcr, src, bs, h1, h2, ⟨h3, h4⟩, h5⟩ hnc
    exact (hR.1.1 j pc p acq sc pcr src bs rr h1 h2 h3 h4 h5 hnc).1
  refine ⟨hw, hops, hT, hP, hlast, fun hd => ?_⟩
  obtain ⟨j, pc, p, acq, sc, pcr, src, bs, rr, h1, h2, h3, h4, h5, h6⟩ := hI.2.2.1 hd
  exact ⟨j, rr, ⟨pc, p, acq, sc, pcr, src, bs, h1, h2, ⟨h3, h4⟩, h5⟩,
    hlast j rr ⟨pc, p, acq, sc, pcr, src, bs, h1, h2, ⟨h3, h4⟩, h5⟩ h6, h6⟩

set_option maxHeartbeats 8000000 in
/-- The address register of load `j` holds the warp group's accumulator column of chunk `j`. -/
theorem Consumer.ld_addr_reg {c : Consumer.D} {t : TState} {j : Fin 16}
    (hat : (code L g).AtD (.inr (.cons c)) t) (hs : c.site = .load j) :
    t.regs (Consumer.ldAddr j) =
      some (b32 (256 * (Consumer.tidOf L g / 32 / 4) + 16 * j.val)) := by
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := c
  simp only at hs hat
  subst hs
  fin_cases j
  all_goals
    exact reg_b32 hat.2.2.2.2 (by lit_mem) (by cons_values)

/-- A state at an event of a thread. -/
theorem state_at (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) (hne : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    ∃ d, Frame.stateAt (code L) X g k = some (some d) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨σ, hσ⟩ : ∃ σ, Frame.stateAt (code L) X g k = some σ := by
    rcases htr.fired he with ⟨τ, -, ha, -⟩ | ⟨-, hub⟩
    · exact ⟨τ, ha⟩
    · obtain ⟨pc', f, h⟩ := hub
      exact absurd h (hne pc' f)
  cases σ with
  | none => exact absurd hσ (tracked hpre hX g k hg)
  | some d => exact ⟨d, hσ⟩

set_option maxHeartbeats 8000000 in
/-- **A collective event is at a position of its warp's sequence** that its count before it, with
the thread's response polls, determines. -/
theorem tc_coll_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k pc : Nat} {kd : TcKind} (he : X.get (g, k) = some ⟨pc, .tc kd⟩)
    (hcoll : isTcColl ⟨pc, .tc kd⟩ = true) :
    g % L.block / 32 < 8 ∧ ∃ p, pc = tcCollPc p ∧ TcCollKind L g p kd ∧
      TcCollAt L g p ((X.tr g).take k) := by
  have hlen : k < (X.tr g).length := len_of_get he
  have he' : (X.tr g)[k]? = some ⟨pc, .tc kd⟩ := he
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  obtain ⟨d, hσ⟩ := state_at hpre hX hg he (by intro _ _ h; cases h)
  obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hcount := tcColl_count ((X.tr g).take k)
  rcases isTcColl_cases hcoll with hd | htm
  · -- a data event: a consumer's load or its wait
    obtain ⟨c, rfl, hs⟩ := data_role hpre hX hg he hσ hd
    obtain ⟨hw, hops, hT, hP, hlast, -⟩ := cons_counts hpre hX hg hlen hσ
    change kernel.code[c.site.pc]? = some ins at hc
    change Fires c.site.pc (eventTmpl Prod L g t ins.op) _ o at hfire
    have hops' : tmemOps ((X.tr g).take k) = if g % L.block / 32 = 0 then 1 else 0 := by
      rw [hops]
      rcases hs with ⟨j, hj⟩ | ⟨j, hj⟩ <;> by_cases h0 : g % L.block / 32 = 0 <;>
        simp [ThreadD.tmemOps, hj, h0]
    have hR := hcount
    rw [hops'] at hR
    rcases hs with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [hj] at hc hfire
      obtain rfl := Option.some.inj (hc.symm.trans (Consumer.code_load j))
      obtain ⟨vals, hev⟩ := fires_tcLd_addr (Consumer.ld_addr_reg hat hj)
        (by simp only [Consumer.tidOf]; have := j.isLt; omega) hfire hd
      simp only [Event.mk.injEq, Kind.tc.injEq] at hev
      obtain ⟨rfl, rfl⟩ := hev
      have hpos : c.tcPos = 2 * j.val := by simp [Consumer.D.tcPos, hj]
      have hopen : Consumer.tileOpen c = 1 := by simp [Consumer.tileOpen, hj]
      have hj16 := j.isLt
      refine ⟨hw, 2 * j.val, ?_, ?_, ?_⟩
      · simp only [tcCollPc, show 2 * j.val < 32 by omega, ↓reduceIte, Nat.mul_mod_right,
          show 2 * j.val / 2 = j.val by omega]
        rfl
      · simp only [TcCollKind, show 2 * j.val < 32 by omega, ↓reduceIte, Nat.mul_mod_right,
          show 2 * j.val / 2 = j.val by omega]
        exact ⟨vals, rfl⟩
      · refine ⟨fun _ => ⟨by omega, by omega⟩, fun h => by omega, fun h => by omega,
          fun h => absurd h (by omega), fun _ => hlast⟩
    · rw [hj] at hc hfire
      obtain rfl := Option.some.inj (hc.symm.trans (Consumer.code_wait j))
      have hev := fires_tcWaitLd hb hfire
      simp only [Event.mk.injEq, Kind.tc.injEq] at hev
      obtain ⟨rfl, rfl⟩ := hev
      have hpos : c.tcPos = 2 * j.val + 1 := by simp [Consumer.D.tcPos, hj]
      have hopen : Consumer.tileOpen c = 1 := by simp [Consumer.tileOpen, hj]
      have hj16 := j.isLt
      refine ⟨hw, 2 * j.val + 1, ?_, ?_, ?_⟩
      · simp only [tcCollPc, show 2 * j.val + 1 < 32 by omega, ↓reduceIte,
          show (2 * j.val + 1) % 2 = 1 by omega, show (2 * j.val + 1) / 2 = j.val by omega,
            Nat.one_ne_zero]
        rfl
      · simp only [TcCollKind, show 2 * j.val + 1 < 32 by omega, ↓reduceIte,
          show (2 * j.val + 1) % 2 = 1 by omega, Nat.one_ne_zero]
      · refine ⟨fun _ => ⟨by omega, by omega⟩, fun h => by omega, fun h => by omega,
          fun h => absurd h (by omega), fun _ => hlast⟩
  · -- a paired operation: warp 0's allocation, relinquishment or deallocation
    obtain ⟨grp, dst, act, rfl⟩ : ∃ grp dst act, kd = .resource grp dst act := by
      cases kd <;> simp_all [isTmemOp]
    obtain ⟨hw0, hgrp, hpc, hshape, -⟩ := tmem_event_at hpre hX hg he
    subst hgrp
    have hsite := tmem_site hat hc hfire htm
    obtain ⟨hops, hTW⟩ := tmem_ops_at hpre hX hg hlen hσ
    have hw0' : decide (g % L.block / 32 = 0) = true := by simpa using hw0
    rw [hw0'] at hops hTW
    rcases d with ⟨site, w⟩ | (l | m | sd | c)
    · change site = .alloc at hsite
      subst hsite
      have hdata : dataOps ((X.tr g).take k) = 0 :=
        (consInv hpre hg htr k _ hσ).2.2.2.1
      simp only [ThreadD.tmemOps] at hops
      rw [hops] at hpc hshape
      change kernel.code[Flow.tmemAlloc_0]? = some ins at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
      have hbase := hpre.sharedRange
      unfold sharedBytes at hbase
      have hal := hpre.sharedAlignment
      have hr44 : t.regs 90 = some (b32 L.sharedBase) :=
        (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
          (congrArg some (by pro_values))
      have hr45 : t.regs 91 = some (b32 512) :=
        (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
          (congrArg some (by pro_values))
      change Fires Flow.tmemAlloc_0 (eventTmpl Prod L g t _) _ o at hfire
      rw [tcAlloc_tmpl0 hb hr44 (by omega) (by omega) hr45 hat.2.1] at hfire
      obtain ⟨hev, -⟩ := hfire
      simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hev
      obtain ⟨-, -, rfl, rfl⟩ := hev
      refine ⟨by omega, 32, by simpa [tcCollPc] using hpc, ?_, ?_⟩
      · simp only [TcCollKind, show ¬ (32 < 32) by omega, ↓reduceIte]
      · refine ⟨fun h => absurd h (by omega), fun _ => hw0, fun _ => by omega,
          fun h => absurd h (by omega), fun h => absurd rfl h⟩
    · exact hsite.elim
    · exact hsite.elim
    · exact hsite.elim
    · obtain ⟨hw, hops', hT, hP, hlast, hread⟩ := cons_counts hpre hX hg hlen hσ
      have hR := hcount
      rcases hsite with hs | hs
      · simp only [ThreadD.tmemOps, ↓reduceIte, hs] at hops
        rw [hops] at hpc hshape hR
        change kernel.code[c.site.pc]? = some ins at hc
        change Fires c.site.pc (eventTmpl Prod L g t ins.op) _ o at hfire
        rw [hs] at hc hfire
        change kernel.code[Flow.tmemRelinquish_0]? = some ins at hc
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemRelinquish_0)
        obtain ⟨-, rfl, -⟩ := fires_tcRelinquish_resource hfire rfl
        have hpos : c.tcPos = 0 := by simp [Consumer.D.tcPos, hs]
        have hopen : Consumer.tileOpen c = 0 := by simp [Consumer.tileOpen, hs]
        have hdoom : c.doomed := by simp [Consumer.D.doomed, hs]
        refine ⟨hw, 33, by simpa [tcCollPc] using hpc, ?_, ?_⟩
        · simp only [TcCollKind, show ¬ (33 < 32) by omega, ↓reduceIte]
          simp only [TmemShape] at hshape
          simp [hshape]
        · refine ⟨fun h => absurd h (by omega), fun _ => hw0, fun h => absurd h (by omega),
            fun _ => ⟨by omega, hread hdoom⟩, fun _ => hlast⟩
      · simp only [ThreadD.tmemOps, ↓reduceIte, hs] at hops
        rw [hops] at hpc hshape hR
        change kernel.code[c.site.pc]? = some ins at hc
        change Fires c.site.pc (eventTmpl Prod L g t ins.op) _ o at hfire
        rw [hs] at hc hfire
        change kernel.code[Flow.tmemDealloc_0]? = some ins at hc
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemDealloc_0)
        obtain ⟨-, rfl, -⟩ := fires_tcDealloc_resource hfire rfl
        have hpos : c.tcPos = 0 := by simp [Consumer.D.tcPos, hs]
        have hopen : Consumer.tileOpen c = 0 := by simp [Consumer.tileOpen, hs]
        have hdoom : c.doomed := by simp [Consumer.D.doomed, hs]
        refine ⟨hw, 34, by simpa [tcCollPc] using hpc, ?_, ?_⟩
        · simp only [TcCollKind, show ¬ (34 < 32) by omega, ↓reduceIte]
          simp only [TmemShape] at hshape
          simpa using hshape
        · refine ⟨fun h => absurd h (by omega), fun _ => hw0, fun h => absurd h (by omega),
            fun _ => ⟨by omega, hread hdoom⟩, fun _ => hlast⟩

set_option maxHeartbeats 4000000 in
/-- **A consumer exits after all of its collective events**: every tile's, and warp 0's three
operations, its latest response read claiming no CTA. -/
theorem tc_exit_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) (hw : g % L.block / 32 < 8) {k pc : Nat}
    (he : X.get (g, k) = some ⟨pc, .exit⟩) : TcExitAt L g ((X.tr g).take k) := by
  have hlen : k < (X.tr g).length := len_of_get he
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨d, hσ, -⟩ := exit_event_state' hpre hX hg he
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hp := ret_pc hc (fires_exit_op hfire rfl)
  rcases d with ⟨site, w⟩ | (l | m | s | c)
  · change site.pc ∈ _ at hp
    exfalso
    cases site <;> (clear * - hp; revert hp; decide +revert)
  · have := role_warp hpre hX hg _ hlen.le _ hσ
    simp [roleWarp, Prologue.warpOf] at this
    omega
  · have := role_warp hpre hX hg _ hlen.le _ hσ
    simp [roleWarp, Prologue.warpOf] at this
    omega
  · have := role_warp hpre hX hg _ hlen.le _ hσ
    simp [roleWarp, Prologue.warpOf] at this
    omega
  · have hs : c.site = .exit := by
      obtain ⟨site, m, n, m', n', cp, ap, resp, x, acc, base⟩ := c
      change site.pc ∈ _ at hp
      cases site
      case exit => rfl
      all_goals (exfalso; clear * - hp; revert hp; decide +revert)
    obtain ⟨-, hops, hT, hP, -, hread⟩ := cons_counts hpre hX hg hlen hσ
    have hcount := tcColl_count ((X.tr g).take k)
    have hpos : c.tcPos = 0 := by simp [Consumer.D.tcPos, hs]
    have hopen : Consumer.tileOpen c = 0 := by simp [Consumer.tileOpen, hs]
    have hdoom : c.doomed := by simp [Consumer.D.doomed, hs]
    refine ⟨?_, hread hdoom⟩
    by_cases h0 : g % L.block / 32 = 0 <;> simp [ThreadD.tmemOps, hs, h0] at hops <;>
      simp only [h0, ↓reduceIte] <;> omega

end

end PTX.Kernels.Fp16Gemm8192.Proof
