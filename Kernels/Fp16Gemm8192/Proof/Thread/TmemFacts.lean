-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ClusterCount
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleWarp
public import Kernels.Fp16Gemm8192.Proof.Thread.Tracked
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerExit
public import Kernels.Fp16Gemm8192.Proof.Thread.ExitSite

@[expose] public section

/-! # A thread's paired Tensor Memory operations in an execution

Along a thread's trace without undefined behaviour, its paired Tensor Memory operations count
its state's (`tmem_ops_fact`, a projection of the run invariant `ClInv`). An operation is made
by warp 0, is the thread's `n`-th of the allocation, the relinquishment and the deallocation, at
that operation's site and of its shape (`tmem_event_fact`). A thread of warp 0 is in the rank
table before its next operation (`tmem_stage_fact`), and exits after all three
(`tmem_exit_fact`). A thread at an operation's site fires the operation or undefined behaviour
(`tmem_fire_fact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}

/-- A thread's trace without undefined behaviour has prefixes without it. -/
theorem noUb_take (hnu : ∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) (k : Nat) :
    NoUb ((X.tr g).take k) := by
  intro e he f hk
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take he)
  exact hnu j e.pc f (by rw [← hk]; exact hj)

/-- **A thread's paired Tensor Memory operations count its state's.** -/
theorem tmem_ops_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) (hnu : ∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) {k : Nat} {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g k = some (some d)) :
    tmemOps ((X.tr g).take k) = d.tmemOps (decide (g % L.block / 32 = 0)) ∧
      d.TmemWarp (decide (g % L.block / 32 = 0)) := by
  have hi := (clusterInv hpre hg (Frame.trace (fun _ => sound hpre) hX hg) k _ hσ).2.2.2.2
  exact ⟨hi.1 (noUb_take hnu k), hi.2⟩

/-- A prologue state past the shuffle holds the thread's warp index. -/
theorem prologue_w (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} (hk : k ≤ (X.tr g).length) {p : Prologue.D}
    (hσ : Frame.stateAt (code L) X g k = some (some (.inl p))) (hs : p.site ≠ .shfl) :
    p.w = g % L.block / 32 := by
  obtain ⟨hki, hw, -⟩ := (onPath_all hpre hX hg k hk).1 p hσ
  apply hw
  rw [hki]
  obtain ⟨site, w⟩ := p
  cases site <;> simp only [Prologue.index, Prologue.fenceIdx] at hs ⊢
  all_goals first | exact absurd rfl hs | omega | (split_ifs <;> omega)

/-- The column count register at the allocation holds 512. -/
theorem alloc_cols {d : Prologue.D} {t : TState} (h : Holds t.regs (Prologue.facts L g d))
    (hs : d.site = .alloc) : readBits L g t 32 (.reg 91) =
      .ok (truncBits 32 (BitVec.ofNat 64 512)) := by
  have hr : t.regs 91 = some (b32 512) := by
    have hl : 91 ∈ Flow.live d.site.pc := by rw [hs]; table_decide
    have := holds_mem h (Flow.mem_factsFrom hl)
    simpa [Prologue.valueOf, Prologue.values, PTX.Flow.lookupLit] using this
  simp [readBits, readReg, hr, b32, bind, Except.bind, pure, Except.pure]

/-- The column count register at the deallocation holds 512. -/
theorem dealloc_cols {d : Consumer.D} {t : TState} (h : Holds t.regs (Consumer.facts L g d))
    (hs : d.site = .dealloc) :
    readBits L g t 32 (.reg 875) = .ok (truncBits 32 (BitVec.ofNat 64 512)) := by
  have hr : t.regs 875 = some (b32 512) := by
    have hl : 875 ∈ Flow.live d.site.pc := by rw [hs]; table_decide
    have := holds_mem h (Flow.mem_factsFrom hl)
    simpa [Consumer.valueOf, Consumer.values, Consumer.accValues, Consumer.dataTable,
      Consumer.packTable, PTX.Flow.lookupLit] using this
  simp [readBits, readReg, hr, b32, bind, Except.bind, pure, Except.pure]

theorem toNat_512 : (truncBits 32 (BitVec.ofNat 64 512)).toNat = 512 := by
  simp [truncBits]

set_option maxHeartbeats 8000000 in
/-- **A paired Tensor Memory operation** is made by warp 0, in group two; it is the thread's
`n`-th, at the `n`-th operation's site and of its shape, and the state after it is the `n`-th
operation's successor. -/
theorem tmem_event_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) (hnu : ∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) {k pc : Nat}
    {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request}
    (he : X.get (g, k) = some ⟨pc, .tc (.resource grp dst act)⟩) :
    g % L.block / 32 = 0 ∧ grp = .two ∧ pc = tmemPc (tmemOps ((X.tr g).take k)) ∧
      TmemShape (tmemOps ((X.tr g).take k)) act ∧
      ∃ d, Frame.stateAt (code L) X g (k + 1) = some (some d) ∧
        TmemAfter (tmemOps ((X.tr g).take k)) d := by
  have hlen : k < (X.tr g).length := len_of_get he
  have he' : (X.tr g)[k]? = some ⟨pc, .tc (.resource grp dst act)⟩ := he
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨σ, hσ⟩ : ∃ σ, Frame.stateAt (code L) X g k = some σ := by
    rcases htr.fired he with ⟨τ, -, ha, -⟩ | ⟨-, hub⟩
    · exact ⟨τ, ha⟩
    · obtain ⟨pc', f, h⟩ := hub
      cases h
  obtain ⟨d, rfl⟩ : ∃ d, σ = some d := by
    cases σ with
    | none => exact absurd hσ (tracked hpre hX g k hg)
    | some d => exact ⟨d, rfl⟩
  obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hsite := tmem_site hat hc hfire (e := ⟨pc, .tc (.resource grp dst act)⟩) rfl
  have hpc : pc = (code L g).pc d := by
    rcases fires_tmemTmpl (tmem_tmpl hat hsite hc) hfire with ⟨f, h⟩ | ⟨dst', act', h⟩ <;>
      simp only [Event.mk.injEq] at h <;> exact h.1
  obtain ⟨hops, hw⟩ := tmem_ops_fact hpre hX hg hnu hσ
  rw [hops]
  rcases d with ⟨site, w⟩ | (l | m | s | c)
  · change site = .alloc at hsite
    subst hsite
    have hw0 : w = 0 := hw (.inl rfl)
    have hW : w = g % L.block / 32 := prologue_w hpre hX hg hlen.le hσ (by simp)
    change kernel.code[Flow.tmemAlloc_0]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
    obtain ⟨-, hgrp, n, hn, hact⟩ := fires_tcAlloc_resource hfire rfl
    rw [alloc_cols hat.2.2.2.2 rfl] at hn
    obtain rfl := (Except.ok.inj hn).symm
    show g % L.block / 32 = 0 ∧ grp = .two ∧ pc = tmemPc 0 ∧ TmemShape 0 act ∧
      ∃ d, Frame.stateAt (code L) X g (k + 1) = some (some d) ∧ TmemAfter 0 d
    subst hact
    refine ⟨by omega, hgrp, hpc, by rw [toNat_512]; rfl, ?_⟩
    rw [stateAt_succ_inl he' hσ]
    simp only [Prologue.next]
    split_ifs
    · refine ⟨_, rfl, ?_⟩
      exact ⟨_, rfl, .inl rfl⟩
    · refine ⟨_, rfl, ?_⟩
      exact ⟨_, rfl, .inr rfl⟩
  · exact hsite.elim
  · exact hsite.elim
  · exact hsite.elim
  · obtain ⟨site, m, n, m', n', cp, ap, resp, x, acc, base⟩ := c
    have hsucc : Frame.stateAt (code L) X g (k + 1) =
      (Consumer.next L g ⟨site, m, n, m', n', cp, ap, resp, x,
        acc, base⟩ ⟨pc, .tc (.resource grp dst act)⟩).map (Option.map (.inr ∘ .cons)) := by
      rw [Frame.stateAt_succ he', hσ]
      rfl
    rcases hsite with h | h <;> simp only at h <;> subst h
    · have hw0 : decide (g % L.block / 32 = 0) = true := hw (by simp)
      have h0 : g % L.block / 32 = 0 := by simpa using hw0
      rw [hw0]
      change kernel.code[Flow.tmemRelinquish_0]? = some ins at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemRelinquish_0)
      obtain ⟨hgrp, -, hact⟩ := fires_tcRelinquish_resource hfire rfl
      show g % L.block / 32 = 0 ∧ grp = .two ∧ pc = tmemPc 1 ∧ TmemShape 1 act ∧
        ∃ d, Frame.stateAt (code L) X g (k + 1) = some (some d) ∧ TmemAfter 1 d
      refine ⟨h0, hgrp, hpc, hact, ?_⟩
      rw [hsucc]
      exact ⟨_, rfl, _, rfl, rfl⟩
    · have hw0 : decide (g % L.block / 32 = 0) = true := hw (by simp)
      have h0 : g % L.block / 32 = 0 := by simpa using hw0
      rw [hw0]
      change kernel.code[Flow.tmemDealloc_0]? = some ins at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemDealloc_0)
      obtain ⟨hgrp, -, n'', a, hn, hact⟩ := fires_tcDealloc_resource hfire rfl
      rw [dealloc_cols hat.2.2.2.2 rfl] at hn
      obtain rfl := (Except.ok.inj hn).symm
      show g % L.block / 32 = 0 ∧ grp = .two ∧ pc = tmemPc 2 ∧ TmemShape 2 act ∧
        ∃ d, Frame.stateAt (code L) X g (k + 1) = some (some d) ∧ TmemAfter 2 d
      refine ⟨h0, hgrp, hpc, ⟨a, by rw [hact, toNat_512]⟩, ?_⟩
      rw [hsucc]
      exact ⟨_, rfl, _, rfl, rfl⟩

/-- **A thread of warp 0 is in the rank table before its next operation.** -/
theorem tmem_stage_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) (hnu : ∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩)
    (h0 : g % L.block / 32 = 0) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length =
      some (some d)) : TmemStage (tmemOps (X.tr g)) d := by
  obtain ⟨hops, hw⟩ := tmem_ops_fact hpre hX hg hnu hσ
  rw [List.take_length] at hops
  rw [hops]
  have hw0 : decide (g % L.block / 32 = 0) = true := by simpa using h0
  rw [hw0]
  rcases d with ⟨site, w⟩ | (l | m | s | c)
  · cases site
    case shfl | elect | alloc =>
      simp [ThreadD.tmemOps, TmemStage, Prologue.Site.vtime]
    case init i =>
      have := i.isLt
      simp [ThreadD.tmemOps, TmemStage, Prologue.Site.vtime]
      omega
    case allocWrite | warpBar => simp [ThreadD.tmemOps, TmemStage, ThreadD.exitOff]
    all_goals
      have hW := prologue_w hpre hX hg le_rfl hσ (by simp)
      simp only at hW
      simp [ThreadD.tmemOps, TmemStage, ThreadD.exitOff, hW, h0]
  · have := role_warp hpre hX hg _ le_rfl _ hσ
    simp [roleWarp, Prologue.warpOf] at this
    omega
  · have := role_warp hpre hX hg _ le_rfl _ hσ
    simp [roleWarp, Prologue.warpOf] at this
    omega
  · have := role_warp hpre hX hg _ le_rfl _ hσ
    simp [roleWarp, Prologue.warpOf] at this
    omega
  · obtain ⟨site, m, n, m', n', cp, ap, resp, x, acc, base⟩ := c
    cases site <;> simp [ThreadD.tmemOps, TmemStage, ThreadD.exitOff, Consumer.exitOff]

/-- **A thread of warp 0 exits after its three operations.** -/
theorem tmem_exit_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) (hnu : ∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩)
    (h0 : g % L.block / 32 = 0) {k pc : Nat} (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    tmemOps ((X.tr g).take k) = 3 := by
  have hlen : k < (X.tr g).length := len_of_get he
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨d, hσ, -⟩ := exit_event_state' hpre hX hg he
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hp := ret_pc hc (fires_exit_op hfire rfl)
  obtain ⟨hops, -⟩ := tmem_ops_fact hpre hX hg hnu hσ
  rw [hops]
  have hw0 : decide (g % L.block / 32 = 0) = true := by simpa using h0
  rw [hw0]
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
  · obtain ⟨site, m, n, m', n', cp, ap, resp, x, acc, base⟩ := c
    change site.pc ∈ _ at hp
    cases site
    case exit => rfl
    all_goals (exfalso; clear * - hp; revert hp; decide +revert)

/-- **A thread at a paired Tensor Memory site fires the operation or undefined behaviour.** -/
theorem tmem_fire_fact (hpre : Pre P L mem0) (hg : g < L.threads) {d : ThreadD} {t : TState}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hat : d.AtTmem) (hr : Run kernel Prod L g {} (X.tr g) (some t)) :
    ∃ t1 m, Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧ out kernel Prod L g t1 = .ev m ∧
      TmemTmpl .two m := by
  have hσ' : (code L g).toMachine.after (some (code L g).init) (X.tr g) = some (some d) := by
    have h := hσ
    simp only [Frame.stateAt, List.take_length] at h
    exact h
  obtain ⟨t1, hl, hgood⟩ := Code.end_site (sound hpre hg) hr hσ'
  have hout := Code.site_out (sound hpre hg) hgood
  obtain ⟨ins, hc, -, -⟩ := ((sound hpre hg).steps d).site hgood.2
  simp only [Code.tmpl, hc] at hout
  exact ⟨t1, _, hl, hout, tmem_tmpl hgood.1 hat hc⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof
