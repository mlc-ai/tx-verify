-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.TmemFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.UbSite
public import Kernels.Fp16Gemm8192.Proof.Thread.InputIssues
public import Lemmas.Flow.AllocTmpl

@[expose] public section

/-! # A thread's paired Tensor Memory operations, at each event

The events of a thread before one of its events are not undefined behaviour (undefined behaviour
ends a trace), so the counts of its run invariant hold there without assuming anything of the
rest of the trace (`tmem_ops_at`): a paired operation is warp 0's `n`-th, of its shape
(`tmem_event_at`). A deallocation frees the base its thread read from its CTA's base word right
before it (`dealloc_base_fact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}

/-- A thread's paired operations before one of its events count its state's. -/
theorem tmem_ops_at (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {d : ThreadD} (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) :
    tmemOps ((X.tr g).take k) = d.tmemOps (decide (g % L.block / 32 = 0)) ∧
      d.TmemWarp (decide (g % L.block / 32 = 0)) := by
  have hi := (clusterInv hpre hg (Frame.trace (fun _ => sound hpre) hX hg) k _ hσ).2.2.2.2
  obtain ⟨o, hrun⟩ := hX.thr g hg
  exact ⟨hi.1 (run_noUb_take hrun k hk), hi.2⟩

set_option maxHeartbeats 8000000 in
/-- **A paired operation is warp 0's `n`-th, of its shape**, at every event. -/
theorem tmem_event_at (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k pc : Nat}
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
  obtain ⟨hops, hw⟩ := tmem_ops_at hpre hX hg hlen hσ
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

set_option maxHeartbeats 4000000 in
/-- **A thread of warp 0 exits after its three operations**, at every exit. -/
theorem tmem_exit_at (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads)
    (h0 : g % L.block / 32 = 0) {k pc : Nat} (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    tmemOps ((X.tr g).take k) = 3 := by
  have hlen : k < (X.tr g).length := len_of_get he
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨d, hσ, -⟩ := exit_event_state' hpre hX hg he
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hp := ret_pc hc (fires_exit_op hfire rfl)
  obtain ⟨hops, -⟩ := tmem_ops_at hpre hX hg hlen hσ
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

set_option maxHeartbeats 4000000 in
/-- **A deallocation frees the base its thread read** from its CTA's base word right before it: the
column the read's bytes hold, as a 32-bit integer. -/
theorem dealloc_base_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k pc : Nat} {grp : CtaGroup} {dst : Option Loc} {a n : Nat}
    (he : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩) :
    0 < k ∧ ∃ pcr ra bs, X.get (g, k - 1) = some ⟨pcr, .rd ra bs⟩ ∧
      ra.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∧ ra.size = 4 ∧
      ∀ col, bs = (b32 col).toBytes.map some → a = col % 2 ^ 32 := by
  have hlen : k < (X.tr g).length := len_of_get he
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
  have hsite := tmem_site hat hc hfire (e := ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩) rfl
  rcases d with p | (l | m | s | c)
  · exfalso
    change p.site = .alloc at hsite
    obtain ⟨site, w⟩ := p
    simp only at hsite
    subst hsite
    change kernel.code[Flow.tmemAlloc_0]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
    exact absurd (fires_tcAlloc_resource hfire rfl).2.2 (by rintro ⟨n, -, h⟩; cases h)
  · exact hsite.elim
  · exact hsite.elim
  · exact hsite.elim
  · obtain ⟨site, mm, nn, m', n', cp, ap, resp, x, acc, base⟩ := c
    rcases hsite with hs | hs <;> simp only at hs <;> subst hs
    · exfalso
      change kernel.code[Flow.tmemRelinquish_0]? = some ins at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemRelinquish_0)
      obtain ⟨-, -, h⟩ := fires_tcRelinquish_resource hfire rfl
      cases h
    · obtain ⟨hk0, pcr, ra, bs, hrd, hloc, hsz, hrb⟩ := dealloc_pred hpre hX hg hlen.le hσ rfl
      refine ⟨hk0, pcr, ra, bs, hrd, hloc, hsz, fun col hbs => ?_⟩
      rw [hbs, rebuild_b32] at hrb
      simp only [Except.ok.injEq] at hrb
      change kernel.code[Flow.tmemDealloc_0]? = some ins at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemDealloc_0)
      have hr : t.regs 874 = some (b32 col) :=
        (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
          (congrArg some (by cons_values; exact hrb.symm))
      have hr29 : t.regs 875 = some (b32 512) :=
        (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
          (congrArg some (by cons_values))
      have hb : L.block % 32 = 0 := by rw [hpre.block]
      change Fires _ (eventTmpl Prod L g t (.tcDealloc .two (.reg 874) (.reg 875))) _ o at hfire
      simp only [eventTmpl, tcTmpl, readBits_b32' hr, readBits_b32' hr29, hb, bind, Except.bind,
        pure, Except.pure] at hfire
      rw [show (truncBits 32 (BitVec.ofNat 64 512)).toNat = 512 by decide] at hfire
      simp [Tmem.validColumns, ofExec, Fires] at hfire
      obtain ⟨⟨-, -, -, rfl, -⟩, -⟩ := hfire
      simp [truncBits]
      omega

end

end PTX.Kernels.Fp16Gemm8192.Proof
