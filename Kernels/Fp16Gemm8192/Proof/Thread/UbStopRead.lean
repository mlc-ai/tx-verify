-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.UbSite

@[expose] public section

/-! # Where a thread's machine stops

A role's machine stops after an event it fires only at its read of the response buffer, when the
bytes read are no response (`Loader.next_none`, ...), and a consumer's also at its read of the base
word, when the bytes do not rebuild to a value, and at a load's wait, when a loaded value is not a
single-precision float (`Consumer.next_none`). Every other event the site fires is of the kind its
step expects (the sites' event lemmas). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t u : TState}

set_option maxHeartbeats 4000000 in
theorem Loader.next_none (hpre : Pre P L mem0) {d : Loader.D} {ins : Instr} {e : Event}
    (h : At t d.site.pc (Loader.facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u))
    (hn : Loader.next L g d e = none) :
    d.site = .clcLoad ∧ ∃ a bs, e.kind = .rd a bs ∧ Flow.responseOf bs = none := by
  obtain ⟨site, m, n, q, cp, r, x⟩ := d
  cases site with
  | wait b =>
    obtain ⟨_, _, _, rfl⟩ := Loader.wait_event hpre b rfl h hc hf
    simp [Loader.next] at hn
  | clcWait =>
    obtain ⟨_, _, _, _, -, rfl⟩ := Loader.clcWait_event hpre rfl h hc hf
    simp [Loader.next] at hn
  | drain i =>
    obtain ⟨_, _, _, rfl⟩ := Loader.drain_event hpre i rfl h hc hf
    revert hn
    simp only [Loader.next]
    split_ifs <;> simp
  | clcLoad =>
    obtain ⟨a, bs, hk, -⟩ := Loader.clcLoad_read hpre rfl h hc hf
    refine ⟨rfl, a, bs, hk, ?_⟩
    simpa [Loader.next, hk] using hn
  | clcStatus | clcFirst =>
    code_at hc
    subst hc
    obtain ⟨_, _, -, -, rfl, -⟩ := fires_clcQuery hf
    simp [Loader.next] at hn
  | exit =>
    code_at hc
    subst hc
    simp [eventTmpl, Fires] at hf
  | _ =>
    revert hn
    simp only [Loader.next]
    try split_ifs
    all_goals simp

set_option maxHeartbeats 4000000 in
theorem Mma.next_none (hpre : Pre P L mem0) {d : Mma.D} {ins : Instr} {e : Event} (hi : Mma.Inv d)
    (h : At t d.site.pc (Mma.facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u))
    (hn : Mma.next L g d e = none) :
    d.site = .clcLoad ∧ ∃ a bs, e.kind = .rd a bs ∧ Flow.responseOf bs = none := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  cases site with
  | elect =>
    code_at hc
    subst hc
    obtain ⟨_, _, _, rfl, -⟩ := fires_elect hf
    revert hn
    simp only [Mma.next]
    split_ifs <;> simp
  | clcWait =>
    obtain ⟨_, _, _, _, -, rfl⟩ := Mma.clcWait_event hpre rfl h hc hf
    simp [Mma.next] at hn
  | accWait =>
    obtain ⟨_, _, _, rfl⟩ := Mma.accWait_event hpre rfl hi h hc hf
    simp [Mma.next] at hn
  | full s =>
    obtain ⟨_, _, _, rfl⟩ := Mma.full_event hpre s rfl hi h hc hf
    simp [Mma.next] at hn
  | clcLoad =>
    obtain ⟨a, bs, hk, -⟩ := Mma.clcLoad_read hpre rfl h hc hf
    refine ⟨rfl, a, bs, hk, ?_⟩
    simpa [Mma.next, hk] using hn
  | clcStatus | clcFirst =>
    code_at hc
    subst hc
    obtain ⟨_, _, -, -, rfl, -⟩ := fires_clcQuery hf
    simp [Mma.next] at hn
  | exit =>
    code_at hc
    subst hc
    simp [eventTmpl, Fires] at hf
  | _ =>
    revert hn
    simp only [Mma.next]
    try split_ifs
    all_goals simp

set_option maxHeartbeats 4000000 in
theorem Scheduler.next_none (hpre : Pre P L mem0) {d : Scheduler.D} {ins : Instr} {e : Event}
    (hi : Scheduler.Inv d) (h : At t d.site.pc (Scheduler.facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u))
    (hn : Scheduler.next L g d e = none) :
    d.site = .clcLoad ∧ ∃ a bs, e.kind = .rd a bs ∧ Flow.responseOf bs = none := by
  obtain ⟨site, ap, cp, r, x⟩ := d
  cases site with
  | elect =>
    code_at hc
    subst hc
    obtain ⟨_, _, _, rfl, -⟩ := fires_elect hf
    revert hn
    simp only [Scheduler.next]
    split_ifs <;> simp
  | ackWait =>
    obtain ⟨_, _, _, rfl⟩ := Scheduler.ackWait_event hpre hi rfl h hc hf
    revert hn
    simp only [Scheduler.next]
    split_ifs <;> simp
  | clcWait =>
    obtain ⟨_, _, _, rfl⟩ := Scheduler.clcWait_event hpre hi rfl h hc hf
    revert hn
    simp only [Scheduler.next]
    split_ifs <;> simp
  | clcLoad =>
    obtain ⟨a, bs, hk, -⟩ := Scheduler.clcLoad_read hpre rfl h hc hf
    refine ⟨rfl, a, bs, hk, ?_⟩
    simpa [Scheduler.next, hk] using hn
  | clcStatus | clcFirst =>
    code_at hc
    subst hc
    obtain ⟨_, _, -, -, rfl, -⟩ := fires_clcQuery hf
    simp [Scheduler.next] at hn
  | exit =>
    code_at hc
    subst hc
    simp [eventTmpl, Fires] at hf
  | _ =>
    revert hn
    simp only [Scheduler.next]
    try split_ifs
    all_goals simp

set_option maxHeartbeats 4000000 in
theorem Consumer.next_none (hpre : Pre P L mem0) {d : Consumer.D} {ins : Instr} {e : Event}
    (hi : Consumer.Inv d) (hat : (code L g).AtD (.inr (.cons d)) t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u))
    (hn : Consumer.next L g d e = none) :
    (d.site = .clcLoad ∧ ∃ a bs, e.kind = .rd a bs ∧ Flow.responseOf bs = none) ∨
      (d.site = .ldBase ∧ ∃ a bs f, e.kind = .rd a bs ∧ rebuild 3 bs = .error f) ∨
      ∃ j, d.site = .loadWait j := by
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site with
  | clcWait =>
    obtain ⟨_, _, _, _, -, rfl⟩ := Consumer.clcWait_event hpre rfl hat.2.2.2.2 hc hf
    simp [Consumer.next] at hn
  | accWait =>
    obtain ⟨_, _, _, rfl⟩ := Consumer.accWait_event hpre rfl hi hat.2.2.2.2 hc hf
    simp [Consumer.next] at hn
  | clcLoad =>
    obtain ⟨a, bs, hk, -⟩ := Consumer.clcLoad_read hpre rfl hat hc hf
    refine .inl ⟨rfl, a, bs, hk, ?_⟩
    simpa [Consumer.next, hk] using hn
  | clcStatus | clcFirst =>
    code_at hc
    subst hc
    obtain ⟨_, _, -, -, rfl, -⟩ := fires_clcQuery hf
    simp [Consumer.next] at hn
  | load j =>
    change kernel.code[(Consumer.Site.load j).pc]? = some ins at hc
    rw [Consumer.code_load j] at hc
    cases hc
    obtain ⟨_, _, -, rfl, -⟩ := fires_tcLd (fun _ h => by cases h) hf
    simp [Consumer.next] at hn
  | loadWait j => exact .inr (.inr ⟨j, rfl⟩)
  | ldBase =>
    code_at hc
    subst hc
    obtain ⟨a, bs, rfl, -⟩ := fires_load rfl rfl hf
    refine .inr (.inl ⟨rfl, a, bs, ?_⟩)
    revert hn
    simp only [Consumer.next]
    cases hr : rebuild 3 bs with
    | ok v => simp
    | error f => exact fun _ => ⟨f, by simp⟩
  | exit =>
    code_at hc
    subst hc
    simp [eventTmpl, Fires] at hf
  | _ =>
    revert hn
    simp only [Consumer.next]
    try split_ifs
    all_goals simp

set_option maxHeartbeats 4000000 in
theorem Prologue.next_none {d : Prologue.D} {ins : Instr} {e : Event}
    (hat : (code L g).AtD (.inl d) t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u))
    (hn : Prologue.next L g d e = none) : False := by
  obtain ⟨site, w⟩ := d
  cases site with
  | alloc =>
    code_at hc
    subst hc
    obtain ⟨_, _, rfl, -⟩ := fires_tcAlloc hat.2.1 hf
    revert hn
    simp only [Prologue.next]
    split_ifs <;> simp
  | roleElect =>
    code_at hc
    subst hc
    obtain ⟨_, _, _, rfl, -⟩ := fires_elect hf
    revert hn
    simp only [Prologue.next]
    split_ifs <;> simp
  | _ =>
    revert hn
    simp only [Prologue.next]
    try split_ifs
    all_goals (try split)
    all_goals (try split_ifs)
    all_goals simp

variable {X : Execution}

/-- A role at its read of the response buffer has just polled its response barrier
successfully. -/
theorem poll_before (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {r : Prologue.Role} (hk : k ≤ (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr r))) (h1 : r.clcStage = 1) :
    0 < k ∧ ∃ pc p acq sc, X.get (g, k - 1) =
      some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hrel : QueryRel L g r.clcStage r.resp ((X.tr g).take k) := queryInv hpre hg htr k _ hσ
  obtain ⟨pc, p, acq, sc, hl⟩ := hrel.1 h1
  rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left hk] at hl
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hl
    · exact h
  refine ⟨hk0, pc, p, acq, sc, ?_⟩
  rw [List.getElem?_take_of_lt (by omega)] at hl
  exact hl

set_option maxHeartbeats 4000000 in
/-- **Where a followed thread's machine stops**: after a read of its CTA's response buffer whose
bytes are no response, after a read of the base word whose bytes do not rebuild to a value, or
after a Tensor Memory data event. -/
theorem stop_read_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {e : Event} {d : ThreadD} (he : X.get (g, k) = some e)
    (hk : k + 1 < (X.tr g).length) (hσ : Frame.stateAt (code L) X g k = some (some d))
    (hn : Frame.stateAt (code L) X g (k + 1) = none) :
    (∃ a bs, e.kind = .rd a bs ∧ a.loc = ⟨.shared, g / L.block, L.sharedBase + 144⟩ ∧
        a.size = 16 ∧ Flow.responseOf bs = none ∧ 0 < k ∧ ∃ pc p acq sc, X.get (g, k - 1) =
          some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩) ∨
      (∃ a bs f, e.kind = .rd a bs ∧ a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∧ a.size = 4 ∧
        rebuild 3 bs = .error f) ∨
      isTcData e = true := by
  have hkl : k ≤ (X.tr g).length := by omega
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨τ, u, ha, hf⟩ := htr.fired_some he hk
  have hτ : τ = some d := Option.some.inj (ha.symm.trans hσ)
  subst hτ
  obtain ⟨t, ins, hat, hinv, hc, hfire⟩ := Code.fired_site (sound hpre hg) hf
  have hnext : (code L g).next d e = none := by
    rw [Frame.stateAt_succ he, hσ] at hn
    exact hn
  rcases d with p | (l | m | sd | cs)
  · exact (Prologue.next_none hat hc hfire hnext).elim
  · have hl : Loader.next L g l e = none := by
      simpa [code] using hnext
    obtain ⟨hs, a, bs, hk', hr⟩ := Loader.next_none hpre hat hc hfire hl
    obtain ⟨a', bs', hk'', hloc, hsz⟩ := Loader.clcLoad_read hpre hs hat hc hfire
    rw [hk'] at hk''
    cases hk''
    exact .inl ⟨a, bs, hk', hloc, hsz, hr, poll_before hpre hX hg hkl hσ
      (by simp [Prologue.Role.clcStage, Loader.D.clcStage, hs])⟩
  · have hl : Mma.next L g m e = none := by
      simpa [code] using hnext
    obtain ⟨hs, a, bs, hk', hr⟩ := Mma.next_none hpre hinv.1 hat hc hfire hl
    obtain ⟨a', bs', hk'', hloc, hsz⟩ := Mma.clcLoad_read hpre hs hat hc hfire
    rw [hk'] at hk''
    cases hk''
    exact .inl ⟨a, bs, hk', hloc, hsz, hr, poll_before hpre hX hg hkl hσ
      (by simp [Prologue.Role.clcStage, Mma.D.clcStage, hs])⟩
  · have hl : Scheduler.next L g sd e = none := by
      simpa [code] using hnext
    obtain ⟨hs, a, bs, hk', hr⟩ := Scheduler.next_none hpre hinv.1 hat hc hfire hl
    obtain ⟨a', bs', hk'', hloc, hsz⟩ := Scheduler.clcLoad_read hpre hs hat hc hfire
    rw [hk'] at hk''
    cases hk''
    exact .inl ⟨a, bs, hk', hloc, hsz, hr, poll_before hpre hX hg hkl hσ
      (by simp [Prologue.Role.clcStage, Scheduler.D.clcStage, hs])⟩
  · have hl : Consumer.next L g cs e = none := by
      simpa [code] using hnext
    rcases Consumer.next_none hpre hinv.1 hat hc hfire hl with
      ⟨hs, a, bs, hk', hr⟩ | ⟨hs, a, bs, f, hk', hr⟩ | ⟨j, hs⟩
    · obtain ⟨a', bs', hk'', hloc, hsz⟩ := Consumer.clcLoad_read hpre hs hat hc hfire
      rw [hk'] at hk''
      cases hk''
      exact .inl ⟨a, bs, hk', hloc, hsz, hr, poll_before hpre hX hg hkl hσ
        (by simp [Prologue.Role.clcStage, Consumer.D.clcStage, hs])⟩
    · obtain ⟨hloc, hsz⟩ := Consumer.ldBase_read hpre hs hat hc hfire a bs hk'
      exact .inr (.inl ⟨a, bs, f, hk', hloc, hsz, hr⟩)
    · refine .inr (.inr ?_)
      change kernel.code[cs.site.pc]? = some ins at hc
      rw [hs, Consumer.code_wait j] at hc
      cases hc
      change Fires cs.site.pc (eventTmpl Prod L g t .tcWaitLd) e (some u) at hfire
      have hb : L.block % 32 = 0 := by rw [hpre.block]
      simp only [eventTmpl, tcTmpl, hb, ofExec, Fires] at hfire
      rw [hfire.1]
      rfl

end

end PTX.Kernels.Fp16Gemm8192.Proof
