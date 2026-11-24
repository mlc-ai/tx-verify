-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerTc
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleRun

@[expose] public section

/-! # A consumer's data events keep its machine running on single-precision words

A Tensor Memory data event is fired by a consumer at a load or at a load's wait (`data_role`). A
load always steps to its wait, whose accumulator holds the load's words in the load's chunk
(`next_loadWait`); the wait steps on when no conversion of those words faults
(`Consumer.chunkOk`), and no conversion of two single-precision floats does. So a consumer whose
loads returned single-precision floats does not stop after a data event: its state is a
consumer's (`data_live`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- **A data event is a consumer's**, at a load or at a load's wait. -/
theorem data_role {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {e : Event} (he : X.get (g, k) = some e) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g k = some (some d)) (hd : isTcData e = true) :
    ∃ c, d = .inr (.cons c) ∧ ((∃ j, c.site = .load j) ∨ ∃ j, c.site = .loadWait j) := by
  obtain ⟨o, hf⟩ := (Frame.trace (fun _ => sound hpre) hX hg).fired_at he hσ
  obtain ⟨t, ins, -, -, hc, hfire⟩ := Code.fired_site (sound hpre hg) hf
  have hpc := OpPcsFast.mem kernel_tcData_pcs hc (fires_tcData_op hfire hd)
  rcases d with p | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | c)
  · exfalso
    change kernel.code[p.site.pc]? = some ins at hc
    change Fires p.site.pc (eventTmpl Prod L g t ins.op) e o at hfire
    exact absurd hd (by simp [Prologue.not_tcData hc hfire])
  · exfalso; change site.pc ∈ _ at hpc; clear hc hfire hf hσ; revert hpc
    cases site <;> simp only [Loader.Site.pc] <;> decide +revert
  · exfalso; change site.pc ∈ _ at hpc; clear hc hfire hf hσ; revert hpc
    cases site <;> simp only [Mma.Site.pc] <;> decide +revert
  · exfalso; change site.pc ∈ _ at hpc; clear hc hfire hf hσ; revert hpc
    cases site <;> simp only [Scheduler.Site.pc] <;> decide +revert
  · change kernel.code[c.site.pc]? = some ins at hc
    change Fires c.site.pc (eventTmpl Prod L g t ins.op) e o at hfire
    exact ⟨c, rfl, Consumer.data_site hc hfire hd⟩

/-- A data event of a Tensor Memory load instruction is the load. -/
theorem fires_tcLd_data {A : List Assumption} {t : TState} {ds : List Nat} {ta : Nat}
    {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.tcLd ds ta)) e o) (hd : isTcData e = true)
    (hw : A.any (·.tcLdWait t.pc) = false := by hooks_off) :
    ∃ a vals, e = ⟨pc, .tc (.ld a vals .s32x32b)⟩ := by
  rw [eventTmpl_tcLd_noWait hw] at hf
  simp only [tcTmpl] at hf
  cases ha : readBits L g t 32 (.reg ta) with
  | error f =>
    simp [ofExec, ha, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hf
    split_ifs at hf <;> simp only [Fires] at hf <;> obtain ⟨rfl, -⟩ := hf <;>
      simp [isTcData] at hd
  | ok a =>
    simp [ofExec, ha, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf
    split_ifs at hf <;> simp only [Fires] at hf
    all_goals first
      | (obtain ⟨rfl, -⟩ := hf; simp [isTcData] at hd)
      | (obtain ⟨vals, -, rfl, -⟩ := hf
         exact ⟨_, vals, rfl⟩)

/-- **The step into a load's wait is the load**: the wait's accumulator holds the load's words
in the load's chunk. -/
theorem Consumer.next_loadWait {c c' : Consumer.D} {e : Event} {j : Fin 16}
    (hn : Consumer.next L g c e = some (some c')) (hs : c'.site = .loadWait j) :
    c.site = .load j ∧ ∃ a vals sh, e.kind = .tc (.ld a vals sh) ∧
      c'.acc = Consumer.loadAcc c.acc j.val vals := by
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := c
  cases site <;> simp only [Consumer.next] at hn
  all_goals repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try (simp only [Option.map_eq_some_iff, Option.some.injEq] at hn
                  obtain ⟨_, -, rfl⟩ := hn))
  all_goals (try subst hn)
  all_goals simp_all

/-- A single-precision float, or the zero word, reads as a single-precision float. -/
theorem f32_word_ok {v : Value} (h : (∃ r, v = .float .f32 r) ∨ v = b32 0) :
    (valFloat .f32 v).toBool = true := by
  rcases h with ⟨r, rfl⟩ | rfl
  · simp [valFloat, pure, Except.pure, Except.toBool]
  · simp [valFloat_z0, Except.toBool]

/-- **A consumer's data event leaves its machine running**, at a consumer's state, when every word
its earlier loads returned is a single-precision float. -/
theorem data_live {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {e : Event} (he : X.get (g, k) = some e) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g k = some (some d)) (hd : isTcData e = true)
    (hwords : ∀ k' pc a vals sh, k' < k → X.get (g, k') = some ⟨pc, .tc (.ld a vals sh)⟩ →
      ∀ v ∈ vals, ∃ r, v = .float .f32 r) :
    ∃ c', Frame.stateAt (code L) X g (k + 1) = some (some (.inr (.cons c'))) := by
  obtain ⟨c, rfl, hs⟩ := data_role hpre hX hg he hσ hd
  have hsucc := Frame.stateAt_succ (C := code L) (X := X) (g := g) (k := k) he
  rw [hσ] at hsucc
  rw [hsucc]
  change ∃ c', (Consumer.next L g c e).map (Option.map (Sum.inr ∘ Prologue.Role.cons)) =
    some (some (.inr (.cons c')))
  rcases hs with ⟨j, hj⟩ | ⟨j, hj⟩
  · have htr := Frame.trace (fun _ => sound hpre) hX hg
    obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
    change kernel.code[c.site.pc]? = some ins at hc
    change Fires c.site.pc (eventTmpl Prod L g t ins.op) e o at hfire
    rw [hj] at hc hfire
    obtain rfl := Option.some.inj (hc.symm.trans (Consumer.code_load j))
    obtain ⟨_, vals, rfl⟩ := fires_tcLd_data hfire hd
    obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := c
    simp only at hj
    subst hj
    simp [Consumer.next]
  · -- the state before the wait is the load's
    cases k with
    | zero =>
      simp only [Frame.stateAt, List.take_zero, Machine.after] at hσ
      cases hσ
    | succ k =>
      obtain ⟨e', he'⟩ : ∃ e', X.get (g, k) = some e' := by
        have hlt : k + 1 < (X.tr g).length := len_of_get he
        exact ⟨_, List.getElem?_eq_getElem (show k < (X.tr g).length by omega)⟩
      have hprev := Frame.stateAt_succ (C := code L) (X := X) (g := g) (k := k) he'
      rw [hσ] at hprev
      cases hσ' : Frame.stateAt (code L) X g k with
      | none => rw [hσ'] at hprev; cases hprev
      | some σ' =>
        rw [hσ'] at hprev
        cases σ' with
        | none => cases hprev
        | some d' =>
          have hn : (code L g).next d' e' = some (some (.inr (.cons c))) := hprev.symm
          have hwait : ∃ c', Consumer.next L g c' e' = some (some c) := by
            rcases d' with p | (l | m | s | c')
            · have := Prologue.next_cons (L := L) (g := g) (p := p) (e := e') hn
              rw [this] at hj
              cases hj
            · obtain ⟨_, -, h'⟩ := next_of_loader hn; cases h'
            · obtain ⟨_, -, h'⟩ := next_of_mma hn; cases h'
            · obtain ⟨_, -, h'⟩ := next_of_sched hn; cases h'
            · obtain ⟨c'', hn', h'⟩ := next_of_cons hn
              cases h'
              exact ⟨c', hn'⟩
          obtain ⟨c', hn'⟩ := hwait
          obtain ⟨-, a, vals, sh, hk, hacc⟩ := Consumer.next_loadWait hn' hj
          obtain ⟨pc', k'⟩ := e'
          simp only at hk
          subst hk
          have hw := hwords k pc' a vals sh (by omega) he'
          have hent : ∀ i, 16 * j.val ≤ i → i < 16 * j.val + 16 →
              ∃ r, valFloat .f32 (c.acc i) = .ok r := by
            intro i hi1 hi2
            have hb : (valFloat .f32 (c.acc i)).toBool = true := by
              rw [hacc]
              unfold Consumer.loadAcc
              simp only [hi1, hi2, and_self, ↓reduceIte]
              apply f32_word_ok
              by_cases hl : i - 16 * j.val < vals.length
              · refine .inl (hw _ ?_)
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
                exact List.getElem_mem hl
              · refine .inr ?_
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
                  Option.getD_none]
            cases hv : valFloat .f32 (c.acc i) with
            | ok r => exact ⟨r, rfl⟩
            | error f => rw [hv] at hb; cases hb
          have hok : Consumer.chunkOk c.acc j = true := by
            refine List.all_eq_true.mpr fun cv hcv => ?_
            obtain ⟨ia, ib, h1, h2, h3, h4, ha, hb, -, -⟩ := (Consumer.cvtTable j).src cv hcv
            obtain ⟨xa, hxa⟩ := hent ia h1 h2
            obtain ⟨xb, hxb⟩ := hent ib h3 h4
            simp [Consumer.cvtOk, ha, hb, Flow.cvtPairE_of_valFloat hxa hxb, Except.toBool]
          obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := c
          simp only at hj hok
          subst hj
          simp only [Consumer.next, hok, ↓reduceIte]
          split <;> simp
