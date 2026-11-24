-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsFire
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStatic
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Base
public import Lemmas.Flow.WaitTmpl
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMachine
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedule
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoader

@[expose] public section

/-! # A waiting thread's next event polls its site's barrier

The generic part of every `ProgressPolls` class's `poll` field (`PollsOn`):

* the role's run invariant holds at the state at the end of a thread's trace (`roleJ_end`): the
  last event of a run that ends in a state does not end the thread (`Run.no_end`), so it fires
  from its state and continues (`Cross.event_cont`), and the invariant's step applies;
* a thread whose machine state at its trace's end is at a poll site reaches, from every run, a
  concrete state of that machine state by local steps (`Frame.end_at`), whose template is that of
  an `mbarrier.try_wait` (`Cross.site_kindOp`): undefined behaviour or a wait with a parity
  below 2, acquiring (`kernel_wait_flags`). When the site's template is never undefined
  behaviour and every wait it fires is on `m` with the parity of the thread's successful polls
  of `m` plus `δ`, the thread's next event polls `m` with that parity (`pollsOn_of_site`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The roles' run invariant at the state at the end of a thread's trace.** -/
theorem roleJ_end (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g : Nat} {d : ThreadD} {t : TState} (hg : g < L.threads)
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hr : Run kernel asms L g {} (X.tr g) (some t)) : roleJ L g d (X.tr g) := by
  rcases hn : (X.tr g).length with _ | n
  · rw [hn, Frame.stateAt_zero] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    rw [List.length_eq_zero_iff.mp hn]
    exact (roleJ_run hpre hg).init
  · rw [hn] at hσ
    have hlt : n < (X.tr g).length := by omega
    have he : X.get (g, n) = some (X.tr g)[n] := List.getElem?_eq_getElem hlt
    have hend := Run.no_end hr _ (List.getElem_mem hlt)
    obtain ⟨d0, t0, ins, u, hσ0, hJ, hat, hi, hc, hf⟩ :=
      Cross.event_cont hpre hX ht (fun g hg => roleJ_run hpre hg) he hend
    have hnext : (code L g).next d0 (X.tr g)[n] = some (some d) := by
      have he' : (X.tr g)[n]? = some (X.tr g)[n] := he
      rw [Frame.stateAt_succ he', hσ0] at hσ
      exact hσ
    have h := (roleJ_run hpre hg).step hJ hat hi hc hf hnext
    have heq : (X.tr g).take n ++ [(X.tr g)[n]] = X.tr g := by
      rw [← Option.toList_some, ← List.getElem?_eq_getElem hlt, ← List.take_add_one,
        List.take_of_length_le (by omega)]
    rwa [heq] at h

/-- **A thread at a poll site polls its barrier next.** When every template of the site at a
concrete state of the thread's machine state is not undefined behaviour, and every wait it fires
is on `m` with the parity of the thread's successful polls of `m` plus `δ`, the thread's next
event polls `m` with that parity. -/
theorem pollsOn_of_site (hpre : Pre P L mem0) {g : Nat} {d : ThreadD} {m : Loc} {δ : Nat}
    (hg : g < L.threads) (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .wait)
    (hub : ∀ t ins, (code L g).AtD d t → (code L g).inv d →
      kernel.code[(code L g).pc d]? = some ins → ∀ f, eventTmpl asms L g t ins.op ≠ .ub f)
    (hev : ∀ t ins, (code L g).AtD d t → (code L g).inv d →
      kernel.code[(code L g).pc d]? = some ins → ∀ l p ok acq sc u,
      Fires ((code L g).pc d) (eventTmpl asms L g t ins.op) ⟨(code L g).pc d, .wait l p ok acq sc⟩
        (some u) → l = m ∧ p % 2 = (okPolls m (X.tr g) + δ) % 2) :
    PollsOn L X g m δ := by
  refine ⟨(code L g).pc d, (okPolls m (X.tr g) + δ) % 2, Nat.mod_mod _ _, fun t hr ok => ?_⟩
  obtain ⟨t1, ins, hl, hat, hinv, hc, hout⟩ :=
    Frame.end_at (C := code L) (fun _ hg => sound hpre hg) hg hr hσ
  have hop := Cross.site_kindOp d hc
  rw [hk] at hop
  obtain ⟨gd, op⟩ := ins
  cases op <;> simp only [Cross.kindOp, Bool.false_eq_true] at hop
  rename_i p' b off par acq0 sc0
  have hflags := List.all_eq_true.mp kernel_wait_flags _ (List.mem_of_getElem? hc)
  simp only [Bool.and_eq_true, beq_iff_eq] at hflags
  obtain ⟨rfl, -⟩ := hflags
  rcases eventTmpl_mbarWait_cases (A := asms) (L := L) (g := g) (t := t1) (p := p') (b := b)
    (off := off) (par := par) (acq := true) (sc := sc0) with ⟨f, hf⟩ | ⟨l, q, k, sc', hq2, htm⟩
  · exact absurd hf (hub t1 ⟨gd, _⟩ hat hinv hc f)
  have hfire : ∀ ok', Fires ((code L g).pc d)
      (eventTmpl asms L g t1 (.mbarWait p' b off par true sc0))
      ⟨(code L g).pc d, .wait l q ok' true sc'⟩ (some (k ok')) := fun ok' => by
    rw [htm]
    exact ⟨ok', rfl, rfl⟩
  obtain ⟨rfl, hpar⟩ := hev t1 ⟨gd, _⟩ hat hinv hc l q true true sc' _ (hfire true)
  have hq : q = (okPolls l (X.tr g) + δ) % 2 := by omega
  subst hq
  have hpc : t1.pc = (code L g).pc d := hat.1
  refine ⟨t1, k ok, sc', hl, eventTmpl asms L g t1 (.mbarWait p' b off par true sc0), hout, ?_⟩
  rw [hpc]
  exact hfire ok

/-- **`pollsOn_of_site` with the roles' run invariant at the trace's end** (which holds when the
thread's run ends in a state; otherwise the poll is vacuous). -/
theorem pollsOn_of_end (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g : Nat} {d : ThreadD} {m : Loc} {δ : Nat}
    (hg : g < L.threads) (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .wait)
    (hub : roleJ L g d (X.tr g) → ∀ t ins, (code L g).AtD d t → (code L g).inv d →
      kernel.code[(code L g).pc d]? = some ins → ∀ f, eventTmpl asms L g t ins.op ≠ .ub f)
    (hev : roleJ L g d (X.tr g) → ∀ t ins, (code L g).AtD d t → (code L g).inv d →
      kernel.code[(code L g).pc d]? = some ins → ∀ l p ok acq sc u,
      Fires ((code L g).pc d) (eventTmpl asms L g t ins.op) ⟨(code L g).pc d, .wait l p ok acq sc⟩
        (some u) → l = m ∧ p % 2 = (okPolls m (X.tr g) + δ) % 2) :
    PollsOn L X g m δ := by
  by_cases hrun : ∃ t, Run kernel asms L g {} (X.tr g) (some t)
  · obtain ⟨t, hr⟩ := hrun
    have hJ := roleJ_end hpre hX ht hg hσ hr
    exact pollsOn_of_site hpre hg hσ hk (hub hJ) (hev hJ)
  · exact ⟨0, (okPolls m (X.tr g) + δ) % 2, Nat.mod_mod _ _,
      fun t hr => absurd ⟨t, hr⟩ hrun⟩

/-! ### The state at the trace's end without a run -/

theorem Idle.site_ret (s : Idle.Site) (h : s.pc ∈ [Flow.exit_0]) : s = .exit := by
  cases s <;> first | rfl | (exfalso; revert h; decide)

theorem Prologue.site_not_ret (s : Prologue.Site) : s.pc ∉ [Flow.exit_0] := by
  cases s <;> site_decide

/-- A state at the exit's position does not continue. -/
theorem next_ret {g : Nat} {d : ThreadD} {e : Event} (h : (code L g).pc d ∈ [Flow.exit_0]) :
    (code L g).next d e = none := by
  rcases d with p | r
  · exact absurd h (Prologue.site_not_ret p.site)
  · cases r with
    | idle s =>
      have hs := Idle.site_ret s.site h
      obtain ⟨site⟩ := s
      simp only at hs
      subst hs
      rfl
    | loader d =>
      have hs := Loader.site_ret d.site h
      obtain ⟨site, _⟩ := d
      simp only at hs
      subst hs
      rfl
    | mma d =>
      have hs := Facts.mma_site_ret d.site h
      obtain ⟨site, _⟩ := d
      simp only at hs
      subst hs
      rfl
    | store d =>
      have hs := Facts.store_site_ret d.site h
      obtain ⟨site, _⟩ := d
      simp only at hs
      subst hs
      rfl
    | softmax d =>
      have hs := Facts.soft_site_ret d.site h
      obtain ⟨site, _⟩ := d
      simp only at hs
      subst hs
      rfl
    | corr d =>
      have hs := Facts.corr_site_ret d.site h
      obtain ⟨site, _⟩ := d
      simp only at hs
      subst hs
      rfl

/-- **The roles' run invariant and the machine state's invariant at the trace's end**, when no
site template is undefined behaviour: the last event, if any, does not end the thread (an
undefined behaviour stops the machine, `TcFacts_ub_stop`; an exit leaves it, `next_ret`), so it
fires from its state and continues into the end state. -/
theorem end_good (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) (hok : Cross.SitesTmplOk L) {g : Nat} {d : ThreadD}
    (hg : g < L.threads) (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) :
    roleJ L g d (X.tr g) ∧ (code L g).inv d := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  rcases hn : (X.tr g).length with _ | n
  · rw [hn, Frame.stateAt_zero] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    rw [List.length_eq_zero_iff.mp hn]
    exact ⟨(roleJ_run hpre hg).init, ⟨by simp, by simp⟩⟩
  rw [hn] at hσ
  have hlt : n < (X.tr g).length := by omega
  have he : X.get (g, n) = some (X.tr g)[n] := List.getElem?_eq_getElem hlt
  have he' : (X.tr g)[n]? = some (X.tr g)[n] := he
  have hend : ¬ Ends (X.tr g)[n] := by
    rintro (⟨f, hf⟩ | hx)
    · have hu : X.get (g, n) = some ⟨((X.tr g)[n]).pc, .ub f⟩ := by rw [he, ← hf]
      rcases TcFacts_ub_stop hpre hX ht hok hg hu with h | h
      · have h' : Frame.stateAt (code L) X g n = none := h
        rw [Frame.stateAt_succ he', h'] at hσ
        cases hσ
      · have h' : Frame.stateAt (code L) X g n = some none := h
        rw [Frame.stateAt_succ he', h'] at hσ
        cases hσ
    · have hx' : X.get (g, n) = some ⟨((X.tr g)[n]).pc, .exit⟩ := by rw [he, ← hx]
      obtain ⟨d0, hσ0⟩ := Frame.event_state hC hX ht hx' (fun _ _ h => by cases h)
      obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hC hX hx' hσ0
      have hret : retOp ins.op = true := retOp_of_fires hf rfl
      have hnx := next_ret (e := (X.tr g)[n]) (OpPcsFast.mem kernel_ret_pcs hc hret)
      rw [Frame.stateAt_succ he', hσ0] at hσ
      change (code L g).next d0 _ = _ at hσ
      rw [hnx] at hσ
      cases hσ
  obtain ⟨d0, t0, ins, u, hσ0, hJ, hat, hi, hc, hf⟩ :=
    Cross.event_cont hpre hX ht (fun g hg => roleJ_run hpre hg) he hend
  have hnext : (code L g).next d0 (X.tr g)[n] = some (some d) := by
    rw [Frame.stateAt_succ he', hσ0] at hσ
    exact hσ
  have h := (roleJ_run hpre hg).step hJ hat hi hc hf hnext
  have heq : (X.tr g).take n ++ [(X.tr g)[n]] = X.tr g := by
    rw [← Option.toList_some, ← List.getElem?_eq_getElem hlt, ← List.take_add_one,
      List.take_of_length_le (by omega)]
  rw [heq] at h
  refine ⟨h, ?_⟩
  rcases ((hC g hg).steps d0).step ins hat hi hc hf with (hs | ⟨d', t', hs, -, hgood⟩) | ⟨hs, -⟩
  · rw [hnext] at hs; cases hs
  · rw [hnext] at hs
    obtain rfl := Option.some.inj (Option.some.inj hs)
    exact hgood.2
  · rw [hnext] at hs; cases hs

end
end PTX.Kernels.FlashAttn4Fwd.Proof
