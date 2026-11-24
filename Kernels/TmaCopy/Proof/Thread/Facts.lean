-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmaCopy.Proof.Interface
public import Lemmas.Flow.RunInv

@[expose] public section

/-! # `tma_copy`: the thread facts

At each site of thread 0 the instruction's template is its site's (`site_tmpl`), so its event is
the site's event (`event_of_tmpl`). Along a thread's run its events so far are fixed by its
state (`Along`, the run invariant, proved by `Code.run_inv`). The machine never gives up
(`tracked`); it stops only after a read whose bytes rebuild to no value, after a store of a value
that is not one word, and after the exit, so an event after it stopped is undefined behaviour
right after such a read. `thread_facts` collects `ThreadFacts`. -/

namespace PTX.Kernels.TmaCopy.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {A B : Nat} {x : Value} {mem0 : Mem0} {g : Nat}

/-- A thread at a site other than the exit is thread 0. -/
theorem along_zero {s : Site} {pre : List Event} (h : Along L A B g s pre) : s ≠ .exit → g = 0 := by
  cases s <;> first | exact fun hs => absurd rfl hs | exact fun _ => h.1

/-- **The template of each site**, of thread 0 at every site but the exit. -/
theorem site_tmpl (hpre : Pre L A B x mem0) {s : Site} {t : TState} {pre : List Event}
    (hJ : Along L A B g s pre) (hat : (code L A B g).AtD s t) :
    SiteTmpl L A B s ((code L A B g).tmpl (some s) t) := by
  cases s with
  | exit => exact tmpl_exit
  | store v =>
    obtain ⟨rfl, -, bs, -, hv, hl⟩ := hJ
    have hb := rebuild_bytes_of_length hv hl
    rw [tmpl_store hpre hat, storeValue_of_bytes (by rw [hb])]
    exact .inl ⟨hb, _, rfl⟩
  | _ =>
    obtain rfl := along_zero hJ nofun
    first
      | exact ⟨_, tmpl_init hpre hat⟩
      | exact ⟨_, tmpl_fence⟩
      | exact ⟨_, tmpl_arrive hpre hat⟩
      | exact ⟨_, tmpl_bulk hpre hat⟩
      | exact ⟨_, tmpl_wait hpre hat⟩
      | exact ⟨_, tmpl_load hpre hat⟩

/-- **The event of a site's template.** -/
theorem event_of_tmpl {s : Site} {m : Tmpl} {e : Event} {o : Option TState}
    (hm : SiteTmpl L A B s m) (hf : Fires s.pc m e o) : SiteEvent L A B s e := by
  cases s with
  | init => obtain ⟨u, rfl⟩ := hm; exact hf.1
  | fence => obtain ⟨u, rfl⟩ := hm; exact hf.1
  | arrive => obtain ⟨u, rfl⟩ := hm; exact hf.1
  | bulk => obtain ⟨u, rfl⟩ := hm; exact hf.1
  | wait =>
    obtain ⟨k, rfl⟩ := hm
    obtain ⟨ok, he, -⟩ := hf
    exact ⟨ok, he⟩
  | load =>
    obtain ⟨k, rfl⟩ := hm
    obtain ⟨bs, -, he, -⟩ := hf
    exact ⟨bs, he⟩
  | store v =>
    rcases hm with ⟨hv, u, rfl⟩ | ⟨hv, f, rfl⟩
    · exact .inl ⟨hv, hf.1⟩
    · exact .inr ⟨hv, f, hf.1⟩
  | exit => subst hm; exact hf.1

/-- The event at a followed state whose instruction fires, given the thread at a site other than
the exit is thread 0. -/
theorem site_event (hpre : Pre L A B x mem0) {s : Site} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {pre : List Event} (hJ : Along L A B g s pre)
    (hat : (code L A B g).AtD s t)
    (hc : kernel.code[s.pc]? = some ins) (hf : Fires s.pc (eventTmpl [] L g t ins.op) e o) :
    SiteEvent L A B s e := by
  have hm := site_tmpl hpre hJ hat
  simp only [Code.tmpl, code, hc] at hm
  exact event_of_tmpl hm hf

/-- One step of the run invariant. -/
theorem along_step (hpre : Pre L A B x mem0) {s s' : Site} {pre : List Event} {e : Event}
    {t : TState} {ins : Instr} {o : Option TState} (hJ : Along L A B g s pre)
    (hat : (code L A B g).AtD s t) (hc : kernel.code[s.pc]? = some ins)
    (hf : Fires s.pc (eventTmpl [] L g t ins.op) e o) (hn : next s e = some (some s')) :
    Along L A B g s' (pre ++ [e]) := by
  have hev := site_event hpre hJ hat hc hf
  cases s with
  | init =>
    obtain ⟨h0, rfl⟩ := hJ
    cases hn
    rw [hev]
    exact ⟨h0, rfl⟩
  | fence =>
    obtain ⟨h0, rfl⟩ := hJ
    cases hn
    rw [hev]
    exact ⟨h0, rfl⟩
  | arrive =>
    obtain ⟨h0, rfl⟩ := hJ
    cases hn
    rw [hev]
    exact ⟨h0, rfl⟩
  | bulk =>
    obtain ⟨h0, rfl⟩ := hJ
    cases hn
    rw [hev]
    exact ⟨h0, 0, by simp [issue]⟩
  | wait =>
    obtain ⟨h0, n, rfl⟩ := hJ
    obtain ⟨ok, rfl⟩ := hev
    cases ok
    · simp only [next, waitE] at hn
      cases hn
      exact ⟨h0, n + 1, by simp [List.replicate_succ']⟩
    · simp only [next, waitE] at hn
      cases hn
      exact ⟨h0, n, rfl⟩
  | load =>
    have hm := site_tmpl hpre hJ hat
    simp only [Code.tmpl, code, hc] at hm
    obtain ⟨k, hm⟩ := hm
    rw [hm] at hf
    obtain ⟨bs, hl, he, -⟩ := hf
    obtain ⟨h0, n, rfl⟩ := hJ
    obtain ⟨bs', rfl⟩ := hev
    obtain rfl : bs = bs' := by
      simp only [rdE, Event.mk.injEq, Kind.rd.injEq] at he
      exact he.2.2.symm
    simp only [next, rdE] at hn
    split at hn
    · rename_i v hv
      cases hn
      exact ⟨h0, n, bs, by simp, hv, hl⟩
    · cases hn
  | store v =>
    obtain ⟨h0, n, bs, rfl, hv, -⟩ := hJ
    rcases hev with ⟨hb, rfl⟩ | ⟨-, f, rfl⟩
    · simp only [next, wrE] at hn
      cases hn
      exact .inr ⟨h0, n, bs, v, by simp, hv, hb⟩
    · simp [next] at hn
  | exit => simp [next] at hn

variable {X : Execution}

/-- **The run invariant holds at every followed state.** -/
theorem along (hpre : Pre L A B x mem0) (hX : Consistent L kernel [] mem0 X) (hg : g < L.threads)
    {k : Nat} {s : Site} (hσ : stateAt L A B X g k = some (some s)) :
    Along L A B g s ((X.tr g).take k) := by
  have htr := Frame.trace (C := code L A B) (fun _ h => sound hpre h) hX hg
  refine Code.run_inv (sound hpre hg) htr (Along L A B g) ?_ ?_ k s hσ
  · show Along L A B g (if g = 0 then .init else .exit) []
    split_ifs with hg0
    · exact ⟨hg0, rfl⟩
    · exact .inl ⟨hg0, rfl⟩
  · intro s s' pre e t ins o hJ hat _ hc hf hn
    exact along_step hpre hJ hat hc hf hn

/-- The machine never gives up a thread: a step continues in a state or stops. -/
theorem next_ne (s : Site) (e : Event) : next s e ≠ some none := by
  cases s <;> simp only [next] <;> (repeat' split) <;> simp

/-- The machine follows every thread. -/
theorem tracked : Frame.Tracked (code L A B) X :=
  Frame.tracked_of_next fun _ s e => next_ne s e

/-- **The event at a followed state** is its site's. -/
theorem event (hpre : Pre L A B x mem0) (hX : Consistent L kernel [] mem0 X) {k : Nat}
    {e : Event} {s : Site} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : stateAt L A B X g k = some (some s)) : SiteEvent L A B s e := by
  have hC : ∀ g < L.threads, (code L A B g).Sound := fun _ h => sound hpre h
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site hC hX he hσ
  exact site_event hpre (along hpre hX hg hσ) hat hc hf

/-- An event that ends the thread is its last. -/
theorem end_last (hX : Consistent L kernel [] mem0 X) (hg : g < L.threads) {i : Nat} {e : Event}
    (he : X.get (g, i) = some e) (hk : Flow.Ends e) : i + 1 = (X.tr g).length := by
  obtain ⟨o, hr⟩ := hX.thr g hg
  exact Flow.Run.end_last hr he hk

/-- **An event after the machine stopped** is undefined behaviour right after a read whose bytes
are not one 4-byte value. -/
theorem dead (hpre : Pre L A B x mem0) (hX : Consistent L kernel [] mem0 X) {k : Nat}
    {e : Event} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : stateAt L A B X g k = none) : ∃ pc f bs, e = ⟨pc, .ub f⟩ ∧ 0 < k ∧
      X.get (g, k - 1) = some (rdE L.sharedBase bs) ∧ ∀ v, rebuild 3 bs = .ok v → v.bytes ≠ 4 := by
  have hC : ∀ g < L.threads, (code L A B g).Sound := fun _ h => sound hpre h
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨i, s, hi, hs, hs'⟩ := Frame.first_stop tracked hg hσ
  obtain ⟨ei, hei⟩ : ∃ ei, X.get (g, i) = some ei :=
    ⟨_, List.getElem?_eq_getElem (show i < (X.tr g).length by omega)⟩
  have hn : next s ei = none := by
    rw [Frame.stateAt_succ hei, hs] at hs'
    exact hs'
  have hlast : ¬ Flow.Ends ei := fun hend => by
    have := end_last hX hg hei hend
    omega
  have hev := event hpre hX hg hei hs
  -- the stop is a load whose bytes rebuild to no value
  obtain ⟨bs, rfl, hbad⟩ : ∃ bs, ei = rdE L.sharedBase bs ∧ ∀ v, rebuild 3 bs = .ok v → False := by
    cases s with
    | wait =>
      obtain ⟨ok, rfl⟩ := hev
      simp [next, waitE] at hn
    | load =>
      obtain ⟨bs, rfl⟩ := hev
      refine ⟨bs, rfl, fun v hv => ?_⟩
      simp [next, rdE, hv] at hn
    | store v =>
      rcases hev with ⟨-, rfl⟩ | ⟨-, f, rfl⟩
      · simp [next, wrE] at hn
      · exact absurd (.inl ⟨f, rfl⟩) hlast
    | exit => subst hev; exact absurd (.inr rfl) hlast
    | _ => simp [next] at hn
  -- the next event, at a dead state, is undefined behaviour, the last event
  have hi1 : i + 1 ≤ k := hi
  obtain ⟨e1, he1⟩ : ∃ e1, X.get (g, i + 1) = some e1 :=
    ⟨_, List.getElem?_eq_getElem (show i + 1 < (X.tr g).length by omega)⟩
  obtain ⟨pc, f, rfl⟩ : ∃ pc f, e1 = ⟨pc, .ub f⟩ := by
    rcases Frame.fired hC hX he1 with ⟨σ, o, hσ1, -⟩ | ⟨-, h⟩
    · rw [hs'] at hσ1; cases hσ1
    · exact h
  have hend := end_last hX hg he1 (.inl ⟨f, rfl⟩)
  obtain rfl : k = i + 1 := by omega
  rw [he1] at he
  cases he
  exact ⟨pc, f, bs, rfl, by omega, by simpa using hei, fun v hv _ => hbad v hv⟩

/-- **A pending thread fires its site's template** after local steps. -/
theorem fire (hpre : Pre L A B x mem0) (hX : Consistent L kernel [] mem0 X) {s : Site}
    {t : TState} (hg : g < L.threads) (hσ : stateAt L A B X g (X.tr g).length = some (some s))
    (hrun : Run kernel [] L g {} (X.tr g) (some t)) :
    ∃ t1 m, Relation.ReflTransGen (Tau kernel [] L g) t t1 ∧ t1.pc = s.pc ∧
      out kernel [] L g t1 = .ev m ∧ SiteTmpl L A B s m := by
  have hC : ∀ g < L.threads, (code L A B g).Sound := fun _ h => sound hpre h
  obtain ⟨t1, ins, hl, hat, -, hc, hout⟩ := Frame.end_at hC hg hrun hσ
  have hc' : kernel.code[s.pc]? = some ins := hc
  have hm := site_tmpl hpre (along hpre hX hg hσ) hat
  simp only [Code.tmpl, code, hc'] at hm
  exact ⟨t1, _, hl, hat.1, hout, hm⟩

/-- **The thread facts of a consistent execution.** -/
theorem thread_facts (hpre : Pre L A B x mem0) (hX : Consistent L kernel [] mem0 X) :
    ThreadFacts L A B X where
  sound := fun _ h => sound hpre h
  tracked := tracked
  event := fun hg he hσ => event hpre hX hg he hσ
  along := fun hg _ hσ => along hpre hX hg hσ
  dead := fun hg he hσ => dead hpre hX hg he hσ
  fire := fun hg hσ hrun => fire hpre hX hg hσ hrun

end

end PTX.Kernels.TmaCopy.Proof
