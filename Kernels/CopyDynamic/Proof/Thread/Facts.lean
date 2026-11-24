-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyDynamic.Proof.Interface
public import Lemmas.Flow.RunInv

@[expose] public section

/-! # `copy_dynamic`: the thread facts

Each site performs one event (`site_event`): the load reads `A[g]`, the store writes its value to
`B[g]` when it is one 4-byte word and is undefined behaviour otherwise, the exit exits. Along a
thread's run its events so far are fixed by its state (`Along`, the run invariant, proved by
`Code.run_inv`): nothing at the load, the read at the store, the read and the write or nothing at
the exit. The machine never gives up (`tracked`), and stops only after a read whose bytes rebuild
to no value. `threadFacts` collects what the layers above use. -/

namespace PTX.Kernels.CopyDynamic.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0} {g : Nat}

theorem reg_at {s : Site} {t : TState} {r : Nat} (h : At t s.pc (facts A B N g s))
    (hl : r ∈ Flow.live s.pc) : t.regs r = some (valueOf A B N g s r) :=
  holds_mem h.2.2.2.2 (Flow.mem_factsFrom hl)

/-- The event a site performs. -/
def SiteEvent (A B g : Nat) : Site → Event → Prop
  | .load, e => ∃ bs, e = rdE A g bs
  | .store v, e => (∃ w, storeValue 32 v = .ok w ∧ e = wrE B g w) ∨
      ∃ f, storeValue 32 v = .error f ∧ e = ⟨Flow.store_0, .ub f⟩
  | .exit, e => e = ⟨Flow.exit_0, .exit⟩

/-- A store value that the store rule rejects is no four-byte word. -/
theorem storeValue_error_bytes {v : Value} {f : Fault} (h : storeValue 32 v = .error f) :
    v.bytes ≠ 4 := by
  intro hb
  rw [storeValue_of_bytes (w := 32) (v := v) (by simpa using hb)] at h
  cases h

/-- **The event of each site**, at a thread `g < N` for the load and the store. -/
theorem site_event (hpre : Pre L A B N x mem0) {s : Site} {t : TState} {e : Event}
    {o : Option TState} {ins : Instr} (hgN : s ≠ .exit → g < N)
    (hat : (code L A B N g).AtD s t) (hc : kernel.code[s.pc]? = some ins)
    (hf : Fires s.pc (eventTmpl [] L g t ins.op) e o) : SiteEvent A B g s e := by
  have h : At t s.pc (facts A B N g s) := hat
  cases s with
  | load =>
    have hgN := hgN nofun
    have hrA := hpre.rangeA
    have haA := hpre.alignA
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
    have h15 : t.regs 15 = some (b64 (A + 4 * g)) := by
      rw [reg_at h (by table_decide)]; cd_values
    simp only [eventTmpl] at hf
    rw [memTmpl_load rfl rfl rfl rfl (by decide)] at hf
    change Fires _ (loadTmpl [] L g t .global false 32 [8] 15 0) e o at hf
    rw [loadTmpl_global h.2.1 h15 (by omega) (by decide) (by omega)] at hf
    obtain ⟨bs, -, rfl, -⟩ := hf
    exact ⟨bs, rfl⟩
  | store v =>
    have hgN := hgN nofun
    have hrB := hpre.rangeB
    have haB := hpre.alignB
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_0)
    have h16 : t.regs 16 = some (b64 (B + 4 * g)) := by
      rw [reg_at h (by table_decide)]; cd_values
    have h8 : t.regs 8 = some v := by
      rw [reg_at h (by table_decide)]; cd_values
    simp only [eventTmpl] at hf
    rw [memTmpl_store rfl rfl rfl rfl (by decide)] at hf
    change Fires _ (storeTmpl L g t .global 32 16 0 [.reg 8]) e o at hf
    rw [storeTmpl_global h.2.1 h16 (by omega) (by decide) (by omega) h8] at hf
    rcases hsv : storeValue 32 v with f | w
    · simp only [hsv] at hf
      exact .inr ⟨f, hsv, hf.1⟩
    · simp only [hsv] at hf
      exact .inl ⟨w, hsv, hf.1⟩
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    exact hf.1

/-- The events of a thread before it is at a site: the run invariant. -/
def Along (A B N g : Nat) : Site → List Event → Prop
  | .load, pre => g < N ∧ pre = []
  | .store v, pre => g < N ∧ ∃ bs, pre = [rdE A g bs] ∧ rebuild 3 bs = .ok v
  | .exit, pre => (N ≤ g ∧ pre = []) ∨
      (g < N ∧ ∃ bs v w, pre = [rdE A g bs, wrE B g w] ∧ rebuild 3 bs = .ok v ∧
        storeValue 32 v = .ok w)

theorem along_ne_exit {s : Site} {pre : List Event} (h : Along A B N g s pre) :
    s ≠ .exit → g < N := by
  cases s with
  | load => exact fun _ => h.1
  | store => exact fun _ => h.1
  | exit => exact fun hs => absurd rfl hs

/-- **The run invariant**: at every state of its run a thread has made the events of `Along`. -/
theorem along {X : Execution} (hpre : Pre L A B N x mem0) (hX : Consistent L kernel [] mem0 X)
    (hg : g < L.threads) :
    ∀ k s, Frame.stateAt (code L A B N) X g k = some (some s) →
      Along A B N g s ((X.tr g).take k) := by
  have htr := Frame.trace (C := code L A B N) (fun _ h => sound hpre h) hX hg
  refine Code.run_inv (sound hpre hg) htr (Along A B N g) ?_ ?_
  · show Along A B N g (if g < N then .load else .exit) []
    split_ifs with hgN
    · exact ⟨hgN, rfl⟩
    · exact .inl ⟨by omega, rfl⟩
  · intro s s' pre e t ins o hJ hat _ hc hf hn
    have hev := site_event hpre (along_ne_exit hJ) hat hc hf
    cases s with
    | load =>
      obtain ⟨hgN, rfl⟩ := hJ
      obtain ⟨bs, rfl⟩ := hev
      simp only [code, next, rdE] at hn
      split at hn
      · rename_i v hv
        cases hn
        exact ⟨hgN, bs, rfl, hv⟩
      · cases hn
    | store v =>
      obtain ⟨hgN, bs, rfl, hv⟩ := hJ
      rcases hev with ⟨w, hsv, rfl⟩ | ⟨f, hsv, rfl⟩
      · simp only [code, next, wrE] at hn
        cases hn
        exact .inr ⟨hgN, bs, v, w, rfl, hv, hsv⟩
      · simp [code, next] at hn
    | exit => simp [code, next] at hn

/-- The machine never gives up on a thread. -/
theorem tracked {X : Execution} : Frame.Tracked (code L A B N) X :=
  Frame.tracked_of_next fun _ d e => by
    cases d with
    | load =>
      simp only [code, next]
      split
      · split <;> simp
      · simp
    | store => simp only [code, next]; split <;> simp
    | exit => simp [code, next]

variable {X : Execution}

/-- **Each event of a thread** fires from a state of its machine, with the run invariant there,
or is undefined behaviour after the machine stopped. -/
theorem event_at (hpre : Pre L A B N x mem0) (hX : Consistent L kernel [] mem0 X) {k : Nat}
    {e : Event} (he : X.get (g, k) = some e) :
    (∃ s, Frame.stateAt (code L A B N) X g k = some (some s) ∧
      Along A B N g s ((X.tr g).take k) ∧ SiteEvent A B g s e) ∨
    (Frame.stateAt (code L A B N) X g k = none ∧ ∃ pc f, e = ⟨pc, .ub f⟩) := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hC : ∀ g < L.threads, (code L A B N g).Sound := fun _ h => sound hpre h
  rcases Frame.fired hC hX he with ⟨σ, o, hσ, -⟩ | h
  · cases σ with
    | none => exact absurd hσ (tracked g k hg)
    | some s =>
      have hJ := along hpre hX hg k s hσ
      obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site hC hX he hσ
      exact .inl ⟨s, hσ, hJ, site_event hpre (along_ne_exit hJ) hat hc hf⟩
  · exact .inr h

theorem get_lt {k : Nat} {e : Event} (he : X.get (g, k) = some e) : k < (X.tr g).length :=
  (List.getElem?_eq_some_iff.mp he).1

/-- A prefix fixes the position and the events before it. -/
theorem take_eq {k : Nat} {p : List Event} (hk : k < (X.tr g).length)
    (h : (X.tr g).take k = p) : k = p.length ∧ ∀ i < p.length, X.get (g, i) = p[i]? := by
  have hl := congrArg List.length h
  simp only [List.length_take] at hl
  refine ⟨by omega, fun i hi => ?_⟩
  change (X.tr g)[i]? = _
  rw [← h]
  exact (List.getElem?_take_of_lt (by omega)).symm

/-- An event that ends the thread is its last. -/
theorem end_last (hX : Consistent L kernel [] mem0 X) (hg : g < L.threads) {i : Nat} {e : Event}
    (he : X.get (g, i) = some e) (hk : Flow.Ends e) : i + 1 = (X.tr g).length := by
  obtain ⟨o, hr⟩ := hX.thr g hg
  exact Flow.Run.end_last hr he hk

/-- **The thread facts.** -/
theorem threadFacts (hpre : Pre L A B N x mem0) (hX : Consistent L kernel [] mem0 X) :
    ThreadFacts L A B N X where
  tracked := tracked
  kinds := by
    rintro ⟨g, k⟩ e he
    rcases event_at hpre hX he with ⟨s, -, -, hev⟩ | ⟨-, pc, f, rfl⟩
    · cases s with
      | load =>
        obtain ⟨bs, rfl⟩ := hev
        exact .inl ⟨_, _, rfl⟩
      | store v =>
        rcases hev with ⟨w, -, rfl⟩ | ⟨f, -, rfl⟩
        · exact .inr (.inl ⟨_, _, rfl⟩)
        · exact .inr (.inr (.inr ⟨f, rfl⟩))
      | exit =>
        subst hev
        exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr ⟨f, rfl⟩))
  reads := by
    intro g k pc a bs he
    rcases event_at hpre hX he with ⟨s, -, hJ, hev⟩ | ⟨-, pc', f, hf⟩
    · cases s with
      | load =>
        obtain ⟨hgN, hp⟩ := hJ
        obtain ⟨bs', hb⟩ := hev
        simp only [rdE, Event.mk.injEq, Kind.rd.injEq] at hb
        exact ⟨(take_eq (get_lt he) hp).1, hgN, hb.2.1⟩
      | store v =>
        rcases hev with ⟨w, -, hb⟩ | ⟨f, -, hb⟩
        · simp [wrE] at hb
        · simp at hb
      | exit => simp [SiteEvent] at hev
    · simp at hf
  writes := by
    intro g k pc a bs he
    rcases event_at hpre hX he with ⟨s, -, hJ, hev⟩ | ⟨-, pc', f, hf⟩
    · cases s with
      | load =>
        obtain ⟨bs', hb⟩ := hev
        simp [rdE] at hb
      | store v =>
        obtain ⟨hgN, rb, hp, hv⟩ := hJ
        rcases hev with ⟨w, hsv, hb⟩ | ⟨f, hsv, hb⟩
        · simp only [wrE, Event.mk.injEq, Kind.wr.injEq] at hb
          obtain ⟨hk, h0⟩ := take_eq (get_lt he) hp
          exact ⟨hk, hgN, hb.2.1, rb, v, w, h0 0 (by simp), hv, hsv, hb.2.2⟩
        · simp at hb
      | exit => simp [SiteEvent] at hev
    · simp at hf
  ub := by
    intro g k pc f he
    have hg : g < L.threads := Frame.lt_of_get hX he
    rcases event_at hpre hX he with ⟨s, -, hJ, hev⟩ | ⟨hσ, -⟩
    · cases s with
      | load =>
        obtain ⟨bs', hb⟩ := hev
        simp [rdE] at hb
      | store v =>
        obtain ⟨hgN, rb, hp, hv⟩ := hJ
        rcases hev with ⟨w, -, hb⟩ | ⟨f, hsv, hb⟩
        · simp [wrE] at hb
        · refine ⟨hgN, rb, (take_eq (get_lt he) hp).2 0 (by simp), fun v' hv' => ?_⟩
          rw [hv] at hv'
          cases hv'
          exact storeValue_error_bytes hsv
      | exit => simp [SiteEvent] at hev
    · obtain ⟨i, s, hi, hs, hs'⟩ := Frame.first_stop tracked hg hσ
      have hik : i < (X.tr g).length := by have := get_lt he; omega
      obtain ⟨ei, hei⟩ : ∃ ei, X.get (g, i) = some ei :=
        ⟨_, List.getElem?_eq_getElem hik⟩
      rw [Frame.stateAt_succ hei, hs] at hs'
      have hn : (code L A B N g).next s ei = none := hs'
      have hlast : ¬ Flow.Ends ei := fun hk => by
        have := end_last hX hg hei hk
        have := get_lt he
        omega
      rcases event_at hpre hX hei with ⟨s', hs'', hJ, hev⟩ | ⟨hσ', -⟩
      · rw [hs] at hs''
        cases hs''
        cases s with
        | load =>
          obtain ⟨hgN, hp⟩ := hJ
          obtain ⟨rb, rfl⟩ := hev
          refine ⟨hgN, rb, ?_, fun v hv => ?_⟩
          · obtain ⟨rfl, -⟩ := take_eq hik hp
            exact hei
          · simp [code, next, rdE, hv] at hn
        | store v =>
          rcases hev with ⟨w, -, rfl⟩ | ⟨f', -, rfl⟩
          · simp [code, next, wrE] at hn
          · exact absurd (.inl ⟨f', rfl⟩) hlast
        | exit =>
          subst hev
          exact absurd (.inr rfl) hlast
      · rw [hs] at hσ'
        cases hσ'
  exit_write := by
    intro g k pc he hgN
    rcases event_at hpre hX he with ⟨s, -, hJ, hev⟩ | ⟨-, pc', f, hf⟩
    · cases s with
      | load =>
        obtain ⟨bs', hb⟩ := hev
        simp [rdE] at hb
      | store v =>
        rcases hev with ⟨w, -, hb⟩ | ⟨f, -, hb⟩
        · simp [wrE] at hb
        · simp at hb
      | exit =>
        rcases hJ with ⟨hNg, -⟩ | ⟨-, rb, v, w, hp, -, -⟩
        · omega
        · exact ⟨_, _, _, (take_eq (get_lt he) hp).2 1 (by simp)⟩
    · simp at hf

end

end PTX.Kernels.CopyDynamic.Proof
