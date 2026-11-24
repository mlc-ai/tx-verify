-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.AddOne.Proof.Interface
public import Lemmas.Flow.RunInv
public import Lemmas.Kernel.Fragment

@[expose] public section

/-! # `add_one`: the thread facts

Each site performs one event (`site_event`): the load reads `A[g]`, the store writes the sum to
`A[g]` when it is one 4-byte word and is undefined behaviour otherwise, the exit exits. Along a
thread's run its events so far are fixed by its state (`Along`, the run invariant, proved by
`Code.run_inv`): nothing at the load, the read at the store, the read and the write at the exit.
The machine never gives up (`tracked`), and stops only after a read whose bytes give no sum. As a
fragment (`frag`, with the expected read `Expect`), its undefined behaviour therefore follows an
unexpected read (`Frame.thread_noUb`). `threadFacts` collects what the layers above use. -/

namespace PTX.Kernels.AddOne.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {A : Nat} {x : Nat → BitVec 32} {mem0 : Mem0} {g : Nat}

theorem reg_at {s : Site} {t : TState} {r : Nat} (h : At t s.pc (facts A g s))
    (hl : r ∈ Flow.live s.pc) : t.regs r = some (valueOf A g s r) :=
  holds_mem h.2.2.2.2 (Flow.mem_factsFrom hl)

/-- The event a site performs. A store writes the value of its source, which the store rule of
THREAD-ACCESS takes from `storeValue`: the stored value itself for a four-byte source, its low
four bytes for a wider one, and a fault otherwise. -/
def SiteEvent (A g : Nat) : Site → Event → Prop
  | .load, e => ∃ bs, e = rdE A g bs
  | .store w, e => (∃ v, storeValue 32 w = .ok v ∧ e = wrE A g v) ∨
      ∃ f, storeValue 32 w = .error f ∧ e = ⟨Flow.store_0, .ub f⟩
  | .exit, e => e = ⟨Flow.exit_0, .exit⟩

/-- **The event of each site.** -/
theorem site_event (hpre : Pre L A x mem0) (hg : g < L.threads) {s : Site} {t : TState}
    {e : Event} {o : Option TState} {ins : Instr}
    (hat : (code L A g).AtD s t) (hc : kernel.code[s.pc]? = some ins)
    (hf : Fires s.pc (eventTmpl [] L g t ins.op) e o) : SiteEvent A g s e := by
  have h : At t s.pc (facts A g s) := hat
  have hgb : g < L.block := by simpa [Launch.threads, hpre.grid] using hg
  have hrA := hpre.rangeA
  have haA := hpre.alignA
  cases s with
  | load =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
    have h6 : t.regs 6 = some (b64 (A + 4 * g)) := by
      rw [reg_at h (by table_decide)]; ao_values
    simp only [eventTmpl] at hf
    rw [memTmpl_load rfl rfl rfl rfl (by decide)] at hf
    change Fires _ (loadTmpl [] L g t .global false 32 [2] 6 0) e o at hf
    rw [loadTmpl_global h.2.1 h6 (by omega) (by decide) (by omega)] at hf
    obtain ⟨bs, -, rfl, -⟩ := hf
    exact ⟨bs, rfl⟩
  | store w =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_0)
    have h6 : t.regs 6 = some (b64 (A + 4 * g)) := by
      rw [reg_at h (by table_decide)]; ao_values
    have h3 : t.regs 3 = some w := by
      rw [reg_at h (by table_decide)]; ao_values
    simp only [eventTmpl] at hf
    rw [memTmpl_store rfl rfl rfl rfl (by decide)] at hf
    change Fires _ (storeTmpl L g t .global 32 6 0 [.reg 3]) e o at hf
    rw [storeTmpl_global h.2.1 h6 (by omega) (by decide) (by omega) h3] at hf
    rcases hsv : storeValue 32 w with f | v'
    · simp only [hsv] at hf
      exact .inr ⟨f, hsv, hf.1⟩
    · simp only [hsv] at hf
      exact .inl ⟨v', hsv, hf.1⟩
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    exact hf.1

/-- A store value that the store rule rejects is no four-byte word. -/
theorem storeValue_error_bytes {v : Value} {f : Fault} (h : storeValue 32 v = .error f) :
    v.bytes ≠ 4 := by
  intro hb
  rw [storeValue_of_bytes (w := 32) (v := v) (by simpa using hb)] at h
  cases h

/-- The events of a thread before it is at a site: the run invariant. -/
def Along (L : Launch) (A g : Nat) : Site → List Event → Prop
  | .load, pre => pre = []
  | .store w, pre => ∃ bs v, pre = [rdE A g bs] ∧ rebuild 3 bs = .ok v ∧ incr L g v = .ok w
  | .exit, pre => ∃ bs v w w', pre = [rdE A g bs, wrE A g w'] ∧ rebuild 3 bs = .ok v ∧
      incr L g v = .ok w ∧ storeValue 32 w = .ok w'

/-- **The run invariant**: at every state of its run a thread has made the events of `Along`. -/
theorem along {X : Execution} (hpre : Pre L A x mem0) (hX : Consistent L kernel [] mem0 X)
    (hg : g < L.threads) :
    ∀ k s, Frame.stateAt (code L A) X g k = some (some s) →
      Along L A g s ((X.tr g).take k) := by
  have htr := Frame.trace (C := code L A) (fun _ h => sound hpre h) hX hg
  refine Code.run_inv (sound hpre hg) htr (Along L A g) rfl ?_
  intro s s' pre e t ins o hJ hat _ hc hf hn
  have hev := site_event hpre hg hat hc hf
  cases s with
  | load =>
    subst hJ
    obtain ⟨bs, rfl⟩ := hev
    simp only [code, next, rdE] at hn
    split at hn
    · rename_i v hv
      split at hn
      · rename_i w hw
        cases hn
        exact ⟨bs, v, rfl, hv, hw⟩
      · cases hn
    · cases hn
  | store w =>
    obtain ⟨bs, v, rfl, hv, hw⟩ := hJ
    rcases hev with ⟨w', hsv, rfl⟩ | ⟨f, hsv, rfl⟩
    · simp only [code, next, wrE] at hn
      cases hn
      exact ⟨bs, v, w, _, rfl, hv, hw, hsv⟩
    · simp [code, next] at hn
  | exit => simp [code, next] at hn

/-- The machine never gives up on a thread. -/
theorem next_ne (s : Site) (e : Event) : next L g s e ≠ some none := by
  cases s <;> simp only [next] <;> (repeat' split) <;> simp

theorem tracked {X : Execution} : Frame.Tracked (code L A) X :=
  Frame.tracked_of_next fun _ s e => next_ne s e

/-- The reference invariant: the store carries a 4-byte value. -/
def Ref : Site → Prop
  | .store w => w.bytes = 4
  | _ => True

/-- What the load must return: bytes whose sum is a 4-byte value. -/
def Expect (L : Launch) (g : Nat) : Site → Event → Prop
  | .load, e => ∀ a bs, e.kind = .rd a bs →
      ∃ v w, rebuild 3 bs = .ok v ∧ incr L g v = .ok w ∧ w.bytes = 4
  | _, _ => True

/-- The thread as a fragment: it follows every value, and faults only on an unexpected one. -/
def frag (L : Launch) (A g : Nat) : Fragment kernel [] L g :=
  ⟨code L A g, SiteEvent A g, fun _ => .any, Ref, Expect L g⟩

theorem frag_ok (hpre : Pre L A x mem0) (hg : g < L.threads) : (frag L A g).Ok := fun s =>
  { step := (sound hpre hg).steps s
    shape := fun hat _ hc hf => site_event hpre hg hat hc hf
    stop_iff := fun {e} _ _ => iff_of_false (next_ne s e) (not_not.mpr (RetKind.accepts_any e))
    ref_next := fun {e} _ hJ hE hev => by
      cases s with
      | load =>
        obtain ⟨bs, rfl⟩ := hev
        obtain ⟨v, w, hv, hw, hb⟩ := hE _ bs rfl
        simp [frag, code, next, rdE, hv, hw, Ref, hb]
      | store w =>
        rcases hev with ⟨v, -, rfl⟩ | ⟨f, hsv, rfl⟩
        · simp [frag, code, next, wrE, Ref]
        · exact absurd hJ (storeValue_error_bytes hsv)
      | exit => subst hev; simp [frag, code, next, Ends]
    ref_safe := fun {e} _ hJ hev f => by
      cases s with
      | load => obtain ⟨bs, rfl⟩ := hev; simp [rdE]
      | store w =>
        rcases hev with ⟨v, -, rfl⟩ | ⟨f, hsv, rfl⟩
        · simp [wrE]
        · exact absurd hJ (storeValue_error_bytes hsv)
      | exit => subst hev; simp }

variable {X : Execution}

/-- **Each event of a thread** fires from a state of its machine, with the run invariant there,
or is undefined behaviour after the machine stopped. -/
theorem event_at (hpre : Pre L A x mem0) (hX : Consistent L kernel [] mem0 X) {k : Nat}
    {e : Event} (he : X.get (g, k) = some e) :
    (∃ s, Frame.stateAt (code L A) X g k = some (some s) ∧
      Along L A g s ((X.tr g).take k) ∧ SiteEvent A g s e) ∨
    (Frame.stateAt (code L A) X g k = none ∧ ∃ pc f, e = ⟨pc, .ub f⟩) := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hC : ∀ g < L.threads, (code L A g).Sound := fun _ h => sound hpre h
  rcases Frame.fired hC hX he with ⟨σ, o, hσ, -⟩ | h
  · cases σ with
    | none => exact absurd hσ (tracked g k hg)
    | some s =>
      have hJ := along hpre hX hg k s hσ
      obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site hC hX he hσ
      exact .inl ⟨s, hσ, hJ, site_event hpre hg hat hc hf⟩
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

/-- **The thread facts.** -/
theorem threadFacts (hpre : Pre L A x mem0) (hX : Consistent L kernel [] mem0 X) :
    ThreadFacts L A X where
  tracked := tracked
  kinds := by
    rintro ⟨g, k⟩ e he
    rcases event_at hpre hX he with ⟨s, -, -, hev⟩ | ⟨-, pc, f, rfl⟩
    · cases s with
      | load =>
        obtain ⟨bs, rfl⟩ := hev
        exact .inl ⟨_, _, rfl⟩
      | store w =>
        rcases hev with ⟨v, -, rfl⟩ | ⟨f, -, rfl⟩
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
        obtain ⟨bs', hb⟩ := hev
        simp only [rdE, Event.mk.injEq, Kind.rd.injEq] at hb
        exact ⟨(take_eq (get_lt he) hJ).1, hb.2.1⟩
      | store w =>
        rcases hev with ⟨v, -, hb⟩ | ⟨f, -, hb⟩
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
      | store w =>
        obtain ⟨rb, v, hp, hv, hw⟩ := hJ
        rcases hev with ⟨w', hsw, hb⟩ | ⟨f, hsw, hb⟩
        · simp only [wrE, Event.mk.injEq, Kind.wr.injEq] at hb
          obtain ⟨hk, h0⟩ := take_eq (get_lt he) hp
          exact ⟨hk, hb.2.1, rb, v, w, w', h0 0 (by simp), hv, hw, hsw, hb.2.2⟩
        · simp at hb
      | exit => simp [SiteEvent] at hev
    · simp at hf
  ub := by
    intro g k pc f he
    have hg : g < L.threads := Frame.lt_of_get hX he
    by_contra hno
    simp only [not_exists, not_and, not_forall, not_not] at hno
    refine (Frame.thread_noUb (F := frag L A) (fun _ h => sound hpre h) (fun _ h => frag_ok hpre h)
      hX trivial (n := k + 1) ?_).1 k (by omega) _ he f rfl
    intro j _ s e hj hσ _
    cases s with
    | load =>
      obtain ⟨bs, rfl⟩ := (Frame.fired_ev (F := frag L A) (fun _ h => sound hpre h)
        (fun _ h => frag_ok hpre h) hX hj hσ).1
      obtain ⟨rfl, -⟩ := take_eq (get_lt hj) (along hpre hX hg j .load hσ)
      intro a bs' hk
      simp only [rdE, Kind.rd.injEq] at hk
      obtain ⟨-, rfl⟩ := hk
      obtain ⟨v, w, hv, hw, hb⟩ := hno bs hj
      exact ⟨v, w, hv, hw, hb⟩
    | _ => trivial
  exit_write := by
    intro g k pc he
    rcases event_at hpre hX he with ⟨s, -, hJ, hev⟩ | ⟨-, pc', f, hf⟩
    · cases s with
      | load =>
        obtain ⟨bs', hb⟩ := hev
        simp [rdE] at hb
      | store w =>
        rcases hev with ⟨v, -, hb⟩ | ⟨f, -, hb⟩
        · simp [wrE] at hb
        · simp at hb
      | exit =>
        obtain ⟨rb, v, w, w', hp, -, -, -⟩ := hJ
        exact ⟨_, _, _, (take_eq (get_lt he) hp).2 1 (by simp)⟩
    · simp at hf

end

end PTX.Kernels.AddOne.Proof
