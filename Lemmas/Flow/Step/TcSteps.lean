-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.SiteCases
public import Lemmas.Flow.EventCont
public import Lemmas.Flow.Async

@[expose] public section

/-! # Step combinators for Tensor Memory loads, stores and waits and for `bar.arrive`

A proof tool (promoted from the tml-fa4 correction warps' proof). Nothing here is specific to a
kernel.

* `fires_barArrive_next`, `fires_tcWaitSt_next`: `bar.arrive` with a count and
  `tcgen05.wait::st` continue at the next instruction; `advances` tries them where this module is
  imported.
* `fires_tcSt_next`: a `tcgen05.st` at a site no assumption selects with `tcStWaitLd`
  continues at the next instruction.
* `Code.step_issueAt`: `step_issue` whose continuation lemma may use the thread's program
  counter and sub-step (the `tcStWaitLd` selection of `tcgen05.st` depends on the program
  counter).
* `holds_setRegs_live`: after a Tensor Memory load the facts of a table over the registers live
  after the load hold, from those live before it, when the table gives each destination its
  loaded value and every other register the value it had.
* `Code.step_tcLd`: a `tcgen05.ld` no assumption selects with `tcLdWait`, whose machine
  records the loaded values (or stops).
* `Code.step_tcStWait`, `Code.step_tcStStore` (with `fires_tcStTmpl_next`): the two sub-steps
  of a `tcgen05.st` an assumption selects with `tcStWaitLd`: the implicit wait stays at the
  instruction at sub-step 1; the store continues at the next instruction.
* `Code.step_tcLdLoad`, `Code.step_tcLdWait`: the two sub-steps of a `tcgen05.ld` an
  assumption selects with `tcLdWait`: the load stays at the instruction at sub-step 1 with the
  destinations written; the implicit wait continues at the next instruction. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.EventFrame

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

theorem fires_barArrive_next {t u : TState} {a b : Opnd} {al : Bool} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.barArrive a b al)) e (some u)) : u = PTX.next t := by
  simp only [eventTmpl, barTmpl] at hf
  repeat' split at hf
  all_goals simp_all [Fires]

theorem fires_tcWaitSt_next {t u : TState} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t .tcWaitSt) e (some u)) : u = PTX.next t := by
  have hm : CallbackFrame (· = PTX.next t) (eventTmpl A L g t .tcWaitSt) := by
    simp only [eventTmpl, tcTmpl]
    apply ofExec_frame
    repeat' first
      | rfl
      | exact True.intro
      | split
  exact callbackFrame_fires (P := (· = PTX.next t)) hm hf

theorem fires_tcSt_next {t u : TState} {ta : Nat} {ss : List Opnd} {sh : TcShape} {pc : Nat}
    {e : Event} (hw : A.any (·.tcStWaitLd t.pc) = false)
    (hf : Fires pc (eventTmpl A L g t (.tcSt ta ss sh)) e (some u)) : u = PTX.next t := by
  have hm : CallbackFrame (· = PTX.next t) (eventTmpl A L g t (.tcSt ta ss sh)) := by
    simp only [eventTmpl, tcStTmpl, hw, Bool.false_eq_true, ↓reduceIte]
    cases sh with
    | packed16 s =>
      simp only [tcTmpl]
      apply ofExec_frame
      repeat' first
        | rfl
        | exact True.intro
        | (apply allOk_bind; intro v)
        | split
    | _ =>
      simp only [tcTmpl]
      apply ofExec_frame
      repeat' first
        | rfl
        | exact True.intro
        | (apply allOk_bind; intro v)
        | split
  exact callbackFrame_fires (P := (· = PTX.next t)) hm hf

/-- The template of a `tcgen05.st` itself (after its implicit wait, when an assumption selects
`tcStWaitLd`): the store continues at the next instruction. -/
theorem fires_tcStTmpl_next {t u : TState} {ta : Nat} {ss : List Opnd} {sh : TcShape}
    {pc : Nat} {e : Event} (hf : Fires pc (tcTmpl L g t (.tcSt ta ss sh)) e (some u)) :
    u = PTX.next t := by
  have hm : CallbackFrame (· = PTX.next t) (tcTmpl L g t (.tcSt ta ss sh)) := by
    cases sh with
    | packed16 s =>
      simp only [tcTmpl]
      apply ofExec_frame
      repeat' first
        | rfl
        | exact True.intro
        | (apply allOk_bind; intro v)
        | split
    | _ =>
      simp only [tcTmpl]
      apply ofExec_frame
      repeat' first
        | rfl
        | exact True.intro
        | (apply allOk_bind; intro v)
        | split
  exact callbackFrame_fires (P := (· = PTX.next t)) hm hf

/-- The facts of a table over the registers `live'` live after a load into `ds`, from those
over `live` before it: each destination holds its loaded value in the table `val'`, and every
other register of `live'` is in `live` with the same value in both tables. -/
theorem holds_setRegs_live {t : TState} {ds live live' : List Nat} {vals : List Value}
    {val val' : Nat → Value} (hF : Holds t.regs (factsFrom live val)) (hnd : ds.Nodup)
    (hlen : vals.length = ds.length)
    (hds : ∀ p < ds.length, val' (ds.getD p 0) = vals.getD p (b32 0))
    (hother : ∀ r ∈ live', r ∉ ds → r ∈ live ∧ val' r = val r) :
    Holds (setRegs t ds vals).regs (factsFrom live' val') := by
  refine holds_of_pointwise fun r hr => ?_
  by_cases hd : r ∈ ds
  · obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hd
    have hpx : p < vals.length := by omega
    have hv := hds p hp
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some] at hv
    rw [hv]
    exact setRegs_get ds _ t p _ _ hnd (List.getElem?_eq_getElem hp)
      (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpx])
  · obtain ⟨hl, hv⟩ := hother r hr hd
    rw [setRegs_other t ds vals r hd, hv]
    exact holds_mem hF (mem_factsFrom hl)

/-- After a write of the registers `ds`, the facts of a table over `live'` hold when no register
of `live'` is written and each is in `live` with the same value in both tables
(`holds_setRegs_live` without destinations: a Tensor Memory load into data registers that the
table does not name). -/
theorem holds_setRegs_frame {t : TState} {ds live live' : List Nat} {vals : List Value}
    {val val' : Nat → Value} (hF : Holds t.regs (factsFrom live val))
    (hother : ∀ r ∈ live', r ∉ ds ∧ r ∈ live ∧ val' r = val r) :
    Holds (setRegs t ds vals).regs (factsFrom live' val') := by
  refine holds_of_pointwise fun r hr => ?_
  obtain ⟨hd, hl, hv⟩ := hother r hr
  rw [setRegs_other t ds vals r hd, hv]
  exact holds_mem hF (mem_factsFrom hl)

namespace Code

variable {K : Kernel} {C : Code K A L g}

/-- `step_issue` with a continuation lemma that reads the thread's program counter and
sub-step. -/
theorem step_issueAt {d dn : C.D} {ins0 : Instr} (hc0 : K.code[C.pc d]? = some ins0)
    (hadv : ∀ {t e u}, t.pc = C.pc d → Fires (C.pc d) (eventTmpl A L g t ins0.op) e (some u) →
      u = PTX.next t)
    (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0) (ha : C.acc d = [])
    (hl : C.Lands d (C.pc d + 1) (C.facts d) dn) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain rfl := hadv h.1 hf
  exact hl.cont hi (hn e) (At.next (at_of_atD h hs ha))

/-- A `tcgen05.ld` (no `.pack::16b`, no reduction) at a site no assumption selects with
`tcLdWait`: the machine's successor is a function `nv` of the loaded values; each successor is
reached from the next instruction with the facts `F' vals`, which the load establishes. -/
theorem step_tcLd {d : C.D} {nv : List Value → Option (Option C.D)} {gd : Option (Nat × Bool)}
    {ds : List Nat} {ta : Nat} {sh : TcShape} {F' : List Value → List (Nat × Value)}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .tcLd ds ta sh none⟩) (hsh : ∀ s, sh ≠ .packed16 s)
    (hw : A.any (·.tcLdWait (C.pc d)) = false)
    (hn : ∀ a vals, C.next d ⟨C.pc d, .tc (.ld a vals sh)⟩ = nv vals)
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hF : ∀ (t : TState) vals d', nv vals = some (some d') → vals.length = ds.length →
      Holds t.regs (C.facts d) → Holds (setRegs t ds vals).regs (F' vals))
    (hnn : ∀ vals, nv vals ≠ none)
    (hl : ∀ vals d', nv vals = some (some d') → C.Lands d (C.pc d + 1) (F' vals) d') :
    C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨a, vals, hlen, rfl, rfl⟩ := fires_tcLd hsh hf (by rw [h.1]; exact hw)
  have hnv := hn a vals
  rcases hv : nv vals with _ | _ | d'
  · exact absurd hv (hnn vals)
  · exact .inl (.inl (hnv.trans hv))
  · have hR := hF t vals d' hv hlen h0.2.2.2.2
    have hsk := setRegs_skel (PTX.next t) ds vals
    have hreg := setRegs_next_regs t ds vals
    refine (hl vals d' hv).cont hi (hnv.trans hv) ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hsk.1]; simp [PTX.next, h0.1]
    · rw [hsk.2.1]; exact h0.2.1
    · rw [hsk.2.2.1]; exact h0.2.2.1
    · rw [hsk.2.2.2]; exact h0.2.2.2.1
    · rw [hreg]; exact hR

/-- The load of a `tcgen05.ld` an assumption selects with `tcLdWait` (sub-step 0): the machine
moves to `nv vals`, a state at the same instruction at sub-step 1 whose facts the load
establishes. -/
theorem step_tcLdLoad {d : C.D} {nv : List Value → Option (Option C.D)}
    {gd : Option (Nat × Bool)} {ds : List Nat} {ta : Nat} {sh : TcShape} {a0 : Nat}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .tcLd ds ta sh none⟩) (hsh : ∀ s, sh ≠ .packed16 s)
    (hw : A.any (·.tcLdWait (C.pc d)) = true)
    (hta : (ta, b32 a0) ∈ C.facts d) (ha0 : a0 < 2 ^ 32)
    (hn : ∀ a vals, C.next d ⟨C.pc d, .tc (.ld a vals sh)⟩ = nv vals)
    (hs : C.sub d = 0) (ha : C.acc d = []) (hnn : ∀ vals, nv vals ≠ none)
    (hd' : ∀ vals d', nv vals = some (some d') →
      C.pc d' = C.pc d ∧ C.sub d' = 1 ∧ C.acc d' = [] ∧ (C.inv d → C.inv d') ∧
      (vals.length = ds.length → ∀ t : TState, Holds t.regs (C.facts d) →
        Holds (setRegs t ds vals).regs (C.facts d'))) :
    C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨vals, hlen, rfl, rfl⟩ :=
    fires_tcLd_load hsh (by rw [h.1]; exact hw) h0.2.1 (holds_mem h0.2.2.2.2 hta) ha0 hf
  have hnv := hn a0 vals
  rcases hv : nv vals with _ | _ | d'
  · exact absurd hv (hnn vals)
  · exact .inl (.inl (hnv.trans hv))
  · obtain ⟨hpc, hsub, hacc, hinv, hF⟩ := hd' vals d' hv
    have hsk := setRegs_skel (PTX.next t) ds vals
    have hreg := setRegs_next_regs t ds vals
    refine .inl (.inr ⟨d', _, hnv.trans hv, .refl, ⟨?_, ?_, ?_, ?_, ?_⟩, hinv hi⟩)
    · show t.pc = C.pc d'
      rw [hpc, h0.1]
    · show 1 = C.sub d'
      rw [hsub]
    · show (setRegs (PTX.next t) ds vals).acc = C.acc d'
      rw [hsk.2.2.1, hacc]; exact h0.2.2.1
    · show (setRegs (PTX.next t) ds vals).fault = none
      rw [hsk.2.2.2]; exact h0.2.2.2.1
    · show Holds (setRegs (PTX.next t) ds vals).regs (C.facts d')
      rw [hreg]; exact hF hlen t h0.2.2.2.2

/-- The implicit wait of a `tcgen05.ld` an assumption selects with `tcLdWait` (sub-step 1):
the thread continues at the next instruction with the facts of the wait's state. -/
theorem step_tcLdWait {d dn : C.D} {gd : Option (Nat × Bool)} {ds : List Nat} {ta : Nat}
    {sh : TcShape} (hc0 : K.code[C.pc d]? = some ⟨gd, .tcLd ds ta sh none⟩)
    (hw : A.any (·.tcLdWait (C.pc d)) = true)
    (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 1) (ha : C.acc d = [])
    (hl : C.Lands d (C.pc d + 1) (C.facts d) dn) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨rfl, rfl⟩ := fires_tcLd_wait (by rw [h.1]; exact hw) (by rw [h.2.1, hs]; decide) hf
  refine hl.cont hi (hn _) ⟨by simp [PTX.next, h.1], rfl, h.2.2.1.trans ha, h.2.2.2.1, ?_⟩
  exact h.2.2.2.2

/-- The implicit wait of a `tcgen05.st` that an assumption selects with `tcStWaitLd`, at
sub-step 0: the thread waits for its Tensor Memory loads and stays at the instruction, at
sub-step 1, with the same facts (the state `dn`). A launch whose block is not a whole number of
warps faults there; the machine owes nothing for it. -/
theorem step_tcStWait {d dn : C.D} {gd : Option (Nat × Bool)} {ta : Nat} {ss : List Opnd}
    {sh : TcShape} (hc0 : K.code[C.pc d]? = some ⟨gd, .tcSt ta ss sh⟩)
    (hw : A.any (·.tcStWaitLd (C.pc d)) = true) (hs : C.sub d = 0)
    (hn : ∀ e, C.next d e = some (some dn)) (hpc : C.pc dn = C.pc d) (hs' : C.sub dn = 1)
    (ha : C.acc dn = C.acc d) (hF : C.facts dn = C.facts d) (hinv : C.inv d → C.inv dn) :
    C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have hw' : A.any (·.tcStWaitLd t.pc) = true := by rw [h.1]; exact hw
  have ht : t.sub = 0 := h.2.1.trans hs
  simp only [eventTmpl, tcStTmpl, hw', ht, ↓reduceIte] at hf
  split at hf
  · obtain ⟨-, hu⟩ := hf
    cases hu
    refine .inl (.inr ⟨dn, _, hn e, .refl, ⟨?_, ?_, ?_, h.2.2.2.1, ?_⟩, hinv hi⟩)
    · exact h.1.trans hpc.symm
    · exact hs'.symm
    · exact h.2.2.1.trans ha.symm
    · rw [hF]; exact h.2.2.2.2
  · exact absurd hf.2 (by simp)

/-- The store of a `tcgen05.st` that an assumption selects with `tcStWaitLd`, at sub-step 1
after its wait: the thread continues at the next instruction with the same facts. -/
theorem step_tcStStore {d dn : C.D} {gd : Option (Nat × Bool)} {ta : Nat} {ss : List Opnd}
    {sh : TcShape} (hc0 : K.code[C.pc d]? = some ⟨gd, .tcSt ta ss sh⟩)
    (hw : A.any (·.tcStWaitLd (C.pc d)) = true) (hs : C.sub d = 1) (ha : C.acc d = [])
    (hn : ∀ e, C.next d e = some (some dn)) (hl : C.Lands d (C.pc d + 1) (C.facts d) dn) :
    C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have hw' : A.any (·.tcStWaitLd t.pc) = true := by rw [h.1]; exact hw
  have ht : t.sub = 1 := h.2.1.trans hs
  simp only [eventTmpl, tcStTmpl, hw', ht, ↓reduceIte, Nat.one_ne_zero] at hf
  obtain rfl := fires_tcStTmpl_next hf
  exact hl.cont hi (hn e) (At.next ⟨h.1, rfl, h.2.2.1.trans ha, h.2.2.2.1, h.2.2.2.2⟩)

end Code

end

/-- `advances` also passes `bar.arrive` with a count and `tcgen05.wait::st`. -/
macro_rules | `(tactic| advances) => `(tactic| exact fun hf => PTX.Flow.fires_barArrive_next hf)
macro_rules | `(tactic| advances) => `(tactic| exact fun hf => PTX.Flow.fires_tcWaitSt_next hf)

end PTX.Flow
