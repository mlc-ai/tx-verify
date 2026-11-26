-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepForQ
public import Lemmas.Flow.SegQOps
public import Lemmas.Flow.NcLoadVecU
public import Lemmas.Flow.ShflU
public import Lemmas.Flow.WaitU
public import Lemmas.Flow.StoreU
public import Lemmas.Flow.AdvanceU

@[expose] public section

/-! # Strict one-step lemmas under a tag invariant

The strict counterparts (`Code.StepForQ`) of the UB-tolerant combinators of a control machine
(`Code.waitU`, `Code.ldvNcU`, `Code.shflAnyU`, `Code.scalarStoreU`, `Code.vstU`, `Code.advanceU`)
for the invariant `QT qt`. The event's payloads are well formed (`Wf`): a rebuilt `.nc` payload
and a shuffle's word are 32-bit bit patterns, so the registers they write have the tags `qt` asks
of them. `afterWrites` is the bulk check of the tags after a step: the tags at `pc + 1` are those
of the written registers, or were there before. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- The tags at `pc + 1` are those of the registers the step writes (`ws`), or already held at
`pc`, or among those `ex` that the state's facts give (a divisor known nonzero). -/
def afterWrites (qt : Nat → Env) (pc : Nat) (ws : List (Nat × Tag)) (ex : Env := []) : Bool :=
  (qt (pc + 1)).all fun p => match ws.lookup p.1 with
    | some tg => p.2 == tg
    | none => (qt pc).lookup p.1 == some p.2 || ex.lookup p.1 == some p.2

theorem QT.after {qt : Nat → Env} {t u : TState} {pc : Nat} {ws : List (Nat × Tag)}
    {ex : Env} (ht : QT qt t) (hex : Typed ex t) (hpc : t.pc = pc) (hu : u.pc = pc + 1)
    (hw : ∀ r tg, ws.lookup r = some tg → tg.ok (u.regs r))
    (hf : ∀ r, ws.lookup r = none → u.regs r = t.regs r) (h : afterWrites qt pc ws ex = true) :
    QT qt u := by
  intro r tg hr
  rw [hu] at hr
  simp only [afterWrites, List.all_eq_true] at h
  have h1 := h _ (lookup_mem hr)
  have ht' : Typed (qt pc) t := by simpa [QT, hpc] using ht
  cases hl : ws.lookup r with
  | some tg' =>
    simp only [hl, beq_iff_eq] at h1
    subst h1
    exact hw r _ hl
  | none =>
    simp only [hl, Bool.or_eq_true, beq_iff_eq] at h1
    rw [hf r hl]
    rcases h1 with h1 | h1
    · exact ht' r tg h1
    · exact hex r tg h1

theorem QT.same {qt : Nat → Env} {t u : TState} (ht : QT qt t) (hpc : u.pc = t.pc)
    (hr : u.regs = t.regs) : QT qt u := by
  intro r tg h
  rw [hpc] at h
  rw [hr]
  exact ht r tg h

/-- A state reached by a segment from the state after an event is strictly good. -/
theorem landQ {Q : TState → Prop} {d : C.D} {u : TState} {a : Nat} {F : List (Nat × Value)}
    (hu : At u a F) (hq : Q u) (hl : SegQ K A L g Q a F (C.pc d) (C.facts d)) (hi : C.inv d)
    (hs : C.sub d = 0) (ha : C.acc d = []) :
    ∃ t', Relation.ReflTransGen (Tau K A L g) u t' ∧ C.Good (some d) t' ∧ Q t' := by
  obtain ⟨s, hr, hA, hQ⟩ := hl u hu hq
  exact ⟨s, hr, ⟨⟨hA.1, hA.2.1.trans hs.symm, hA.2.2.1.trans ha.symm, hA.2.2.2.1, hA.2.2.2.2⟩,
    hi⟩, hQ⟩

theorem lookup2_none {r r0 r1 : Nat} {a b : Tag} (h : [(r0, a), (r1, b)].lookup r = none) :
    ¬ r = r0 ∧ ¬ r = r1 := by
  constructor
  · intro h'; subst h'; simp [List.lookup] at h
  · intro h'; subst h'; by_cases h0 : r == r0 <;> simp [List.lookup, h0] at h

/-- **A poll under the tag invariant**: the wait writes the predicate `r`. -/
theorem waitQ {qt : Nat → Env} {ex : Env} {Wf : Event → Prop} {d : C.D} {dst : Bool → C.D}
    {r base : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope}
    (hc : K.code[C.pc d]? = some ⟨none, .mbarWait r base off par acq sc⟩)
    (hoff : r ∉ (C.facts d).map Prod.fst)
    (hn : ∀ m q ok s, C.next d ⟨C.pc d, .wait m q ok acq s⟩ = some (some (dst ok)))
    (hs : C.sub d = 0) (ha : C.acc d = []) (hs' : ∀ ok, C.sub (dst ok) = 0)
    (ha' : ∀ ok, C.acc (dst ok) = []) (hi : ∀ ok, C.inv (dst ok))
    (hex : ∀ t, C.AtD d t → Typed ex t)
    (hq : afterWrites qt (C.pc d) [(r, .pred)] ex = true)
    (seg : ∀ ok, SegQ K A L g (QT qt) (C.pc d + 1) ((r, .pred ok) :: C.facts d)
      (C.pc (dst ok)) (C.facts (dst ok))) (e : Event) : C.StepForQ (QT qt) Wf d e := by
  intro t u ins h _ hins hQ _ hf
  have hexT := hex t h
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  rw [← h.1] at hf
  obtain ⟨m, q, ok, s, rfl, rfl⟩ := fires_wait hf
  rw [h.1]
  have ht := At.set (r := r) (v := .pred ok) (at_of_atD h hs ha)
    (fun q hq he => hoff (he ▸ List.mem_map_of_mem hq))
  have hQ' : QT qt (PTX.next (setReg t r (.pred ok))) :=
    QT.after hQ hexT h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1]) (fun r' tg hl => by
      by_cases hr : r' = r
      · subst hr
        simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
        subst hl
        exact ⟨ok, by simp [PTX.next, setReg]⟩
      · have : (r' == r) = false := by simpa using hr
        simp [List.lookup, this] at hl)
      (fun r' hl => by
        have : ¬ r' = r := fun h' => by simp [List.lookup, h'] at hl
        simp [PTX.next, setReg, Function.update_of_ne this]) hq
  obtain ⟨t', hr, hg, hq'⟩ := landQ ht hQ' (seg ok) (hi ok) (hs' ok) (ha' ok)
  exact .inl ⟨dst ok, t', hn m q ok s, hr, hg, hq'⟩

/-- **An element of a pair of `.nc` loads** into registers `r0 r1` the facts do not name; the
payload is a 32-bit word (`hW`), as is the first element (`hbits`). -/
theorem ldvNcQ {qt : Nat → Env} {ex : Env} {Wf : Event → Prop} {d : C.D}
    {dok : Value → C.D} {a : MemAccess}
    {live : List Nat} {val : Nat → Value} {base w r0 r1 : Nat} {sp : Space}
    (hc0 : K.code[C.pc d]? = some ⟨none, .mem a⟩) (_hl : (Op.mem a).isLocal = false)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hregs : a.regs = [r0, r1])
    (hW : ∀ e, Wf e → ∀ x bs, e.kind = .nc x bs → ∃ y, rebuild 3 bs = .ok (.bits 32 y))
    (hlast : ¬ C.sub d + 1 < 2 → ∃ y0, C.acc d = [.bits 32 y0])
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .nc x bs⟩ = some (some (dok v)))
    (mid : C.sub d + 1 < 2 → ∀ v, C.pc (dok v) = C.pc d ∧
      C.sub (dok v) = C.sub d + 1 ∧ C.acc (dok v) = C.acc d ++ [v] ∧
      C.facts (dok v) = C.facts d ∧ C.inv (dok v))
    (hF : C.facts d = factsFrom live val) (hoff : ∀ r ∈ live, r ∉ a.regs)
    (hex : ∀ t, C.AtD d t → Typed ex t)
    (hq : afterWrites qt (C.pc d) [(r0, .bits 32), (r1, .bits 32)] ex = true)
    (last : ¬ C.sub d + 1 < 2 → ∀ v, C.sub (dok v) = 0 ∧ C.acc (dok v) = [] ∧
      C.inv (dok v) ∧ SegQ K A L g (QT qt) (C.pc d + 1) (C.facts d) (C.pc (dok v))
        (C.facts (dok v))) (e : Event) : C.StepForQ (QT qt) Wf d e := by
  intro t u ins h hi hc hQ hWe hf
  have hexT := hex t h
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_loadNc hru hloc hb hk hsem hnc hf
  obtain ⟨hP, hS0, hA, hFl, hR⟩ := h
  obtain ⟨y, hy⟩ := hW _ hWe x bs rfl
  have hlen : a.regs.length = 2 := by rw [hregs]; rfl
  by_cases hm : C.sub d + 1 < 2
  · obtain ⟨hpc, hs, ha, hF', hinv⟩ := mid hm (.bits 32 y)
    have hm' : t.sub + 1 < a.regs.length := by rw [hS0, hlen]; exact hm
    have hu : afterLoad t a.regs bs =
        { t with sub := t.sub + 1, acc := t.acc ++ [.bits 32 y] } := by
      simp [afterLoad, hy, hm']
    rw [hu]
    refine .inl ⟨dok (.bits 32 y), _, hok x bs _ hy, .refl, ⟨⟨?_, ?_, ?_, hFl, ?_⟩, hinv⟩,
      QT.same hQ rfl rfl⟩
    · exact hP.trans hpc.symm
    · show t.sub + 1 = C.sub (dok _)
      rw [hS0, hs]
    · show t.acc ++ [_] = C.acc (dok _)
      rw [hA, ha]
    · rw [hF']; exact hR
  · obtain ⟨hs0, ha0, hinv, seg⟩ := last hm (.bits 32 y)
    obtain ⟨y0, h0⟩ := hlast hm
    have hm' : ¬ t.sub + 1 < a.regs.length := by rw [hS0, hlen]; exact hm
    have hacc : t.acc = [.bits 32 y0] := hA.trans h0
    obtain ⟨u0, hu0⟩ : ∃ u0, u0 = afterLoad t a.regs bs := ⟨_, rfl⟩
    have hu : u0 = { setRegs t [r0, r1] [.bits 32 y0, .bits 32 y] with
        pc := t.pc + 1, sub := 0, acc := [] } := by
      have hm2 : ¬ t.sub = 0 := by omega
      rw [hu0]; simp [afterLoad, hy, hm2, hacc, hregs]
    obtain ⟨-, -, -, hskF⟩ := setRegs_skel t [r0, r1] [.bits 32 y0, .bits 32 y]
    have hAt : At u0 (C.pc d + 1) (C.facts d) := by
      have hreg := hR
      rw [hF] at hreg
      have hoff' : ∀ r ∈ live, r ∉ [r0, r1] := by rw [← hregs]; exact hoff
      rw [hu]
      refine ⟨by show t.pc + 1 = _; rw [hP], rfl, rfl, ?_, ?_⟩
      · show (setRegs t [r0, r1] [.bits 32 y0, .bits 32 y]).fault = none
        rw [hskF]; exact hFl
      · rw [hF]
        exact holds_setRegs_frame hreg (fun r hr => ⟨hoff' r hr, hr, rfl⟩)
    have hQ' : QT qt u0 := by
      rw [hu]
      refine QT.after hQ hexT hP (by simp [hP]) (fun r tg hl => ?_) (fun r hl => ?_) hq
      · by_cases h1 : r = r1
        · subst h1
          by_cases e0 : (r == r0) = true <;> simp [List.lookup, e0] at hl <;> subst hl <;>
            exact ⟨y, by simp [setRegs, setReg]⟩
        · by_cases h0 : r = r0
          · subst h0
            simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
            subst hl
            exact ⟨y0, by simp [setRegs, setReg, Function.update_of_ne h1]⟩
          · have e1 : (r == r0) = false := by simpa using h0
            have e2 : (r == r1) = false := by simpa using h1
            simp [List.lookup, e1, e2] at hl
      · obtain ⟨h0, h1⟩ := lookup2_none hl
        simp [setRegs, setReg, Function.update_of_ne h1, Function.update_of_ne h0]
    obtain ⟨t', hr, hg, hq'⟩ := landQ hAt hQ' seg hinv hs0 ha0
    rw [← hu0]
    exact .inl ⟨dok (.bits 32 y), t', hok x bs _ hy, hr, hg, hq'⟩

/-- **A data shuffle under the tag invariant**: the received word is 32 bits (`hW`); it goes
into `r`, the validity into `p`. -/
theorem shflAnyQ {qt : Nat → Env} {ex : Env} {Wf : Event → Prop} {d dn : C.D} {mode : ShflMode}
    {ty : Option DType} {r p : Nat} {a b c mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨none, .warp ⟨.shfl mode, ty, [some r, some p], [a, b, c],
      some mask⟩⟩)
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r) (hp : ∀ q ∈ C.facts d, q.1 ≠ p) (hrp : r ≠ p)
    (hW : ∀ e, Wf e → ∀ m av bv cv recv ok, e.kind = .shfl m av bv cv recv ok →
      ∃ y, recv = .bits 32 y)
    (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0) (ha : C.acc d = [])
    (hs' : C.sub dn = 0) (ha' : C.acc dn = []) (hi : C.inv dn)
    (hex : ∀ t, C.AtD d t → Typed ex t)
    (hq : afterWrites qt (C.pc d) [(r, .bits 32), (p, .pred)] ex = true)
    (seg : ∀ recv ok, SegQ K A L g (QT qt) (C.pc d + 1)
      ((p, .pred ok) :: (r, recv) :: C.facts d) (C.pc dn) (C.facts dn)) (e : Event) :
    C.StepForQ (QT qt) Wf d e := by
  intro t u ins h _ hc hQ hWe hf
  have hexT := hex t h
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := some p) hf
  obtain ⟨y, rfl⟩ := hW _ hWe _ av bv cv recv ok rfl
  have hat1 : At (setReg t r (.bits 32 y)) (C.pc d) ((r, .bits 32 y) :: C.facts d) :=
    ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, Function.update_self .., holds_update h0.2.2.2.2 hr⟩
  have hp' : ∀ q ∈ (r, Value.bits 32 y) :: C.facts d, q.1 ≠ p := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hrp
    · exact hp q hq
  have hu := At.set (v := .pred ok) hat1 hp'
  have hQ' : QT qt (PTX.next (setReg (setReg t r (.bits 32 y)) p (.pred ok))) := by
    refine QT.after hQ hexT h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1]) (fun r' tg hl => ?_)
      (fun r' hl => ?_) hq
    · by_cases h1 : r' = p
      · subst h1
        have e0 : (r' == r) = false := beq_eq_false_iff_ne.mpr (Ne.symm hrp)
        simp [List.lookup, e0] at hl
        subst hl
        exact ⟨ok, by simp [PTX.next, setReg]⟩
      · by_cases h0 : r' = r
        · subst h0
          simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
          subst hl
          exact ⟨y, by simp [PTX.next, setReg, Function.update_of_ne h1]⟩
        · have e1 : (r' == r) = false := by simpa using h0
          have e2 : (r' == p) = false := by simpa using h1
          simp [List.lookup, e1, e2] at hl
    · obtain ⟨h0, h1⟩ := lookup2_none hl
      simp [PTX.next, setReg, Function.update_of_ne h0, Function.update_of_ne h1]
  obtain ⟨t', hr', hg, hq'⟩ := landQ hu hQ' (seg _ ok) hi hs' ha'
  exact .inl ⟨dn, t', hn _, hr', hg, hq'⟩

/-- **A continuing event under the tag invariant**: it advances to the next instruction and
writes nothing (an arrival, a fence), then goes on by a segment. -/
theorem advanceQ {qt : Nat → Env} {ex : Env} {Wf : Event → Prop} {d dn : C.D} {op : Op}
    (hc : K.code[C.pc d]? = some ⟨none, op⟩)
    (ha : ∀ {t u e}, Fires (C.pc d) (eventTmpl A L g t op) e (some u) → u = PTX.next t)
    (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0) (hacc : C.acc d = [])
    (hs' : C.sub dn = 0) (hacc' : C.acc dn = []) (hi : C.inv dn)
    (hex : ∀ t, C.AtD d t → Typed ex t)
    (hq : afterWrites qt (C.pc d) [] ex = true)
    (seg : SegQ K A L g (QT qt) (C.pc d + 1) (C.facts d) (C.pc dn) (C.facts dn)) (e : Event) :
    C.StepForQ (QT qt) Wf d e := by
  intro t u ins h _ hins hQ _ hf
  have hexT := hex t h
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  obtain rfl := ha hf
  have hQ' : QT qt (PTX.next t) :=
    QT.after hQ hexT h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1]) (fun r tg hl => by simp at hl)
      (fun r _ => rfl) hq
  obtain ⟨t', hr, hg, hq'⟩ := landQ (At.next (at_of_atD h hs hacc)) hQ' seg hi hs' hacc'
  exact .inl ⟨dn, t', hn e, hr, hg, hq'⟩

/-- **A scalar store under the tag invariant**. -/
theorem scalarStoreQ {qt : Nat → Env} {ex : Env} {Wf : Event → Prop} {d dn : C.D} {a : MemAccess}
    (hc : K.code[C.pc d]? = some ⟨none, .mem a⟩) (hst : a.kind = .store)
    (hlen : a.srcs.length = 1) (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0)
    (ha : C.acc d = []) (hs' : C.sub dn = 0) (ha' : C.acc dn = []) (hi : C.inv dn)
    (hex : ∀ t, C.AtD d t → Typed ex t)
    (hq : afterWrites qt (C.pc d) [] ex = true)
    (seg : SegQ K A L g (QT qt) (C.pc d + 1) (C.facts d) (C.pc dn) (C.facts dn)) (e : Event) :
    C.StepForQ (QT qt) Wf d e := by
  intro t u ins h _ hins hQ _ hf
  have hexT := hex t h
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  obtain ⟨_, _, rfl, rfl⟩ := fires_st hst hf
  rw [afterStore_last (by rw [h.2.1, hs, hlen]; decide)]
  have hQ' : QT qt { t with pc := t.pc + 1, sub := 0 } :=
    QT.after hQ hexT h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1]) (fun r tg hl => by simp at hl)
      (fun r _ => rfl) hq
  obtain ⟨t', hr, hg, hq'⟩ := landQ (u := {t with pc := t.pc + 1, sub := 0})
    ⟨congrArg (· + 1) h.1, rfl, h.2.2.1.trans ha, h.2.2.2.1, h.2.2.2.2⟩ hQ' seg hi hs' ha'
  exact .inl ⟨dn, t', hn _, hr, hg, hq'⟩

/-- **An element of a vector store under the tag invariant** (two elements): before the last the
machine counts it at the same instruction, at the last it continues by a segment. -/
theorem vstQ {qt : Nat → Env} {ex : Env} {Wf : Event → Prop} {d dn : C.D} {a : MemAccess}
    (hc : K.code[C.pc d]? = some ⟨none, .mem a⟩) (hst : a.kind = .store)
    (hn : ∀ e, C.next d e = some (some dn)) (hacc : C.acc d = [])
    (mid : C.sub d + 1 < a.srcs.length → C.pc dn = C.pc d ∧ C.sub dn = C.sub d + 1 ∧
      C.acc dn = [] ∧ C.facts dn = C.facts d ∧ C.inv dn)
    (hex : ∀ t, C.AtD d t → Typed ex t)
    (hq : afterWrites qt (C.pc d) [] ex = true)
    (last : ¬ C.sub d + 1 < a.srcs.length → C.sub dn = 0 ∧ C.acc dn = [] ∧ C.inv dn ∧
      SegQ K A L g (QT qt) (C.pc d + 1) (C.facts d) (C.pc dn) (C.facts dn)) (e : Event) :
    C.StepForQ (QT qt) Wf d e := by
  intro t u ins h _ hins hQ _ hf
  have hexT := hex t h
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  obtain ⟨_, _, rfl, rfl⟩ := fires_st hst hf
  obtain ⟨hP, hS0, hA, hFl, hR⟩ := h
  by_cases hm : C.sub d + 1 < a.srcs.length
  · obtain ⟨hpc, hs, ha, hF, hinv⟩ := mid hm
    rw [afterStore_mid (by rw [hS0]; exact hm)]
    refine .inl ⟨dn, _, hn _, .refl, ⟨⟨hP.trans hpc.symm, ?_, hA.trans (hacc.trans ha.symm), hFl,
      hF ▸ hR⟩, hinv⟩, QT.same hQ rfl rfl⟩
    show t.sub + 1 = C.sub dn
    rw [hS0, hs]
  · obtain ⟨hs0, ha0, hinv, seg⟩ := last hm
    rw [afterStore_last (by rw [hS0]; exact hm)]
    have hQ' : QT qt { t with pc := t.pc + 1, sub := 0 } :=
      QT.after hQ hexT hP (by show t.pc + 1 = C.pc d + 1; rw [hP]) (fun r tg hl => by simp at hl)
        (fun r _ => rfl) hq
    obtain ⟨t', hr, hg, hq'⟩ := landQ (u := { t with pc := t.pc + 1, sub := 0 })
      ⟨congrArg (· + 1) hP, rfl, hA.trans hacc, hFl, hR⟩ hQ' seg hinv hs0 ha0
    exact .inl ⟨dn, t', hn _, hr, hg, hq'⟩

end PTX.Flow.Code
