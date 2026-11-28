-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQFB
public import Lemmas.Flow.StepForQPcP

@[expose] public section

/-! # Strict one-step lemmas that use a fact of the state after the event

The twins of `advanceF` (for an instruction with a guard), `shflF` and `ldWF` for the step
obligation `StepForQP (QTF qt) P`: the segment after the event may use `P` of the state the
event reaches, as the typed windows with single pieces do (`TauAll R`,
`Lemmas/Flow/TypedSingleG.lean`). -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged PTX.Flow.TyG

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- A continuing event of a possibly guarded instruction that writes nothing. -/
theorem advanceFP {qt : Nat → EnvF} {Wf : Event → Prop} {P : TState → Prop} {d dn : C.D}
    {op : Op} {gd : Option (Nat × Bool)} (hc : K.code[C.pc d]? = some ⟨gd, op⟩)
    (ha : ∀ {t u e}, Fires (C.pc d) (eventTmpl A L g t op) e (some u) → u = PTX.next t)
    (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0) (hacc : C.acc d = [])
    (hs' : C.sub dn = 0) (hacc' : C.acc dn = []) (hi : C.inv dn)
    (hq : afterF qt (C.pc d) [] = true)
    (seg : SegQ K A L g (fun t => QTF qt t ∧ P t) (C.pc d + 1) (C.facts d) (C.pc dn)
      (C.facts dn)) (e : Event) : C.StepForQP (QTF qt) P Wf d e := by
  intro t u ins h _ hins hQ _ hf hPu
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  obtain rfl := ha hf
  have hQ' : QTF qt (PTX.next t) :=
    QTF.after1 hQ h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1]) (fun r _ => rfl)
      (fun p hp => by simp at hp) hq
  obtain ⟨t', hr, hg, hq'⟩ := landQ (Q := fun t => QTF qt t ∧ P t)
    (At.next (at_of_atD h hs hacc)) ⟨hQ', hPu⟩ seg hi hs' hacc'
  exact .inl ⟨dn, t', hn e, hr, hg, hq'.1⟩

/-- A data shuffle: the received word has the tag `tr` (`hW`); it goes into `r`, the validity
into `p`. -/
theorem shflFP {qt : Nat → EnvF} {Wf : Event → Prop} {P : TState → Prop} {d dn : C.D}
    {mode : ShflMode} {ty : Option DType} {r p : Nat} {a b c mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨none, .warp ⟨.shfl mode, ty, [some r, some p], [a, b, c],
      some mask⟩⟩)
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r) (hp : ∀ q ∈ C.facts d, q.1 ≠ p) (hrp : r ≠ p)
    {tr : TagF} (hW : ∀ e, Wf e → ∀ m av bv cv recv ok, e.kind = .shfl m av bv cv recv ok →
      tr.ok (some recv))
    (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0) (ha : C.acc d = [])
    (hs' : C.sub dn = 0) (ha' : C.acc dn = []) (hi : C.inv dn)
    (hq : afterF qt (C.pc d) [(r, tr), (p, .old .pred)] = true)
    (seg : ∀ recv ok, SegQ K A L g (fun t => QTF qt t ∧ P t) (C.pc d + 1)
      ((p, .pred ok) :: (r, recv) :: C.facts d) (C.pc dn) (C.facts dn)) (e : Event) :
    C.StepForQP (QTF qt) P Wf d e := by
  intro t u ins h _ hc hQ hWe hf hPu
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := some p) hf
  have hy := hW _ hWe _ av bv cv recv ok rfl
  have hat1 : At (setReg t r recv) (C.pc d) ((r, recv) :: C.facts d) :=
    ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, Function.update_self .., holds_update h0.2.2.2.2 hr⟩
  have hp' : ∀ q ∈ (r, recv) :: C.facts d, q.1 ≠ p := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hrp
    · exact hp q hq
  have hu := At.set (v := .pred ok) hat1 hp'
  have hQ' : QTF qt (PTX.next (setReg (setReg t r recv) p (.pred ok))) := by
    refine QTF.after1 hQ h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1]) (fun r' hl => ?_)
      (fun q hq' => ?_) hq
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hl
      simp [PTX.next, setReg, Function.update_of_ne hl.1, Function.update_of_ne hl.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · simpa [PTX.next, setReg, Function.update_of_ne hrp] using hy
      · exact ⟨ok, by simp [PTX.next, setReg]⟩
  obtain ⟨t', hr', hg, hq'⟩ := landQ (Q := fun t => QTF qt t ∧ P t) hu ⟨hQ', hPu⟩ (seg _ ok)
    hi hs' ha'
  exact .inl ⟨dn, t', hn _, hr', hg, hq'.1⟩

/-- A scalar weak load of a possibly guarded instruction: the event is of an executed
instruction, so the guard is not read. -/
theorem ldWFP {qt : Nat → EnvF} {Wf : Event → Prop} {P : TState → Prop} {Pv : Value → Prop}
    {d : C.D} {f : Value → C.D} {a : MemAccess} {r : Nat} {gd : Option (Nat × Bool)}
    (hc : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
    (hext : a.ext = .same) (hr : a.regs = [r])
    (hW : ∀ e, Wf e → e.pc = C.pc d → ∀ x bs, e.kind = .rd x bs →
      ∃ v, rebuild 3 bs = .ok v ∧ Pv v)
    (hn : ∀ x bs v, rebuild 3 bs = .ok v → Pv v →
      C.next d ⟨C.pc d, .rd x bs⟩ = some (some (f v)))
    (hs : C.sub d = 0) (ha : C.acc d = []) (hoff : ∀ p ∈ C.facts d, p.1 ≠ r)
    {tr : TagF} (hv : ∀ v, Pv v → tr.ok (some v))
    (hq : afterF qt (C.pc d) [(r, tr)] = true)
    (hok : ∀ v, Pv v → C.sub (f v) = 0 ∧ C.acc (f v) = [] ∧ C.inv (f v) ∧
      SegQ K A L g (fun t => QTF qt t ∧ P t) (C.pc d + 1) ((r, v) :: C.facts d) (C.pc (f v))
        (C.facts (f v))) (e : Event) : C.StepForQP (QTF qt) P Wf d e := by
  intro t u ins h _ hc' hQ hWe hf hPu
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf hext
  obtain ⟨v, hy, hPv⟩ := hW _ hWe (by rw [← h.1]) x bs rfl
  have ht := at_of_atD h hs ha
  rw [hr, afterLoad_ok ht.2.1 ht.2.2.1 hy] at hPu ⊢
  obtain ⟨hs', ha', hi, seg⟩ := hok v hPv
  obtain ⟨hP, hS0, hA, hFl, hR⟩ := ht
  have hu : At { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] }
      (C.pc d + 1) ((r, v) :: C.facts d) :=
    ⟨by show t.pc + 1 = _; rw [hP], rfl, rfl, hFl, Function.update_self ..,
      holds_update hR hoff⟩
  have hQ' : QTF qt { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] } :=
    QTF.after1 hQ hP (by show t.pc + 1 = C.pc d + 1; rw [hP]) (fun r' hl => by
      simp [setReg, Function.update_of_ne (by simpa using hl)])
      (fun q hq' => by
        simp only [List.mem_singleton] at hq'
        subst hq'
        simpa [setReg] using hv v hPv) hq
  obtain ⟨t', hr', hg, hq'⟩ := landQ (Q := fun t => QTF qt t ∧ P t) hu ⟨hQ', hPu⟩ seg hi hs' ha'
  exact .inl ⟨f v, t', hn x bs v hy hPv, hr', hg, hq'.1⟩

end PTX.Flow.Code
