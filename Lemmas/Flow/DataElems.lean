-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataLoad
public import Lemmas.Flow.OutLit

@[expose] public section

/-! # A value machine's data steps at vector loads and at events without data

Proof tools, generic over the kernel, beside `DataStep.load` (`Lemmas/Flow/DataLoad.lean`):

* `DataStep.loadE`: a load of several elements whose successors before the last element have
  data facts that the start state's facts give (the registers are written only by the last
  element; the state after an earlier element performs the next element's event);
* `DataStep.next`: an event that continues at `PTX.next t` (`fires_tcWaitLd_next`,
  `fires_tcFenceBefore_next` for `tcgen05.wait::ld` and `tcgen05.fence::before_thread_sync`);
* `holds_zip_lookupD`: facts on loaded registers restated by `lookupD`, with literal keys. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- A state with the start state's registers that performs an event is the only state local
steps reach from it. -/
theorem stays_regs {u t : TState} {G : List (Nat × Value)} (hs : Stops K A L g u)
    (hr : u.regs = t.regs) (hG : Holds t.regs G) :
    ∀ t', Relation.ReflTransGen (Tau K A L g) u t' → Stops K A L g t' → Holds t'.regs G := by
  intro t' h _
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hc, -⟩
  · rw [hr]; exact hG
  · exact absurd hc (not_tau_of_stops hs)

/-- **The data step of a load of several elements**: before the last element the successors'
facts follow from the state's; from the last one, as `DataStep.load` (a payload that does not
rebuild faults the thread). -/
theorem DataStep.loadE {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {a : MemAccess} {Q : Value → C'.D → Prop}
    (hc : K.code[C'.pc d]? = some ⟨none, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
    (he : a.ext = .same) (hl : (Op.mem a).isLocal = false)
    (hmid : C'.sub d + 1 < a.regs.length → ∀ e d', C'.next d e = some (some d') →
      ∀ R, Holds R (C'.facts d) → Holds R (dF d'))
    (hN : ¬ C'.sub d + 1 < a.regs.length → ∀ x bs d' v,
      C'.next d ⟨C'.pc d, .rd x bs⟩ = some (some d') → rebuild 3 bs = .ok v → Q v d')
    (hrun : C'.inv d → ∀ v d' t, Q v d' → C'.AtD d t →
      let u := { setRegs t a.regs (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] }
      (∀ t', Relation.ReflTransGen (Tau K A L g) u t' → Stops K A L g t' →
        Holds t'.regs (dF d')) ∨ Machine.Dead (K := K) (A := A) (L := L) (g := g) u) :
    DataStep C' dF d := by
  intro t e u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  obtain ⟨hp, hsb, hac, hft, hF⟩ := hat
  by_cases hm : C'.sub d + 1 < a.regs.length
  · have hm' : t.sub + 1 < a.regs.length := by rw [hsb]; exact hm
    refine .inl ?_
    cases hr : rebuild 3 bs with
    | error f =>
      have hu : afterLoad t a.regs bs = { t with fault := some f } := by simp [afterLoad, hr]
      rw [hu]
      exact stays_regs (u := { t with fault := some f }) ⟨_, rfl⟩ rfl (hmid hm _ d' hn _ hF)
    | ok v =>
      have hu : afterLoad t a.regs bs = { t with sub := t.sub + 1, acc := t.acc ++ [v] } := by
        simp [afterLoad, hr, hm']
      rw [hu]
      refine stays_regs ⟨_, out_event (t := { t with sub := t.sub + 1, acc := t.acc ++ [v] })
        hft (by rw [show t.pc = C'.pc d from hp]; exact hc) rfl hl⟩ rfl (hmid hm _ d' hn _ hF)
  · cases hv : rebuild 3 bs with
    | error f =>
      exact .inr (Machine.dead_of_fault (f := f) (by simp [afterLoad, hv]))
    | ok v =>
      have hq := hN hm x bs d' v hn hv
      have hm' : ¬ t.sub + 1 < a.regs.length := by rw [hsb]; exact hm
      have hu : afterLoad t a.regs bs =
          { setRegs t a.regs (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] } := by
        simp [afterLoad, hv, hm']
      rw [hu]
      exact hrun hi v d' t hq ⟨hp, hsb, hac, hft, hF⟩

/-- **The data step of an event that continues at the next instruction.** -/
theorem DataStep.next {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {op : Op} (hc : K.code[C'.pc d]? = some ⟨none, op⟩)
    (hu : ∀ t e u, Fires (C'.pc d) (eventTmpl A L g t op) e (some u) → u = PTX.next t)
    (hrun : C'.inv d → ∀ e d' t, C'.next d e = some (some d') → C'.AtD d t →
      (∀ t', Relation.ReflTransGen (Tau K A L g) (PTX.next t) t' → Stops K A L g t' →
        Holds t'.regs (dF d')) ∨ Machine.Dead (K := K) (A := A) (L := L) (g := g) (PTX.next t)) :
    DataStep C' dF d := by
  intro t e u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain rfl := hu t e u hf
  exact hrun hi e d' t hn hat

theorem fires_tcWaitLd_next {t u : TState} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t .tcWaitLd) e (some u)) : u = PTX.next t := by
  simp only [eventTmpl, tcTmpl, ofExec, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hf
  by_cases hb : L.block % 32 = 0 <;> simp [hb, Fires] at hf
  exact hf.2

theorem fires_tcFenceBefore_next {t u : TState} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t .tcFenceBefore) e (some u)) : u = PTX.next t := by
  simp only [eventTmpl, tcTmpl] at hf
  simp_all [Fires]

/-- Facts on the registers `ds` of a load of as many values, restated by `lookupD`. -/
theorem holds_zip_lookupD {R : Nat → Option Value} {ds : List Nat} {vs : List Value}
    (h : Holds R (ds.zip vs)) (hl : vs.length = ds.length) :
    Holds R (factsFrom ds (lookupD (ds.zip vs))) := by
  refine holds_lookupD h ?_
  rw [List.map_fst_zip (by omega)]
  simp

end
end PTX.Flow.Code
