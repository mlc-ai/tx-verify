-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.Combinators
public import Lemmas.Flow.DataLoad
public import Lemmas.Flow.StrictWindow

@[expose] public section

/-! # Step combinators of vector loads

A proof tool, beside `step_load_sel` (`Combinators.lean`) for a load of several registers, one
element per event. `step_vload_mid`: an element that is not the last keeps the value read in the
accumulator and stays at the instruction. `step_vload_last`: the last element writes the
destinations from the accumulator and the value read, and the machine's successor is a function
`nv` of that value (it follows it to a state or stops following). -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- An element of a vector load other than the last: the thread stays at the instruction with the
next element and the value read appended, the facts unchanged. -/
theorem step_vload_mid {d : C.D} {dn : Value → C.D} {gd : Option (Nat × Bool)} {a : MemAccess}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
    (he : a.ext = .same) (hsub : C.sub d + 1 < a.regs.length)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = some (some (dn v)))
    (herr : ∀ x bs f, rebuild 3 bs = .error f →
      C.next d ⟨C.pc d, .rd x bs⟩ = none ∨ C.next d ⟨C.pc d, .rd x bs⟩ = some none)
    (hpc : ∀ v, C.pc (dn v) = C.pc d) (hs : ∀ v, C.sub (dn v) = C.sub d + 1)
    (ha : ∀ v, C.acc (dn v) = C.acc d ++ [v]) (hF : ∀ v, C.facts (dn v) = C.facts d)
    (hinv : C.inv d → ∀ v, C.inv (dn v)) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  cases hv : rebuild 3 bs with
  | error f =>
    rcases herr x bs f hv with hn | hn
    · exact .inr ⟨hn, Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
    · exact .inl (.inl hn)
  | ok v =>
    rw [afterLoad_mid hv (by rw [h.2.1]; exact hsub)]
    refine .inl (.inr ⟨dn v, _, hok x bs v hv, .refl, ⟨?_, ?_, ?_, h.2.2.2.1, ?_⟩, hinv hi v⟩)
    · exact h.1.trans (hpc v).symm
    · show t.sub + 1 = C.sub (dn v)
      rw [h.2.1, hs]
    · show t.acc ++ [v] = C.acc (dn v)
      rw [h.2.2.1, ha]
    · rw [hF]; exact h.2.2.2.2

/-- The last element of a vector load: the destinations are written from the accumulator and the
value read; the successor is a function of the value read. -/
theorem step_vload_last {d : C.D} {nv : Value → Option (Option C.D)} {gd : Option (Nat × Bool)}
    {a : MemAccess} (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .load)
    (hnc : a.nc = false) (he : a.ext = .same) (hsub : ¬ C.sub d + 1 < a.regs.length)
    (hnd : a.regs.Nodup) (hoff : ∀ q ∈ C.facts d, q.1 ∉ a.regs)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = nv v)
    (herr : ∀ x bs f, rebuild 3 bs = .error f →
      C.next d ⟨C.pc d, .rd x bs⟩ = none ∨ C.next d ⟨C.pc d, .rd x bs⟩ = some none)
    (hnn : ∀ v, nv v ≠ none)
    (hl : ∀ v d', nv v = some (some d') →
      C.Lands d (C.pc d + 1) (a.regs.zip (C.acc d ++ [v]) ++ C.facts d) d') : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  cases hv : rebuild 3 bs with
  | error f =>
    rcases herr x bs f hv with hn | hn
    · exact .inr ⟨hn, Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
    · exact .inl (.inl hn)
  | ok v =>
    rw [afterLoad_last hv (by rw [h.2.1]; exact hsub)]
    have hn := hok x bs v hv
    rcases hnv : nv v with _ | _ | d'
    · exact absurd hnv (hnn v)
    · exact .inl (.inl (hn.trans hnv))
    · refine (hl v d' hnv).cont hi (hn.trans hnv) ?_
      obtain ⟨hp, -, ha, hf0, hF⟩ := h
      obtain ⟨-, -, -, hskF⟩ := setRegs_skel t a.regs (t.acc ++ [v])
      refine ⟨by show t.pc + 1 = _; rw [hp], rfl, rfl, hskF.trans hf0, (holds_append _ _ _).mpr
        ⟨?_, holds_setRegs_off hF hoff⟩⟩
      rw [← ha]
      exact holds_setRegs_zip t a.regs (t.acc ++ [v]) hnd

/-- The same strict step for one event `e` that does not read bytes that fail to rebuild
(`hwf`): the machine need not stop on such an event. -/
theorem stepFor_vload_mid {d : C.D} {dn : Value → C.D} {gd : Option (Nat × Bool)} {a : MemAccess}
    {e : Event} (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .load)
    (hnc : a.nc = false) (he : a.ext = .same) (hsub : C.sub d + 1 < a.regs.length)
    (hwf : ∀ x bs, e = ⟨C.pc d, .rd x bs⟩ → ∃ v, rebuild 3 bs = .ok v)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = some (some (dn v)))
    (hpc : ∀ v, C.pc (dn v) = C.pc d) (hs : ∀ v, C.sub (dn v) = C.sub d + 1)
    (ha : ∀ v, C.acc (dn v) = C.acc d ++ [v]) (hF : ∀ v, C.facts (dn v) = C.facts d)
    (hinv : C.inv d → ∀ v, C.inv (dn v)) : C.StepFor d e := by
  intro t u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  obtain ⟨v, hv⟩ := hwf x bs rfl
  rw [afterLoad_mid hv (by rw [h.2.1]; exact hsub)]
  refine .inl (.inr ⟨dn v, _, hok x bs v hv, .refl, ⟨?_, ?_, ?_, h.2.2.2.1, ?_⟩, hinv hi v⟩)
  · exact h.1.trans (hpc v).symm
  · show t.sub + 1 = C.sub (dn v)
    rw [h.2.1, hs]
  · show t.acc ++ [v] = C.acc (dn v)
    rw [h.2.2.1, ha]
  · rw [hF]; exact h.2.2.2.2

end
end PTX.Flow.Code
