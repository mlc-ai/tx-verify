-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQ

@[expose] public section

/-! # An element of a vector store whose facts shrink

`Code.vstQW`: `Code.vstQ` with the facts of the next element weaker than those of this one
(a fact of the machine that only the elements up to this one need). -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- **An element of a vector store under the tag invariant**; the next element's facts weaken. -/
theorem vstQW {qt : Nat → Env} {ex : Env} {Wf : Event → Prop} {d dn : C.D} {a : MemAccess}
    (hc : K.code[C.pc d]? = some ⟨none, .mem a⟩) (hst : a.kind = .store)
    (hn : ∀ e, C.next d e = some (some dn)) (hacc : C.acc d = [])
    (mid : C.sub d + 1 < a.srcs.length → C.pc dn = C.pc d ∧ C.sub dn = C.sub d + 1 ∧
      C.acc dn = [] ∧ (∀ R, Holds R (C.facts d) → Holds R (C.facts dn)) ∧ C.inv dn)
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
      hF _ hR⟩, hinv⟩, QT.same hQ rfl rfl⟩
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
