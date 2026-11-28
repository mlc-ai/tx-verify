-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQFP

@[expose] public section

/-! # A load whose destination the table after it does not name

`ldWFP` for a destination register that has no tag at the next pc: the word read needs no tag. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged PTX.Flow.TyG

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

theorem QTF.afterU {qt : Nat → EnvF} {t u : TState} {pc : Nat} (ht : QTF qt t) (hpc : t.pc = pc)
    (hu : u.pc = pc + 1) (hw : ∀ r ∈ (qt (pc + 1)).map Prod.fst, u.regs r = t.regs r)
    (h : afterF qt pc [] = true) : QTF qt u := by
  have ht' : TypedF (qt pc) t := by simpa [QTF, hpc] using ht
  unfold QTF
  rw [hu]
  intro r tg hr
  simp only [afterF, List.all_eq_true, List.nil_append] at h
  rw [hw r (List.mem_map_of_mem (f := Prod.fst) (lookup_mem' hr))]
  exact TagF.sat_ok (v := t.regs r) (need := tg) (h := (qt pc).lookup r)
    (h (r, tg) (lookup_mem' hr)) (fun tg' h' => ht' r tg' h')

/-- A scalar weak load of a possibly guarded instruction into a register the next table omits. -/
theorem ldWFPu {qt : Nat → EnvF} {Wf : Event → Prop} {P : TState → Prop}
    {d : C.D} {f : Value → C.D} {a : MemAccess} {r : Nat} {gd : Option (Nat × Bool)}
    (hc : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
    (hext : a.ext = .same) (hr : a.regs = [r])
    (hW : ∀ e, Wf e → e.pc = C.pc d → ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v)
    (hn : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = some (some (f v)))
    (hs : C.sub d = 0) (ha : C.acc d = []) (hoff : ∀ p ∈ C.facts d, p.1 ≠ r)
    (hnk : r ∉ (qt (C.pc d + 1)).map Prod.fst) (hq : afterF qt (C.pc d) [] = true)
    (hok : ∀ v, C.sub (f v) = 0 ∧ C.acc (f v) = [] ∧ C.inv (f v) ∧
      SegQ K A L g (fun t => QTF qt t ∧ P t) (C.pc d + 1) ((r, v) :: C.facts d) (C.pc (f v))
        (C.facts (f v))) (e : Event) : C.StepForQP (QTF qt) P Wf d e := by
  intro t u ins h _ hc' hQ hWe hf hPu
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf hext
  obtain ⟨v, hy⟩ := hW _ hWe (by rw [← h.1]) x bs rfl
  have ht := at_of_atD h hs ha
  rw [hr, afterLoad_ok ht.2.1 ht.2.2.1 hy] at hPu ⊢
  obtain ⟨hs', ha', hi, seg⟩ := hok v
  obtain ⟨hP, hS0, hA, hFl, hR⟩ := ht
  have hu : At { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] }
      (C.pc d + 1) ((r, v) :: C.facts d) :=
    ⟨by show t.pc + 1 = _; rw [hP], rfl, rfl, hFl, Function.update_self ..,
      holds_update hR hoff⟩
  have hQ' : QTF qt { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] } :=
    QTF.afterU hQ hP (by show t.pc + 1 = C.pc d + 1; rw [hP]) (fun r' hl => by
      have : r' ≠ r := fun e => hnk (e ▸ hl)
      simp [setReg, Function.update_of_ne this]) hq
  obtain ⟨t', hr', hg, hq'⟩ := landQ (Q := fun t => QTF qt t ∧ P t) hu ⟨hQ', hPu⟩ seg hi hs' ha'
  exact .inl ⟨f v, t', hn x bs v hy, hr', hg, hq'.1⟩

end PTX.Flow.Code
