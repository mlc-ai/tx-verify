-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQ
public import Lemmas.Flow.SegQFH

@[expose] public section

/-! # Strict one-step lemmas under the float tag invariant

The twins of `StepsQ.lean`'s `waitQ`, `advanceQ`, `scalarStoreQ` and `vstQ` for `QTF qt`: the
tags are those of `TagF` (a datum of four bytes among them), and the written registers are listed
as `(register, tag)` pairs that `afterF` checks. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged PTX.Flow.TyG

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

theorem QTF.same {qt : Nat → EnvF} {t u : TState} (ht : QTF qt t) (hpc : u.pc = t.pc)
    (hr : u.regs = t.regs) : QTF qt u := by
  intro r tg h
  rw [hpc] at h
  rw [hr]
  exact ht r tg h

/-- A poll under the float tag invariant: the wait writes the predicate `r`. -/
theorem waitF {qt : Nat → EnvF} {Wf : Event → Prop} {d : C.D} {dst : Bool → C.D}
    {r base : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope}
    (hc : K.code[C.pc d]? = some ⟨none, .mbarWait r base off par acq sc⟩)
    (hoff : r ∉ (C.facts d).map Prod.fst)
    (hn : ∀ m q ok s, C.next d ⟨C.pc d, .wait m q ok acq s⟩ = some (some (dst ok)))
    (hs : C.sub d = 0) (ha : C.acc d = []) (hs' : ∀ ok, C.sub (dst ok) = 0)
    (ha' : ∀ ok, C.acc (dst ok) = []) (hi : ∀ ok, C.inv (dst ok))
    (hq : afterF qt (C.pc d) [(r, .old .pred)] = true)
    (seg : ∀ ok, SegQ K A L g (QTF qt) (C.pc d + 1) ((r, .pred ok) :: C.facts d)
      (C.pc (dst ok)) (C.facts (dst ok))) (e : Event) : C.StepForQ (QTF qt) Wf d e := by
  intro t u ins h _ hins hQ _ hf
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  rw [← h.1] at hf
  obtain ⟨m, q, ok, s, rfl, rfl⟩ := fires_wait hf
  rw [h.1]
  have ht := At.set (r := r) (v := .pred ok) (at_of_atD h hs ha)
    (fun q hq he => hoff (he ▸ List.mem_map_of_mem hq))
  have hQ' : QTF qt (PTX.next (setReg t r (.pred ok))) :=
    QTF.after1 hQ h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1])
      (fun r' hr' => by simp [PTX.next, setReg, Function.update_of_ne (by simpa using hr')])
      (fun p hp => by
        simp only [List.mem_singleton] at hp
        subst hp
        exact ⟨ok, by simp [PTX.next, setReg]⟩) hq
  obtain ⟨t', hr, hg, hq'⟩ := landQ ht hQ' (seg ok) (hi ok) (hs' ok) (ha' ok)
  exact .inl ⟨dst ok, t', hn m q ok s, hr, hg, hq'⟩

/-- A continuing event under the float tag invariant: it advances to the next instruction and
writes nothing, then goes on by a segment. -/
theorem advanceF {qt : Nat → EnvF} {Wf : Event → Prop} {d dn : C.D} {op : Op}
    (hc : K.code[C.pc d]? = some ⟨none, op⟩)
    (ha : ∀ {t u e}, Fires (C.pc d) (eventTmpl A L g t op) e (some u) → u = PTX.next t)
    (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0) (hacc : C.acc d = [])
    (hs' : C.sub dn = 0) (hacc' : C.acc dn = []) (hi : C.inv dn)
    (hq : afterF qt (C.pc d) [] = true)
    (seg : SegQ K A L g (QTF qt) (C.pc d + 1) (C.facts d) (C.pc dn) (C.facts dn)) (e : Event) :
    C.StepForQ (QTF qt) Wf d e := by
  intro t u ins h _ hins hQ _ hf
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  obtain rfl := ha hf
  have hQ' : QTF qt (PTX.next t) :=
    QTF.after1 hQ h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1]) (fun r _ => rfl)
      (fun p hp => by simp at hp) hq
  obtain ⟨t', hr, hg, hq'⟩ := landQ (At.next (at_of_atD h hs hacc)) hQ' seg hi hs' hacc'
  exact .inl ⟨dn, t', hn e, hr, hg, hq'⟩

/-- A scalar store under the float tag invariant. -/
theorem scalarStoreF {qt : Nat → EnvF} {Wf : Event → Prop} {d dn : C.D} {a : MemAccess}
    (hc : K.code[C.pc d]? = some ⟨none, .mem a⟩) (hst : a.kind = .store)
    (hlen : a.srcs.length = 1) (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0)
    (ha : C.acc d = []) (hs' : C.sub dn = 0) (ha' : C.acc dn = []) (hi : C.inv dn)
    (hq : afterF qt (C.pc d) [] = true)
    (seg : SegQ K A L g (QTF qt) (C.pc d + 1) (C.facts d) (C.pc dn) (C.facts dn)) (e : Event) :
    C.StepForQ (QTF qt) Wf d e := by
  intro t u ins h _ hins hQ _ hf
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  obtain ⟨_, _, rfl, rfl⟩ := fires_st hst hf
  rw [afterStore_last (by rw [h.2.1, hs, hlen]; decide)]
  have hQ' : QTF qt { t with pc := t.pc + 1, sub := 0 } :=
    QTF.after1 hQ h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1]) (fun r _ => rfl)
      (fun p hp => by simp at hp) hq
  obtain ⟨t', hr, hg, hq'⟩ := landQ (u := {t with pc := t.pc + 1, sub := 0})
    ⟨congrArg (· + 1) h.1, rfl, h.2.2.1.trans ha, h.2.2.2.1, h.2.2.2.2⟩ hQ' seg hi hs' ha'
  exact .inl ⟨dn, t', hn _, hr, hg, hq'⟩

/-- An element of a vector store under the float tag invariant. -/
theorem vstF {qt : Nat → EnvF} {Wf : Event → Prop} {d dn : C.D} {a : MemAccess}
    (hc : K.code[C.pc d]? = some ⟨none, .mem a⟩) (hst : a.kind = .store)
    (hn : ∀ e, C.next d e = some (some dn)) (hacc : C.acc d = [])
    (mid : C.sub d + 1 < a.srcs.length → C.pc dn = C.pc d ∧ C.sub dn = C.sub d + 1 ∧
      C.acc dn = [] ∧ C.facts dn = C.facts d ∧ C.inv dn)
    (hq : afterF qt (C.pc d) [] = true)
    (last : ¬ C.sub d + 1 < a.srcs.length → C.sub dn = 0 ∧ C.acc dn = [] ∧ C.inv dn ∧
      SegQ K A L g (QTF qt) (C.pc d + 1) (C.facts d) (C.pc dn) (C.facts dn)) (e : Event) :
    C.StepForQ (QTF qt) Wf d e := by
  intro t u ins h _ hins hQ _ hf
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  obtain ⟨_, _, rfl, rfl⟩ := fires_st hst hf
  obtain ⟨hP, hS0, hA, hFl, hR⟩ := h
  by_cases hm : C.sub d + 1 < a.srcs.length
  · obtain ⟨hpc, hs, ha, hF, hinv⟩ := mid hm
    rw [afterStore_mid (by rw [hS0]; exact hm)]
    refine .inl ⟨dn, _, hn _, .refl, ⟨⟨hP.trans hpc.symm, ?_, hA.trans (hacc.trans ha.symm), hFl,
      hF ▸ hR⟩, hinv⟩, QTF.same hQ rfl rfl⟩
    show t.sub + 1 = C.sub dn
    rw [hS0, hs]
  · obtain ⟨hs0, ha0, hinv, seg⟩ := last hm
    rw [afterStore_last (by rw [hS0]; exact hm)]
    have hQ' : QTF qt { t with pc := t.pc + 1, sub := 0 } :=
      QTF.after1 hQ hP (by show t.pc + 1 = C.pc d + 1; rw [hP]) (fun r _ => rfl)
        (fun p hp => by simp at hp) hq
    obtain ⟨t', hr, hg, hq'⟩ := landQ (u := { t with pc := t.pc + 1, sub := 0 })
      ⟨congrArg (· + 1) hP, rfl, hA.trans hacc, hFl, hR⟩ hQ' seg hinv hs0 ha0
    exact .inl ⟨dn, t', hn _, hr, hg, hq'⟩

end PTX.Flow.Code
