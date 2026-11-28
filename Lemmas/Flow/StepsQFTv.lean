-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQFT

@[expose] public section

/-! # `tcLdFP` with the loaded words among the facts

The words a `tcgen05.ld` returns are facts of the state after it, in the registers it names. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged PTX.Flow.TyG

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

theorem setRegs_zip (t : TState) : ∀ (ds : List Nat) (vs : List Value), ds.Nodup →
    ∀ p ∈ ds.zip vs, (setRegs t ds vs).regs p.1 = some p.2
  | [], _, _, p, hp => by simp at hp
  | _ :: _, [], _, p, hp => by simp at hp
  | d :: ds, v :: vs, hnd, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · simp only
      change (setRegs (setReg t d v) ds vs).regs d = some v
      rw [setRegs_other _ ds vs d (List.nodup_cons.mp hnd).1]
      simp [setReg]
    · exact setRegs_zip (setReg t d v) ds vs (List.nodup_cons.mp hnd).2 p hp

theorem tcLdFPv {qt : Nat → EnvF} {Wf : Event → Prop} {P : TState → Prop} {d : C.D}
    {f : List Value → C.D} {ds : List Nat} {ta : Nat} {sh : TcShape}
    (hc : K.code[C.pc d]? = some ⟨none, .tcLd ds ta sh⟩) (hsh : ∀ s, sh ≠ .packed16 s)
    (hw : A.any (·.tcLdWait (C.pc d)) = false) (hnd : ds.Nodup)
    (hoff : ∀ p ∈ C.facts d, p.1 ∉ ds)
    (hW : ∀ e, Wf e → e.pc = C.pc d → ∀ a vals, e.kind = .tc (.ld a vals sh) →
      ∀ v ∈ vals, Dat32 v)
    (hn : ∀ a vals, C.next d ⟨C.pc d, .tc (.ld a vals sh)⟩ = some (some (f vals)))
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hq : afterF qt (C.pc d) (ds.map fun r => (r, TagF.dat32)) = true)
    (hok : C.inv d → ∀ vals : List Value, vals.length = ds.length → (∀ v ∈ vals, Dat32 v) →
      C.sub (f vals) = 0 ∧ C.acc (f vals) = [] ∧ C.inv (f vals) ∧
      SegQ K A L g (fun t => QTF qt t ∧ P t) (C.pc d + 1) (ds.zip vals ++ C.facts d)
        (C.pc (f vals)) (C.facts (f vals))) (e : Event) : C.StepForQP (QTF qt) P Wf d e := by
  intro t u ins h hinv hc' hQ hWe hf hPu
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  have ht := at_of_atD h hs ha
  obtain ⟨hP, hS0, hA, hFl, hR⟩ := ht
  obtain ⟨a, vals, hlen, rfl, rfl⟩ := fires_tcLd hsh hf (by rw [hP]; exact hw)
  obtain ⟨hp, hsb, hac, hfl⟩ := setRegs_skel (PTX.next t) ds vals
  have hu : At (setRegs (PTX.next t) ds vals) (C.pc d + 1) (ds.zip vals ++ C.facts d) :=
    ⟨hp.trans (congrArg (· + 1) hP), hsb.trans hS0, hac.trans hA, hfl.trans hFl,
      (holds_append _ _ _).mpr ⟨holds_of_forall fun p hp => by
          rw [setRegs_next_regs]; exact setRegs_zip t ds vals hnd p hp,
        Havoc.holds_of_forall fun p hp => by
          rw [setRegs_next_regs, setRegs_other t ds vals _ (hoff p hp)]
          exact holds_mem hR hp⟩⟩
  have hQ' : QTF qt (setRegs (PTX.next t) ds vals) :=
    QTF.after1 hQ hP (by rw [hp]; exact hP ▸ rfl) (fun r hr => by
        simp only [List.map_map, Function.comp_def, List.map_id'] at hr
        rw [setRegs_next_regs, setRegs_other t ds vals _ hr])
      (fun q hq' => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq'
        obtain ⟨i, hi', hri⟩ := List.getElem_of_mem hr
        have hv : vals[i]? = some vals[i] := List.getElem?_eq_getElem (by omega)
        rw [setRegs_next_regs]
        have := setRegs_get ds vals t i r vals[i] hnd (by rw [← hri]; simp) hv
        exact ⟨_, this, hW _ hWe rfl a vals rfl _ (List.getElem_mem _)⟩) hq
  obtain ⟨hs', ha', hi, seg⟩ := hok hinv vals hlen (hW _ hWe rfl a vals rfl)
  obtain ⟨t', hr, hg, hq'⟩ := landQ (Q := fun t => QTF qt t ∧ P t) hu ⟨hQ', hPu⟩ seg hi hs' ha'
  exact .inl ⟨f vals, t', hn a vals, hr, hg, hq'.1⟩

end PTX.Flow.Code
