-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarMember

@[expose] public section

/-! # An exit that a barrier release counts, and the dependency cycle it closes

A thread that exits while other threads still wait at a CTA barrier generation is counted by the
release of that generation: its exit record is a need of every `bar.sync` of the generation
(`ctaBarNeeds`, `CtaBarCounted`). The dependency order (DEP-ORDER, `DependencyOk.acyclic`) then
orders the exit before the return of those `bar.sync` events. This file gives two facts about it.

* `Sources.arrival_or_exit`: for a named barrier whose arrivals follow one group (`Sources`,
  `Shape`), a participant lane of the CTA of a passed `bar.sync` either has the arrival of the same
  source ordinal or has an exit event that is a witness of the `bar.sync`'s return.
* `Consistent.no_exit_cycle`: the exit `E` of a thread cannot be a witness of the return of a
  blocking event `f` when the thread of `E` waited, before `E`, at a blocking event `W` one of
  whose witnesses `Z` is a later event of the thread of `f`. The four steps
  `(E, issued) → (f, returned) → (Z, issued) → (W, returned) → (E, issued)` form a cycle of
  `DepStep`.
-/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- **No exit closes a dependency cycle through two blocking events.** The exit `E` is a witness of
the return of the blocking event `f`; `Z` is a later event of the thread of `f` and a witness of
the return of the blocking event `W`, and `E` is a later event of the thread of `W`. -/
theorem _root_.PTX.Consistent.no_exit_cycle (hX : Consistent L K A mem0 X) {E f Z W : EvId}
    (hEf : Witness L X (.thread E) f)
    (hf : ∃ ev b, X.get f = some ev ∧ ev.kind.resume = .blocking b) (hfZ : TraceBefore X f Z)
    (hZW : Witness L X (.thread Z) W)
    (hW : ∃ ev b, X.get W = some ev ∧ ev.kind.resume = .blocking b) (hWE : TraceBefore X W E) :
    False := by
  obtain ⟨ef, bf, hgf, hbf⟩ := hf
  obtain ⟨ew, bw, hgw, hbw⟩ := hW
  have s1 : DepStep L K X (.thread E, false) (.thread f, true) := DepStep.of_witness L hEf
  have s2 : DepStep L K X (.thread f, true) (.thread Z, false) :=
    DepStep.of_resumes L (Resumes.of_blocking hgf hbf hfZ)
  have s3 : DepStep L K X (.thread Z, false) (.thread W, true) := DepStep.of_witness L hZW
  have s4 : DepStep L K X (.thread W, true) (.thread E, false) :=
    DepStep.of_resumes L (Resumes.of_blocking hgw hbw hWE)
  have hc : Relation.TransGen (DepStep L K X) (.thread E, false) (.thread E, false) :=
    .tail (.tail (.tail (.single s1) s2) s3) s4
  exact hX.dependency.acyclic (.cluster 0) trivial _
    (Relation.TransGen.mono (fun _ _ => Or.inl) _ _ hc)

variable {count : Option Nat} {p : Finset Nat} {id : Nat}

/-- **A participant of a passed generation arrived in it, or its exit is a witness of the
pass.** For a named barrier whose arrivals follow one group: a participant lane `g` of the CTA of
a passed `bar.sync` `f` has the arrival of `f`'s source ordinal, or an exit event that the release
of `f`'s generation counts (its exit record is at or before the record completing the
generation), so the exit is a witness of `f`'s return. -/
theorem Sources.arrival_or_exit (hX : Consistent L K A mem0 X) (hS : Sources L X count p id)
    (hG : Shape L count p id) {f : EvId} {pc : Nat} {cnt : Option Nat}
    (hf : X.IsBarrier f id cnt pc) (hpassed : f.2 + 1 < (X.tr f.1).length) {g : Nat}
    (hcta : g / L.block = f.1 / L.block) (hw : (g % L.block) / 32 ∈ p) :
    (∃ i pc' m, X.get (g, i) = some ⟨pc', .bar id count m⟩ ∧
      ((X.tr g).take i).countP (Execution.isBarId id) =
        ((X.tr f.1).take f.2).countP (Execution.isBarId id)) ∨
    ∃ y pcx, y.1 = g ∧ X.get y = some ⟨pcx, .exit⟩ ∧ Witness L X (.thread y) f := by
  obtain ⟨key, hkey, hdone⟩ := ctaBarDone_of_returned hX hf hpassed
  have hk := hS.arrival_key hX hG hf (CtaBarK.arrival hkey)
  have hfg : f.1 < L.threads := hkey.1
  have hb := block_pos_of_thread_lt hfg
  set c := f.1 / L.block with hcdef
  have hc : c < L.grid := cta_lt hfg
  set l := g % L.block with hldef
  have hl : l < L.block := Nat.mod_lt _ hb
  have hthr : c * L.block + l = g := by
    rw [← hcta, Nat.mul_comm]
    exact Nat.div_add_mod g L.block
  set φ := ((X.tr f.1).take f.2).countP (Execution.isBarId id) with hφ
  have hidl := hG.id_lt
  have hmod : key % 16 = id := by rw [hk]; omega
  have hdiv : key / 16 = φ := by rw [hk]; omega
  obtain ⟨ic, hic⟩ := hdone
  have hic' := hic
  obtain ⟨r0, s0, t0, hr0, hs0, ht0, hbefore, hafter⟩ := hic'
  have hrun : run L.block {} ((X.barriers c).take (ic + 1)) = .ok t0 := by
    rw [List.take_add_one, hr0, run_append, hs0]
    simp [run, ht0, Except.bind]
  by_cases hx : l ∈ t0.exited
  · right
    obtain ⟨a, ha⟩ := run_exited_mem hrun hx
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ha
    have hjl : j < ic + 1 := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      simp only [List.length_take] at this
      omega
    have hj' : (X.barriers c)[j]? = some (.exit l a) := by
      rwa [List.getElem?_take_of_lt hjl] at hj
    obtain ⟨-, ha1, pcx, hget⟩ := (hX.ctaBar.2 c hc).2.1 _ (List.mem_of_getElem? hj')
    have hag : a.1 = g := ha1.trans hthr
    have hcnt : CtaBarCounted L X f a :=
      ⟨key, ic, hkey, hic, j, .exit l a, hj', by simp [Record.refs], by omega, .inr ⟨l, rfl⟩⟩
    have hy : a ∈ (X.barriers c).flatMap Record.refs :=
      List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hj', by simp [Record.refs]⟩
    exact ⟨a, pcx, hag, hget, Witness.of_need L (ctaBarCounted_witnessed L X f a hf hy hcnt)
      ⟨_, hget⟩ rfl⟩
  · left
    obtain ⟨i, lanes, e', hrec', hm, hgen⟩ := completed_participant_record (phase := φ)
      (hS.completed hX hc (ic + 1)) hG.pos hG.target rfl hG.bound hrun
      (by rw [hmod, hdiv] at hafter; rw [hafter]; omega) hl hw hx
    have hi : i < ic + 1 := by
      have hh := (List.getElem?_eq_some_iff.mp hrec').1
      simp only [List.length_take] at hh
      omega
    have hreal : (X.barriers c)[i]? = some (.arrival id (l / 32) count lanes) := by
      simpa only [List.getElem?_take, ite_eq_left hi] using hrec'
    obtain ⟨-, he1', pc', m', he'⟩ :=
      ((hX.ctaBar.2 c hc).2.1 _ (List.mem_of_getElem? hreal)) (l, e') hm
    simp only at he1'
    have hee : e'.1 = g := he1'.trans hthr
    have hge : e'.1 < L.threads := by rw [he1']; exact cta_thread_lt hc hl
    have hgenFull : GenerationOf L.block (X.barriers (e'.1 / L.block)) e' id φ := by
      have hh := hgen.append (ys := (X.barriers c).drop (ic + 1))
      rw [show e'.1 / L.block = c by rw [hee, hcta]]
      simpa only [List.take_append_drop] using hh
    have hk' : CtaBarArrivalK L X e' (id + 16 * φ) :=
      CtaBarArrivalK.of_generation hX.ctaBar hge hG.id_lt hgenFull
    have hkey' := hS.arrival_key hX hG he' hk'
    obtain ⟨e1, e2⟩ := e'
    simp only at hee he' hkey'
    subst hee
    exact ⟨e2, pc', m', he', by omega⟩

end
end PTX.NamedBar
