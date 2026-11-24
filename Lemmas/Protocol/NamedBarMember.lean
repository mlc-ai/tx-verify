-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarArrive

@[expose] public section

/-! # Every participant of a passed generation arrived, with `bar.arrive` participants

`Sources.member_arrival` gives every participant lane an arrival of a passed generation's ordinal
for a kernel without `bar.arrive`. This file gives the same for a group whose participants may use
either form (`Sources.member_arrival_any`): a passed `bar.sync` releases the generation of its
ordinal (`Sources.sync_released`), a release records every participant lane that has not exited
(`completed_participant_record`), and a recorded arrival's generation is its source ordinal
(`Sources.arrival_key`). A lane that has exited is the kernel's case (`hexited`). -/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {count : Option Nat} {p : Finset Nat} {id : Nat}

/-- **A passed generation has every participant's arrival of its ordinal**, of either form: a
participant lane of the CTA that never exits has one by the release; for a lane that exits the
kernel supplies it (`hexited`). -/
theorem Sources.member_arrival_any (hX : Consistent L K A mem0 X) (hS : Sources L X count p id)
    (hG : Shape L count p id) {f : EvId} {pc : Nat} {cnt : Option Nat}
    (hf : X.IsBarrier f id cnt pc) (hpassed : f.2 + 1 < (X.tr f.1).length) {g : Nat}
    (hcta : g / L.block = f.1 / L.block) (hw : (g % L.block) / 32 ∈ p)
    (hexited : (∃ j pcx, X.get (g, j) = some ⟨pcx, .exit⟩) → ∃ i pc' m,
      X.get (g, i) = some ⟨pc', .bar id count m⟩ ∧
        ((X.tr g).take i).countP (Execution.isBarId id) =
          ((X.tr f.1).take f.2).countP (Execution.isBarId id)) :
    ∃ i pc' m, X.get (g, i) = some ⟨pc', .bar id count m⟩ ∧
      ((X.tr g).take i).countP (Execution.isBarId id) =
        ((X.tr f.1).take f.2).countP (Execution.isBarId id) := by
  by_cases hex : ∃ j pcx, X.get (g, j) = some ⟨pcx, .exit⟩
  · exact hexited hex
  have hfg : f.1 < L.threads := by
    obtain ⟨key, hk, -⟩ := ctaBarDone_of_returned hX hf hpassed
    exact hk.1
  have hb := block_pos_of_thread_lt hfg
  set c := f.1 / L.block with hcdef
  have hc : c < L.grid := cta_lt hfg
  set l := g % L.block with hldef
  have hl : l < L.block := Nat.mod_lt _ hb
  have hthr : c * L.block + l = g := by
    rw [← hcta, Nat.mul_comm]
    exact Nat.div_add_mod g L.block
  set φ := ((X.tr f.1).take f.2).countP (Execution.isBarId id) with hφ
  obtain ⟨index, r0, s0, t0, hr0, hs0, ht0, hbefore, hafter⟩ :=
    hS.sync_released hX hG hf hpassed
  have hrun : run L.block {} ((X.barriers c).take (index + 1)) = .ok t0 := by
    rw [List.take_add_one, hr0, run_append, hs0]
    simp [run, ht0, Except.bind]
  have hx : l ∉ t0.exited := by
    intro hm
    obtain ⟨a, ha⟩ := run_exited_mem hrun hm
    obtain ⟨-, hy, pcx, hget⟩ := (hX.ctaBar.2 c hc).2.1 _ (List.mem_of_mem_take ha)
    obtain ⟨y1, y2⟩ := a
    simp only at hy
    subst hy
    exact hex ⟨y2, pcx, by rw [← hthr]; exact hget⟩
  obtain ⟨i, lanes, e', hrec', hm, hgen⟩ := completed_participant_record (phase := φ)
    (hS.completed hX hc (index + 1)) hG.pos hG.target rfl hG.bound hrun
    (by rw [hafter]; omega) hl hw hx
  have hi : i < index + 1 := by
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
    have hh := hgen.append (ys := (X.barriers c).drop (index + 1))
    rw [show e'.1 / L.block = c by rw [hee, hcta]]
    simpa only [List.take_append_drop] using hh
  have hk' : CtaBarArrivalK L X e' (id + 16 * φ) :=
    CtaBarArrivalK.of_generation hX.ctaBar hge hG.id_lt hgenFull
  have hkey := hS.arrival_key hX hG he' hk'
  obtain ⟨e1, e2⟩ := e'
  simp only at hee he' hkey
  subst hee
  exact ⟨e2, pc', m', he', by omega⟩

end
end PTX.NamedBar
