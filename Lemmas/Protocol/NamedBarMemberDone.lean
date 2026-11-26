-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarMember

@[expose] public section

/-! # Every participant of a released generation arrived

`Sources.member_arrival_done` is `member_arrival_any` for a `bar.sync` whose generation is done
(`CtaBarDone`) instead of one with a later event: the proof is the same from the release. -/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {count : Option Nat} {p : Finset Nat} {id : Nat}

/-- A `bar.sync` whose generation is done releases the generation of its ordinal. -/
theorem sync_released_done (hX : Consistent L K A mem0 X) (hS : Sources L X count p id)
    (hG : Shape L count p id) {f : EvId} {pc : Nat} {cnt : Option Nat}
    (hf : X.IsBarrier f id cnt pc)
    (hdone : ∃ key, CtaBarK L X f key ∧ CtaBarDone L X (f.1 / L.block) key) :
    Released L.block (X.barriers (f.1 / L.block)) id
      (((X.tr f.1).take f.2).countP (Execution.isBarId id)) := by
  obtain ⟨key, hkey, hd⟩ := hdone
  have hk := hS.arrival_key hX hG hf (CtaBarK.arrival hkey)
  subst hk
  have := hG.id_lt
  unfold CtaBarDone at hd
  rwa [show (id + 16 * ((X.tr f.1).take f.2).countP (Execution.isBarId id)) % 16 = id by omega,
    show (id + 16 * ((X.tr f.1).take f.2).countP (Execution.isBarId id)) / 16 =
      ((X.tr f.1).take f.2).countP (Execution.isBarId id) by omega] at hd

/-- **A released generation has every participant's arrival of its ordinal**: the release of a
`bar.sync`'s generation (`hdone`) in place of a later event of its thread. -/
theorem Sources.member_arrival_done (hX : Consistent L K A mem0 X) (hS : Sources L X count p id)
    (hG : Shape L count p id) {f : EvId} {pc : Nat} {cnt : Option Nat}
    (hf : X.IsBarrier f id cnt pc)
    (hdone : ∃ key, CtaBarK L X f key ∧ CtaBarDone L X (f.1 / L.block) key) {g : Nat}
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
    obtain ⟨key, hk, -⟩ := hdone
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
    sync_released_done hX hS hG hf hdone
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
