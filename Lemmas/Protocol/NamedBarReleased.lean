-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarArrive

@[expose] public section

/-! # A released generation has every participant's arrival

A proof tool for named barriers whose arrivals follow their group (`Sources`, `Shape`). When
generation `G` of barrier `id` of a CTA is released, every lane of a participant warp of that
CTA either made its arrival with `G` earlier events on the barrier or exited
(`Sources.arrival_of_released`): a live lane is a participant of every completed generation
(`completed_participant_record`), and the generation of its recorded arrival is its ordinal
(`Sources.arrival_key`). -/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {count : Option Nat} {p : Finset Nat} {id : Nat}

/-- **A released generation has every participant's arrival**: a lane of a participant warp of
the CTA made an arrival on the barrier with `G` earlier events on it, or exited. -/
theorem Sources.arrival_of_released (hX : Consistent L K A mem0 X) (hS : Sources L X count p id)
    (hG : Shape L count p id) {c G g : Nat} (hd : Released L.block (X.barriers c) id G)
    (hg : g < L.threads) (hc : g / L.block = c) (hw : (g % L.block) / 32 ∈ p) :
    (∃ i pc cnt m, X.get (g, i) = some ⟨pc, .bar id cnt m⟩ ∧
      ((X.tr g).take i).countP (Execution.isBarId id) = G) ∨
    ∃ k pc, X.get (g, k) = some ⟨pc, .exit⟩ := by
  have hcl := cta_lt hg
  rw [hc] at hcl
  have hb := block_pos_of_thread_lt hg
  set l := g % L.block with hldef
  have hl : l < L.block := Nat.mod_lt _ hb
  have hthr : c * L.block + l = g := by
    rw [← hc, Nat.mul_comm]
    exact Nat.div_add_mod g L.block
  obtain ⟨index, r0, s0, t0, hr0, hs0, ht0, hbefore, hafter⟩ := hd
  have hrun : run L.block {} ((X.barriers c).take (index + 1)) = .ok t0 := by
    rw [List.take_add_one, hr0, run_append, hs0]
    simp [run, ht0, Except.bind]
  by_cases hx : l ∈ t0.exited
  · obtain ⟨a, ha⟩ := run_exited_mem hrun hx
    obtain ⟨-, ha1, pcx, hget⟩ := (hX.ctaBar.2 _ hcl).2.1 _ (List.mem_of_mem_take ha)
    right
    have hae : a.1 = g := by rw [ha1]; exact hthr
    exact ⟨a.2, pcx, by rw [← hae]; exact hget⟩
  obtain ⟨i, lanes, e', hrec', hm, hgen⟩ := completed_participant_record (phase := G)
    (hS.completed hX hcl (index + 1)) hG.pos hG.target rfl hG.bound hrun
    (by rw [hafter]; omega) hl hw hx
  have hi : i < index + 1 := by
    have hh := (List.getElem?_eq_some_iff.mp hrec').1
    simp only [List.length_take] at hh
    omega
  have hreal : (X.barriers c)[i]? = some (.arrival id (l / 32) count lanes) := by
    simpa only [List.getElem?_take, ite_eq_left hi] using hrec'
  obtain ⟨-, he1', pc', m', he'⟩ :=
    ((hX.ctaBar.2 c hcl).2.1 _ (List.mem_of_getElem? hreal)) (l, e') hm
  simp only at he1'
  have hee : e'.1 = g := he1'.trans hthr
  have hgenFull : GenerationOf L.block (X.barriers c) e' id G := by
    have hh := hgen.append (ys := (X.barriers c).drop (index + 1))
    simpa only [List.take_append_drop] using hh
  have hk' : CtaBarArrivalK L X e' (id + 16 * G) := by
    apply CtaBarArrivalK.of_generation hX.ctaBar (hee ▸ hg) hG.id_lt
    rw [hee, hc]
    exact hgenFull
  have hkey := hS.arrival_key hX hG he' hk'
  simp only at hkey
  left
  refine ⟨e'.2, pc', count, m', ?_, ?_⟩
  · rw [← hee]
    exact he'
  · rw [← hee]
    omega

end
end PTX.NamedBar
