-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Lib.BarLaneKeys
public import Lemmas.Protocol.NamedBarSources
public import Lemmas.Protocol.NamedBarArrive

@[expose] public section

/-!
# Every lane of a loop group has the arrival a passed loop lane passed

The loop-group analogue of `NamedBar.early_member_arrival` (`BarEarlyMember.lean`): a barrier whose
arrivals follow `PhSources` (`BarLaneKeys.lean`) has, for each source ordinal whose generation was
released by a passed arrival of a loop warp, an arrival of that ordinal by *every* lane of the loop
group in the CTA, an exiting lane from the premise `hexited`. The proof is the second half of
`D_key_of_released`: a lane that never exits has a record in every released generation
(`completed_D_record`), and the record's event is the lane's arrival of that ordinal.
-/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section

section Exec

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {D : Finset Nat} {cD : Option Nat} {start id : Nat} {nD : Nat}
  [hK : Fact K.NoBarArrive]

/-- **Every loop lane of the CTA has the arrival of the ordinal a passed loop lane passed.** -/
theorem D_member_arrival (hX : Consistent L K A mem0 X) (hS : PhSources L X D cD start id)
    (hD : D ⊆ Finset.range (warps L.block)) (hcard : D.card = nD) (hnD : nD ≠ warps L.block)
    (hcD : target L.block cD = .ok nD) {f : EvId} {pc : Nat} {cnt : Option Nat}
    (hf : X.IsBarrier f id cnt pc) (hpassed : f.2 + 1 < (X.tr f.1).length)
    (hwf : (f.1 % L.block) / 32 ∈ D) {g : Nat} (hcta : g / L.block = f.1 / L.block)
    (hw : (g % L.block) / 32 ∈ D)
    (hexited : (∃ j pcx, X.get (g, j) = some ⟨pcx, .exit⟩) →
      ∃ i pc' cnt', X.IsBarrier (g, i) id cnt' pc' ∧
        ((X.tr g).take i).countP (Execution.isBarId id) =
          ((X.tr f.1).take f.2).countP (Execution.isBarId id)) :
    ∃ i pc' cnt', X.IsBarrier (g, i) id cnt' pc' ∧
      ((X.tr g).take i).countP (Execution.isBarId id) =
        ((X.tr f.1).take f.2).countP (Execution.isBarId id) := by
  by_cases hex : ∃ j pcx, X.get (g, j) = some ⟨pcx, .exit⟩
  · exact hexited hex
  obtain ⟨key, hkf, hdone⟩ := ctaBarDone_of_returned hX hf hpassed
  have hfg : f.1 < L.threads := hkf.1
  have hb0 : 0 < L.block := block_pos_of_thread_lt hfg
  have hc : f.1 / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb0).mpr hfg
  have hlocal : g % L.block < L.block := Nat.mod_lt _ hb0
  have hkeq := D_arrival_key hX hS hD hcard hnD hcD hf hwf (CtaBarK.arrival hkf)
  have hid : key % 16 = id := by
    obtain ⟨count', pc'', he'⟩ := hkf.2.1
    exact (Kind.bar.inj (Event.mk.inj (Option.some.inj (he'.symm.trans hf))).2).1
  have hlt16 : id < 16 := by
    obtain ⟨index, s, warp, cnt', lanes, g', hr, hs, hm, hphase, t, ht⟩ := hkf.2.2
    have := hX.ctaBar.arrival_id_lt hr
    rw [hid] at this
    exact this
  set φ := ((X.tr f.1).take f.2).countP (Execution.isBarId id) with hφ
  have hmod : (id + 16 * φ) % 16 = id := by omega
  have hdiv : (id + 16 * φ) / 16 = φ := by omega
  have hrel : Released L.block (X.barriers (f.1 / L.block)) id φ := by
    unfold CtaBarDone at hdone
    rw [hkeq, hmod, hdiv] at hdone
    exact hdone
  have hprot := hS.protocol hX hc
  have hthr : f.1 / L.block * L.block + g % L.block = g := by
    rw [← hcta, Nat.mul_comm]
    exact Nat.div_add_mod g L.block
  have hno : ∀ j pc', X.get (f.1 / L.block * L.block + g % L.block, j) ≠
      some ⟨pc', .exit⟩ := by
    rw [hthr]
    exact fun j pcx h => hex ⟨j, pcx, h⟩
  obtain ⟨-, -, last, hlast⟩ := hX.ctaBar.2 (f.1 / L.block) hc
  have hlt : φ < (last.slots id).generation := released_generation_lt hlast hrel
  have hlive : g % L.block ∉ last.exited := by
    intro hm
    obtain ⟨a, ha⟩ := run_exited_mem hlast hm
    obtain ⟨-, hy, pcx, hget⟩ := (hX.ctaBar.2 (f.1 / L.block) hc).2.1 _ ha
    have hae : a = (f.1 / L.block * L.block + g % L.block, a.2) := Prod.ext hy rfl
    exact hno a.2 pcx (hae ▸ hget)
  obtain ⟨i, cnt', lanes, e', hi, hmem, hord, -⟩ := completed_D_record hD hcard hnD hcD hprot
    hlast hlt hlocal hw hlive
  obtain ⟨s1, t1, hat, hp1⟩ := run_at_record hlast hi
  obtain ⟨hql, hq2, hqw, ⟨pce, hbar⟩, hord', -⟩ := record_ordinal hX hc hlast hi hat
    (q := (g % L.block, e')) hmem
  have hee : e'.1 = g := by
    have := hq2
    simp only at this
    rw [this, hthr]
  obtain ⟨mode, hget⟩ := hbar
  have hbar' : X.IsBarrier e' id cnt' pce := hX.isBarrier_of_arrival hK.out ⟨mode, hget⟩
  obtain ⟨e1, e2⟩ := e'
  simp only at hee
  subst hee
  rw [hord'] at hord
  exact ⟨e2, pce, cnt', hbar', hord⟩

end Exec

end
end PTX.NamedBar
