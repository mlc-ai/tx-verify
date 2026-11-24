-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Lib.BarEarly

@[expose] public section

/-!
# Every participant has the early arrival that a passed thread passed

The generic part of the base-word chain. `BarEarly.early_same_ordinal_baseCausality` takes both
arrivals as given; this file gives the arrival of every participant thread of the CTA at a
passed source ordinal `φ ≤ N` (`early_member_arrival`): a thread that never exits has it by the
release of generation `φ` (`released_member_key`, with the group's protocol of the records before
the completion from `early_protocol`), and a thread that exits has it by the kernel's own
statement `hexited` (a thread that exits has made all its early arrivals).

Local generic lemmas, for promotion to `Lemmas/Protocol`.
-/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  [hK : Fact K.NoBarArrive]

/-- **Every participant thread of the CTA has an arrival of the source ordinal a passed thread
passed**, when the ordinal is at most `N`. A thread that exits has it from `hexited`. -/
theorem early_member_arrival (hX : Consistent L K A mem0 X) {n : Nat} (hn : 0 < n)
    {count : Option Nat} (hcount : target L.block count = .ok n) {p : Finset Nat}
    (hcard : p.card = n) (hbound : ∀ w ∈ p, w < L.block / 32) {id N : Nat} (hid : id < 16)
    (hS : EarlySources L X count p id N) {f : EvId} {pc : Nat}
    (hf : X.IsBarrier f id count pc) (hpassed : f.2 + 1 < (X.tr f.1).length)
    (hN : ((X.tr f.1).take f.2).countP (Execution.isBarId id) ≤ N) {g : Nat}
    (hcta : g / L.block = f.1 / L.block) (hw : (g % L.block) / 32 ∈ p)
    (hexited : (∃ j pcx, X.get (g, j) = some ⟨pcx, .exit⟩) →
      ∃ i pc', X.IsBarrier (g, i) id count pc' ∧ ((X.tr g).take i).countP (Execution.isBarId id) =
        ((X.tr f.1).take f.2).countP (Execution.isBarId id)) :
    ∃ i pc', X.IsBarrier (g, i) id count pc' ∧
      ((X.tr g).take i).countP (Execution.isBarId id) =
        ((X.tr f.1).take f.2).countP (Execution.isBarId id) := by
  by_cases hex : ∃ j pcx, X.get (g, j) = some ⟨pcx, .exit⟩
  · exact hexited hex
  obtain ⟨key, hkf0, hdone⟩ := ctaBarDone_of_returned hX hf hpassed
  have hfg : f.1 < L.threads := hkf0.1
  have hb0 : 0 < L.block := block_pos_of_thread_lt hfg
  have hc : f.1 / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb0).mpr hfg
  have hthr : f.1 / L.block * L.block + g % L.block = g := by
    rw [← hcta, Nat.mul_comm]
    exact Nat.div_add_mod g L.block
  have hno : ∀ j pcx, X.get (f.1 / L.block * L.block + g % L.block, j) ≠
      some ⟨pcx, .exit⟩ := by
    rw [hthr]
    exact fun j pcx h => hex ⟨j, pcx, h⟩
  obtain ⟨-, -, last, hlast⟩ := hX.ctaBar.2 (f.1 / L.block) hc
  set φ := ((X.tr f.1).take f.2).countP (Execution.isBarId id) with hφ
  have hkid : key % 16 = id := by
    obtain ⟨count', pc'', he'⟩ := hkf0.2.1
    exact (Kind.bar.inj (Event.mk.inj (Option.some.inj (he'.symm.trans hf))).2).1
  have hgen := hkf0.2.2
  rw [hkid] at hgen
  have hφG : φ ≤ key / 16 := ordinal_le_generation hX hc hgen
  have hrel : Released L.block (X.barriers (f.1 / L.block)) id (key / 16) := by
    have hd' := hdone
    unfold CtaBarDone at hd'
    rw [hkid] at hd'
    exact hd'
  have hlt : key / 16 < (last.slots id).generation := released_generation_lt hlast hrel
  have hrelφ : Released L.block (X.barriers (f.1 / L.block)) id φ :=
    released_of_lt hlast (by omega)
  obtain ⟨e, pc', he1, he, hcount', -⟩ := released_member_key hX hn hcount hc hid hrelφ
    (fun idx hcomp => early_protocol hX hS hc hN hcomp) hcard hbound (Nat.mod_lt g hb0) hw hno
  have hge : e.1 = g := by rw [he1, hthr]
  obtain ⟨e1, e2⟩ := e
  simp only at hge
  subst hge
  exact ⟨e2, pc', he, hcount'⟩

end
end PTX.NamedBar
