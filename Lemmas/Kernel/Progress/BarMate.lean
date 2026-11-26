-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Bar
public import Lemmas.Protocol.NamedBarArrive
public import Lemmas.Step.CtaBarNamed

@[expose] public section

/-! # A released `bar.sync` releases a lane of its CTA with the same ordinal

Two lanes of a CTA whose last events are `bar.sync` on one named barrier, with the same ordinal
there, wait for one generation: the barrier has a group (`NamedBar.Shape`) whose arrivals are its
warps' (`NamedBar.Sources`), the generation of an arrival is its ordinal
(`NamedBar.Sources.arrival_key`), and an arrival of a released generation is recorded in it
(`NamedBar.Sources.key_of_released`). So when one lane's last event is ready, so is the other's
(`Sched.released_of_mate`). -/

namespace PTX.Sched

open PTX NamedBar CtaBarrier

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {count : Option Nat} {p : Finset Nat} {id : Nat}

/-- **A released `bar.sync` releases a lane of the CTA with the same ordinal.** -/
theorem released_of_mate (hX : Consistent L K A mem0 X) (hS : Sources L X count p id)
    (hG : Shape L count p id) {g h pc pc' : Nat} {cnt cnt' : Option Nat}
    (hh : h < L.threads) (hc : g / L.block = h / L.block)
    (hlg : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar id cnt .sync⟩)
    (hlh : X.get (h, (X.tr h).length - 1) = some ⟨pc', .bar id cnt' .sync⟩)
    (hord : ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) =
      ((X.tr h).take ((X.tr h).length - 1)).countP (Execution.isBarId id))
    (hrel : Step.Released L X g) : Step.Released L X h := by
  have hid := hG.id_lt
  have hrdy := hrel.ready pc _ hlg rfl
  have hcond := hrdy (.cond (∃ key, CtaBarK L X (g, (X.tr g).length - 1) key ∧
    CtaBarDone L X (g / L.block) key)) (by
      simp [Needs, hlg, KindNeeds, ctaBarNeeds])
  obtain ⟨key, hk, hd⟩ := hcond
  have hkey := hS.arrival_key hX hG hlg (CtaBarK.arrival hk)
  subst hkey
  simp only at hd
  unfold CtaBarDone at hd
  rw [show (id + 16 * ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id)) % 16
      = id by omega,
    show (id + 16 * ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id)) / 16
      = ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) by omega] at hd
  rw [hc, hord] at hd
  have hkh := hS.key_of_released hX hG (e := (h, (X.tr h).length - 1)) hlh hh hd
  refine ⟨fun pc2 k hget _ => ?_⟩
  have hget' : X.get (h, (X.tr h).length - 1) = some ⟨pc', .bar id cnt' .sync⟩ := hlh
  rw [hlh] at hget
  cases hget
  refine ready_of_released hX.ctaBar hlh
    (key := id + 16 * ((X.tr h).take ((X.tr h).length - 1)).countP (Execution.isBarId id))
    ⟨hkh.1, ⟨cnt', pc', ?_⟩, hkh.2.2⟩ ?_
  · rw [show (id + 16 * ((X.tr h).take ((X.tr h).length - 1)).countP (Execution.isBarId id)) % 16
      = id by omega]
    exact hlh
  · unfold CtaBarDone
    rw [show (id + 16 * ((X.tr h).take ((X.tr h).length - 1)).countP (Execution.isBarId id)) % 16
      = id by omega,
      show (id + 16 * ((X.tr h).take ((X.tr h).length - 1)).countP (Execution.isBarId id)) / 16
      = ((X.tr h).take ((X.tr h).length - 1)).countP (Execution.isBarId id) by omega]
    exact hd

end

end PTX.Sched
