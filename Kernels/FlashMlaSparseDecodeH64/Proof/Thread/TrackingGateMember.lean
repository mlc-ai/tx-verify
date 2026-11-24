-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingGateRelease
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingInitSources

@[expose] public section

/-! # Participation in the actual prologue gate -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.CtaBarrier

private instance : Fact kernel.NoBarArrive := ⟨by
  unfold Kernel.NoBarArrive
  decide +kernel⟩

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- A released prologue gate supplies a real gate event for each lane of that CTA. -/
theorem gate_member_zero {X : Execution} {g : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hg : g < L.threads)
    (hRelease : Released L.block (X.barriers (g / L.block)) 0 0) :
    ∃ j, X.get (g, j) = some ⟨97, .bar 0 none .sync⟩ ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.prologue .barrier)) ∧
      CtaBarK L X (g, j) 0 := by
  by_cases hExit : ∃ j tag, X.get (g, j) = some ⟨tag, .exit⟩
  · obtain ⟨i, _, he⟩ := hExit
    obtain ⟨j, hj, hGate, hd⟩ := exit_follows_gate hpre hX (fun g hg => (hs g hg).machine) he
    exact ⟨j, hGate, hd, (passed_gate_zero hpre hX hs hGate hd (hj.trans (PTX.len_of_get he))).1⟩
  · have hc := NamedBar.cta_lt hg
    have hb : 0 < L.block := by rw [hpre.block]; decide
    have hgLocal : g % L.block < L.block := Nat.mod_lt _ hb
    have hw : g % L.block / 32 ∈ Finset.range 12 := by
      rw [hpre.block] at *
      exact Finset.mem_range.mpr (by omega)
    have hbound : ∀ w ∈ Finset.range 12, w < L.block / 32 := by
      rw [hpre.block]
      exact fun w hw => Finset.mem_range.mp hw
    have hthread : g / L.block * L.block + g % L.block = g := by
      rw [Nat.mul_comm, Nat.div_add_mod]
    obtain ⟨e, _, hh, _, _, hKey⟩ := NamedBar.released_member_key hX (by decide : 0 < 12)
      (by rw [hpre.block]; rfl) hc (by decide) hRelease
      (fun i hi => zero_generation_protocol hpre hX hs hc hi) (by decide) hbound hgLocal hw
      (fun j tag => by rw [hthread]; exact fun he => hExit ⟨j, tag, he⟩)
    rw [hthread] at hh
    obtain ⟨e1, j⟩ := e
    change e1 = g at hh
    subst e1
    obtain ⟨he, hd⟩ := zero_generation_source hpre hX hs hKey.arrival
    exact ⟨j, he, hd, hKey⟩

/-- A followed role event obtains its gate's actual release of generation zero. -/
theorem gate_of_followed_role {X : Execution} {g i : Nat} {d : Machine.ThreadD} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d)) (hrole : ∀ s, d ≠ .prologue s) :
    ∃ j, j + 1 < i ∧ CtaBarK L X (g, j) 0 ∧ Released L.block (X.barriers (g / L.block)) 0 0 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨j, hj, hGate, hst⟩ := gate_in_followed_prefix hX (hs g hg).machine he hd hrole
  obtain ⟨hKey, hRelease⟩ := passed_gate_zero hpre hX hs hGate hst (hj.trans (PTX.len_of_get he))
  exact ⟨j, hj, hKey, hRelease⟩

/-- The real CTA prologue gate publishes a known real initializer before a followed role event.
Its proof only needs the two actual endpoints and the released gate history. -/
theorem init_before_followed_role {X : Execution} {g h i k : Nat} {j : Fin 23} {d : Machine.ThreadD}
    {e f : Event} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hf : X.get (h, k) = some f)
    (hInit : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue (.init j))))
    (hUser : Frame.stateAt (Machine.code P L) X h k = some (some d)) (hrole : ∀ s, d ≠ .prologue s)
    (hcta : ctaOf L g = ctaOf L h) :
    baseCausality L X (g, i) (h, k) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨b, hb, hkey, hrelease⟩ := gate_of_followed_role hpre hX hs hf hUser hrole
  change g / L.block = h / L.block at hcta
  rw [← hcta] at hrelease
  obtain ⟨a, _, ha, hw⟩ := gate_member_zero hpre hX hs hg hrelease
  exact .single (.inr (.inl ⟨⟨hg, Frame.lt_of_get hX hf, hcta⟩, 0, a, b,
    hw.arrival, hkey, RingInitSources.init_before_gate hInit ha, by omega, PTX.len_of_get hf⟩))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
