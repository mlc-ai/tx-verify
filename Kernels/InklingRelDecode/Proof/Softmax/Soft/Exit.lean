-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.Lane

@[expose] public section

/-! # The lane enters the epilogue typed

At the first event of a data lane from 2565 on, the value thread machine is at the first state of
the epilogue, the strict window of the softmax ends in the stop state at which the event fires,
and that stop state has the tags of the lane (`EpiAt`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The entry of the epilogue**: the first event of a data lane from 2565 on, after the barrier
at 573 and the events of the softmax's window. -/
theorem epi_at (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) (hv : Iface.LateValues L X)
    (lane : g % L.block < 128)
    {j i : Nat} {e5 ei : Event} (hji : j < i) (he5 : X.get (g, j) = some e5)
    (hei : X.get (g, i) = some ei) (hge : 2565 ≤ ei.pc)
    (hpcw : ∀ i' ev, j < i' → i' < i → X.get (g, i') = some ev → ev.pc < 2565)
    (hE : ∀ t0 t1 u, Run kernel Assumptions.all L g {} ((X.tr g).take j) (some t0) →
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 t1 →
      EStep kernel Assumptions.all L g t1 e5 (some u) →
      u.pc = 574 ∧ u.fault = none ∧ TypedF Iface.entryEnv u)
    (hLW : ∀ i' ev, j < i' → i' < i → X.get (g, i') = some ev → Strict.LWf ev) :
    EpiAt Q L X g i := by
  have hg := Frame.lt_of_get hX hei
  have hji : j + 1 < i := by
    by_contra hc
    obtain rfl : i = j + 1 := by omega
    obtain ⟨o, hr⟩ := hX.thr g hg
    obtain ⟨t0, t1, u, hrun, htau, hes, hru⟩ :=
      run_split hr he5 (List.getElem?_eq_some_iff.mp hei).1
    obtain ⟨hu574, -, -⟩ := hE t0 t1 u hrun htau hes
    obtain ⟨o1, hes1⟩ := next_step hr hru hei hu574
    have := EventFrame.estep_source_pc hes1
    omega
  have hC : ∀ g < L.threads, (lateThread Q L g).SoundU := fun g hg => lateThread_sound hp hg
  obtain ⟨σ, hs, hok', t0, t1, o', hrun, htau, hgd, hq, hes⟩ :=
    soft_window hp hX hf base hv lane hji he5 hei hpcw hE hLW
  obtain ⟨ins, hc, hfire⟩ := Code.fired_of_good (hC g hg) hgd hes
  have hpcσ := EventFrame.fires_source_pc hfire
  obtain ⟨w, ent, n, hentok, ⟨s, rfl⟩ | ⟨z, rfl⟩⟩ := hok'
  · exfalso
    have hsite : s.c.site ≠ .epilogue := by
      intro h
      have := hgd.2.2
      simp [epiExit, h] at this
    have := Softmax.Site.pc_range s.c.site
    have h1 : (lateThread Q L g).pc (softSt w ent s n) = s.c.site.pc := rfl
    rcases this with h | h
    · omega
    · exact hsite h
  · obtain ⟨hb0, -, hob, hlb⟩ := hentok
    refine ⟨⟨w, ent, z, n, hs, hb0, hob, hlb⟩, ?_, ?_⟩
    · intro d ei' hd hei'
      rw [hs] at hd
      obtain rfl := Option.some.inj (Option.some.inj hd)
      obtain rfl := Option.some.inj (hei'.symm.trans hei)
      exact ⟨t0, t1, o', hrun, htau, hgd, hes⟩
    · intro d t0' t1' hd hrun' htau' hgd'
      rw [hs] at hd
      obtain rfl := Option.some.inj (Option.some.inj hd)
      obtain rfl := Option.some.inj (Run.det hrun' hrun)
      obtain rfl := stop_unique htau' htau (Code.stops_of_good (hC g hg) hgd')
        (stops_of_estep hes)
      exact hq

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
