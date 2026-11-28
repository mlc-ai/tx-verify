-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.LaneNoUb
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Common.WorkerSound
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.BaseWord
import Kernels.InklingRelDecode.Proof.Common.WorkerReads
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.Sound
import Kernels.InklingRelDecode.Proof.Mma.Export.Broadcast
import Lemmas.Flow.StrictLift
import Lemmas.Flow.AllocTmpl

@[expose] public section

/-! # No undefined behaviour in a worker lane

A worker lane's states are the startup's and the dispatch warp's (`worker_lane`); the dispatch
warp's steps are strict, its templates are not undefined behaviour and it dies only on the exit
(`worker_stepFor`, `worker_safe`, `worker_live`), given the table's reference at the state, the
zero base word, the page words of the loader, and the broadcast word `7`. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- What a worker state at an event's index has: the table's reference, the zero base word, the
warp's range. -/
private theorem context (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) (hg : g < L.threads) {j w x d n}
    (hj : j ≤ (X.tr g).length) (nu : Frame.NoUbBefore X g j)
    (hd : Frame.stateAt (thread Q L) X g j = some (some (.inr ⟨.inl (.dispatch w x), d⟩, n))) :
    workerInv Q L g w x d n ∧ w = b32 0 ∧ 128 ≤ g % L.block ∧ x.toNat < 8 := by
  obtain ⟨low, eq⟩ := worker_warp hp hX hj hd
  refine ⟨(reached_table hf hg nu hd).2, recorded_zero hp hX base hj nu hd, low, ?_⟩
  have blk : g % L.block < 256 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  rw [eq, BitVec.toNat_ofNat]
  omega

/-- **A worker lane has no undefined behaviour.** -/
theorem worker_noUb (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) (words : RoleBytes L X)
    (pair : CountBytes Q L X) (hg : g < L.threads) (hw : 128 ≤ g % L.block)
    (he : X.get (g, k) = some e) (f : Fault) : e.kind ≠ .ub f := by
  have hC : ∀ g < L.threads, (thread Q L g).SoundU := fun g hg => thread_sound hp hg
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  refine lane_noUb hp hX hf base hg he
    (Rest := fun d => ∃ w x d' n, d = (.inr ⟨.inl (.dispatch w x), d'⟩, n)) ?_ ?_ ?_ ?_ ?_ f
  case refine_1 =>
    intro j d hj hd
    rcases worker_lane hp hX hw (by omega) hd with ⟨s, n, rfl⟩ | h
    exacts [.inl ⟨s, n, rfl⟩, .inr h]
  case refine_2 =>
    intro σ hσ _
    rcases worker_lane hp hX hw hk hσ with ⟨s, n, rfl⟩ | h
    exacts [.inl ⟨s, n, rfl⟩, .inr h]
  case refine_3 =>
    rintro j dj ej ⟨w, x, d', n, rfl⟩ hej hd nuj
    have hj : j ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp hej).1.le
    have nu : Frame.NoUbBefore X g j := fun u hu => nuj u (by omega)
    obtain ⟨inv, hw0, -, -⟩ := context hp hX hf base hg hj nu hd
    have sf : (workerCode Q L g w x).StepFor d' ej := by
      apply worker_stepFor hp hw0 d' ej inv
      · rintro r s rfl ⟨u, hu⟩ a bs hkd v hv
        have resp := loader_page_response hp hX hej hd inv.2.1
        unfold Loader.PageResponse at resp
        rw [hu, hkd] at resp
        obtain ⟨_, _, _, _, rfl⟩ := resp v hv
        exact ⟨_, rfl⟩
      · rintro r s rfl a b c y ok h
        have site : ej.pc = 2464 ∨ ej.pc = 2512 := by
          rcases h with rfl | rfl <;> simp [Flow.shfl_13, Flow.shfl_14]
        rcases h with rfl | rfl <;>
          · rw [Mma.Export.broadcast_seven hp hX hf words inv.1 hej site]
            rfl
    exact @Code.counted_stepFor _ _ L g _ Cls cls _ ej
      (@Code.glue_inr_stepFor _ _ L g (Startup.code Q L g) (Role ⊕ Startup.Entry)
        (Code.withStubs (frag Q L g) Startup.Entry.pc)
        (Code.gatedExit Startup.enterOf (sel L g)) (Sum.inl (Role.dispatch w x)) d' ej sf) n
  case refine_4 =>
    intro σ t ins ⟨w, x, d', n, hσ'⟩ hσ hJ hpc hgood hc f'
    subst hσ'
    obtain ⟨inv, hw0, -, hx⟩ := context hp hX hf base hg hk (Frame.noUbBefore_of_get hX he) hσ
    exact worker_safe hp hg hw0 hx d' inv hgood.1 hc f'
  case refine_5 =>
    rintro i d v ⟨w, x, d', n, rfl⟩ hv hd hJ nui hn
    have hik : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp hv).1
    have nu : Frame.NoUbBefore X g i := fun u hu => nui u (by omega)
    obtain ⟨inv, hw0, hw', hx⟩ := context hp hX hf base hg hik.le nu hd
    have hu : ∀ f, v.kind ≠ .ub f := fun f => nui i (by omega) v hv f
    obtain ⟨t, ins, o, hat, hi, hc, hfi⟩ := Frame.fired_siteU hC hX hv hd hu
    have pc := Frame.event_pcU hC hX hv hd hu
    have hn' : (workerCode Q L g w x).next d' v = none := by
      rcases d' with ds | ⟨i', s'⟩ <;>
        simpa [thread, Code.roleThread, Code.counted, Code.glue, workerCode, Code.loopGlue]
          using hn
    have blk : g % L.block < 256 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
    refine worker_live hp hg ⟨by omega, by omega⟩
      (decide (((X.tr g).take i).countP (Execution.isBarId 1) = 1)) d' inv hat hc hfi hu
      ?_ ?_ ?_ hn'
    · rintro r rfl hr ac bs hkd
      obtain ⟨pv, kv⟩ := v
      change kv = _ at hkd
      subst hkd
      change pv = r.site.pc at pc
      rw [hr] at pc
      have hv' : X.get (g, i) = some ⟨2340, .rd ac bs⟩ := by rw [← show pv = 2340 from pc]; exact hv
      simpa only [decide_eq_true_eq] using words hv'
    · rintro r s rfl hs ac bs hkd
      obtain ⟨pv, kv⟩ := v
      change kv = _ at hkd
      subst hkd
      have resp := loader_response hp hX pair hv hd
      rcases hs with hs | hs | ⟨u, hs⟩
      · simp only [Loader.PairResponse, hs] at resp
        rw [resp]
        exact ⟨_, rebuild_b32 _⟩
      · simp only [Loader.PairResponse, hs] at resp
        rw [resp]
        exact ⟨_, rebuild_b32 _⟩
      · change pv = s.site.pc at pc
        subst pc
        have site : s.site.pc = 2382 ∨ s.site.pc = 2399 := by
          rw [hs]; cases u <;> simp [Loader.Site.pc]
        obtain ⟨v', h1, -⟩ := Loader.page_rebuild (rest := dispatchRegs Q L g w x) hp hX hg hv hat
          hc hfi rfl inv.2.1 site
        exact ⟨v', h1⟩
    · rintro r s rfl hs ac bs hkd
      obtain ⟨pv, kv⟩ := v
      change kv = _ at hkd
      subst hkd
      change pv = s.site.pc at pc
      rw [hs] at pc
      have hv' : X.get (g, i) = some ⟨2423, .rd ac bs⟩ := by rw [← show pv = 2423 from pc]; exact hv
      obtain ⟨j, -, -, val⟩ := pair hv' (.inr rfl)
      rw [val]
      exact ⟨_, rebuild_b32 _⟩

end
end PTX.Kernels.InklingRelDecode.Proof
