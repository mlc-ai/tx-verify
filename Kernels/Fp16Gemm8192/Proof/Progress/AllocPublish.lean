-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.NextPlain
import Lemmas.Tmem.AllocResultDependency

@[expose] public section

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow PTX.Tmem.Pair

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A completed allocation either has a result or leaves the representative lane at its ready
result store. -/
theorem allocation_publication (hpre : Pre P L mem0) (ht : ThreadFacts L X)
    (hX : Consistent L kernel Prod mem0 X) (hub : ¬ HasUb X)
    {i : EvId} {pc : Nat} {group : CtaGroup} {dst : Option Loc} {count : Nat}
    (he : X.get i = some ⟨pc, .tc (.resource group dst (.alloc count))⟩)
    (hr : ReturnReady L X i) :
    (∃ store addr, AllocResult L X store i addr) ∨
      ∃ g w, SameWarp L i.1 g ∧ Frame.Pending L X g ∧ Step.Released L X g ∧
        Frame.stateAt (code L) X g (X.tr g).length = some (some (.inl ⟨.allocWrite, w⟩)) := by
  obtain ⟨cta, r, hrec, lane, hlane⟩ := hr.1
  have hv := ((hX.tmemPair.1 cta).1 r hrec).2.2
  have hp := hv.2.2.1 lane
  rw [hlane, he] at hp
  obtain ⟨hpc, hgroup, hdst, hreq⟩ := by
    simpa only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq]
      using hp.symm
  have hwarp := WarpRequest.event_sameWarp hv lane 0
  rw [hlane] at hwarp
  let g := (r.own.event L 0).1
  let j := (r.own.event L 0).2
  have hget := hv.2.2.1 0
  rw [hpc, hgroup, hdst, hreq] at hget
  change X.get (g, j) = some ⟨pc, .tc (.resource group dst (.alloc count))⟩ at hget
  have hg := hwarp.1.2.1
  have hlen : j < (X.tr g).length := len_of_get hget
  obtain ⟨hwg, _, _, hshape, _⟩ := ht.tmem_event hg (noUb_of hub g) hget
  have hzero : g % L.block = 0 := by
    have hmod : g % L.block = r.own.warp * 32 := by
      have hlt : r.own.warp * 32 < L.block := by have := hv.2.1; omega
      simp only [g, WarpRequest.event, Fin.val_zero, Nat.add_zero]
      rw [Nat.mul_comm r.own.cta, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    change g % L.block / 32 = 0 at hwg
    rw [hmod, Nat.mul_div_cancel _ (by decide)] at hwg
    simp [hmod, hwg]
  have hcount : tmemOps ((X.tr g).take j) = 0 := by
    have hn := lt_of_tmemShape hshape
    generalize tmemOps ((X.tr g).take j) = n at hshape hn
    interval_cases n <;> simp_all [TmemShape]
  have hlead : laneOf L g = 0 := by simp [laneOf, hzero]
  have hfirst := (Prologue.first_iff L g).2 hzero
  obtain ⟨d, hs⟩ := Frame.state_of_noUb ht.sound hX ht.tracked hub hget
  obtain ⟨t, ins, o, hat, _, hcode, hfire⟩ := Frame.fired_site ht.sound hX hget hs
  have hsite := tmem_site hat hcode hfire (e := ⟨pc, .tc (.resource group dst (.alloc count))⟩) rfl
  cases d with
  | inr role =>
    cases role with
    | loader => exact hsite.elim
    | mma => exact hsite.elim
    | sched => exact hsite.elim
    | cons d =>
      have hops := (tmem_ops_fact hpre hX hg (noUb_of hub g) hs).1
      change tmemOps ((X.tr g).take j) = _ at hops
      rw [hcount] at hops
      rcases hsite with h | h <;> simp [h, hwg, ThreadD.tmemOps] at hops
  | inl d =>
    change d.site = .alloc at hsite
    have hj := (stateAt_prologue hpre hX (g := g) hg hlen.le hs).1
    have h20 : j = 20 := by
      simpa [Prologue.index, hsite, hfirst] using hj
    by_cases hstored : 21 < (X.tr g).length
    · obtain ⟨col, ha, hw, _⟩ := first_alloc hpre hX hg hzero hstored
      have hsame := ha
      rw [← h20, hget] at hsame
      obtain ⟨htag, _, haddr, h512⟩ := by
        simpa only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq]
          using hsame
      have hc := (WarpRequest.event_props hv 0).1
      have hstore : X.get (g, j + 1) = some
          ⟨r.own.pc, .wr { loc := ⟨.shared, g / L.block, L.sharedBase⟩, size := 4 }
            (PTX.Proof.b32 col).toBytes⟩ := by rw [h20, hpc, htag]; exact hw
      left
      exact ⟨_, _, hlane ▸ AllocResult.of_warpRequest hv (hreq.trans h512)
        (hdst.trans haddr) rfl hc hstore lane⟩
    · have hend : (X.tr g).length = j + 1 := by omega
      have hstate := Frame.stateAt_succ (C := code L) hget
      rw [hs] at hstate
      have hs' : Frame.stateAt (code L) X g (X.tr g).length =
          some (some (.inl ⟨.allocWrite, d.w⟩)) := by
        rw [hend, hstate]
        change Prologue.next L g d ⟨pc, .tc (.resource group dst (.alloc count))⟩ = _
        simp [Prologue.next, hsite, hlead]
      have hret : ReturnReady L X (g, j) := by
        refine ⟨⟨cta, r, hrec, 0, rfl⟩, fun _ => ?_⟩
        obtain ⟨ws, hcomp, w, hw, lane', hwLane⟩ :=
          hr.2 ⟨pc, group, dst, .alloc count, he, trivial⟩
        obtain ⟨grp', hv'⟩ := hcomp.valid hX.tmemPair hw
        have hwEq := WarpRequest.Valid.ext hv hv' (hlane.trans hwLane.symm)
        subst w
        exact ⟨ws, hcomp, r.own, hw, 0, rfl⟩
      right
      refine ⟨g, d.w, hwarp, ⟨hg, ?_, ?_⟩, ⟨fun pc' kind hlast _ => ?_⟩, hs'⟩
      · exact not_canceled_of_peer hX hg (by
          intro hn
          simp [hn, Execution.get, g] at hget) rfl
      · intro tag hexit
        have hexit' : X.get (g, j) = some ⟨tag, .exit⟩ := by
          have hk : (X.tr g).length - 1 = j := by omega
          rw [← hk]
          change (X.tr g)[(X.tr g).length - 1]? = _
          rw [← List.getLast?_eq_getElem?]
          exact hexit
        rw [hget] at hexit'
        cases hexit'
      · rw [show (X.tr g).length - 1 = j by omega, hget] at hlast
        cases hlast
        rw [show (X.tr g).length - 1 = j by omega]
        exact ReturnReady.ready hX.tmemPair hget hret (fun _ _ h => (h hlead).elim)

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
