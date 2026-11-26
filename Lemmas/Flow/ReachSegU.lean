-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ReachFrame
public import Lemmas.Flow.Havoc
public import Lemmas.Flow.DataElems
public import Lemmas.Flow.NcLoadU
public import Lemmas.Flow.Next

@[expose] public section

/-! # `Reach` through control segments, and data steps of `.nc` loads and polls

Proof tools, generic over the kernel, for value machines whose data facts cross control code:

* `SegU.reach_then`: a control segment (`SegU`) followed by a `Reach`;
* `SegU.frameSet`: a control segment keeps the facts on registers a frame set does not write;
* `Reach.append`: two `Reach`es from the same facts;
* `DataStep.loadNc`: a scalar `.nc` load (the successor is the state after the load);
* `DataStep.wait`: an `mbarrier` wait (the successor holds the wait's predicate). -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **A control segment followed by a `Reach`.** -/
theorem SegU.reach_then {s q : Nat} {F G H : List (Nat × Value)}
    (h : SegU K A L g s F q G) (hR : Reach K A L g q G H) : Reach K A L g s F H := by
  intro u hu
  rcases h u hu with ⟨t2, hr, ht2⟩ | hd
  · rcases hR t2 ht2 with h2 | hd
    · refine .inl fun t' hr' hs => h2 t' ?_ hs
      rcases rtg_tau_total hr hr' with h' | h'
      · exact h'
      · rcases Relation.ReflTransGen.cases_head h' with e | ⟨c, hc, -⟩
        · exact e ▸ .refl
        · exact absurd hc (not_tau_of_stops hs)
    · exact .inr (dead_of_rtg hr hd)
  · exact .inr hd

/-- **A control segment keeps the facts a frame set does not write.** -/
theorem SegU.frameSet (hA : RulesFrame A) {S : List Nat} {s q : Nat}
    {F G H : List (Nat × Value)} (h : SegU K A L g s F q G)
    (hB : frameSetB K S (H.map Prod.fst) = true) (hS : ∀ pc ∈ S, Assumption.SegFreePc A pc)
    (hs : (S.contains s || evAtB K s) = true) : SegU K A L g s (F ++ H) q (G ++ H) := by
  intro t ht
  obtain ⟨htp, -, -, -, htF⟩ := id ht
  have hF := (holds_append _ _ _).mp htF
  rcases h t (At.mono ht hF.1) with ⟨u, hr, hu⟩ | hd
  · obtain ⟨-, -, -, -, huG⟩ := id hu
    exact .inl ⟨u, hr, At.mono hu ((holds_append _ _ _).mpr
      ⟨huG, (rtg_frameSet hA hB hS (htp ▸ hs) hF.2 hr).2⟩)⟩
  · exact .inr hd

/-- **Two `Reach`es from the same facts.** -/
theorem Reach.append {p : Nat} {F G1 G2 : List (Nat × Value)} (h1 : Reach K A L g p F G1)
    (h2 : Reach K A L g p F G2) : Reach K A L g p F (G1 ++ G2) := by
  intro u hu
  rcases h1 u hu with a | hd
  · rcases h2 u hu with b | hd
    · exact .inl fun t' hr hs => (holds_append _ _ _).mpr ⟨a t' hr hs, b t' hr hs⟩
    · exact .inr hd
  · exact .inr hd

/-- **The data step of a scalar `.nc` load**: from the state after it (bytes that do not rebuild
fault). -/
theorem DataStep.loadNc {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {a : MemAccess} {r base w : Nat} {sp : Space}
    (hc : K.code[C'.pc d]? = some ⟨none, .mem a⟩)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hr : a.regs = [r]) (hs : C'.inv d → C'.sub d = 0)
    (ha : C'.inv d → C'.acc d = [])
    (hrun : C'.inv d → ∀ x bs v d' t, C'.next d ⟨C'.pc d, .nc x bs⟩ = some (some d') →
      C'.AtD d t →
      (∀ t', Relation.ReflTransGen (Tau K A L g)
        { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] } t' → Stops K A L g t' →
        Holds t'.regs (dF d')) ∨ Machine.Dead (K := K) (A := A) (L := L) (g := g)
        { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] }) :
    DataStep C' dF d := by
  intro t e u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_loadNc hru hloc hb hk hsem hnc hf
  rw [hr]
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr (Machine.dead_of_fault (K := K) (A := A) (L := L) (g := g) (f := f)
      (u := afterLoad t [r] bs) (by simp only [afterLoad, hv]))
  | ok v =>
    rw [afterLoad_ok (hat.2.1.trans (hs hi)) (hat.2.2.1.trans (ha hi)) hv]
    exact hrun hi x bs v d' t hn hat

/-- **The data step of an `mbarrier` wait**: from the state with the wait's predicate. -/
theorem DataStep.wait {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {p base : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope}
    (hc : K.code[C'.pc d]? = some ⟨none, .mbarWait p base off par acq sc⟩)
    (hrun : C'.inv d → ∀ m q ok s d' t, C'.next d ⟨C'.pc d, .wait m q ok acq s⟩ = some (some d') →
      C'.AtD d t →
      (∀ t', Relation.ReflTransGen (Tau K A L g) (PTX.next (setReg t p (.pred ok))) t' →
        Stops K A L g t' → Holds t'.regs (dF d')) ∨
        Machine.Dead (K := K) (A := A) (L := L) (g := g) (PTX.next (setReg t p (.pred ok)))) :
    DataStep C' dF d := by
  intro t e u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  rw [← hat.1] at hf
  obtain ⟨m, q, ok, s, rfl, rfl⟩ := fires_wait hf
  rw [hat.1] at hn
  exact hrun hi m q ok s d' t hn hat

end
end PTX.Flow.Code
