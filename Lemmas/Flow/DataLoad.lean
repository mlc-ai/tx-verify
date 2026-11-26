-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataOver
public import Lemmas.Flow.Async
public import Lemmas.Flow.EventCont
public import Lemmas.Flow.RunFrame
public import Lemmas.Flow.SegStop

@[expose] public section

/-! # A value machine's data steps at loads and stores

A proof tool, generic over the kernel, for `DataStep` (`Lemmas/Flow/DataOver.lean`). It reduces
a site's data step to the local code after its event, from the concrete state the event leaves:

* `DataStep.nil`: every successor has no data facts;
* `DataStep.load`: a load into `a.regs`; before its last element the successors have no data
  facts, after it the state is the start state with the loaded values set and the next pc;
* `DataStep.store`: a one-source store; the state is the start state at the next pc.

`holds_setRegs_off` carries facts on other registers across the loaded values, `holds_setRegs_zip`
states the loaded ones. `Reach p F G`: from facts `F` at `p`, the first state that performs an event
holds `G`, or the thread is dead; a run to an event gives it (`SegD.reach`). -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- Facts on registers a load does not write hold after it. -/
theorem holds_setRegs_off {t : TState} {ds : List Nat} {vs : List Value}
    {F : List (Nat × Value)} (h : Holds t.regs F) (hoff : ∀ q ∈ F, q.1 ∉ ds) :
    Holds (setRegs t ds vs).regs F :=
  holds_of_mem fun r v hm => by
    rw [setRegs_other t ds vs r (hoff (r, v) hm)]; exact holds_mem h hm

/-- A data step where no successor has data facts. -/
theorem DataStep.nil {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    (h : ∀ e d', C'.next d e = some (some d') → dF d' = []) : DataStep C' dF d := by
  intro t e u d' ins _ _ _ _ hn
  exact .inl fun _ _ _ => by rw [h e d' hn]; trivial

/-- **The data step of a load**: from the state after its last element. -/
theorem DataStep.load {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {a : MemAccess} {Q : Value → C'.D → Prop}
    (hc : K.code[C'.pc d]? = some ⟨none, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
    (he : a.ext = .same)
    (hmid : C'.sub d + 1 < a.regs.length → ∀ e d', C'.next d e = some (some d') → dF d' = [])
    (hN : ¬ C'.sub d + 1 < a.regs.length → ∀ x bs d',
      C'.next d ⟨C'.pc d, .rd x bs⟩ = some (some d') → ∃ v, rebuild 3 bs = .ok v ∧ Q v d')
    (hrun : C'.inv d → ∀ v d' t, Q v d' → C'.AtD d t →
      let u := { setRegs t a.regs (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] }
      (∀ t', Relation.ReflTransGen (Tau K A L g) u t' → Stops K A L g t' →
        Holds t'.regs (dF d')) ∨ Machine.Dead (K := K) (A := A) (L := L) (g := g) u) :
    DataStep C' dF d := by
  intro t e u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  by_cases hm : C'.sub d + 1 < a.regs.length
  · exact .inl fun _ _ _ => by rw [hmid hm _ d' hn]; trivial
  · obtain ⟨v, hv, hq⟩ := hN hm x bs d' hn
    have hm' : ¬ t.sub + 1 < a.regs.length := by rw [hat.2.1]; exact hm
    have hu : afterLoad t a.regs bs =
        { setRegs t a.regs (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] } := by
      simp [afterLoad, hv, hm']
    rw [hu]
    exact hrun hi v d' t hq hat

/-- **The data step of a one-source store**: from the start state at the next pc. -/
theorem DataStep.store {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {a : MemAccess} (hc : K.code[C'.pc d]? = some ⟨none, .mem a⟩) (hk : a.kind = .store)
    (hs : a.srcs.length = 1)
    (hrun : C'.inv d → ∀ e d' t, C'.next d e = some (some d') → C'.AtD d t →
      (∀ t', Relation.ReflTransGen (Tau K A L g) { t with pc := t.pc + 1, sub := 0 } t' →
        Stops K A L g t' → Holds t'.regs (dF d')) ∨
        Machine.Dead (K := K) (A := A) (L := L) (g := g) { t with pc := t.pc + 1, sub := 0 }) :
    DataStep C' dF d := by
  intro t e u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨-, -, -, rfl⟩ := fires_st hk hf
  have hu : afterStore t a.srcs = { t with pc := t.pc + 1, sub := 0 } := by
    simp [afterStore, hs]
  rw [hu]
  exact hrun hi e d' t hn hat

/-- The loaded values are in their registers. -/
theorem holds_setRegs_zip : ∀ (t : TState) (ds : List Nat) (vs : List Value), ds.Nodup →
    Holds (setRegs t ds vs).regs (ds.zip vs)
  | _, [], _, _ => trivial
  | _, _ :: _, [], _ => trivial
  | t, d :: ds, v :: vs, hnd => by
    have hnd' := List.nodup_cons.mp hnd
    refine ⟨?_, holds_setRegs_zip (setReg t d v) ds vs hnd'.2⟩
    show (setRegs (setReg t d v) ds vs).regs d = some v
    rw [setRegs_other _ _ _ _ hnd'.1]; simp [setReg]

/-- From facts `F` at `p`: the first state that performs an event holds `G`, or the thread is
dead. -/
def Reach (K : Kernel) (A : List Assumption) (L : Launch) (g p : Nat)
    (F G : List (Nat × Value)) : Prop :=
  ∀ u, At u p F → (∀ t', Relation.ReflTransGen (Tau K A L g) u t' → Stops K A L g t' →
    Holds t'.regs G) ∨ Machine.Dead (K := K) (A := A) (L := L) (g := g) u

theorem Reach.weaken_start {p : Nat} {F F' G : List (Nat × Value)} (h : Reach K A L g p F G)
    (hF : ∀ R, Holds R F' → Holds R F) : Reach K A L g p F' G :=
  fun u hu => h u (At.mono hu (hF _ hu.2.2.2.2))

/-- **A run to an event reaches its end facts** (restated under the run's condition). -/
theorem SegD.reach {n s b : Nat} {F G G' : List (Nat × Value)} {C : Prop} {ins : Instr}
    (h : SegD K A L g n s F b G C) (hc : K.code[b]? = some ins) (hg : Code.GuardTrue G ins.guard)
    (hl : ins.op.isLocal = false) (hG : C → ∀ R, Holds R G → Holds R G') :
    Reach K A L g s F G' := by
  intro u hu
  by_cases hC : C
  · obtain ⟨t2, hr, ht2⟩ := (h u hu).1 hC
    exact .inl (DataStep.of_run (run_rtg hr) (stops_of_at ht2 hc hg hl) (hG hC _ ht2.2.2.2.2))
  · exact .inr ((h u hu).2 hC)

end
end PTX.Flow.Code
