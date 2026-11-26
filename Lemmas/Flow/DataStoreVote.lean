-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataElems
public import Lemmas.Flow.CtlStepsU
public import Lemmas.Flow.Vector

@[expose] public section

/-! # A value machine's data steps at vector stores and at `vote.any`

Proof tools, generic over the kernel, beside `DataStep.store` (`Lemmas/Flow/DataLoad.lean`):

* `DataStep.storeE`: a store of several source registers (one element per event); before the
  last element the successors' facts follow from the state's (the registers are unchanged), after
  it the state is the start state at the next pc;
* `DataStep.voteAny`: a `vote.any` event, whose result is written to its predicate destination;
  the successor's facts come from the state after the event with that predicate set. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **The data step of a store of several elements.** -/
theorem DataStep.storeE {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {a : MemAccess} (hc : K.code[C'.pc d]? = some ⟨none, .mem a⟩) (hl : (Op.mem a).isLocal = false)
    (hk : a.kind = .store)
    (hmid : C'.sub d + 1 < a.srcs.length → ∀ e d', C'.next d e = some (some d') →
      ∀ R, Holds R (C'.facts d) → Holds R (dF d'))
    (hrun : C'.inv d → ¬ C'.sub d + 1 < a.srcs.length → ∀ e d' t,
      C'.next d e = some (some d') → C'.AtD d t →
      (∀ t', Relation.ReflTransGen (Tau K A L g) { t with pc := t.pc + 1, sub := 0 } t' →
        Stops K A L g t' → Holds t'.regs (dF d')) ∨
        Machine.Dead (K := K) (A := A) (L := L) (g := g) { t with pc := t.pc + 1, sub := 0 }) :
    DataStep C' dF d := by
  intro t e u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨_, _, rfl, rfl⟩ := fires_st hk hf
  obtain ⟨hp, hsb, hac, hft, hF⟩ := hat
  by_cases hm : C'.sub d + 1 < a.srcs.length
  · have hm' : t.sub + 1 < a.srcs.length := by rw [hsb]; exact hm
    rw [afterStore_mid hm']
    exact .inl (stays_regs ⟨_, out_event (t := { t with sub := t.sub + 1 }) hft
      (by rw [show t.pc = C'.pc d from hp]; exact hc) rfl hl⟩ rfl (hmid hm _ d' hn _ hF))
  · have hm' : ¬ t.sub + 1 < a.srcs.length := by rw [hsb]; exact hm
    rw [afterStore_last hm']
    exact hrun hi hm _ d' t hn ⟨hp, hsb, hac, hft, hF⟩

/-- **The data step of a `vote.any`**: from the state after the event with its result set. -/
theorem DataStep.voteAny {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {ty dv pr neg mask}
    (hc : K.code[C'.pc d]? = some ⟨none, .warp ⟨.vote .any neg, ty, [some dv], [.reg pr],
      some mask⟩⟩)
    (hrun : C'.inv d → ∀ m p r d' t,
      C'.next d ⟨C'.pc d, .voteMode .any m p r⟩ = some (some d') → C'.AtD d t →
      (∀ t', Relation.ReflTransGen (Tau K A L g) (PTX.next (setReg t dv (.pred r))) t' →
        Stops K A L g t' → Holds t'.regs (dF d')) ∨
        Machine.Dead (K := K) (A := A) (L := L) (g := g) (PTX.next (setReg t dv (.pred r)))) :
    DataStep C' dF d := by
  intro t e u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨m, p, r, rfl, rfl⟩ := fires_voteAnyU hf
  exact hrun hi m p r d' t hn hat

end
end PTX.Flow.Code
