-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataStepE
public import Lemmas.Flow.DataTcLoad
public import Lemmas.Flow.DataElems
public import Lemmas.Flow.DataStoreVote
public import Lemmas.Flow.DataTcSt
public import Lemmas.Flow.ReachSegU
public import Lemmas.Flow.DataLoadNcV
public import Lemmas.Flow.DataElect

@[expose] public section

/-! # The strict data steps of the kinds of events

Strict twins (`DataStepE`, no dead alternative) of the data steps `DataStep.{tcLoad, loadE, store,
voteAny, storeE, next, tcSt, loadNc, loadNcV, wait, elect}`: the same hypotheses, with the run
continuation `hrun` stated without `∨ Dead`. A load's data step is for an event whose bytes
rebuild (`EvRdOk`, `EvNcOk`): bytes that do not rebuild fault the thread. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem DataStepE.tcLoad {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {e : Event} {ds : List Nat} {ta : Nat} {sh : TcShape}
    (hc : K.code[C'.pc d]? = some ⟨none, .tcLd ds ta sh none⟩) (hsh : ∀ s, sh ≠ .packed16 s)
    (hw : A.any (·.tcLdWait (C'.pc d)) = false)
    (hrun : C'.inv d → ∀ a vals d' t, C'.next d ⟨C'.pc d, .tc (.ld a vals sh)⟩ = some (some d') →
      vals.length = ds.length → C'.AtD d t →
      ∀ t', Relation.ReflTransGen (Tau K A L g) (setRegs (PTX.next t) ds vals) t' →
        Stops K A L g t' → Holds t'.regs (dF d')) :
    DataStepE C' dF d e := by
  intro t u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  have hw' : A.any (·.tcLdWait t.pc) = false := by rw [hat.1]; exact hw
  obtain ⟨a, vals, hl, rfl, rfl⟩ := fires_tcLd hsh hf hw'
  exact hrun hi a vals d' t hn hl hat

theorem DataStepE.loadE {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {e : Event} {a : MemAccess} {Q : Value → C'.D → Prop}
    (hc : K.code[C'.pc d]? = some ⟨none, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
    (he : a.ext = .same) (hl : (Op.mem a).isLocal = false) (hwf : EvRdOk e)
    (hmid : C'.sub d + 1 < a.regs.length → ∀ e d', C'.next d e = some (some d') →
      ∀ R, Holds R (C'.facts d) → Holds R (dF d'))
    (hN : ¬ C'.sub d + 1 < a.regs.length → ∀ x bs d' v,
      C'.next d ⟨C'.pc d, .rd x bs⟩ = some (some d') → rebuild 3 bs = .ok v → Q v d')
    (hrun : C'.inv d → ∀ v d' t, Q v d' → C'.AtD d t →
      let u := { setRegs t a.regs (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] }
      ∀ t', Relation.ReflTransGen (Tau K A L g) u t' → Stops K A L g t' →
        Holds t'.regs (dF d')) :
    DataStepE C' dF d e := by
  intro t u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  obtain ⟨hp, hsb, hac, hft, hF⟩ := hat
  obtain ⟨v, hv⟩ := hwf x bs rfl
  by_cases hm : C'.sub d + 1 < a.regs.length
  · have hm' : t.sub + 1 < a.regs.length := by rw [hsb]; exact hm
    have hu : afterLoad t a.regs bs = { t with sub := t.sub + 1, acc := t.acc ++ [v] } := by
      simp [afterLoad, hv, hm']
    rw [hu]
    exact stays_regs ⟨_, out_event (t := { t with sub := t.sub + 1, acc := t.acc ++ [v] })
      hft (by rw [show t.pc = C'.pc d from hp]; exact hc) rfl hl⟩ rfl (hmid hm _ d' hn _ hF)
  · have hq := hN hm x bs d' v hn hv
    have hm' : ¬ t.sub + 1 < a.regs.length := by rw [hsb]; exact hm
    have hu : afterLoad t a.regs bs =
        { setRegs t a.regs (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] } := by
      simp [afterLoad, hv, hm']
    rw [hu]
    exact hrun hi v d' t hq ⟨hp, hsb, hac, hft, hF⟩

theorem DataStepE.store {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {e : Event} {a : MemAccess} (hc : K.code[C'.pc d]? = some ⟨none, .mem a⟩)
    (hk : a.kind = .store) (hs : a.srcs.length = 1)
    (hrun : C'.inv d → ∀ e d' t, C'.next d e = some (some d') → C'.AtD d t →
      ∀ t', Relation.ReflTransGen (Tau K A L g) { t with pc := t.pc + 1, sub := 0 } t' →
        Stops K A L g t' → Holds t'.regs (dF d')) :
    DataStepE C' dF d e := by
  intro t u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨-, -, -, rfl⟩ := fires_st hk hf
  have hu : afterStore t a.srcs = { t with pc := t.pc + 1, sub := 0 } := by
    simp [afterStore, hs]
  rw [hu]
  exact hrun hi _ d' t hn hat

theorem DataStepE.storeE {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {e : Event} {a : MemAccess} (hc : K.code[C'.pc d]? = some ⟨none, .mem a⟩)
    (hl : (Op.mem a).isLocal = false) (hk : a.kind = .store)
    (hmid : C'.sub d + 1 < a.srcs.length → ∀ e d', C'.next d e = some (some d') →
      ∀ R, Holds R (C'.facts d) → Holds R (dF d'))
    (hrun : C'.inv d → ¬ C'.sub d + 1 < a.srcs.length → ∀ e d' t,
      C'.next d e = some (some d') → C'.AtD d t →
      ∀ t', Relation.ReflTransGen (Tau K A L g) { t with pc := t.pc + 1, sub := 0 } t' →
        Stops K A L g t' → Holds t'.regs (dF d')) :
    DataStepE C' dF d e := by
  intro t u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨_, _, rfl, rfl⟩ := fires_st hk hf
  obtain ⟨hp, hsb, hac, hft, hF⟩ := hat
  by_cases hm : C'.sub d + 1 < a.srcs.length
  · have hm' : t.sub + 1 < a.srcs.length := by rw [hsb]; exact hm
    rw [afterStore_mid hm']
    exact stays_regs ⟨_, out_event (t := { t with sub := t.sub + 1 }) hft
      (by rw [show t.pc = C'.pc d from hp]; exact hc) rfl hl⟩ rfl (hmid hm _ d' hn _ hF)
  · have hm' : ¬ t.sub + 1 < a.srcs.length := by rw [hsb]; exact hm
    rw [afterStore_last hm']
    exact hrun hi hm _ d' t hn ⟨hp, hsb, hac, hft, hF⟩

theorem DataStepE.voteAny {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {e : Event} {ty dv pr neg mask}
    (hc : K.code[C'.pc d]? = some ⟨none, .warp ⟨.vote .any neg, ty, [some dv], [.reg pr],
      some mask⟩⟩)
    (hrun : C'.inv d → ∀ m p r d' t,
      C'.next d ⟨C'.pc d, .voteMode .any m p r⟩ = some (some d') → C'.AtD d t →
      ∀ t', Relation.ReflTransGen (Tau K A L g) (PTX.next (setReg t dv (.pred r))) t' →
        Stops K A L g t' → Holds t'.regs (dF d')) :
    DataStepE C' dF d e := by
  intro t u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨m, p, r, rfl, rfl⟩ := fires_voteAnyU hf
  exact hrun hi m p r d' t hn hat

theorem DataStepE.next {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {e : Event} {op : Op} (hc : K.code[C'.pc d]? = some ⟨none, op⟩)
    (hu : ∀ t e u, Fires (C'.pc d) (eventTmpl A L g t op) e (some u) → u = PTX.next t)
    (hrun : C'.inv d → ∀ e d' t, C'.next d e = some (some d') → C'.AtD d t →
      ∀ t', Relation.ReflTransGen (Tau K A L g) (PTX.next t) t' → Stops K A L g t' →
        Holds t'.regs (dF d')) :
    DataStepE C' dF d e := by
  intro t u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain rfl := hu t e u hf
  exact hrun hi e d' t hn hat

theorem DataStepE.tcSt {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {e : Event} {ta : Nat} {ss : List Opnd} {sh : TcShape}
    (hc : K.code[C'.pc d]? = some ⟨none, .tcSt ta ss sh⟩)
    (hw : A.any (·.tcStWaitLd (C'.pc d)) = false)
    (hrun : C'.inv d → ∀ e d' t, C'.next d e = some (some d') → C'.AtD d t →
      ∀ t', Relation.ReflTransGen (Tau K A L g) (PTX.next t) t' → Stops K A L g t' →
        Holds t'.regs (dF d')) :
    DataStepE C' dF d e := by
  intro t u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain rfl := fires_tcSt_next (hat.1 ▸ hw) hf
  exact hrun hi e d' t hn hat

theorem DataStepE.loadNcV {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {e : Event} {a : MemAccess} {r base w : Nat} {sp : Space} (hwf : EvNcOk e)
    (hc : K.code[C'.pc d]? = some ⟨none, .mem a⟩)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hr : a.regs = [r]) (hs : C'.inv d → C'.sub d = 0)
    (ha : C'.inv d → C'.acc d = [])
    (hrun : C'.inv d → ∀ x bs v, rebuild 3 bs = .ok v → ∀ d' t,
      C'.next d ⟨C'.pc d, .nc x bs⟩ = some (some d') → C'.AtD d t →
      ∀ t', Relation.ReflTransGen (Tau K A L g)
        { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] } t' → Stops K A L g t' →
        Holds t'.regs (dF d')) :
    DataStepE C' dF d e := by
  intro t u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_loadNc hru hloc hb hk hsem hnc hf
  rw [hr]
  obtain ⟨v, hv⟩ := hwf x bs rfl
  rw [afterLoad_ok (hat.2.1.trans (hs hi)) (hat.2.2.1.trans (ha hi)) hv]
  exact hrun hi x bs v hv d' t hn hat

theorem DataStepE.loadNc {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {e : Event} {a : MemAccess} {r base w : Nat} {sp : Space} (hwf : EvNcOk e)
    (hc : K.code[C'.pc d]? = some ⟨none, .mem a⟩)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hr : a.regs = [r]) (hs : C'.inv d → C'.sub d = 0)
    (ha : C'.inv d → C'.acc d = [])
    (hrun : C'.inv d → ∀ x bs v d' t, C'.next d ⟨C'.pc d, .nc x bs⟩ = some (some d') →
      C'.AtD d t →
      ∀ t', Relation.ReflTransGen (Tau K A L g)
        { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] } t' → Stops K A L g t' →
        Holds t'.regs (dF d')) :
    DataStepE C' dF d e :=
  DataStepE.loadNcV hwf hc hru hloc hb hk hsem hnc hr hs ha
    fun hi x bs v _ d' t hn hat => hrun hi x bs v d' t hn hat

theorem DataStepE.wait {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {e : Event} {p base : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope}
    (hc : K.code[C'.pc d]? = some ⟨none, .mbarWait p base off par acq sc⟩)
    (hrun : C'.inv d → ∀ m q ok s d' t, C'.next d ⟨C'.pc d, .wait m q ok acq s⟩ = some (some d') →
      C'.AtD d t →
      ∀ t', Relation.ReflTransGen (Tau K A L g) (PTX.next (setReg t p (.pred ok))) t' →
        Stops K A L g t' → Holds t'.regs (dF d')) :
    DataStepE C' dF d e := by
  intro t u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  rw [← hat.1] at hf
  obtain ⟨m, q, ok, s, rfl, rfl⟩ := fires_wait hf
  rw [hat.1] at hn
  exact hrun hi m q ok s d' t hn hat

theorem DataStepE.elect {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {e : Event} {ty : Option DType} {r p : Nat} {mask : Opnd}
    (hc : K.code[C'.pc d]? = some ⟨none, .warp ⟨.elect, ty, [some r, some p], [], some mask⟩⟩)
    (hrun : C'.inv d → ∀ mk inst ld d' t,
      C'.next d ⟨C'.pc d, .elect mk inst ld⟩ = some (some d') → C'.AtD d t →
      ∀ t', Relation.ReflTransGen (Tau K A L g)
          (PTX.next (setReg (setReg t r (.bits 32 (BitVec.ofNat 64 ld))) p
            (.pred (laneOf L g == ld)))) t' →
        Stops K A L g t' → Holds t'.regs (dF d')) :
    DataStepE C' dF d e := by
  intro t u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
  exact hrun hi mk inst ld d' t hn hat

end
end PTX.Flow.Code
