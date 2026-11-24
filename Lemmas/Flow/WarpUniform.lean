-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Lemmas.Flow.Polls
public import Lemmas.Flow.Next
public import Lemmas.Flow.NotWait
public import Lemmas.Register.RegisterFrame

@[expose] public section

/-! # Kernels without warp-divergent executions

A guard value or an index recorded by `Walk` comes from an instruction that compares the value
between the threads of its uniform scope (`visit`, `Instr.laneCompared`). A kernel without such
instructions has no `WarpDivergent` execution (`not_warpDivergent`).

A kernel whose only such instructions are the branches of its wait loops
(`Kernel.pollGuardsOk`: each is a `bra.uni` on the predicate of the unguarded
`mbarrier.try_wait` right before it, entered only from there) has no `WarpDivergent` execution
when each poll position polls one object in all lanes of a warp (`PollObjUniform`) and two
lanes of a warp polling at a position whose branch no assumption selects with `uniPoll` are
ordered (`PollOrdered`): `not_warpDivergent_polls`. At such a branch the record right before is the
poll (`Walk.poll_before`); at a selected branch polls of one object are exempt
(`PollAgreeExempt`, ASM-POLL-AGREE), and at the others the polls give ordered branch executions
(`VisitBefore`, through `DepBefore`). -/

namespace PTX

open PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

/-! ## The execution-dependency order -/

section Dep
variable {L : Launch} {X : Execution}

/-- A step of the dependency order is a dependency. -/
theorem DepBefore.of_depStep {K : Kernel} {e f : EvId}
    (h : DepStep L K X (.thread e, false) (.thread f, false)) : DepBefore L K X e f :=
  .single (.inl h)

/-- A dependency extends to a later event of the target's thread. -/
theorem DepBefore.po_tail {K : Kernel} {e : EvId} {g b k : Nat}
    (h : DepBefore L K X e (g, b)) (hb : b < k) (hk : k < (X.tr g).length) :
    DepBefore L K X e (g, k) :=
  .tail h (.inr ⟨rfl, rfl, (g, b), (g, k), rfl, rfl, ⟨rfl, hb, hk⟩⟩)

end Dep

/-! ## Records -/

@[simp] theorem visit_pc (K : Kernel) (L : Launch) (g : Nat) (t : TState)
    (ev : Option Event) : (visit K L g t ev).pc = t.pc := rfl

@[simp] theorem visit_ev (K : Kernel) (L : Launch) (g : Nat) (t : TState)
    (ev : Option Event) : (visit K L g t ev).ev = ev := rfl

theorem visit_guard {K : Kernel} {L : Launch} {g : Nat} {t : TState} {ev : Option Event} {b : Bool}
    (h : (visit K L g t ev).guard = some b) :
    ∃ ins, K.code[t.pc]? = some ins ∧ ins.op.uniform = true ∧ ins.guard.isSome = true := by
  unfold visit at h
  simp only at h
  split at h
  · rename_i ins hins
    split_ifs at h with hc
    · simp only [Bool.and_eq_true] at hc
      exact ⟨ins, hins, hc.1, hc.2⟩
  · cases h

/-- The instruction compares a value between the threads of its uniform scope: a guard that must
be uniform (`Op.uniform` with a guard), or the index of a `brx.idx.uni`, which the rule compares
whether or not the instruction is guarded. -/
def Instr.laneCompared (ins : Instr) : Bool :=
  (ins.op.uniform && ins.guard.isSome) || match ins.op with
    | .brx _ _ true => true
    | _ => false

/-- The instruction of a record with a guard value compares a lane value between the threads of
its uniform scope. -/
theorem visit_compared_guard {K : Kernel} {L : Launch} {g : Nat} {t : TState} {ev : Option Event}
    {b : Bool} (h : (visit K L g t ev).guard = some b) :
    ∃ ins, K.code[t.pc]? = some ins ∧ ins.laneCompared = true := by
  obtain ⟨ins, hins, hu, hg⟩ := visit_guard h
  exact ⟨ins, hins, by simp [Instr.laneCompared, hu, hg]⟩

/-- The instruction of a record with an index compares a lane value between the threads of its
uniform scope. -/
theorem visit_compared_index {K : Kernel} {L : Launch} {g : Nat} {t : TState} {ev : Option Event}
    {x : Nat} (h : (visit K L g t ev).index = some x) :
    ∃ ins, K.code[t.pc]? = some ins ∧ ins.laneCompared = true := by
  dsimp only [visit] at h
  split at h
  · rename_i ins hins
    refine ⟨ins, hins, ?_⟩
    unfold uniIndex at h
    split at h
    · simp_all [Instr.laneCompared]
    · cases h
  · cases h

/-! ## Static checks -/

/-- Some instruction of the kernel branches to `pc`. -/
def Kernel.branchTarget (K : Kernel) (pc : Nat) : Bool :=
  K.code.any fun ins => match ins.op with
    | .bra target _ => target == pc
    | .brx _ targets _ => targets.contains pc
    | _ => false

/-- The instruction at `pc` is a `bra.uni` guarded by the predicate that the unguarded
`mbarrier.try_wait` at `pc - 1` writes, and no branch enters `pc`. -/
def Kernel.pollBranch (K : Kernel) (pc : Nat) : Bool :=
  0 < pc && !K.branchTarget pc &&
    match K.code[pc]?, K.code[pc - 1]? with
    | some ⟨some (p, _), .bra _ true⟩, some ⟨none, .mbarWait dst ..⟩ => p == dst
    | _, _ => false

/-- No instruction compares a guard or an index between the threads of its uniform scope. -/
def Kernel.noUniformGuards (K : Kernel) : Bool :=
  K.code.all fun ins => !ins.laneCompared

/-- Every instruction that compares a guard or an index between lanes is a poll branch. -/
def Kernel.pollGuardsOk (K : Kernel) : Bool :=
  K.code.zipIdx.all fun p => !p.1.laneCompared || K.pollBranch p.2

theorem branchTarget_of {K : Kernel} {q tgt : Nat} {ins : Instr} {u : Bool}
    (hc : K.code[q]? = some ins) (hop : ins.op = .bra tgt u) : K.branchTarget tgt = true := by
  unfold Kernel.branchTarget
  refine List.any_eq_true.mpr ⟨ins, List.mem_of_getElem? hc, ?_⟩
  simp [hop]

theorem branchTarget_of_brx {K : Kernel} {q pc : Nat} {ins : Instr} {i : Opnd}
    {targets : List Nat} {u : Bool} (hc : K.code[q]? = some ins) (hop : ins.op = .brx i targets u)
    (hm : pc ∈ targets) : K.branchTarget pc = true := by
  unfold Kernel.branchTarget
  refine List.any_eq_true.mpr ⟨ins, List.mem_of_getElem? hc, ?_⟩
  simp [hop, hm]

/-- A local step of the instruction at `t.pc` to a `pc` that no branch targets lands at the next
position. -/
theorem LocalFrame.pc_succ {K : Kernel} {ins : Instr} {t t' : TState}
    (hc : K.code[t.pc]? = some ins) (hf : LocalFrame ins.op t t')
    (hnt : K.branchTarget t'.pc = false) : t'.pc = t.pc + 1 := by
  rcases hf.pc with hpc | hpc
  · unfold nextPc at hpc
    split at hpc
    · rename_i tgt u hop
      rw [hpc, branchTarget_of hc hop] at hnt
      cases hnt
    · exact hpc
  · unfold BrxTarget at hpc
    split at hpc
    · rename_i i targets u hop
      rw [branchTarget_of_brx hc hop hpc] at hnt
      cases hnt
    · exact hpc.elim

theorem pollBranch_spec {K : Kernel} {pc : Nat} (h : K.pollBranch pc = true) :
    0 < pc ∧ K.branchTarget pc = false ∧ ∃ dst neg tgt base off par acq sc,
      K.code[pc]? = some ⟨some (dst, neg), .bra tgt true⟩ ∧
      K.code[pc - 1]? = some ⟨none, .mbarWait dst base off par acq sc⟩ := by
  unfold Kernel.pollBranch at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨h0, hb⟩, hm⟩ := h
  refine ⟨h0, hb, ?_⟩
  split at hm
  · rename_i p neg tgt dst base off par acq sc hc hp
    simp only [beq_iff_eq] at hm
    subst hm
    exact ⟨p, neg, tgt, base, off, par, acq, sc, hc, hp⟩
  · cases hm

/-- A poll branch is a position of the code. -/
theorem pollBranch_lt {K : Kernel} {pc : Nat} (h : K.pollBranch pc = true) :
    pc < K.code.length := by
  obtain ⟨-, -, dst, neg, tgt, base, off, par, acq, sc, hcb, -⟩ := pollBranch_spec h
  exact (List.getElem?_eq_some_iff.mp hcb).1

/-- An instruction that compares a guard or an index between lanes is a poll branch. -/
theorem pollGuardsOk_lane {K : Kernel} (hK : K.pollGuardsOk = true) {pc : Nat} {ins : Instr}
    (hc : K.code[pc]? = some ins) (hl : ins.laneCompared = true) : K.pollBranch pc = true := by
  have h := List.all_eq_true.mp hK (ins, pc) (List.mem_zipIdx_iff_getElem?.mpr hc)
  simpa [hl] using h

/-- A guarded instruction that requires a uniform guard is a poll branch. -/
theorem pollGuardsOk_uniform {K : Kernel} (hK : K.pollGuardsOk = true) {pc : Nat} {ins : Instr}
    (hc : K.code[pc]? = some ins) (hu : ins.op.uniform = true) (hg : ins.guard.isSome = true) :
    K.pollBranch pc = true :=
  pollGuardsOk_lane hK hc (by simp [Instr.laneCompared, hu, hg])

/-! ## Walks -/

section Walks
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- One step of a walk: a local step (`ev = none`) or an event with a next state. -/
def WStep (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat) (s : TState)
    (ev : Option Event) (s' : TState) : Prop :=
  (ev = none ∧ Tau K A L g s s') ∨ ∃ e, ev = some e ∧ EStep K A L g s e (some s')

theorem Walk.events {t : TState} {es : List Event} {vs : List Visit}
    (h : Walk K A L g t es vs) : es = vs.filterMap Visit.ev := by
  induction h with
  | stop => rfl
  | tau _ _ ih => simp only [List.filterMap_cons, visit_ev, ih]
  | ev _ _ ih => simp only [List.filterMap_cons, visit_ev, ih]
  | last _ => simp only [List.filterMap_cons, visit_ev, List.filterMap_nil]

theorem Walk.drop {t : TState} {es : List Event} {vs : List Visit}
    (h : Walk K A L g t es vs) : ∀ r, ∃ s es', Walk K A L g s es' (vs.drop r) := by
  induction h with
  | stop t => intro r; exact ⟨t, [], by simpa using Walk.stop t⟩
  | @tau t t' es vs ht hw ih =>
    intro r
    cases r with
    | zero => exact ⟨t, es, .tau ht hw⟩
    | succ r => simpa using ih r
  | @ev t t' e es vs he hw ih =>
    intro r
    cases r with
    | zero => exact ⟨t, e :: es, .ev he hw⟩
    | succ r => simpa using ih r
  | @last t e he =>
    intro r
    cases r with
    | zero => exact ⟨t, [e], .last he⟩
    | succ r => exact ⟨t, [], by simpa using Walk.stop t⟩

theorem Walk.cons_inv {s : TState} {es : List Event} {v : Visit} {rest : List Visit}
    (h : Walk K A L g s es (v :: rest)) :
    ∃ ev, v = visit K L g s ev ∧
      ((∃ s' es', WStep K A L g s ev s' ∧ Walk K A L g s' es' rest) ∨
        (∃ e, ev = some e ∧ EStep K A L g s e none ∧ rest = [])) := by
  cases h with
  | tau ht hw => exact ⟨none, rfl, .inl ⟨_, _, .inl ⟨rfl, ht⟩, hw⟩⟩
  | ev he hw => exact ⟨_, rfl, .inl ⟨_, _, .inr ⟨_, rfl, he⟩, hw⟩⟩
  | last he => exact ⟨_, rfl, .inr ⟨_, rfl, he, rfl⟩⟩

theorem Walk.get_at {t : TState} {es : List Event} {vs : List Visit}
    (h : Walk K A L g t es vs) {r : Nat} {v : Visit} (hv : vs[r]? = some v) :
    ∃ s es' rest, Walk K A L g s es' (v :: rest) ∧ vs.drop r = v :: rest := by
  obtain ⟨s, es', hw⟩ := h.drop r
  obtain ⟨hlt, hv'⟩ := List.getElem?_eq_some_iff.mp hv
  rw [List.drop_eq_getElem_cons hlt, hv'] at hw
  exact ⟨s, es', _, hw, by rw [List.drop_eq_getElem_cons hlt, hv']⟩

/-- Every record is the record of a step from some state. -/
theorem Walk.state {t : TState} {es : List Event} {vs : List Visit}
    (h : Walk K A L g t es vs) {r : Nat} {v : Visit} (hv : vs[r]? = some v) :
    ∃ s ev, v = visit K L g s ev := by
  obtain ⟨s, es', rest, hw, hd⟩ := h.get_at hv
  obtain ⟨ev, rfl, -⟩ := hw.cons_inv
  exact ⟨s, ev, rfl⟩

theorem Walk.zero_pc {t : TState} {es : List Event} {vs : List Visit}
    (h : Walk K A L g t es vs) {v : Visit} (hv : vs[0]? = some v) : v.pc = t.pc := by
  cases vs with
  | nil => simp at hv
  | cons w rest =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
    subst hv
    obtain ⟨ev, rfl, -⟩ := h.cons_inv
    rfl

/-- Records `r` and `r + 1`: the step from the state of record `r` leads to the state of
record `r + 1`. -/
theorem Walk.step_at {t : TState} {es : List Event} {vs : List Visit}
    (h : Walk K A L g t es vs) {r : Nat} {v w : Visit} (hv : vs[r]? = some v)
    (hw : vs[r + 1]? = some w) :
    ∃ s ev s' ev', v = visit K L g s ev ∧ w = visit K L g s' ev' ∧ WStep K A L g s ev s' := by
  obtain ⟨s, es', rest, hws, hd⟩ := h.get_at hv
  have hr : rest[0]? = some w := by
    have h1 : (v :: rest)[1]? = vs[r + 1]? := by rw [← hd, List.getElem?_drop]
    simpa [hw] using h1
  cases rest with
  | nil => simp at hr
  | cons w' rest =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
    subst hr
    obtain ⟨ev, rfl, hst⟩ := hws.cons_inv
    rcases hst with ⟨s', es', hstep, hw'⟩ | ⟨-, -, -, hnil⟩
    · obtain ⟨ev', rfl, -⟩ := hw'.cons_inv
      exact ⟨s, ev, s', ev', rfl, rfl, hstep⟩
    · cases hnil

/-- The event of record `r` is the thread's event after the events of the records before. -/
theorem Walk.event_get {X : Execution} {t : TState} {es : List Event} {vs : List Visit}
    (h : Walk K A L g t es vs) (hp : es <+: X.tr g) {r : Nat} {v : Visit} {e : Event}
    (hv : vs[r]? = some v) (he : v.ev = some e) :
    X.get (g, ((vs.take r).filterMap Visit.ev).length) = some e ∧
      (X.tr g).take ((vs.take r).filterMap Visit.ev).length = (vs.take r).filterMap Visit.ev := by
  obtain ⟨tl, htl⟩ := hp
  have hsplit : vs = vs.take r ++ v :: vs.drop (r + 1) := by
    obtain ⟨hlt, hv'⟩ := List.getElem?_eq_some_iff.mp hv
    conv_lhs => rw [← List.take_append_drop r vs]
    rw [List.drop_eq_getElem_cons hlt, hv']
  have hes := h.events
  rw [hsplit, List.filterMap_append, List.filterMap_cons, he] at hes
  rw [hes, List.append_assoc, List.cons_append] at htl
  have hget : X.get (g, ((vs.take r).filterMap Visit.ev).length) =
      (X.tr g)[((vs.take r).filterMap Visit.ev).length]? := rfl
  rw [hget, ← htl]
  simp

/-! ## Steps -/

/-- A step from an unguarded poll is its poll event, and sets the predicate to the result. -/
theorem wstep_poll {s s' : TState} {ev : Option Event} (hs : WStep K A L g s ev s')
    {dst base : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope}
    (hc : K.code[s.pc]? = some ⟨none, .mbarWait dst base off par acq sc⟩) :
    ∃ m p ok sc', ev = some ⟨s.pc, .wait m p ok acq sc'⟩ ∧
      s' = next (setReg s dst (.pred ok)) := by
  rcases hs with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · exfalso
    unfold Tau out at ht
    cases hf : s.fault <;> simp [hf, hc, guardHolds, Op.isLocal, pure, Except.pure] at ht
  · obtain ⟨ins, hc', -, hfire⟩ := estep_event_source he
    rw [hc] at hc'
    cases hc'
    obtain ⟨m, p, ok, sc', rfl, rfl⟩ := fires_wait hfire
    exact ⟨m, p, ok, sc', rfl, rfl⟩

/-- A step into a local instruction that no branch targets comes from the position before it. -/
theorem wstep_into {s s' : TState} {ev : Option Event} (hs : WStep K A L g s ev s')
    (hloc : ∀ t op t', execLocalA A L g t op = .ok t' → LocalFrame op t t')
    (hnt : K.branchTarget s'.pc = false) {ins : Instr} (hc : K.code[s'.pc]? = some ins)
    (hl : ins.op.isLocal = true) : s.pc + 1 = s'.pc := by
  rcases hs with ⟨-, ht⟩ | ⟨e, -, he⟩
  · unfold Tau out at ht
    cases hf : s.fault with
    | some f => simp [hf] at ht
    | none =>
      simp only [hf] at ht
      cases hc' : K.code[s.pc]? with
      | none => simp [hc'] at ht
      | some ins' =>
        simp only [hc'] at ht
        cases hg : guardHolds s ins'.guard with
        | error f => simp [hg] at ht
        | ok b =>
          cases b with
          | false =>
            simp only [hg, Out.tau.injEq] at ht
            subst ht
            rfl
          | true =>
            simp only [hg] at ht
            split at ht
            · split at ht
              · rename_i t1 hex
                simp only [Out.tau.injEq] at ht
                subst ht
                exact (LocalFrame.pc_succ hc' (hloc _ _ _ hex) hnt).symm
              · cases ht
            · cases ht
  · obtain ⟨-, hpc⟩ := estep_return_pc he hloc
    rcases hpc with hpc | hpc
    · obtain ⟨ins', hc', hl', -⟩ := estep_event_source he
      rw [← hpc, hc] at hc'
      cases hc'
      rw [hl] at hl'
      cases hl'
    · exact hpc.symm

/-! ## The poll before a poll branch -/

/-- At a poll branch, the record before is the poll's event. -/
theorem Walk.poll_before {es : List Event} {vs : List Visit} (h : Walk K A L g {} es vs)
    (hloc : ∀ t op t', execLocalA A L g t op = .ok t' → LocalFrame op t t')
    {i : Nat} {v : Visit} (hv : vs[i]? = some v) (hb : K.pollBranch v.pc = true) :
    0 < i ∧ ∃ u m p ok acq sc, vs[i - 1]? = some u ∧
      u.ev = some ⟨v.pc - 1, .wait m p ok acq sc⟩ := by
  obtain ⟨h0, hnt, dst, neg, tgt, base, off, par, acq, sc, hcb, hcw⟩ := pollBranch_spec hb
  have hi : 0 < i := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have := h.zero_pc hv
      simp only at this
      omega
    · exact hi
  refine ⟨hi, ?_⟩
  obtain ⟨u, hu⟩ : ∃ u, vs[i - 1]? = some u := by
    have := (List.getElem?_eq_some_iff.mp hv).1
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hv' : vs[i - 1 + 1]? = some v := by rwa [Nat.sub_add_cancel hi]
  obtain ⟨s, ev, s', ev', rfl, rfl, hst⟩ := h.step_at hu hv'
  simp only [visit_pc] at hnt hcb hcw h0 ⊢
  have hpc := wstep_into hst hloc hnt hcb rfl
  rw [← hpc, Nat.add_sub_cancel] at hcw
  obtain ⟨m, p, ok, sc', rfl, -⟩ := wstep_poll hst hcw
  refine ⟨_, m, p, ok, acq, sc', hu, ?_⟩
  simp only [visit_ev, ← hpc, Nat.add_sub_cancel]

end Walks

/-! ## The theorems -/

/-- **No warp-divergent execution** for a kernel without instructions that compare a guard or an
index between lanes. -/
theorem not_warpDivergent {L : Launch} {K : Kernel} {A : List Assumption} {X : Execution}
    (hK : K.noUniformGuards = true) : ¬ WarpDivergent L K A X := by
  rintro ⟨g, h, hg, hh, hgh, eg, eh, vg, vh, hpg, hph, hwg, hwh, i, j, pc, vi, vj, hvi, hvj,
    hpi, hpj, hgrp, hdis, hng, hnh, hnot⟩
  obtain ⟨s, ev, rfl⟩ := hwg.state hvi
  obtain ⟨ins, hins, hl⟩ : ∃ ins, K.code[s.pc]? = some ins ∧ ins.laneCompared = true := by
    rcases hdis with ⟨b, -, hb, -, -⟩ | ⟨x, -, hx, -, -⟩
    · exact visit_compared_guard hb
    · exact visit_compared_index hx
  have hall := List.all_eq_true.mp hK ins (List.mem_of_getElem? hins)
  simp [hl] at hall

/-- Each poll position polls one object in all lanes of a warp. -/
def PollObjUniform (L : Launch) (X : Execution) : Prop :=
  ∀ g h k k' pc m m' p p' ok ok' acq acq' sc sc', g < L.threads → h < L.threads →
    SameWarp L g h → X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
    X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩ → m = m'

/-- Two distinct lanes of a warp polling one object at one position whose next position no
assumption selects with `uniPoll`: an event one lane performs after its poll happens before the
other lane's poll in the execution-dependency order. -/
def PollOrdered (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ g h k k' pc m p p' ok ok' acq acq' sc sc', g < L.threads → h < L.threads → g ≠ h →
    SameWarp L g h → X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
    X.get (h, k') = some ⟨pc, .wait m p' ok' acq' sc'⟩ → A.any (·.uniPoll (pc + 1)) = false →
    (∃ a, k < a ∧ DepBefore L K X (g, a) (h, k')) ∨
      (∃ a, k' < a ∧ DepBefore L K X (h, a) (g, k))

/-- The record after a record with an event counts one more event. -/
theorem Visit.events_succ {vs : List Visit} {i : Nat} {u : Visit} (hu : vs[i]? = some u)
    {e : Event} (he : u.ev = some e) : Visit.events vs (i + 1) = Visit.events vs i + 1 := by
  unfold Visit.events
  rw [List.take_add_one, hu]
  simp [List.filterMap_append, he]

/-- **No warp-divergent execution** for a kernel whose guarded uniform instructions are the
branches of its wait loops, when its polls use warp-uniform objects and polls at the branches no
assumption selects with `uniPoll` are ordered. -/
theorem not_warpDivergent_polls {L : Launch} {K : Kernel} {A : List Assumption} {X : Execution}
    (hK : K.pollGuardsOk = true)
    (hloc : ∀ g t op t', execLocalA A L g t op = .ok t' → LocalFrame op t t')
    (hobj : PollObjUniform L X) (hord : PollOrdered L K A X) : ¬ WarpDivergent L K A X := by
  rintro ⟨g, h, hg, hh, hgh, eg, eh, vg, vh, hpg, hph, hwg, hwh, i, j, pc, vi, vj, hvi, hvj,
    hpi, hpj, hgrp, hdis, hng, hnh, hnot⟩
  obtain ⟨s, ev, rfl⟩ := hwg.state hvi
  obtain ⟨ins, hins, hl⟩ : ∃ ins, K.code[s.pc]? = some ins ∧ ins.laneCompared = true := by
    rcases hdis with ⟨b, -, hb, -, -⟩ | ⟨x, -, hx, -, -⟩
    · exact visit_compared_guard hb
    · exact visit_compared_index hx
  have hpb := pollGuardsOk_lane hK hins hl
  simp only [visit_pc] at hpi
  subst hpi
  obtain ⟨h0, -, dst, neg, tgt, base, off, par, acq, sc, hcb, hcw⟩ := pollBranch_spec hpb
  have hw : SameWarp L g h := by
    simpa [Kernel.uniformScopeAt, hcb, Op.uniformScope, SameUniformGroup] using hgrp
  obtain ⟨hi, ug, mg, pg, okg, acqg, scg, hug, hugev⟩ := hwg.poll_before (hloc g) hvi hpb
  have hpb' : K.pollBranch vj.pc = true := by rw [hpj]; exact hpb
  obtain ⟨hj, uh, mh, ph, okh, acqh, sch, huh, huhev⟩ := hwh.poll_before (hloc h) hvj hpb'
  rw [hpj] at huhev
  simp only [visit_pc] at hugev
  obtain ⟨hxg, -⟩ := hwg.event_get hpg hug hugev
  obtain ⟨hxh, -⟩ := hwh.event_get hph huh huhev
  have hm : mg = mh := hobj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg hh hw hxg hxh
  subst hm
  have hig : Visit.events vg i = Visit.events vg (i - 1) + 1 := by
    have := Visit.events_succ hug hugev
    rwa [Nat.sub_add_cancel hi] at this
  have hjh : Visit.events vh j = Visit.events vh (j - 1) + 1 := by
    have := Visit.events_succ huh huhev
    rwa [Nat.sub_add_cancel hj] at this
  cases hs : A.any (·.uniPoll s.pc) with
  | true =>
    exact hnot ⟨hs, ⟨dst, neg, tgt, _, base, off, par, acq, sc, hcb, hcw, rfl⟩, ug, uh, mg, pg,
      ph, okg, okh, acqg, acqh, scg, sch, hug, huh, hi, hj, hugev, huhev⟩
  | false =>
    have hs' : A.any (·.uniPoll (s.pc - 1 + 1)) = false := by rwa [Nat.sub_add_cancel h0]
    rcases hord _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg hh hgh hw hxg hxh hs' with
      ⟨a, ha, hab⟩ | ⟨a, ha, hab⟩
    · exact hng ⟨a, _, by unfold Visit.events at hig ⊢; omega,
        by unfold Visit.events at hjh ⊢; omega, hab⟩
    · exact hnh ⟨a, _, by unfold Visit.events at hjh ⊢; omega,
        by unfold Visit.events at hig ⊢; omega, hab⟩

end

end PTX
