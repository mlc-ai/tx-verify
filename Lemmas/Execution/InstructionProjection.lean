-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.EventProjection
public import Lemmas.Isa.Tmpl

@[expose] public section

namespace PTX.Proof
open PTX
noncomputable section

def eventProjection (S : Nat → Bool) : Op → Bool
  | .mem a => !dynamicAccess (.mem a) && match a.kind, a.sem, a.addr.base with
    | .load, .weak, .reg base _ => S base && a.regs.all (fun r => !S r)
    | .store, .weak, .reg base _ => S base
    | _, _, _ => false
  | .barSync a _ => staticArg S a
  | .barSyncN a b _ => staticArg S a && staticArg S b
  | .warp w => match w.kind, w.dsts, w.srcs, w.mask with
    | .shfl _, some d :: ps, [_, b, c], some mask =>
      !S d && ps.all (fun o => o.all (fun r => !S r)) && [b, c, mask].all (staticArg S)
    | _, _, _, _ => false
  | .ret | .exit => true
  | _ => false

def instructionProjection (S : Nat → Bool) (ins : Instr) : Bool :=
  (match ins.guard with | none => true | some (p, _) => S p) &&
    if ins.op.isLocal then localProjection S ins.op else eventProjection S ins.op

/-- A load's rule is no THREAD-ATOMIC. -/
private theorem rule_ne_atomic_of_load {a : MemAccess} (hk : a.kind = .load) :
    a.rule ≠ some .threadAtomic := by
  intro h
  cases hs : a.space with
  | none =>
    rw [MemAccess.rule, hk, hs] at h
    split_ifs at h <;> cases h
  | some sp =>
    cases sp <;> rw [MemAccess.rule, hk, hs] at h <;> split_ifs at h <;>
      first | cases h | simp_all

/-- A store's rule is no THREAD-ATOMIC. -/
private theorem rule_ne_atomic_of_store {a : MemAccess} (hk : a.kind = .store) :
    a.rule ≠ some .threadAtomic := by
  intro h
  cases hs : a.space <;> rw [MemAccess.rule, hk, hs] at h <;> split_ifs at h <;> cases h

/-- Only an `atom` or `red` has THREAD-ATOMIC as its rule. -/
private theorem kind_of_rule_atomic {a : MemAccess} (h : a.rule = some .threadAtomic) :
    (∃ op, a.kind = .rmw op) ∨ ∃ op, a.kind = .reduce op := by
  cases hk : a.kind with
  | rmw op => exact .inl ⟨op, rfl⟩
  | reduce op => exact .inr ⟨op, rfl⟩
  | load => exact absurd h (rule_ne_atomic_of_load hk)
  | loadUniform | loadReadonly | discard =>
    exact absurd h (by
      intro h
      cases hs : a.space <;> rw [MemAccess.rule, hk, hs] at h
      all_goals cases h)
  | store => exact absurd h (rule_ne_atomic_of_store hk)
  | bulkInit =>
    exact absurd h (by
      intro h
      cases hs : a.space <;> rw [MemAccess.rule, hk, hs] at h <;> split_ifs at h <;> cases h)

namespace ControlAgree
variable {S : Nat → Bool} {t u : TState} {L : Launch} {g : Nat}

theorem eventTmpl {A : List Assumption} {op : Op} (h : ControlAgree S t u)
    (hc : eventProjection S op = true) :
    OutRelated S (.ev (PTX.eventTmpl A L g t op)) (.ev (PTX.eventTmpl A L g u op)) := by
  cases op
  case mem a =>
    -- the projection holds exactly for a weak load or store through a base register
    simp only [eventProjection, Bool.and_eq_true] at hc
    simp only [PTX.eventTmpl, memTmpl]
    split
    · -- THREAD-ACCESS at the located space
      split
      · simp_all
      · split at hc
        · simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hc
          simp_all only [AddrBase.reg.injEq]
          exact h.loadTmpl hc.2.1 hc.2.2
        · simp_all
        · simp_all
      · simp_all
      · split at hc
        · simp_all
        · simp_all only [AddrBase.reg.injEq]
          exact h.storeTmpl hc.2
        · simp_all
      · simp_all
    · -- an atomic access is no weak load or store
      rename_i hr
      rcases kind_of_rule_atomic hr with ⟨op, hk⟩ | ⟨op, hk⟩ <;> simp [hk] at hc
    · split
      · rename_i hn hr
        simp [dynamicAccess_of' hr hn] at hc
      · exact .fault_left _ _
  case warp w =>
    rcases w with ⟨kind, ty, dsts, srcs, mask⟩
    simp only [eventProjection] at hc
    split at hc
    · rename_i m d ps a b c mask
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_cons, List.all_nil,
        Bool.and_true] at hc
      simp only [PTX.eventTmpl]
      rcases warpTmpl_shfl (L := L) (g := g) (t := t) (mode := m) (ty := ty) (d := d) (ps := ps)
          (a := a) (b := b) (c := c) (mask := mask) with ht | ht <;>
        rcases warpTmpl_shfl (L := L) (g := g) (t := u) (mode := m) (ty := ty) (d := d) (ps := ps)
          (a := a) (b := b) (c := c) (mask := mask) with hu | hu <;> rw [ht, hu]
      · refine h.shflTmpl hc.1.1 (fun r hr => ?_) hc.2.1 hc.2.2.1 hc.2.2.2
        have hps := List.all_eq_true.mp hc.1.2
        cases ps with
        | nil => simp at hr
        | cons o ps =>
          have := hps o (by simp)
          cases o <;> simp_all
      all_goals first | exact .fault_left _ _ | exact .fault_right _ _
    · simp at hc
  all_goals simp only [eventProjection, Bool.and_eq_true] at hc
  all_goals try contradiction
  case barSync => exact h.barTmpl (count := none) hc (by simp)
  case barSyncN a b _ => exact h.barTmpl (count := some b) hc.1 (by simpa using hc.2)
  case ret => exact .exit
  case exit => exact .exit

theorem guard {p : Option (Nat × Bool)} (h : ControlAgree S t u)
    (hp : (match p with | none => true | some (r, _) => S r) = true) :
    guardHolds t p = guardHolds u p := by
  cases p with
  | none => rfl
  | some p =>
    obtain ⟨r, b⟩ := p
    simp only [guardHolds, readReg, h.regs r hp]

theorem out {A : List Assumption} (hF : RulesFrame A) (hC : NoControlRule A) {K : Kernel}
    (h : ControlAgree S t u)
    (hK : ∀ ins ∈ K.code, instructionProjection S ins = true)
    (hS : Assumption.SegFreePc A t.pc := by seg_free)
    (hSu : Assumption.SegFreePc A u.pc := by seg_free) :
    OutRelated S (PTX.out K A L g t)
      (PTX.out K A L g u) := by
  unfold PTX.out
  cases ht : t.fault with
  | some f => exact .fault_left _ _
  | none =>
    cases hu : u.fault with
    | some f => exact .fault_right _ _
    | none =>
      rw [h.pc]
      cases hi : K.code[u.pc]? with
      | none => exact .fault_left _ _
      | some ins =>
        have hp := hK ins (List.mem_of_getElem? hi)
        simp only [instructionProjection, Bool.and_eq_true] at hp
        dsimp only
        rw [h.guard hp.1]
        cases hg : guardHolds u ins.guard with
        | error f => exact .fault_left _ _
        | ok enabled =>
          cases enabled with
          | false => exact .tau ⟨congrArg (· + 1) h.pc, rfl, h.regs⟩
          | true =>
            dsimp only
            split
            · rename_i hl
              rw [ite_eq_left hl] at hp
              cases he : execLocalA A L g t ins.op with
              | error f => exact .fault_left _ _
              | ok t' =>
                cases he' : execLocalA A L g u ins.op with
                | error f => exact .fault_right _ _
                | ok u' => exact .tau (h.local_result hF hC hp.2 he he' hS hSu)
            · rename_i hl
              rw [ite_eq_right hl] at hp
              exact h.eventTmpl hp.2

end ControlAgree
end
end PTX.Proof
