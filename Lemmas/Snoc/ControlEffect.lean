-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Register.RegisterFrame

@[expose] public section

namespace PTX.Proof
open PTX
noncomputable section

/-- Carry forms also write the condition code, which a register result cannot express, so they are
not control operations. -/
def carryFree : IntOp → Bool
  | .addCarry .. | .subCarry .. | .madCarry .. => false
  | _ => true

/-- Integer instructions and scalar moves that may control addresses and branches: the integer
instructions with THREAD-INT as their rule, one destination and no carry result, scalar `mov`,
`ld.param` of a scalar parameter and `cvta.to.global.u64`. -/
def controlOp : Op → Bool
  | .int i => i.rule == some .threadInt && i.dsts.length == 1 && carryFree i.op
  | .move m => m.kind == .scalar
  | .mem a => match a.addr.base with
    | .param _ false => true
    | _ => false
  | .addr c => match c with
    | .cvta true .global 64 _ _ => true
    | _ => false
  | _ => false

def controlArgs : Op → List Opnd
  | .int i => i.srcs
  | .move m => m.srcs
  | .addr c => match c with
    | .cvta true .global 64 _ a => [a]
    | _ => []
  | _ => []

/-- The destination and value of an integer instruction with one destination (the result of
`execInt`). -/
def intEffect (L : Launch) (g : Nat) (t : TState) (i : IntInstr) : Exec (Nat × Value) :=
  let w := i.ty.width
  let signed := i.ty.kind? == some .s
  match i.op, i.ty, i.sat, i.dsts, i.srcs with
  | .add, _, true, [some d], _ | .sub, _, true, [some d], _
  | .add, .packed _ _, _, [some d], _ | .sub, .packed _ _, _, [some d], _
  | .min false, .packed _ _, _, [some d], _ | .max false, .packed _ _, _, [some d], _ => do
    let v ← intResult L g t i
    pure (d, v)
  | .add, _, _, [some d], [a, b] => do
    let va ← readValue L g t w a
    let vb ← readValue L g t w b
    match va, vb with
    | .ptr _ _ (.shared ..) _, .bits _ _ | .ptr _ _ (.local _) _, .bits _ _
    | .ptr _ _ .const _, .bits _ _ =>
      let delta ← readBits L g t w b
      let v ← offsetPointer w va (toSigned w delta)
      pure (d, v)
    | .bits _ _, .ptr _ _ (.shared ..) _ | .bits _ _, .ptr _ _ (.local _) _
    | .bits _ _, .ptr _ _ .const _ =>
      let delta ← readBits L g t w a
      let v ← offsetPointer w vb (toSigned w delta)
      pure (d, v)
    | _, _ =>
      let x ← readBits L g t w a; let y ← readBits L g t w b
      pure (d, .bits w (truncBits w (x + y)))
  | .sub, _, _, [some d], [a, b] => do
    let va ← readValue L g t w a
    match va with
    | .ptr _ _ (.shared ..) _ | .ptr _ _ (.local _) _ | .ptr _ _ .const _ =>
      let delta ← readBits L g t w b
      let v ← offsetPointer w va (-(toSigned w delta))
      pure (d, v)
    | _ =>
      let x ← readBits L g t w a; let y ← readBits L g t w b
      pure (d, .bits w (truncBits w (x - y)))
  | .mul .lo, _, _, [some d], [a, b] => do
    let x ← readBits L g t w a; let y ← readBits L g t w b
    pure (d, .bits w (truncBits w (x * y)))
  | .mad .lo, _, _, [some d], [a, b, c] => do
    let x ← readBits L g t w a; let y ← readBits L g t w b; let z ← readBits L g t w c
    pure (d, .bits w (truncBits w (x * y + z)))
  | .mul .hi, _, _, [some d], [a, b] => do
    let x ← readBits L g t w a; let y ← readBits L g t w b
    let p : Int := if signed then toSigned w x * toSigned w y else x.toNat * y.toNat
    pure (d, .bits w (truncBits w (BitVec.ofInt 64 (p / 2 ^ w))))
  | .mul .wide, _, _, [some d], [a, b] => do
    let x ← readBits L g t w a; let y ← readBits L g t w b
    let r : BitVec 64 :=
      if signed then truncBits (2 * w) (BitVec.ofInt 64 (toSigned w x * toSigned w y))
      else BitVec.ofNat 64 (x.toNat * y.toNat)
    pure (d, .bits (2 * w) r)
  | .min false, _, _, [some d], [a, b] | .max false, _, _, [some d], [a, b] => do
    let isMax := i.op == .max false
    let x ← readBits L g t w a; let y ← readBits L g t w b
    let first := compare (if isMax then .gt else .lt) (if signed then .s else .u) w x y
    pure (d, .bits w (if first then x else y))
  | .shl, _, _, [some d], [a, b] => do
    let x ← readBits L g t w a; let s ← readBits L g t 32 b
    let r := if s.toNat ≥ w then 0 else truncBits w (x <<< s.toNat)
    pure (d, .bits w r)
  | .neg, _, _, [some d], [a] => do
    let x ← readBits L g t w a
    pure (d, .bits w (truncBits w (-x)))
  | .and, _, _, [some d], [a, b] =>
    if w = 1 then do
      let x ← readPred L g t a; let y ← readPred L g t b
      pure (d, .pred (x && y))
    else do
      let x ← readBits L g t w a; let y ← readBits L g t w b
      pure (d, .bits w (x &&& y))
  | .or, _, _, [some d], [a, b] =>
    if w = 1 then do
      let x ← readPred L g t a; let y ← readPred L g t b
      pure (d, .pred (x || y))
    else do
      let x ← readBits L g t w a; let y ← readBits L g t w b
      pure (d, .bits w (x ||| y))
  | .xor, _, _, [some d], [a, b] =>
    if w = 1 then do
      let x ← readPred L g t a; let y ← readPred L g t b
      pure (d, .pred (x ^^ y))
    else do
      let x ← readBits L g t w a; let y ← readBits L g t w b
      pure (d, .bits w (x ^^^ y))
  | .not, _, _, [some d], [a] =>
    if w = 1 then do
      let x ← readPred L g t a
      pure (d, .pred (!x))
    else do
      let x ← readBits L g t w a
      pure (d, .bits w (truncBits w (~~~x)))
  | .shr, _, _, [some d], [a, b] => do
    let x ← readBits L g t w a; let s ← readBits L g t 32 b
    if signed then
      pure (d, .bits w (truncBits w (BitVec.ofInt 64 (toSigned w x / 2 ^ min s.toNat w))))
    else pure (d, .bits w (if s.toNat ≥ w then 0 else x >>> s.toNat))
  | .setp cmp none, _, _, [some d], [a, b] => do
    let x ← readBits L g t w a; let y ← readBits L g t w b
    pure (d, .pred (compare cmp (i.ty.kind?.getD .b) w x y))
  | _, _, _, [some d], _ => do
    let v ← intResult L g t i
    pure (d, v)
  | _, _, _, _, _ => throw .noRule

/-- A proof-only factorization of the register result of a control instruction. -/
def controlEffect (L : Launch) (g : Nat) (t : TState) : Op → Exec (Nat × Value)
  | .int i => match i.rule with
    | some .threadInt => intEffect L g t i
    | _ => throw .noRule
  | .move m => match m.rule, m.kind, m.dsts, m.srcs with
    | some .threadMove, .scalar, [some d], [a] =>
      if m.ty = .pred then do
        let b ← readPred L g t a
        pure (d, .pred b)
      else do
        let w := m.ty.width
        let v ← readValue L g t w a
        unless v.bytes = w / 8 do throw .typeMismatch
        pure (d, v)
    | _, _, _, _ => throw .noRule
  | .mem a => match a.rule, a.addr.base, a.regs with
    | some .threadMove, .param p false, [d] =>
      let w := a.elem.width
      match L.params p with
      | some x => pure (d, a.ext.extendBits w x)
      | none => throw .badParam
    | _, _, _ => throw .noRule
  | .addr c => match c with
    | .cvta true .global 64 d a => do
      let x ← readBits L g t 64 a
      pure (d, .bits 64 x)
    | _ => throw .noRule
  | _ => throw .noRule

private theorem map_bind {α β γ : Type} (r : Exec α) (f : α → Exec β) (h : β → γ) :
    (r >>= f).map h = r >>= fun a => (f a).map h := by cases r <;> rfl

private theorem map_pure {α β : Type} (v : α) (f : α → β) :
    (pure v : Exec α).map f = pure (f v) := rfl

private theorem map_throw {α β : Type} (e : Fault) (f : α → β) :
    (throw e : Exec α).map f = throw e := rfl

/-- No assumption of `A` gives a rule for a control operation. -/
def NoControlRule (A : List Assumption) : Prop :=
  ∀ a ∈ A, ∀ L g t op, controlOp op = true → a.localRule L g t op = none

theorem NoControlRule.nil : NoControlRule [] := by simp [NoControlRule]

theorem NoControlRule.idealReal {name why : String} {s : Assumption.IdealScope}
    {A : List Assumption} (h : NoControlRule A) :
    NoControlRule (Assumption.idealReal name s why :: A) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · intro L g t op hc
    exact Assumption.idealReal_localRule_none fun f hf => by
      cases op <;> simp [controlOp, Assumption.FloatForm.ofOp] at hc hf
  · exact h a ha

theorem NoControlRule.approxExact {name why : String} {fs : List Assumption.ApproxForm}
    {A : List Assumption} (h : NoControlRule A) :
    NoControlRule (Assumption.approxExact name fs why :: A) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · intro L g t op hc
    exact Assumption.approxExact_localRule_none fun f hf => by
      cases op <;> simp [controlOp, Assumption.ApproxForm.ofOp] at hc hf
  · exact h a ha

theorem execLocalA_noOverride {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} (h : ∀ a ∈ A, a.localRule L g t op = none)
    (hS : Assumption.SegFreePc A t.pc := by seg_free) :
    execLocalA A L g t op = execLocal L g t op := by
  rw [(hS.at rfl).exec, execLocalRule_of_none h]

/-- `execInt` and `intEffect` agree on a control instruction. The carry forms are excluded: they
write the condition code through `setCarry`, which the register pair of `intEffect` cannot
express. -/
theorem execInt_intEffect {L : Launch} {g : Nat} {t : TState} {i : IntInstr}
    (h : i.dsts.length = 1) (hcf : carryFree i.op = true) :
    execInt L g t i = (intEffect L g t i).map (fun dv => next (setReg t dv.1 dv.2)) := by
  rcases i with ⟨op, ty, sat, dsts, srcs⟩
  simp only at h
  simp only [execInt, intEffect]
  split
  all_goals first
    | (exact absurd hcf Bool.false_ne_true)
    | (simp only [List.length_cons, List.length_nil] at h; omega)
    | (simp only [map_bind]; congr 1; funext va; congr 1; funext vb
       cases va <;> cases vb <;> (try cases ‹PtrTarget›) <;> simp only [map_bind, map_pure])
    | (simp only [map_bind]; congr 1; funext va
       cases va <;> (try cases ‹PtrTarget›) <;> simp only [map_bind, map_pure])
    | (split <;> simp only [map_bind, map_pure])
    | simp only [map_bind, map_pure, map_throw]

theorem exec_controlEffect {A : List Assumption} (hA : NoControlRule A) {L : Launch} {g : Nat}
    {t : TState} {op : Op} (hc : controlOp op = true)
    (hS : Assumption.SegFreePc A t.pc := by seg_free) :
    execLocalA A L g t op =
      (controlEffect L g t op).map (fun dv => next (setReg t dv.1 dv.2)) := by
  rw [execLocalA_noOverride (fun a ha => hA a ha L g t op hc)]
  cases op <;> simp only [controlOp] at hc <;> try contradiction
  case int i =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rw [execLocal_int hc.1.1]
    simp only [controlEffect, hc.1.1]
    exact execInt_intEffect hc.1.2 hc.2
  case move m =>
    rcases m with ⟨kind, ty, dsts, srcs⟩
    simp only [beq_iff_eq] at hc
    subst hc
    simp only [execLocal, Op.rule, controlEffect]
    cases hr : MoveInstr.rule ⟨.scalar, ty, dsts, srcs⟩ with
    | none => rfl
    | some r =>
      cases r <;> try rfl
      simp only [execMove]
      split
      · split_ifs
        · simp only [map_bind, map_pure]
        · simp only [map_bind]
          congr 1
          funext v
          split <;> rfl
      all_goals first | contradiction | (split <;> first | rfl | simp_all)
  case mem a =>
    simp only [execLocal, Op.rule, controlEffect]
    cases hr : a.rule with
    | none => rfl
    | some r =>
      cases r <;> try rfl
      simp only [execMove]
      split <;> split <;> simp_all [map_pure, map_throw]
  case addr c =>
    cases c with
    | cvta toGlobal sp w d a =>
      split at hc
      · rename_i heq
        injection heq with h1 h2 h3 h4 h5
        subst h1; subst h2; subst h3; subst h4; subst h5
        simp only [execLocal_cvta (c := .cvta true .global 64 d a) (by rfl), execCvta_global,
          controlEffect, map_bind, map_pure]
      · contradiction
    | _ => simp at hc

/-- Agreement of registers used in an operand implies agreement of its integer value. -/
theorem readBits_congr {L : Launch} {g w : Nat} {t u : TState} {a : Opnd}
    (h : ∀ r, a = .reg r → t.regs r = u.regs r) : readBits L g t w a = readBits L g u w a := by
  cases a <;> try rfl
  rename_i r
  simp only [readBits, readReg, h r rfl]

theorem readPred_congr {L : Launch} {g : Nat} {t u : TState} {a : Opnd}
    (h : ∀ r, a = .reg r → t.regs r = u.regs r) : readPred L g t a = readPred L g u a := by
  cases a <;> try rfl
  rename_i r
  simp only [readPred, readReg, h r rfl]

theorem readValue_congr {L : Launch} {g w : Nat} {t u : TState} {a : Opnd}
    (h : ∀ r, a = .reg r → t.regs r = u.regs r) : readValue L g t w a = readValue L g u w a := by
  cases a with
  | reg r => simp [readValue, readReg, h r rfl]
  | f32imm => rfl
  | imm | sreg | sharedSym | localSym | paramSym => rfl

theorem boolCombine_congr {L : Launch} {g : Nat} {t u : TState} {bop : Option BoolOp}
    {cs : List Opnd} (hp : ∀ a ∈ cs, readPred L g t a = readPred L g u a) :
    boolCombine L g t bop cs = boolCombine L g u bop cs := by
  unfold boolCombine
  split <;> simp_all

/-- The value of an integer instruction depends on the registers of its sources only. -/
theorem intResult_congr {L : Launch} {g : Nat} {t u : TState} {i : IntInstr}
    (hb : ∀ a ∈ i.srcs, ∀ w, readBits L g t w a = readBits L g u w a)
    (hp : ∀ a ∈ i.srcs, readPred L g t a = readPred L g u a) :
    intResult L g t i = intResult L g u i := by
  rcases i with ⟨op, ty, sat, dsts, srcs⟩
  simp only at hb hp
  unfold intResult
  split
  · split
    all_goals subst_vars
    all_goals try simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb hp
    all_goals first
      | rfl
      | (rw [boolCombine_congr hp.2.2]; simp only [hb])
      | simp only [hb, hp]
  · rfl

theorem controlEffect_congr {L : Launch} {g : Nat} {t u : TState} {op : Op}
    (h : ∀ a ∈ controlArgs op, ∀ r, a = .reg r → t.regs r = u.regs r) :
    controlEffect L g t op = controlEffect L g u op := by
  have hb : ∀ a ∈ controlArgs op, ∀ w, readBits L g t w a = readBits L g u w a := by
    intro a ha w; exact readBits_congr (h a ha)
  have hv : ∀ a ∈ controlArgs op, ∀ w, readValue L g t w a = readValue L g u w a := by
    intro a ha w; exact readValue_congr (h a ha)
  have hp : ∀ a ∈ controlArgs op, readPred L g t a = readPred L g u a := by
    intro a ha; exact readPred_congr (h a ha)
  cases op <;> simp only [controlArgs] at hb hv hp
  case int i =>
    simp only [controlEffect]
    split
    · have hI := intResult_congr (i := i) hb hp
      rcases i with ⟨op, ty, sat, dsts, srcs⟩
      simp only [intEffect]
      split
      all_goals simp only [List.forall_mem_cons] at hb hv hp
      all_goals simp_all only []
    · rfl
  case move m =>
    rcases m with ⟨kind, ty, dsts, srcs⟩
    simp only [controlEffect]
    split
    · simp only [List.forall_mem_cons] at hb hv hp
      simp_all only []
    · rfl
  case addr c =>
    simp only [controlEffect]
    split
    · simp only [List.forall_mem_cons] at hb hv hp
      simp_all only []
    · rfl
  all_goals rfl

end
end PTX.Proof
