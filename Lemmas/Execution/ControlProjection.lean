-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.ControlEffect

@[expose] public section

namespace PTX.Proof
open PTX
noncomputable section

/-- The address/control registers agree; data registers and vector data buffers may differ. -/
structure ControlAgree (S : Nat → Bool) (t u : TState) : Prop where
  pc : t.pc = u.pc
  sub : t.sub = u.sub
  regs : ∀ r, S r = true → t.regs r = u.regs r

def staticArg (S : Nat → Bool) : Opnd → Bool
  | .reg r => S r
  | _ => true

/-- A `brx.idx`, whose next position depends on its index register. -/
def indexedBranch : Op → Bool
  | .brx .. => true
  | _ => false

def localProjection (S : Nat → Bool) (op : Op) : Bool :=
  ((writesRegs op).all (fun r => !S r) && !indexedBranch op) ||
    (controlOp op && (controlArgs op).all (staticArg S))

namespace ControlAgree
variable {S : Nat → Bool} {t u : TState}

theorem refl (t : TState) : ControlAgree S t t := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem next (h : ControlAgree S t u) : ControlAgree S (PTX.next t) (PTX.next u) :=
  ⟨congrArg (· + 1) h.pc, h.sub, h.regs⟩

theorem setReg (h : ControlAgree S t u) {r : Nat} {v w : Value}
    (hr : S r = false ∨ v = w) : ControlAgree S (PTX.setReg t r v) (PTX.setReg u r w) := by
  refine ⟨h.pc, h.sub, ?_⟩
  intro s hs
  by_cases hsr : s = r
  · subst hsr
    rcases hr with hr | rfl
    · simp [hr] at hs
    · simp [PTX.setReg]
  · simp only [PTX.setReg, Function.update_of_ne hsr]
    exact h.regs s hs

theorem readBits {L : Launch} {g w : Nat} {a : Opnd} (h : ControlAgree S t u)
    (ha : staticArg S a = true) : PTX.readBits L g t w a = PTX.readBits L g u w a := by
  apply readBits_congr
  rintro r rfl
  exact h.regs r ha

theorem readValue {L : Launch} {g w : Nat} {a : Opnd} (h : ControlAgree S t u)
    (ha : staticArg S a = true) : PTX.readValue L g t w a = PTX.readValue L g u w a := by
  apply readValue_congr
  rintro r rfl
  exact h.regs r ha

theorem local_result {A : List Assumption} (hF : RulesFrame A) (hC : NoControlRule A)
    {L : Launch} {g : Nat} {op : Op} {t' u' : TState}
    (h : ControlAgree S t u) (hc : localProjection S op = true)
    (ht : execLocalA A L g t op = .ok t')
    (hu : execLocalA A L g u op = .ok u') (hS : Assumption.SegFreePc A t.pc := by seg_free)
    (hSu : Assumption.SegFreePc A u.pc := by seg_free) :
    ControlAgree S t' u' := by
  simp only [localProjection, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hc
  rcases hc with ⟨hdata, hbrx⟩ | ⟨hop, hargs⟩
  · have ft := execLocalA_frame hF ht hS
    have fu := execLocalA_frame hF hu hSu
    have nb : ∀ p, ¬ BrxTarget op p := by
      intro p hp
      unfold BrxTarget at hp
      split at hp
      · simp_all [indexedBranch]
      · exact hp
    refine ⟨by rw [ft.pc.resolve_right (nb _), fu.pc.resolve_right (nb _), h.pc],
      by rw [ft.sub, fu.sub, h.sub], ?_⟩
    intro r hr
    have hn : r ∉ writesRegs op := by
      intro hm
      have hh := (List.all_eq_true.mp hdata) r hm
      simp [hr] at hh
    rw [ft.regs r hn, fu.regs r hn]
    exact h.regs r hr
  · have he : controlEffect L g t op = controlEffect L g u op := by
      apply controlEffect_congr
      intro a ha r har
      have hh := (List.all_eq_true.mp hargs) a ha
      subst har
      exact h.regs r hh
    rw [exec_controlEffect hC hop hS, he] at ht
    rw [exec_controlEffect hC hop hSu] at hu
    cases hv : controlEffect L g u op with
    | error f => simp [hv, Except.map] at hu
    | ok dv =>
      simp only [hv, Except.map, Except.ok.injEq] at ht hu
      subst ht hu
      exact (h.setReg (.inr rfl)).next


theorem setRegs {ds : List Nat} {vs ws : List Value} (h : ControlAgree S t u)
    (hd : ∀ r ∈ ds, S r = false) : ControlAgree S (PTX.setRegs t ds vs) (PTX.setRegs u ds ws) := by
  have frame : ∀ (t : TState) (vs : List Value),
      (PTX.setRegs t ds vs).pc = t.pc ∧ (PTX.setRegs t ds vs).sub = t.sub ∧
      ∀ r, S r = true → (PTX.setRegs t ds vs).regs r = t.regs r := by
    intro t vs
    induction ds generalizing t vs with
    | nil => exact ⟨rfl, rfl, fun _ _ => rfl⟩
    | cons d ds ih =>
      cases vs with
      | nil => exact ⟨rfl, rfl, fun _ _ => rfl⟩
      | cons v vs =>
        have hh := ih (fun r hr => hd r (by simp [hr])) (PTX.setReg t d v) vs
        refine ⟨hh.1, hh.2.1, ?_⟩
        intro r hr
        rw [show PTX.setRegs t (d :: ds) (v :: vs) =
          PTX.setRegs (PTX.setReg t d v) ds vs from rfl, hh.2.2 r hr]
        have hn : r ≠ d := by intro he; subst r; rw [hd d (by simp)] at hr; cases hr
        exact Function.update_of_ne hn _ _
  obtain ⟨tp, ts, tr⟩ := frame t vs
  obtain ⟨up, us, ur⟩ := frame u ws
  exact ⟨by rw [tp, up, h.pc], by rw [ts, us, h.sub],
    fun r hr => by rw [tr r hr, ur r hr, h.regs r hr]⟩

theorem afterLoad {ds : List Nat} {bs cs : List (Option Byte)} (h : ControlAgree S t u)
    (hd : ∀ r ∈ ds, S r = false) :
    (PTX.afterLoad t ds bs).fault ≠ none ∨ (PTX.afterLoad u ds cs).fault ≠ none ∨
      ControlAgree S (PTX.afterLoad t ds bs) (PTX.afterLoad u ds cs) := by
  unfold PTX.afterLoad
  cases hb : rebuild 3 bs with
  | error f =>
    simp only []
    exact .inl (by simp)
  | ok v =>
    cases hc : rebuild 3 cs with
    | error f =>
      simp only []
      exact .inr (.inl (by simp))
    | ok w =>
      simp only []
      right; right
      by_cases hs : u.sub + 1 < ds.length
      · rw [ite_eq_left (by rw [h.sub]; exact hs), ite_eq_left hs]
        exact ⟨h.pc, congrArg (· + 1) h.sub, h.regs⟩
      · rw [ite_eq_right (by rw [h.sub]; exact hs), ite_eq_right hs]
        have hh := h.setRegs (vs := t.acc ++ [v]) (ws := u.acc ++ [w]) hd
        exact ⟨congrArg (· + 1) h.pc, rfl, hh.regs⟩

theorem afterStore {srcs : List Opnd} (h : ControlAgree S t u) :
    ControlAgree S (PTX.afterStore t srcs) (PTX.afterStore u srcs) := by
  unfold PTX.afterStore
  rw [h.sub]
  split
  · exact ⟨h.pc, rfl, h.regs⟩
  · exact ⟨congrArg (· + 1) h.pc, rfl, h.regs⟩

theorem effAddr {L : Launch} {g : Nat} {sp : Space} {r : Nat} {off : Int}
    (h : ControlAgree S t u) (hr : S r = true) :
    PTX.effAddr L g t sp r off = PTX.effAddr L g u sp r off := by
  cases sp <;> simp only [PTX.effAddr, PTX.sharedEffAddr, PTX.readSharedAddress, PTX.readReg,
    h.regs r hr, h.readValue (show staticArg S (.reg r) = true from hr),
    h.readBits (show staticArg S (.reg r) = true from hr)]

end ControlAgree
end
end PTX.Proof
