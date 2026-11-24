-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegDead
public import Lemmas.Register.RegisterFrame

@[expose] public section

/-! # Registers a straight-line run does not write keep their values

A proof tool, generic over the kernel (promoted from tml-fa4's `Proof2/Lib/RunFrame.lean`). A run of
local steps over straight-line code (no jump), at positions where no assumption takes a segment and
every local rule writes only its instruction's registers (`RulesFrame`), keeps every register that
no instruction of the code writes (`run_frame`). The condition on the code is a Boolean check on the
code's slice (`frameB`), so a piece of a site machine's walk carries facts it does not mention:
`SegD.frame` adds facts on unwritten registers to both ends of a piece. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- An instruction that continues at the next position. -/
def noJump : Op → Bool
  | .bra .. | .brx .. => false
  | _ => true

/-- The instructions `ins` are local, no jump, and none writes a register of `rs`. -/
def frameB (ins : List Instr) (rs : List Nat) : Bool :=
  ins.all fun i => i.op.isLocal && noJump i.op && rs.all fun r => !(writesRegs i.op).contains r

theorem nextPc_noJump {op : Op} (h : noJump op = true) (pc : Nat) : nextPc op pc = pc + 1 := by
  cases op <;> simp_all [noJump, nextPc]

theorem brx_noJump {op : Op} (h : noJump op = true) (pc : Nat) : ¬ BrxTarget op pc := by
  cases op <;> simp_all [noJump, BrxTarget]

/-- **One local step of a no-jump instruction** keeps the registers it does not write. -/
theorem tau_frame (hA : RulesFrame A) {t t1 : TState} {ins : Instr}
    (hc : K.code[t.pc]? = some ins) (hl : ins.op.isLocal = true) (hj : noJump ins.op = true)
    (hS : Assumption.SegFreePc A t.pc) (ht : tauStep K A L g t = some t1) (hf : t.fault = none) :
    t1.pc = t.pc + 1 ∧ t1.fault = none ∧ ∀ r, r ∉ writesRegs ins.op → t1.regs r = t.regs r := by
  unfold tauStep out at ht
  rw [hf, hc] at ht
  simp only at ht
  cases hg : guardHolds t ins.guard with
  | error e => rw [hg] at ht; cases ht
  | ok b =>
    rw [hg] at ht
    cases b with
    | false =>
      simp only [Option.some.injEq] at ht
      subst ht
      exact ⟨rfl, hf, fun _ _ => rfl⟩
    | true =>
      simp only [hl, ↓reduceIte] at ht
      cases he : execLocalA A L g t ins.op with
      | error e => rw [he] at ht; cases ht
      | ok t' =>
        rw [he] at ht
        simp only [Option.some.injEq] at ht
        subst ht
        have fr := execLocalA_frame hA he hS
        refine ⟨?_, fr.fault.trans hf, fr.regs⟩
        rcases fr.pc with h | h
        · rw [h, nextPc_noJump hj]
        · exact absurd h (brx_noJump hj _)

/-- **A straight-line run keeps the registers its code does not write.** -/
theorem run_frame (hA : RulesFrame A) {rs : List Nat} :
    ∀ (n : Nat) (s : Nat) (ins : List Instr) (t t' : TState),
      (K.code.drop s).take n = ins → ins.length = n → frameB ins rs = true →
      (∀ i < n, Assumption.SegFreePc A (s + i)) → t.pc = s → t.fault = none →
      run K A L g n t = some t' → ∀ r ∈ rs, t'.regs r = t.regs r
  | 0, _, _, t, t', _, _, _, _, _, _, h => by
    simp only [run, Option.some.injEq] at h; subst h; intros; rfl
  | n + 1, s, ins, t, t', hcode, hlen, hB, hS, hpc, hf, h => by
    simp only [run] at h
    cases ht : tauStep K A L g t with
    | none => rw [ht] at h; cases h
    | some t1 =>
      rw [ht, Option.bind_some] at h
      have hs : s < K.code.length := by
        have := congrArg List.length hcode
        simp only [List.length_take, List.length_drop, hlen] at this
        omega
      rw [List.drop_eq_getElem_cons hs, List.take_succ_cons] at hcode
      subst hcode
      have hk : K.code[s]? = some K.code[s] := List.getElem?_eq_getElem hs
      simp only [frameB, List.all_cons, Bool.and_eq_true] at hB
      obtain ⟨⟨⟨hl, hj⟩, hw⟩, hB⟩ := hB
      have hS0 := hS 0 (by omega)
      rw [Nat.add_zero, ← hpc] at hS0
      have hk' : K.code[t.pc]? = some K.code[s] := by rw [hpc]; exact hk
      obtain ⟨hpc1, hf1, hfr⟩ := tau_frame hA hk' hl hj hS0 ht hf
      have ih := run_frame hA n (s + 1) _ t1 t' rfl
        (by simp only [List.length_cons] at hlen; omega) hB
        (fun i hi => by rw [Nat.add_assoc, Nat.add_comm 1 i]; exact hS (i + 1) (by omega))
        (by rw [hpc1, hpc]) hf1 h
      intro r hr
      rw [ih r hr, hfr r]
      have := List.all_eq_true.mp hw r hr
      simpa using this

theorem holds_of_mem {R : Nat → Option Value} :
    ∀ {H : List (Nat × Value)}, (∀ r v, (r, v) ∈ H → R r = some v) → Holds R H
  | [], _ => trivial
  | (r, v) :: H, h => ⟨h r v (by simp), holds_of_mem fun r' v' hm => h r' v' (by simp [hm])⟩

/-- **A piece with facts on registers its code does not write**: the facts `H` hold at both ends. -/
theorem SegD.frame (hA : RulesFrame A) {n s b : Nat} {F G H : List (Nat × Value)} {C : Prop}
    {ins : List Instr} (h : SegD K A L g n s F b G C) (hcode : (K.code.drop s).take n = ins)
    (hlen : ins.length = n) (hB : frameB ins (H.map Prod.fst) = true)
    (hS : ∀ i < n, Assumption.SegFreePc A (s + i)) :
    SegD K A L g n s (F ++ H) b (G ++ H) C := by
  intro t ht
  have hF : At t s F := At.mono ht ((holds_append _ _ _).mp ht.2.2.2.2).1
  refine ⟨fun hc => ?_, (h t hF).2⟩
  obtain ⟨t', hr, ht'⟩ := (h t hF).1 hc
  refine ⟨t', hr, ht'.1, ht'.2.1, ht'.2.2.1, ht'.2.2.2.1,
    (holds_append _ _ _).mpr ⟨ht'.2.2.2.2, ?_⟩⟩
  have hH := ((holds_append _ _ _).mp ht.2.2.2.2).2
  have hfr := run_frame hA n s ins t t' hcode hlen hB hS ht.1 ht.2.2.2.1 hr
  refine holds_of_mem fun r v hrv => ?_
  rw [hfr r (List.mem_map_of_mem (f := Prod.fst) hrv)]
  exact holds_mem hH hrv

end
end PTX.Flow
