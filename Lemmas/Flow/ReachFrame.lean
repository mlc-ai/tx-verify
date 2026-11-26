-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataLoad
public import Lemmas.Flow.Determinism

@[expose] public section

/-! # Facts on registers that local code between events does not write

A proof tool, generic over the kernel, for the data steps of a value machine (`Code.Reach`,
`Lemmas/Flow/DataLoad.lean`) across code the value machine does not compute: control code
between two events, possibly with branches. A set `S` of positions whose instructions are local,
no `brx`, write no register of `rs`, and from which a step goes to `S` or to an unguarded event
instruction (`frameSetB`) keeps every fact on `rs` up to the first event (`reach_frameSet`).
`SegD.reach_then` composes a run with a `Reach` after it. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The instruction at `q` is an unguarded event instruction. -/
def evAtB (K : Kernel) (q : Nat) : Bool :=
  match K.code[q]? with
  | some ins => ins.guard.isNone && !ins.op.isLocal
  | none => false

/-- An instruction that is no indexed branch. -/
def noBrx : Op → Bool
  | .brx .. => false
  | _ => true

/-- Each position of `S` holds a local instruction, no `brx`, that writes no register of `rs`,
and its next position and branch target are in `S` or hold an unguarded event instruction. -/
def frameSetB (K : Kernel) (S rs : List Nat) : Bool :=
  S.all fun pc => match K.code[pc]? with
    | some ins => ins.op.isLocal && noBrx ins.op &&
        rs.all (fun r => !(writesRegs ins.op).contains r) &&
        [pc + 1, nextPc ins.op pc].all fun q => S.contains q || evAtB K q
    | none => false

theorem no_tau_evAt {t t1 : TState} (he : evAtB K t.pc = true) : ¬ Tau K A L g t t1 := by
  intro h
  unfold Tau out at h
  unfold evAtB at he
  cases hf : t.fault with
  | some f => rw [hf] at h; cases h
  | none =>
    rw [hf] at h
    cases hc : K.code[t.pc]? with
    | none => rw [hc] at he; cases he
    | some ins =>
      rw [hc] at he h
      dsimp only at h
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_eq_eq_not,
        Bool.not_true] at he
      obtain ⟨hg, hl⟩ := he
      simp only [hg, guardHolds, hl, Bool.false_eq_true, ↓reduceIte] at h
      cases h

/-- One local step from a position of a frame set keeps the facts and lands in the set or at
an event instruction. -/
theorem tau_frameSet (hA : RulesFrame A) {S rs : List Nat} (hB : frameSetB K S rs = true)
    (hS : ∀ pc ∈ S, Assumption.SegFreePc A pc) {t t1 : TState} (hp : S.contains t.pc = true)
    (h : Tau K A L g t t1) :
    (S.contains t1.pc || evAtB K t1.pc) = true ∧ ∀ r ∈ rs, t1.regs r = t.regs r := by
  have hm : t.pc ∈ S := by simpa using hp
  have hb := List.all_eq_true.mp hB t.pc hm
  unfold Tau out at h
  cases hf : t.fault with
  | some f => rw [hf] at h; cases h
  | none =>
    rw [hf] at h
    cases hc : K.code[t.pc]? with
    | none => rw [hc] at hb; cases hb
    | some ins =>
      rw [hc] at hb h
      dsimp only at h
      simp only [Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hb
      obtain ⟨⟨⟨hl, hx⟩, hw⟩, hq1, hq2⟩ := hb
      cases hg : guardHolds t ins.guard with
      | error e => rw [hg] at h; cases h
      | ok b =>
        rw [hg] at h
        cases b with
        | false =>
          cases h
          exact ⟨hq1, fun _ _ => rfl⟩
        | true =>
          simp only [hl, ↓reduceIte] at h
          cases he : execLocalA A L g t ins.op with
          | error e => rw [he] at h; cases h
          | ok t' =>
            rw [he] at h
            cases h
            have fr := execLocalA_frame hA he (hS _ hm)
            refine ⟨?_, fun r hr => fr.regs r fun hmem => ?_⟩
            · rcases fr.pc with e | e
              · rw [e]; exact hq2
              · cases hop : ins.op <;> simp_all [noBrx, BrxTarget]
            · have := hw r hr
              simp_all

/-- **Facts on registers a frame set does not write** hold at every state from its start. -/
theorem rtg_frameSet (hA : RulesFrame A) {S : List Nat} {H : List (Nat × Value)}
    (hB : frameSetB K S (H.map Prod.fst) = true) (hS : ∀ pc ∈ S, Assumption.SegFreePc A pc)
    {u t : TState} (hu : (S.contains u.pc || evAtB K u.pc) = true) (hH : Holds u.regs H)
    (hr : Relation.ReflTransGen (Tau K A L g) u t) :
    (S.contains t.pc || evAtB K t.pc) = true ∧ Holds t.regs H := by
  induction hr with
  | refl => exact ⟨hu, hH⟩
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hHb⟩ := ih
    rcases Bool.or_eq_true_iff.mp hb with hb | hb
    · obtain ⟨hc, hreg⟩ := tau_frameSet hA hB hS hb hbc
      refine ⟨hc, holds_of_mem fun r v hm => ?_⟩
      rw [hreg r (List.mem_map.mpr ⟨(r, v), hm, rfl⟩)]
      exact holds_mem hHb hm
    · exact absurd hbc (no_tau_evAt hb)

/-- **Control code keeps the facts it does not write**: from a position of a frame set (or an
event instruction), the first state that performs an event holds them. -/
theorem reach_frameSet (hA : RulesFrame A) {S : List Nat} {H F : List (Nat × Value)} {p : Nat}
    (hB : frameSetB K S (H.map Prod.fst) = true) (hS : ∀ pc ∈ S, Assumption.SegFreePc A pc)
    (hp : (S.contains p || evAtB K p) = true) (hF : ∀ R, Holds R F → Holds R H) :
    Reach K A L g p F H := by
  intro u hu
  obtain ⟨hup, -, -, -, huF⟩ := hu
  exact .inl fun t' hr _ => (rtg_frameSet hA hB hS (hup ▸ hp) (hF _ huF) hr).2

/-- **A run followed by a `Reach`.** -/
theorem SegD.reach_then {n s q : Nat} {F G H : List (Nat × Value)} {C : Prop}
    (h : SegD K A L g n s F q G C) (hR : Reach K A L g q G H) : Reach K A L g s F H := by
  intro u hu
  by_cases hC : C
  · obtain ⟨t2, hrun, ht2⟩ := (h u hu).1 hC
    rcases hR t2 ht2 with h2 | hd
    · refine .inl fun t' hr hs => h2 t' ?_ hs
      rcases rtg_tau_total (run_rtg hrun) hr with h' | h'
      · exact h'
      · rcases Relation.ReflTransGen.cases_head h' with e | ⟨c, hc, -⟩
        · exact e ▸ .refl
        · exact absurd hc (not_tau_of_stops hs)
    · exact .inr (dead_of_run hrun hd)
  · exact .inr ((h u hu).2 hC)

end
end PTX.Flow.Code
