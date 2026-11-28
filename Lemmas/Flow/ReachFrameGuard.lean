-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ReachFrame

@[expose] public section

/-! # `reach_frameSet` through guarded events

A proof tool, generic over the kernel. `ReachFrame.lean`'s frame set ends at unguarded events. A
guarded event instruction is skipped when its guard is false (the thread goes on to the next
position with its registers) and is where a thread stops when it is true. `frameSetG S rs` also
admits such positions in `S`: a first state that performs an event holds the facts on `rs`
(`reach_frameSetG`), wherever it stops. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- Each position of `S` holds a local instruction that writes no register of `rs`, or a guarded
event instruction; the next position (and a branch target) is in `S` or holds an unguarded
event instruction. -/
def frameSetG (K : Kernel) (S rs : List Nat) : Bool :=
  S.all fun pc => match K.code[pc]? with
    | some ins =>
      (if ins.op.isLocal then noBrx ins.op && rs.all (fun r => !(writesRegs ins.op).contains r)
        && [nextPc ins.op pc].all fun q => S.contains q || evAtB K q
      else ins.guard.isSome) && [pc + 1].all fun q => S.contains q || evAtB K q
    | none => false

theorem tau_frameSetG (hA : RulesFrame A) {S rs : List Nat} (hB : frameSetG K S rs = true)
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
        or_false, forall_eq] at hb
      obtain ⟨hk, hq1⟩ := hb
      cases hg : guardHolds t ins.guard with
      | error e => rw [hg] at h; cases h
      | ok b =>
        rw [hg] at h
        cases b with
        | false => cases h; exact ⟨hq1, fun _ _ => rfl⟩
        | true =>
          cases hl : ins.op.isLocal
          · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h; cases h
          · simp only [hl, ↓reduceIte] at hk h
            obtain ⟨⟨hx, hw⟩, hq2⟩ := by simpa only [Bool.and_eq_true, List.all_eq_true,
              List.mem_cons, List.not_mem_nil, or_false, forall_eq] using hk
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

theorem rtg_frameSetG (hA : RulesFrame A) {S : List Nat} {H : List (Nat × Value)}
    (hB : frameSetG K S (H.map Prod.fst) = true) (hS : ∀ pc ∈ S, Assumption.SegFreePc A pc)
    {u t : TState} (hu : (S.contains u.pc || evAtB K u.pc) = true) (hH : Holds u.regs H)
    (hr : Relation.ReflTransGen (Tau K A L g) u t) :
    (S.contains t.pc || evAtB K t.pc) = true ∧ Holds t.regs H := by
  induction hr with
  | refl => exact ⟨hu, hH⟩
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hHb⟩ := ih
    rcases Bool.or_eq_true_iff.mp hb with hb | hb
    · obtain ⟨hc, hreg⟩ := tau_frameSetG hA hB hS hb hbc
      refine ⟨hc, holds_of_mem fun r v hm => ?_⟩
      rw [hreg r (List.mem_map.mpr ⟨(r, v), hm, rfl⟩)]
      exact holds_mem hHb hm
    · exact absurd hbc (no_tau_evAt hb)

/-- **Control code keeps the facts it does not write**, through guarded events: from a position
of the set (or an unguarded event), the first state that performs an event holds them. -/
theorem reach_frameSetG (hA : RulesFrame A) {S : List Nat} {H F : List (Nat × Value)} {p : Nat}
    (hB : frameSetG K S (H.map Prod.fst) = true) (hS : ∀ pc ∈ S, Assumption.SegFreePc A pc)
    (hp : (S.contains p || evAtB K p) = true) (hF : ∀ R, Holds R F → Holds R H) :
    Reach K A L g p F H := by
  intro u hu
  obtain ⟨hup, -, -, -, huF⟩ := hu
  exact .inl fun t' hr _ => (rtg_frameSetG hA hB hS (hup ▸ hp) (hF _ huF) hr).2

end
end PTX.Flow.Code
