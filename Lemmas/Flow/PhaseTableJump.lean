-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.PhaseTable
public import Lemmas.Flow.Run

@[expose] public section

/-! # Facts by position with runs that jump over positions

A proof tool, generic over the kernel. As `PhaseTable`, a table gives the facts that hold at each
position of a region, but a `spec` position starts a run of several local steps whose positions
the region does not list: `hjump` says that the local steps from a state at such a position (with
the table's facts) reach a state of the region with the table's facts there, or that the thread is
dead (a generated run, `SegD.outs_lit`, by `run_rtg`). Where the thread stops is again not decided
here: the first state that performs an event holds the table's facts at its position. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **One local step from a position of the region.** -/
theorem tau_tableN (hA : RulesFrame A) {ivs keys post spec V1 V2}
    (hscan : tabScan K ivs keys post spec = true)
    (hS : ∀ pc, inIvs ivs pc = true → spec pc = false → Assumption.SegFreePc A pc)
    {t t1 : TState} (hp : inIvs ivs t.pc = true) (hsp' : spec t.pc = false)
    (hH : TabAt keys post V1 V2 t) (h : Tau K A L g t t1) :
    ((inIvs ivs t1.pc || evAtB K t1.pc) = true ∧ TabAt keys post V1 V2 t1) ∨
      Machine.Dead (K := K) (A := A) (L := L) (g := g) t1 := by
  obtain ⟨hsub, hacc, hH⟩ := hH
  obtain ⟨ins, hc, hat⟩ := tabScan_at hscan hp
  simp only [tabAt, hsp', Bool.false_or] at hat
  have hS0 := hS _ hp hsp'
  unfold Tau out at h
  cases hf : t.fault with
  | some f => rw [hf] at h; cases h
  | none =>
    rw [hf] at h
    rw [hc] at h
    dsimp only at h
    cases hg : guardHolds t ins.guard with
    | error e => rw [hg] at h; cases h
    | ok b =>
      rw [hg] at h
      cases b with
      | false =>
        cases h
        by_cases hl : ins.op.isLocal = true
        · simp only [hl, ↓reduceIte, Bool.and_eq_true, List.all_eq_true, List.mem_cons,
            List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hat
          obtain ⟨-, -, ⟨⟨hq, hk⟩, hpo⟩⟩ := hat
          refine .inl ⟨hq, rfl, rfl, holds_phi (q := t.pc + 1) (by simpa using hpo) hH
            fun r hr => ⟨?_, rfl⟩⟩
          simpa using (hk r hr).1
        · simp only [hl, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, List.all_eq_true,
            List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hat
          obtain ⟨-, ⟨hq, hk⟩, hpo⟩ := hat
          refine .inl ⟨hq, rfl, rfl, holds_phi (q := t.pc + 1) (by simpa using hpo) hH
            fun r hr => ⟨?_, rfl⟩⟩
          simpa using hk r hr
      | true =>
        by_cases hl : ins.op.isLocal = true
        · simp only [hl, ↓reduceIte] at h
          cases he : execLocalA A L g t ins.op with
          | error e => rw [he] at h; cases h
          | ok t' =>
            rw [he] at h
            cases h
            have fr := execLocalA_frame hA he hS0
            simp only [hl, ↓reduceIte, Bool.and_eq_true, List.all_eq_true, List.mem_cons,
              List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hat
            obtain ⟨hbr, ⟨⟨hq1, hk1⟩, hpo1⟩, ⟨hq2, hk2⟩, hpo2⟩ := hat
            rcases fr.pc with e | e
            · refine .inl ⟨by rw [e]; exact hq1, fr.sub.trans hsub, fr.acc.trans hacc, ?_⟩
              rw [e]
              refine holds_phi (by simpa using hpo1) hH fun r hr => ⟨?_, ?_⟩
              · simpa using (hk1 r hr).1
              · refine fr.regs r fun hmem => ?_
                have := (hk1 r hr).2
                simp [hmem] at this
            · cases hop : ins.op <;> simp_all [noBrx, BrxTarget]
        · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h
          cases h

/-- A state of the region with the table's facts. -/
def TabGood (K : Kernel) (ivs : List (Nat × Nat)) (keys : Nat → List Nat) (post : Nat → Bool)
    (V1 V2 : Nat → Value) (t : TState) : Prop :=
  (inIvs ivs t.pc || evAtB K t.pc) = true ∧ TabAt keys post V1 V2 t

/-- **Every local path from a position of the region** reaches, at its first event, the table's
facts, or the thread is dead. -/
theorem rtg_tableJ (hA : RulesFrame A) {ivs keys post spec V1 V2}
    (hscan : tabScan K ivs keys post spec = true)
    (hS : ∀ pc, inIvs ivs pc = true → spec pc = false → Assumption.SegFreePc A pc)
    (hjump : ∀ pc, spec pc = true → inIvs ivs pc = true → ∀ t : TState, t.pc = pc →
      t.fault = none → TabAt keys post V1 V2 t →
      (∃ w, Relation.ReflTransGen (Tau K A L g) t w ∧ t ≠ w ∧ TabGood K ivs keys post V1 V2 w) ∨
        Machine.Dead (K := K) (A := A) (L := L) (g := g) t)
    {u t' : TState} (hu : TabGood K ivs keys post V1 V2 u)
    (hr : Relation.ReflTransGen (Tau K A L g) u t') (hs : Stops K A L g t') :
    TabGood K ivs keys post V1 V2 t' ∨ Machine.Dead (K := K) (A := A) (L := L) (g := g) u := by
  have key : ∀ b, Relation.ReflTransGen (Tau K A L g) u b →
      (∃ w, Relation.ReflTransGen (Tau K A L g) b w ∧ TabGood K ivs keys post V1 V2 w) ∨
        Machine.Dead (K := K) (A := A) (L := L) (g := g) u := by
    intro b hb
    induction hb with
    | refl => exact .inl ⟨u, .refl, hu⟩
    | @tail b c hub hbc ih =>
      rcases ih with ⟨w, hw, hg⟩ | hd
      · rcases Relation.ReflTransGen.cases_head hw with rfl | ⟨c', hbc', hcw⟩
        · obtain ⟨hb1, hb2⟩ := hg
          by_cases hp : inIvs ivs b.pc = true
          · by_cases hsp : spec b.pc = true
            · have hfault : b.fault = none := by
                unfold Tau out at hbc
                cases hf : b.fault with
                | none => rfl
                | some f => rw [hf] at hbc; cases hbc
              rcases hjump _ hsp hp b rfl hfault hb2 with ⟨w', hw', hne, hg'⟩ | hd
              · rcases Relation.ReflTransGen.cases_head hw' with rfl | ⟨c', hbc', hcw'⟩
                · exact absurd rfl hne
                · rw [tau_det hbc hbc']; exact .inl ⟨w', hcw', hg'⟩
              · exact .inr (dead_of_rtg hub hd)
            · have hsp' : spec b.pc = false := by simpa using hsp
              rcases tau_tableN hA hscan hS hp hsp' hb2 hbc with h | h
              · exact .inl ⟨c, .refl, h⟩
              · exact .inr (dead_of_rtg (hub.tail hbc) h)
          · exact absurd hbc (no_tau_evAt (by simpa [hp] using hb1))
        · rw [tau_det hbc hbc']; exact .inl ⟨w, hcw, hg⟩
      · exact .inr hd
  rcases key t' hr with ⟨w, hw, hg⟩ | hd
  · rcases Relation.ReflTransGen.cases_head hw with rfl | ⟨d, hd, -⟩
    · exact .inl hg
    · exact absurd hd (not_tau_of_stops hs)
  · exact .inr hd

end
end PTX.Flow.Code
