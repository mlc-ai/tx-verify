-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.FrameScan
public import Lemmas.Flow.ReachSegU

@[expose] public section

/-! # Facts by position, along every local path of a region

A proof tool, generic over the kernel. A table gives, at each position of a region (a union of
intervals), the registers whose facts hold there (`keys`), the valuation they hold under (`post`
selects one of two) and the positions where an instruction writes a fact's register (`spec`).
Along every local step from a position of the region, the facts of the next position hold:
at an ordinary position the instruction writes none of them and they are among the position's
(`tabAt`, a Boolean check of one pass over the code, `tabScan`); at a `spec` position a lemma
gives the step (`rtg_table`). Where the thread stops is not decided here: the first state that
performs an event holds the table's facts at its position, and the control machine says which
position that is. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The table's facts at a position. -/
def phi (keys : Nat → List Nat) (post : Nat → Bool) (V1 V2 : Nat → Value) (pc : Nat) :
    List (Nat × Value) :=
  factsFrom (keys pc) (if post pc then V2 else V1)

/-- A state at a scalar boundary with the table's facts of its position. -/
def TabAt (keys : Nat → List Nat) (post : Nat → Bool) (V1 V2 : Nat → Value) (t : TState) : Prop :=
  t.sub = 0 ∧ t.acc = [] ∧ Holds t.regs (phi keys post V1 V2 t.pc)

/-- The Boolean check of one instruction of the region. -/
def tabAt (K : Kernel) (ivs : List (Nat × Nat)) (keys : Nat → List Nat) (post spec : Nat → Bool)
    (ins : Instr) (pc : Nat) : Bool :=
  spec pc || (if ins.op.isLocal then noBrx ins.op && [nextPc ins.op pc, pc + 1].all fun q =>
      (inIvs ivs q || evAtB K q) && (keys q).all (fun r => (keys pc).contains r &&
        !(writesRegs ins.op).contains r) && (post q == post pc)
    else ins.guard.isSome && [pc + 1].all fun q =>
      (inIvs ivs q || evAtB K q) && (keys q).all (fun r => (keys pc).contains r) &&
        (post q == post pc))

/-- **One pass over the code of each interval.** -/
def tabScan (K : Kernel) (ivs : List (Nat × Nat)) (keys : Nat → List Nat) (post spec : Nat → Bool) :
    Bool :=
  ivs.all fun p => decide (p.1 + p.2 ≤ K.code.length) &&
    (((K.code.drop p.1).take p.2).zipIdx p.1).all fun x => tabAt K ivs keys post spec x.1 x.2

theorem tabScan_at {ivs : List (Nat × Nat)} {keys post spec}
    (h : tabScan K ivs keys post spec = true) {pc : Nat} (hp : inIvs ivs pc = true) :
    ∃ ins, K.code[pc]? = some ins ∧ tabAt K ivs keys post spec ins pc = true := by
  obtain ⟨p, hp, hq⟩ : ∃ p ∈ ivs, p.1 ≤ pc ∧ pc < p.1 + p.2 := by simpa [inIvs] using hp
  have hp' := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp'
  have hlt : pc < K.code.length := by omega
  have hc : K.code[pc]? = some K.code[pc] := List.getElem?_eq_getElem hlt
  have hm : (K.code[pc], pc) ∈ ((K.code.drop p.1).take p.2).zipIdx p.1 := by
    apply List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mpr
    refine ⟨hq.1, ?_⟩
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hq.1]
    exact hc
  exact ⟨_, hc, List.all_eq_true.mp hp'.2 _ hm⟩

theorem holds_phi {keys post V1 V2 q p} {R R' : Nat → Option Value} (hpost : post q = post p)
    (hH : Holds R (phi keys post V1 V2 p)) (hk : ∀ r ∈ keys q, r ∈ keys p ∧ R' r = R r) :
    Holds R' (phi keys post V1 V2 q) := by
  refine holds_of_mem fun r x hm => ?_
  obtain ⟨r', hr', he⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨h1, h2⟩ := hk r' hr'
  rw [h2]
  have := holds_mem hH (mem_factsFrom (val := if post p then V2 else V1) h1)
  simpa only [hpost] using this

/-- **One local step from a position of the region.** -/
theorem tau_table (hA : RulesFrame A) {ivs keys post spec V1 V2}
    (hscan : tabScan K ivs keys post spec = true)
    (hS : ∀ pc, inIvs ivs pc = true → spec pc = false → Assumption.SegFreePc A pc)
    (hspec : ∀ pc, spec pc = true → inIvs ivs pc = true → ∀ t t1 : TState, t.pc = pc →
      TabAt keys post V1 V2 t → Tau K A L g t t1 →
      ((inIvs ivs t1.pc || evAtB K t1.pc) = true ∧ TabAt keys post V1 V2 t1) ∨
        Machine.Dead (K := K) (A := A) (L := L) (g := g) t1)
    {t t1 : TState} (hp : inIvs ivs t.pc = true) (hH : TabAt keys post V1 V2 t)
    (h : Tau K A L g t t1) :
    ((inIvs ivs t1.pc || evAtB K t1.pc) = true ∧ TabAt keys post V1 V2 t1) ∨
      Machine.Dead (K := K) (A := A) (L := L) (g := g) t1 := by
  obtain ⟨hsub, hacc, hH⟩ := hH
  by_cases hsp : spec t.pc = true
  · exact hspec _ hsp hp t t1 rfl ⟨hsub, hacc, hH⟩ h
  have hsp' : spec t.pc = false := by simpa using hsp
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

/-- A dead state's local step leads to a dead state. -/
theorem dead_step {t t1 : TState} (hd : Machine.Dead (K := K) (A := A) (L := L) (g := g) t)
    (h : Tau K A L g t t1) : Machine.Dead (K := K) (A := A) (L := L) (g := g) t1 := by
  obtain ⟨s, f, hs, hf⟩ := hd
  rcases Relation.ReflTransGen.cases_head hs with rfl | ⟨c, hc, hcs⟩
  · exfalso
    unfold Tau at h
    rw [hf] at h
    cases h
  · rw [tau_det h hc]
    exact ⟨s, f, hcs, hf⟩

/-- **A run of one step**: the local step from a state at its start reaches the run's end facts,
or the thread is dead. -/
theorem SegD.tau_one {pc : Nat} {F G : List (Nat × Value)} {C : Prop}
    (h : SegD K A L g 1 pc F (pc + 1) G C) {t t1 : TState} (hF : At t pc F)
    (ht : Tau K A L g t t1) :
    At t1 (pc + 1) G ∨ Machine.Dead (K := K) (A := A) (L := L) (g := g) t1 := by
  by_cases hC : C
  · obtain ⟨u, hr, hu⟩ := (h t hF).1 hC
    have hTau : Tau K A L g t u := tauStep_iff.mp (by simpa [run] using hr)
    rw [tau_det ht hTau]
    exact .inl hu
  · exact .inr (dead_step ((h t hF).2 hC) ht)

/-- **Every local path from a position of the region** keeps the table's facts, or the thread
is dead. -/
theorem rtg_table (hA : RulesFrame A) {ivs keys post spec V1 V2}
    (hscan : tabScan K ivs keys post spec = true)
    (hS : ∀ pc, inIvs ivs pc = true → spec pc = false → Assumption.SegFreePc A pc)
    (hspec : ∀ pc, spec pc = true → inIvs ivs pc = true → ∀ t t1 : TState, t.pc = pc →
      TabAt keys post V1 V2 t → Tau K A L g t t1 →
      ((inIvs ivs t1.pc || evAtB K t1.pc) = true ∧ TabAt keys post V1 V2 t1) ∨
        Machine.Dead (K := K) (A := A) (L := L) (g := g) t1)
    {u t' : TState} (hu : (inIvs ivs u.pc || evAtB K u.pc) = true)
    (hH : TabAt keys post V1 V2 u) (hr : Relation.ReflTransGen (Tau K A L g) u t') :
    ((inIvs ivs t'.pc || evAtB K t'.pc) = true ∧ TabAt keys post V1 V2 t') ∨
      Machine.Dead (K := K) (A := A) (L := L) (g := g) u := by
  induction hr with
  | refl => exact .inl ⟨hu, hH⟩
  | @tail b c hub hbc ih =>
    rcases ih with ⟨hb, hHb⟩ | hd
    · rcases Bool.or_eq_true_iff.mp hb with hb' | hb'
      · rcases tau_table hA hscan hS hspec hb' hHb hbc with h | h
        · exact .inl h
        · exact .inr (dead_of_rtg hub (Machine.dead_of_tau hbc h))
      · exact absurd hbc (no_tau_evAt hb')
    · exact .inr hd

end
end PTX.Flow.Code
