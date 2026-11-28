-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.RegionFrame
public import Lemmas.Flow.FrameScan
public import Lemmas.Flow.Havoc

@[expose] public section

/-! # Local steps inside a region that contains assumption segments

A proof tool, generic over the kernel. `regionB` (`RegionFrame.lean`) needs every position of the
region free of assumption segments. Here a position may start a segment that a hook table
describes (the landing position and the registers the segment clobbers): `regionH` checks the
region with the table, `region_frame_h` keeps the registers of `R` over every run of local steps
that starts in the region. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Flow.Code

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The conditions of `regionH` at one position, on the instruction there. -/
def regionAt (tab : Nat → Option Havoc.Hook) (ivs : List (Nat × Nat)) (R : List Nat) (ins : Instr)
    (pc : Nat) : Bool :=
  (ins.guard.isNone || inIvs ivs (pc + 1)) &&
  (if ins.op.isLocal then
    R.all (fun r => !(writesRegs ins.op).contains r) &&
      (match ins.op with
        | .bra tgt _ => inIvs ivs tgt
        | .brx .. => false
        | _ => inIvs ivs (pc + 1))
  else true) &&
  (match tab pc with
    | none => true
    | some h => inIvs ivs h.stop && h.writes.all (!R.contains ·))

/-- A region of intervals with a hook table, checked in one pass over the code of each interval: a
guarded instruction may be skipped to the next position; a local instruction writes none of `R` and
continues inside (a jump's target, else the next position); a position that starts a segment lands
inside and clobbers none of `R`. -/
def regionH (K : Kernel) (tab : Nat → Option Havoc.Hook) (ivs : List (Nat × Nat)) (R : List Nat) :
    Bool :=
  ivs.all fun p => decide (p.1 + p.2 ≤ K.code.length) &&
    (((K.code.drop p.1).take p.2).zipIdx p.1).all fun x => regionAt tab ivs R x.1 x.2

theorem regionH_at {tab : Nat → Option Havoc.Hook} {ivs : List (Nat × Nat)} {R : List Nat}
    (h : regionH K tab ivs R = true) {pc : Nat} (hpc : inIvs ivs pc = true) {ins : Instr}
    (hc : K.code[pc]? = some ins) : regionAt tab ivs R ins pc = true := by
  obtain ⟨p, hp, hq⟩ : ∃ p ∈ ivs, p.1 ≤ pc ∧ pc < p.1 + p.2 := by simpa [inIvs] using hpc
  have hp' := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp'
  have hlt : pc < K.code.length := by omega
  have hc' : K.code[pc]? = some K.code[pc] := List.getElem?_eq_getElem hlt
  have hm : (K.code[pc], pc) ∈ ((K.code.drop p.1).take p.2).zipIdx p.1 := by
    apply List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mpr
    refine ⟨hq.1, ?_⟩
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hq.1]
    exact hc'
  have := List.all_eq_true.mp hp'.2 _ hm
  rw [hc] at hc'
  obtain rfl := Option.some.inj hc'
  exact this

/-- The segments of the assumptions are the table's. -/
def HooksAny (A : List Assumption) (L : Launch) (g : Nat) (tab : Nat → Option Havoc.Hook) : Prop :=
  ∀ t a u, a ∈ A → a.segmentRule L g t = some (.ok u) →
    ∃ h, tab t.pc = some h ∧ u.pc = h.stop ∧ ∀ r, r ∉ h.writes → u.regs r = t.regs r

private theorem local_frame_rule (hA : RulesFrame A) {t u : TState} {op : Op}
    (h : execLocalRule A L g t op = .ok u) : LocalFrame op t u := by
  unfold execLocalRule at h
  split at h
  · rename_i v hv
    obtain ⟨a, ha, hr⟩ := List.exists_of_findSome?_eq_some hv
    exact hA a ha L g t op u (h ▸ hr)
  · exact execLocal_frame h

/-- **One local step inside a region with segments** stays inside and keeps the registers of `R`. -/
theorem tau_region_h {tab : Nat → Option Havoc.Hook} (hA : RulesFrame A) (hh : HooksAny A L g tab)
    {ivs : List (Nat × Nat)} {R : List Nat} (hB : regionH K tab ivs R = true) {u u1 : TState}
    (ht : Tau K A L g u u1) (h1 : inIvs ivs u.pc = true) :
    inIvs ivs u1.pc = true ∧ ∀ r ∈ R, u1.regs r = u.regs r := by
  unfold Tau out at ht
  cases hf : u.fault with
  | some f => simp [hf] at ht
  | none =>
    simp only [hf] at ht
    cases hc : K.code[u.pc]? with
    | none => simp [hc] at ht
    | some ins =>
      have hT := regionH_at hB h1 hc
      simp only [regionAt, Bool.and_eq_true] at hT
      simp only [hc] at ht
      obtain ⟨⟨hA1, hB2⟩, hT⟩ := hT
      cases hg : guardHolds u ins.guard with
      | error e => simp [hg] at ht
      | ok b =>
        simp only [hg] at ht
        cases b with
        | false =>
          simp only [Out.tau.injEq] at ht
          subst ht
          have hgd : ins.guard.isSome := by
            cases hgi : ins.guard with
            | none => rw [hgi] at hg; simp [guardHolds, pure, Except.pure] at hg
            | some _ => rfl
          refine ⟨?_, fun _ _ => rfl⟩
          simp only [skip]
          simp only [Bool.or_eq_true, Option.isNone_iff_eq_none] at hA1
          rcases hA1 with hb' | hb'
          · rw [hb'] at hgd; cases hgd
          · exact hb'

        | true =>
          by_cases hl : ins.op.isLocal = true
          · simp only [hl, ↓reduceIte] at ht
            cases he : execLocalA A L g u ins.op with
            | error e => simp [he] at ht
            | ok t' =>
              simp only [he, Out.tau.injEq] at ht
              subst ht
              simp only [hl, ↓reduceIte, Bool.and_eq_true] at hB2
              obtain ⟨hw, hj⟩ := hB2
              unfold execLocalA at he
              split at he
              · rename_i v hv
                obtain ⟨a, ha, hr⟩ := List.exists_of_findSome?_eq_some hv
                obtain ⟨hk, htab, hpc, hreg⟩ := hh u a t' ha (he ▸ hr)
                simp only [htab, Bool.and_eq_true] at hT
                refine ⟨hpc ▸ hT.1, fun r hr' => hreg r fun hm => ?_⟩
                have := List.all_eq_true.mp hT.2 r hm
                simp [hr'] at this
              · have fr := local_frame_rule hA he
                refine ⟨?_, fun r hr => fr.regs r (by
                  have := List.all_eq_true.mp hw r hr; simpa using this)⟩
                rcases fr.pc with hp | hp
                · cases hop : ins.op <;> simp only [hop, nextPc] at hj hp <;>
                    first | (rw [hp]; exact hj) | cases hj
                · cases hop : ins.op <;> simp only [hop, BrxTarget] at hj hp; cases hj
          · simp [hl] at ht

/-- **Local steps inside a region with segments** keep the registers of `R`. -/
theorem region_frame_h {tab : Nat → Option Havoc.Hook} (hA : RulesFrame A)
    (hh : HooksAny A L g tab) {ivs : List (Nat × Nat)} {R : List Nat}
    (hB : regionH K tab ivs R = true) {u t' : TState}
    (h : Relation.ReflTransGen (Tau K A L g) u t') (h1 : inIvs ivs u.pc = true) :
    ∀ r ∈ R, t'.regs r = u.regs r := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intros; rfl
  | head ht _ ih =>
    obtain ⟨a1, a3⟩ := tau_region_h hA hh hB ht h1
    intro r hr
    rw [ih a1 r hr, a3 r hr]

end
end PTX.Flow
