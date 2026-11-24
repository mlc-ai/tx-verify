-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.DataState
public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
public import Kernels.TmlFa4Fwd.Proof.Correction.Places
import Kernels.TmlFa4Fwd.Proof.Common.DataSound
import Kernels.TmlFa4Fwd.Proof.Common.DataTrace
import Kernels.TmlFa4Fwd.Proof.Correction.RefCases

@[expose] public section

/-! # The reads a correction lane's data state records

`data_reads`: at a data state of a correction lane, the row sum and the row maximum of a stage are
those its trace read for the stage (`Recs.sum`, `Recs.max`), and the elements of a final chunk
those the chunk's load returned (`Recs.load`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The sites after the read of stage `st`'s row maximum, up to the LSE stores. -/
def rmPos (st : Fin 2) (s : Site) : Bool :=
  decide (8468 + 296 * st.val ≤ s.pc) && decide (s.pc ≤ 9082)

/-- The sites of chunk `j` of final stage `st` after its load. -/
def inChunk (st : Fin 2) (j : Fin 16) : Site → Bool
  | .fwl s i | .fst s i _ => s == st && i == j
  | _ => false

/-- **The reads a data state records.** -/
structure Recs (p : Params) (L : Launch) (X : Execution) (g i : Nat) (d : D) : Prop where
  sum : ∀ st, rsPos st d.site = true → ∃ k < i, ∃ a bs,
    X.get (g, k) = some ⟨(Site.fsum st).pc, .rd a bs⟩ ∧ rebuild 3 bs = .ok (fv (rsOf d.v st))
  max : ∀ st, rmPos st d.site = true → ∃ k < i, ∃ a bs,
    X.get (g, k) = some ⟨(Site.fmax st).pc, .rd a bs⟩ ∧
      rebuild 3 bs = .ok (Assumption.erealValue .f32 (rmOf d.v st).1)
  load : ∀ st j, inChunk st j d.site = true → ∃ k < i, ∃ pc a vals sh n, ∃ d0 : D,
    X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩ ∧
      Frame.stateAt (threadD p L) X g k = some (some (.inr ⟨.correction, d0⟩, n)) ∧
      d0.site = .fld st j ∧ flN 8 vals = some d.v.ys

/-- The sites of the final stages and the LSE stores. -/
private def tailS : Site → Bool
  | .fmax _ | .farr _ | .fw .. | .fld .. | .fwl .. | .fst .. | .fence _ | .fdone .. | .lse _ => true
  | .fbar st | .fsum st => st == 1
  | _ => false

private theorem tail_tab : allSites.all (fun s => [(0 : Fin 2), 1].all fun st =>
    !(rsPos st s || rmPos st s) || tailS s) = true := by decide +kernel

private theorem enter_tab : allSites.all (fun s => (nexts s).all fun s' =>
    [(0 : Fin 2), 1].all fun st => (!rsPos st s' || rsPos st s || s == .fsum st) &&
      (!rmPos st s' || rmPos st s || s == .fmax st)) = true := by decide +kernel

private theorem chunk_tab : allSites.all (fun s => (nexts s).all fun s' =>
    match s' with
    | .fwl st j => s == .fld st j
    | .fst st j 0 => s == .fwl st j
    | .fst st j 1 => s == .fst st j 0
    | _ => true) = true := by decide +kernel

private theorem mem2 (st : Fin 2) : st ∈ [(0 : Fin 2), 1] := by fin_cases st <;> simp

private theorem not_tail_next {d d' : D} {e : Event} (hn : succ p L g d e = some (some d'))
    (st : Fin 2) : (rsPos st d'.site = true → rsPos st d.site = true ∨ d.site = .fsum st) ∧
      (rmPos st d'.site = true → rmPos st d.site = true ∨ d.site = .fmax st) := by
  rcases succ_cases hn with ⟨rfl, -⟩ | ⟨-, -, rfl⟩ | hM
  · exact ⟨.inl, .inl⟩
  · exact ⟨.inl, .inl⟩
  · have h := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp enter_tab d.site
      (mem_allSites _)) d'.site hM.1) st (mem2 st)
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    constructor
    · intro h
      rcases h1 with (h1 | h1) | h1
      · rw [h] at h1; cases h1
      · exact .inl h1
      · exact .inr h1
    · intro h
      rcases h2 with (h2 | h2) | h2
      · rw [h] at h2; cases h2
      · exact .inl h2
      · exact .inr h2

set_option maxHeartbeats 1000000 in
/-- A step in the final stages keeps the row sums and maxima it does not read. -/
private theorem tail_keep {d d' : D} {e : Event} (hn : succ p L g d e = some (some d'))
    (ht : tailS d.site = true) (st : Fin 2) :
    (d.site ≠ .fsum st → rsOf d'.v st = rsOf d.v st) ∧
      (d.site ≠ .fmax st → rmOf d'.v st = rmOf d.v st) := by
  obtain ⟨site, v, k⟩ := d
  obtain ⟨pc, kind⟩ := e
  have pass : ∀ late, ∃ sc, (passStart p L g late ⟨site, v, k⟩).v = { v with sc := sc } := by
    intro late
    unfold passStart D.ite
    cases late <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split <;> exact ⟨_, rfl⟩
  have keep : (∃ sc ys, d'.v = { v with sc := sc, ys := ys }) →
      (Site.fsum st ≠ site → rsOf d'.v st = rsOf v st) ∧
        (Site.fmax st ≠ site → rmOf d'.v st = rmOf v st) := by
    rintro ⟨sc, ys, h⟩
    rw [h]
    fin_cases st <;> exact ⟨fun _ => rfl, fun _ => rfl⟩
  have pass' : ∀ late, ∃ sc ys, (passStart p L g late ⟨site, v, k⟩).v =
      { v with sc := sc, ys := ys } := fun late => (pass late).imp fun sc h => ⟨v.ys, h⟩
  simp only at ht ⊢
  simp only [ne_comm (a := site)]
  cases site <;> simp only [tailS, Bool.false_eq_true] at ht <;> simp only [succ] at hn
  case fbar s | farr s | fwl s j | fence s =>
    simp only [Option.some.injEq] at hn
    subst hn
    exact keep ⟨_, _, rfl⟩
  case fsum s =>
    cases kind <;> try cases hn
    dsimp only at hn
    split at hn <;> try cases hn
    unfold real32 at hn
    split at hn <;> simp only [Option.some.injEq, reduceCtorEq] at hn
    subst hn
    fin_cases s <;> fin_cases st <;> simp [rsOf, rmOf, setRs]
  case fmax s =>
    cases kind <;> try cases hn
    dsimp only at hn
    split at hn <;> try cases hn
    obtain ⟨x, -, rfl⟩ := max32_some hn
    fin_cases s <;> fin_cases st <;> simp [rsOf, rmOf, setRm]
  case fw s i =>
    cases kind <;> cases hn
    rename_i ok _ _
    refine keep ?_
    cases ok <;> exact ⟨_, _, rfl⟩
  case fld s j =>
    cases kind <;> try cases hn
    rename_i tk
    cases tk <;> try cases hn
    dsimp only at hn
    split at hn <;> simp only [Option.some.injEq, reduceCtorEq] at hn
    subst hn
    exact keep ⟨_, _, rfl⟩
  case fst s j h =>
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      exact keep ⟨_, _, rfl⟩
    · split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        exact keep ⟨_, _, rfl⟩
      · split at hn <;>
        · simp only [Option.some.injEq] at hn
          subst hn
          exact keep ⟨_, _, rfl⟩
  case fdone s i =>
    fin_cases s <;> fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] at hn
    case «1».«1» =>
      split at hn <;> simp only [Option.some.injEq, reduceCtorEq] at hn
      subst hn
      refine keep ?_
      unfold afterFinal D.ite
      simp only
      split
      · split
        · exact pass' true
        · exact ⟨_, _, rfl⟩
      · exact ⟨_, _, rfl⟩
    all_goals
      simp only [Option.some.injEq] at hn
      subst hn
      exact keep ⟨_, _, rfl⟩
  case lse i =>
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] at hn
    · split at hn <;> simp only [Option.some.injEq, reduceCtorEq] at hn
      subst hn
      refine keep ?_
      unfold afterLse D.ite
      simp only
      split
      · exact pass' true
      · exact ⟨_, _, rfl⟩
    · simp only [Option.some.injEq] at hn
      subst hn
      exact keep (pass' true)

/-- A step into a chunk after its load is the load, or is in the chunk and keeps its elements. -/
private theorem chunk_prev {d d' : D} {e : Event} (hn : succ p L g d e = some (some d'))
    {st : Fin 2} {j : Fin 16} (hc : inChunk st j d'.site = true) :
    (inChunk st j d.site = true ∧ d'.v.ys = d.v.ys) ∨
      d.site = .fld st j ∧ ∃ a vals sh, e.kind = .tc (.ld a vals sh) ∧
        flN 8 vals = some d'.v.ys := by
  have hsite : inChunk st j d.site = true ∨ d.site = .fld st j := by
    rcases succ_cases hn with ⟨rfl, -⟩ | ⟨-, -, rfl⟩ | hM
    · exact .inl hc
    · exact .inl hc
    · have h := List.all_eq_true.mp (List.all_eq_true.mp chunk_tab d.site (mem_allSites _))
        d'.site hM.1
      revert hc h
      cases d'.site with
      | fwl s i =>
        simp only [inChunk, Bool.and_eq_true, beq_iff_eq]
        rintro ⟨rfl, rfl⟩ h
        exact .inr h
      | fst s i b =>
        simp only [inChunk, Bool.and_eq_true, beq_iff_eq]
        rintro ⟨rfl, rfl⟩ h
        fin_cases b <;>
        · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, beq_iff_eq] at h
          left
          rw [h]
          simp
      | _ => intro hc; cases hc
  rcases hsite with hs | hs
  · refine .inl ⟨hs, ?_⟩
    obtain ⟨site, v, k⟩ := d
    simp only at hs ⊢
    cases site <;> simp only [inChunk, Bool.false_eq_true] at hs <;> simp only [succ] at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      rfl
    · repeat' split at hn
      all_goals
        simp only [Option.some.injEq] at hn
        subst hn
        rfl
  · refine .inr ⟨hs, ?_⟩
    obtain ⟨site, v, k⟩ := d
    obtain ⟨pc, kind⟩ := e
    simp only at hs
    subst hs
    simp only [succ] at hn
    cases kind <;> try cases hn
    rename_i tk
    cases tk <;> try cases hn
    dsimp only at hn
    split at hn <;> simp only [Option.some.injEq, reduceCtorEq] at hn
    subst hn
    rename_i h
    exact ⟨_, _, _, rfl, h⟩

/-- A statistics read, at its successor. -/
private theorem stat_next {d d' : D} {e : Event} {st : Fin 2}
    (hn : succ p L g d e = some (some d')) :
    (d.site = .fsum st → ∃ a bs, e.kind = .rd a bs ∧ rebuild 3 bs = .ok (fv (rsOf d'.v st))) ∧
      (d.site = .fmax st → ∃ a bs, e.kind = .rd a bs ∧
        rebuild 3 bs = .ok (Assumption.erealValue .f32 (rmOf d'.v st).1)) := by
  obtain ⟨site, v, k⟩ := d
  obtain ⟨pc, kind⟩ := e
  constructor <;> rintro h <;> simp only at h <;> subst h <;> simp only [succ] at hn <;>
    cases kind <;> try cases hn
  all_goals
    dsimp only at hn
    split at hn <;> try cases hn
  · rename_i hv
    unfold real32 at hn
    split at hn <;> simp only [Option.some.injEq, reduceCtorEq] at hn
    subst hn
    refine ⟨_, _, rfl, hv.trans ?_⟩
    fin_cases st <;> rfl
  · rename_i hv
    obtain ⟨x, rfl, rfl⟩ := max32_some hn
    refine ⟨_, _, rfl, hv.trans ?_⟩
    fin_cases st <;> rfl

private theorem recs_step {i : Nat} {d d' : D} {e : Event} {n : Cls → Nat}
    (he : X.get (g, i) = some e) (hpc : e.pc = d.site.pc)
    (hs : Frame.stateAt (threadD p L) X g i = some (some (.inr ⟨.correction, d⟩, n)))
    (hR : Recs p L X g i d) (hn : succ p L g d e = some (some d')) : Recs p L X g (i + 1) d' := by
  have tail : ∀ st, (rsPos st d.site || rmPos st d.site) = true → tailS d.site = true := by
    intro st h
    have := List.all_eq_true.mp (List.all_eq_true.mp tail_tab d.site (mem_allSites _)) st (mem2 st)
    simpa [h] using this
  obtain ⟨pc, kind⟩ := e
  simp only at hpc
  subst hpc
  refine ⟨fun st h => ?_, fun st h => ?_, fun st j h => ?_⟩
  · by_cases hf : d.site = .fsum st
    · obtain ⟨a, bs, hk, hv⟩ := (stat_next (st := st) hn).1 hf
      simp only at hk
      subst hk
      exact ⟨i, by omega, a, bs, by rw [← hf]; exact he, hv⟩
    · have h0 := ((not_tail_next hn st).1 h).resolve_right hf
      obtain ⟨k, hk, a, bs, hg, hv⟩ := hR.sum st h0
      exact ⟨k, by omega, a, bs, hg, by
        rw [(tail_keep hn (tail st (by simp [h0])) st).1 hf]; exact hv⟩
  · by_cases hf : d.site = .fmax st
    · obtain ⟨a, bs, hk, hv⟩ := (stat_next (st := st) hn).2 hf
      simp only at hk
      subst hk
      exact ⟨i, by omega, a, bs, by rw [← hf]; exact he, hv⟩
    · have h0 := ((not_tail_next hn st).2 h).resolve_right hf
      obtain ⟨k, hk, a, bs, hg, hv⟩ := hR.max st h0
      exact ⟨k, by omega, a, bs, hg, by
        rw [(tail_keep hn (tail st (by simp [h0])) st).2 hf]; exact hv⟩
  · rcases chunk_prev hn h with ⟨h0, hy⟩ | ⟨h0, a, vals, sh, hk, hv⟩
    · obtain ⟨k, hk, pc, a, vals, sh, n', d0, h1, h2, h3, h4⟩ := hR.load st j h0
      exact ⟨k, by omega, pc, a, vals, sh, n', d0, h1, h2, h3, by rw [hy]; exact h4⟩
    · simp only at hk
      subst hk
      exact ⟨i, by omega, _, a, vals, sh, n, d, he, hs, h0, hv⟩

private theorem recs_init (i : Nat) : Recs p L X g i (D.mk' .setmax {}) := by
  refine ⟨fun st h => ?_, fun st h => ?_, fun _ _ h => ?_⟩
  · fin_cases st <;> cases h
  · fin_cases st <;> cases h
  · cases h

/-- **A data state of a correction lane records its reads.** -/
theorem data_reads (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {i : Nat}
    {d : D} {n : Cls → Nat} (hi : i ≤ (X.tr g).length)
    (hs : Frame.stateAt (threadD p L) X g i = some (some (.inr ⟨.correction, d⟩, n))) :
    Recs p L X g i d :=
  role_induct (r := .correction) (Q := Recs p L X g)
    recs_init
    (fun he hst hR hn => recs_step he
      (Frame.event_pc (fun _ hg => threadD_sound hp hg) hX he hst) hst hR hn) hi hs

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
