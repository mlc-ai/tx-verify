-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Matrix
public import Lemmas.Flow.Step.LoadVec

@[expose] public section

/-! # Step combinators for warp matrix instructions

A proof tool: the `Code.StepOk` obligation (`Step/Combinators.lean`) of a site machine at an
`ldmatrix`, `stmatrix`, `movmatrix` or `mma.sync`, from the inversion lemmas of
`Lemmas/Flow/Matrix.lean`.

* `step_matrix_sel`: an instruction with one event (`mma.sync`, `movmatrix`). The machine's
  successor is a function `nv` of the values the destination registers are rebuilt into
  (`matrixVals`), so a machine can record them; the facts after the event are those values at
  the destinations and the other facts (`vecFacts`, as for a vector load).
* `step_ldmatrix_rd`, `step_ldmatrix_mx`: the two events of `ldmatrix` for a lane that supplies
  a row. The state at sub-step 0 fires the read of the row and moves to a state at the same
  instruction with `sub = 1` and `acc = rowVals bs` for the bytes `bs` read; that state fires the
  matrix event and continues like `step_matrix_sel`.
* `step_stmatrix_mx`, `step_stmatrix_wr`: the two events of `stmatrix` for a lane that supplies
  a row. The state at sub-step 0 fires the matrix event and moves to a state at the same
  instruction with `sub = 1` and `acc = rowVals recv` for the bytes received; that state fires
  the write of the row and continues at the next instruction with the same facts.

`vecFacts_fresh` writes the facts after the event as `(dᵢ, vᵢ) :: … ++ F` when no fact names a
destination; `vec_facts_norm` (`Step/LoadVec.lean`) and `dropReg_factsFrom` serve the general
case.

A fault of the model (an unknown row byte, received bytes that do not rebuild or are not 16
known bytes) leaves the thread dead: there the machine owes `none`, or `some none`. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- The state after a matrix event wrote the values `vs` to the distinct registers `ds`: at the
next instruction, at sub-step 0 with an empty accumulator, with `vs` at `ds` and the other facts
kept (`vecFacts`). -/
theorem at_afterMatrix {t : TState} {s : Nat} {F : List (Nat × Value)} {ds : List Nat}
    {vs : List Value} (hpc : t.pc = s) (hfault : t.fault = none) (hF : Holds t.regs F)
    (hnd : ds.Nodup) :
    At (PTX.next (setRegs { t with sub := 0, acc := [] } ds vs)) (s + 1) (vecFacts ds vs F) := by
  have hsk := setRegs_skel { t with sub := 0, acc := [] } ds vs
  refine ⟨?_, hsk.2.1, hsk.2.2.1, ?_, ?_⟩
  · show (setRegs { t with sub := 0, acc := [] } ds vs).pc + 1 = s + 1
    rw [hsk.1]
    exact congrArg (· + 1) hpc
  · show (setRegs { t with sub := 0, acc := [] } ds vs).fault = none
    rw [hsk.2.2.2]
    exact hfault
  · exact holds_vecFacts (t := { t with sub := 0, acc := [] }) hnd hF

/-- The facts after a write to registers that no fact names: the written values, then the facts
unchanged (`vecFacts` without its `dropReg`). -/
theorem vecFacts_fresh : ∀ {rs : List Nat} {vs : List Value} {F : List (Nat × Value)},
    (∀ q ∈ F, q.1 ∉ rs) → vecFacts rs vs F = rs.zip vs ++ F
  | [], _, _, _ => by simp [vecFacts]
  | _ :: _, [], _, _ => by simp [vecFacts]
  | r :: rs, v :: vs, F, h => by
    have hd : dropReg r F = F :=
      List.filter_eq_self.mpr fun q hq => by simpa using fun e => h q hq (by simp [e])
    simp only [vecFacts, hd, List.zip_cons_cons, List.cons_append]
    rw [vecFacts_fresh fun q hq hm => h q hq (List.mem_cons_of_mem _ hm)]

/-- A site whose continuing events are matrix events of operation `op` that continue as
`afterMatrix t w ds` (`hfire`): the successor is a function `nv` of the values the registers `ds`
are rebuilt into. The common part of `step_matrix_sel` and `step_ldmatrix_mx`. -/
theorem step_afterMatrix {d : C.D} {nv : List Value → Option (Option C.D)} {ins0 : Instr}
    {op : MatrixOp} {w : Nat} {ds : List Nat} (hc0 : K.code[C.pc d]? = some ins0)
    (hfire : ∀ {t e u}, C.AtD d t → Fires (C.pc d) (eventTmpl A L g t ins0.op) e (some u) →
      ∃ own recv, e = ⟨C.pc d, .matrix op own recv⟩ ∧ u = afterMatrix t w ds recv)
    (hnd : ds.Nodup)
    (hok : ∀ own recv vs, matrixVals w ds.length recv = .ok vs →
      C.next d ⟨C.pc d, .matrix op own recv⟩ = nv vs)
    (herr : ∀ own recv f, matrixVals w ds.length recv = .error f →
      C.next d ⟨C.pc d, .matrix op own recv⟩ = none ∨
        C.next d ⟨C.pc d, .matrix op own recv⟩ = some none)
    (hnn : ∀ vs, vs.length = ds.length → nv vs ≠ none)
    (hl : ∀ vs d', vs.length = ds.length → nv vs = some (some d') →
      C.Lands d (C.pc d + 1) (vecFacts ds vs (C.facts d)) d') : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨own, recv, rfl, rfl⟩ := hfire h hf
  cases hv : matrixVals w ds.length recv with
  | error f =>
    rw [afterMatrix_fault hv]
    rcases herr own recv f hv with hn | hn
    · exact .inr ⟨hn, Machine.dead_of_fault (f := f) rfl⟩
    · exact .inl (.inl hn)
  | ok vs =>
    rw [afterMatrix_ok hv]
    have hlen := (matrixVals_length hv).1
    have hn := hok own recv vs hv
    rcases hnv : nv vs with _ | _ | d'
    · exact absurd hnv (hnn vs hlen)
    · exact .inl (.inl (hn.trans hnv))
    · exact (hl vs d' hlen hnv).cont hi (hn.trans hnv)
        (at_afterMatrix h.1 h.2.2.2.1 h.2.2.2.2 hnd)

/-- A matrix instruction with one event (`mma.sync`, `movmatrix`), whose machine's successor is a
function `nv` of the values its destination registers (of `w` bits) are rebuilt into from the
received bytes: it may record them in a state (`some (some d')`) or stop following on them
(`some none`). Received bytes that do not rebuild fault the thread, where the machine stops
(`none`) or stops following it. The facts after the event are the values at the destinations and
the other facts (`vecFacts`); the sub-step and accumulator of `d` are not used. -/
theorem step_matrix_sel {d : C.D} {nv : List Value → Option (Option C.D)}
    {gd : Option (Nat × Bool)} {i : MatrixInstr} {w : Nat}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .matrix i⟩) (hop : ∀ m, i.op ≠ .move m)
    (hw : matrixDstBits i.op = w) (hnd : i.dsts.Nodup)
    (hok : ∀ own recv vs, matrixVals w i.dsts.length recv = .ok vs →
      C.next d ⟨C.pc d, .matrix i.op own recv⟩ = nv vs)
    (herr : ∀ own recv f, matrixVals w i.dsts.length recv = .error f →
      C.next d ⟨C.pc d, .matrix i.op own recv⟩ = none ∨
        C.next d ⟨C.pc d, .matrix i.op own recv⟩ = some none)
    (hnn : ∀ vs, vs.length = i.dsts.length → nv vs ≠ none)
    (hl : ∀ vs d', vs.length = i.dsts.length → nv vs = some (some d') →
      C.Lands d (C.pc d + 1) (vecFacts i.dsts vs (C.facts d)) d') : C.StepOk d :=
  step_afterMatrix hc0 (fun _ hf => hw ▸ fires_matrix_recv hop hf) hnd hok herr hnn hl

/-- `ldmatrix`, first sub-step of a lane that supplies a row: the read of its 16-byte row. With
all bytes known the machine moves to `nv bs`, a state at the same instruction with `sub = 1`,
the accumulator `rowVals bs` and the same facts; an unknown byte faults the thread
(`uninitialized`), where the machine stops (`none`) or stops following it (`some none`). -/
theorem step_ldmatrix_rd {d : C.D} {nv : List (Option Byte) → Option (Option C.D)}
    {gd : Option (Nat × Bool)} {i : MatrixInstr} {m : MatrixMove}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .matrix i⟩) (hop : i.op = .move m)
    (hst : m.store = false) (hsup : laneOf L g < m.num * m.rows) (hs : C.sub d = 0)
    (hok : ∀ x bs, bs.length = 16 → bs.all Option.isSome = true →
      C.next d ⟨C.pc d, .rd x bs⟩ = nv bs)
    (herr : ∀ x bs, bs.length = 16 → bs.all Option.isSome = false →
      C.next d ⟨C.pc d, .rd x bs⟩ = none ∨ C.next d ⟨C.pc d, .rd x bs⟩ = some none)
    (hnn : ∀ bs, bs.length = 16 → bs.all Option.isSome = true → nv bs ≠ none)
    (hmid : ∀ bs d', bs.length = 16 → bs.all Option.isSome = true → nv bs = some (some d') →
      C.pc d' = C.pc d ∧ C.sub d' = 1 ∧ C.acc d' = rowVals bs ∧ C.facts d' = C.facts d ∧
        (C.inv d → C.inv d')) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨loc, bs, -, hlen, rfl, rfl⟩ := fires_ldmatrix_rd hop hst hsup (h.2.1.trans hs) hf
  cases hall : bs.all Option.isSome with
  | false =>
    rcases herr _ bs hlen hall with hn | hn
    · exact .inr ⟨hn, Machine.dead_of_fault (f := .uninitialized) (by simp)⟩
    · exact .inl (.inl hn)
  | true =>
    have hn := hok { loc := loc, size := 16 } bs hlen hall
    rcases hnv : nv bs with _ | _ | d'
    · exact absurd hnv (hnn bs hlen hall)
    · exact .inl (.inl (hn.trans hnv))
    · obtain ⟨hpc, hsub, hacc, hF, hinv⟩ := hmid bs d' hlen hall hnv
      refine .inl (.inr ⟨d', _, hn.trans hnv, .refl, ⟨?_, ?_, ?_, ?_, ?_⟩, hinv hi⟩)
      · simpa using h.1.trans hpc.symm
      · simpa using hsub.symm
      · simpa using hacc.symm
      · simpa using h.2.2.2.1
      · rw [hF]; simpa using h.2.2.2.2

/-- `ldmatrix`, second sub-step (`sub ≠ 0`): the matrix event. The machine's successor is a
function `nv` of the values the destination registers are rebuilt into, as in
`step_matrix_sel`; the thread continues at the next instruction at sub-step 0 with an empty
accumulator, the values at the destinations and the other facts (`vecFacts`). -/
theorem step_ldmatrix_mx {d : C.D} {nv : List Value → Option (Option C.D)}
    {gd : Option (Nat × Bool)} {i : MatrixInstr} {m : MatrixMove}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .matrix i⟩) (hop : i.op = .move m)
    (hst : m.store = false) (hsub : C.sub d ≠ 0) (hnd : i.dsts.Nodup)
    (hok : ∀ own recv vs, matrixVals 32 i.dsts.length recv = .ok vs →
      C.next d ⟨C.pc d, .matrix (.move m) own recv⟩ = nv vs)
    (herr : ∀ own recv f, matrixVals 32 i.dsts.length recv = .error f →
      C.next d ⟨C.pc d, .matrix (.move m) own recv⟩ = none ∨
        C.next d ⟨C.pc d, .matrix (.move m) own recv⟩ = some none)
    (hnn : ∀ vs, vs.length = i.dsts.length → nv vs ≠ none)
    (hl : ∀ vs d', vs.length = i.dsts.length → nv vs = some (some d') →
      C.Lands d (C.pc d + 1) (vecFacts i.dsts vs (C.facts d)) d') : C.StepOk d :=
  step_afterMatrix hc0 (fun {t} _ _ h hf => by
    obtain ⟨recv, he, hu⟩ := fires_ldmatrix_mx hop hst
      (fun hc => hsub (h.2.1.symm.trans hc.2)) hf
    exact ⟨_, recv, he, hu⟩) hnd hok herr hnn hl

/-- `stmatrix`, first sub-step of a lane that supplies a row: the matrix event. With 16 known
bytes received the machine moves to `nv recv`, a state at the same instruction with `sub = 1`,
the accumulator `rowVals recv` and the same facts; other received bytes fault the thread
(`typeMismatch`), where the machine stops (`none`) or stops following it (`some none`). -/
theorem step_stmatrix_mx {d : C.D} {nv : List (Option Byte) → Option (Option C.D)}
    {gd : Option (Nat × Bool)} {i : MatrixInstr} {m : MatrixMove}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .matrix i⟩) (hop : i.op = .move m)
    (hst : m.store = true) (hsup : laneOf L g < m.num * m.rows) (hs : C.sub d = 0)
    (hok : ∀ own recv, recv.length = 16 → recv.all Option.isSome = true →
      C.next d ⟨C.pc d, .matrix (.move m) own recv⟩ = nv recv)
    (herr : ∀ own recv, ¬ (recv.length = 16 ∧ recv.all Option.isSome = true) →
      C.next d ⟨C.pc d, .matrix (.move m) own recv⟩ = none ∨
        C.next d ⟨C.pc d, .matrix (.move m) own recv⟩ = some none)
    (hnn : ∀ recv, recv.length = 16 → recv.all Option.isSome = true → nv recv ≠ none)
    (hmid : ∀ recv d', recv.length = 16 → recv.all Option.isSome = true →
      nv recv = some (some d') →
      C.pc d' = C.pc d ∧ C.sub d' = 1 ∧ C.acc d' = rowVals recv ∧ C.facts d' = C.facts d ∧
        (C.inv d → C.inv d')) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨own, recv, -, rfl, rfl⟩ := fires_stmatrix_mx hop hst (h.2.1.trans hs) hf
  rw [ite_eq_left hsup]
  by_cases hr : recv.length = 16 ∧ recv.all Option.isSome = true
  · rw [ite_eq_left hr]
    have hn := hok own recv hr.1 hr.2
    rcases hnv : nv recv with _ | _ | d'
    · exact absurd hnv (hnn recv hr.1 hr.2)
    · exact .inl (.inl (hn.trans hnv))
    · obtain ⟨hpc, hsub, hacc, hF, hinv⟩ := hmid recv d' hr.1 hr.2 hnv
      refine .inl (.inr ⟨d', _, hn.trans hnv, .refl, ⟨?_, ?_, ?_, ?_, ?_⟩, hinv hi⟩)
      · exact h.1.trans hpc.symm
      · exact hsub.symm
      · exact hacc.symm
      · exact h.2.2.2.1
      · rw [hF]; exact h.2.2.2.2
  · rw [ite_eq_right hr]
    rcases herr own recv hr with hn | hn
    · exact .inr ⟨hn, Machine.dead_of_fault (f := .typeMismatch) rfl⟩
    · exact .inl (.inl hn)

/-- `stmatrix`, second sub-step (`sub ≠ 0`): the write of the 16 received bytes at the lane's
row. The thread continues at the next instruction at sub-step 0 with an empty accumulator and
the same facts, from where the local code leads to the successor `dn`. -/
theorem step_stmatrix_wr {d dn : C.D} {gd : Option (Nat × Bool)} {i : MatrixInstr}
    {m : MatrixMove} (hc0 : K.code[C.pc d]? = some ⟨gd, .matrix i⟩) (hop : i.op = .move m)
    (hst : m.store = true) (hsub : C.sub d ≠ 0)
    (hn : ∀ x bs, C.next d ⟨C.pc d, .wr x bs⟩ = some (some dn))
    (hl : C.Lands d (C.pc d + 1) (C.facts d) dn) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨loc, -, rfl, rfl⟩ := fires_stmatrix_wr hop hst (fun hc => hsub (h.2.1.symm.trans hc)) hf
  exact hl.cont hi (hn _ _) ⟨by simp [PTX.next, h.1], rfl, rfl, h.2.2.2.1, h.2.2.2.2⟩

end
end PTX.Flow.Code
