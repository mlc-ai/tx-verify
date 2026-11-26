-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollPcs
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.NotWarpColl
public import Lemmas.Kernel.Progress.WarpNoBallotOp

@[expose] public section

/-! # The warp-collective events of a trace are at the collective pcs

`coll_iff_pc`: an event of a consistent execution that is no undefined behaviour is a warp
collective exactly when its pc is one of `collPcs`. A warp instruction off `collPcs` is the mode
vote at pc 578, which fires no collective of the count; the instructions at `collPcs` are shuffles
and elections, whose templates fire a shuffle, an election or a fault. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Sched

noncomputable section

/-- A template of a shuffle, an election or a fault. -/
def CollOrUb : Tmpl → Prop
  | .shfl .. | .elect .. | .ub _ => True
  | _ => False

theorem warpTmpl_collOrUb {L : Launch} {g : Nat} {t : TState} {w : WarpInstr}
    (hk : (∃ m, w.kind = .shfl m) ∨ w.kind = .elect) : CollOrUb (warpTmpl L g t w) := by
  unfold warpTmpl
  split
  · simp only [shflTmpl]
    repeat' first | trivial | split
  · rename_i hk'; rcases hk with ⟨m, h⟩ | h <;> simp_all
  · rename_i hk'; rcases hk with ⟨m, h⟩ | h <;> simp_all
  · rename_i hk'; rcases hk with ⟨m, h⟩ | h <;> simp_all
  · rename_i hk'; rcases hk with ⟨m, h⟩ | h <;> simp_all
  · rename_i hk'; rcases hk with ⟨m, h⟩ | h <;> simp_all
  · simp only [electTmpl]
    repeat' first | trivial | split
  · rename_i hk'; rcases hk with ⟨m, h⟩ | h <;> simp_all
  · trivial

/-- A mode vote fires no warp collective of the count. -/
theorem eventTmpl_notColl_voteMode {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} (hop : voteModeOp op = true) : NotColl (eventTmpl A L g t op) := by
  cases op
  case warp w =>
    simp only [eventTmpl, warpTmpl]
    split
    case h_3 =>
      rename_i mode _ _ _ _ hb _ hk _ _ _
      simp only [voteModeOp, hk] at hop
      cases mode <;> simp_all
      all_goals simp only [voteModeTmpl]
      all_goals repeat' first | trivial | split
    all_goals first | trivial | (exfalso; simp_all [voteModeOp])
  all_goals simp [voteModeOp] at hop

/-- The event of a template that is no collective is no collective. -/
theorem fires_notColl {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState} (hn : NotColl m)
    (hf : Fires pc m e o) : isWarpColl e = false := by
  cases m <;> simp only [NotColl] at hn <;> simp only [Fires] at hf <;>
    first
    | (obtain ⟨-, rfl, -⟩ := hf; rfl)
    | (obtain ⟨-, -, rfl, -⟩ := hf; rfl)
    | (obtain ⟨rfl, -⟩ := hf; rfl)

/-- A shuffle or an election. -/
def shflOrElect : Op → Bool
  | .warp w => match w.kind with
    | .shfl _ | .elect => true
    | _ => false
  | _ => false

private theorem warp_ck : kernel.code.zipIdx.all (fun x =>
    !isWarpOp x.1.op || decide (x.2 ∈ collPcs) || voteModeOp x.1.op) = true := by
  decide +kernel

private theorem shfl_ck : kernel.code.zipIdx.all (fun x =>
    !decide (x.2 ∈ collPcs) || shflOrElect x.1.op) = true := by
  decide +kernel

private theorem zip_mem {pc : Nat} {ins : Instr} (h : kernel.code[pc]? = some ins) :
    (ins, pc) ∈ kernel.code.zipIdx := by
  rw [List.mem_iff_getElem?]
  exact ⟨pc, by simp [List.getElem?_zipIdx, h]⟩

variable {L : Launch} {m : Mem0} {X : Execution} {i : EvId} {e : Event}

/-- **A warp-collective event is at a pc of `collPcs`.** -/
theorem coll_event_pc (hX : Consistent L kernel Assumptions.all m X) (he : X.get i = some e)
    (hc : isWarpColl e = true) : e.pc ∈ collPcs := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hi, hf⟩
  · obtain ⟨pc, k⟩ := e
    simp only at hf
    subst hf
    simp [isWarpColl] at hc
  · by_contra hn
    have h := List.all_eq_true.mp warp_ck _ (zip_mem hi)
    simp only [hn, Bool.or_eq_true, Bool.not_eq_true', decide_false, Bool.or_false] at h
    rcases h with h | h
    · have := fires_notColl (eventTmpl_notColl h) hf
      rw [this] at hc
      cases hc
    · have := fires_notColl (eventTmpl_notColl_voteMode h) hf
      rw [this] at hc
      cases hc

/-- **An event at a pc of `collPcs` that is no fault is a warp collective.** -/
theorem coll_of_pc (hX : Consistent L kernel Assumptions.all m X) (he : X.get i = some e)
    (hu : ∀ f, e.kind ≠ .ub f) (hp : e.pc ∈ collPcs) : isWarpColl e = true := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hi, hf⟩
  · exact absurd hf (hu f)
  · have h := List.all_eq_true.mp shfl_ck _ (zip_mem hi)
    simp only [hp, decide_true, Bool.not_true, Bool.false_or] at h
    obtain ⟨w, hw⟩ : ∃ w, ins.op = .warp w := by
      cases hop : ins.op <;> simp_all [shflOrElect]
    rw [hw] at h
    have hk : (∃ m, w.kind = .shfl m) ∨ w.kind = .elect := by
      cases hk : w.kind <;> simp_all [shflOrElect]
    have hT : CollOrUb (eventTmpl Assumptions.all L i.1 t ins.op) := by
      rw [hw]; exact warpTmpl_collOrUb hk
    cases hm : eventTmpl Assumptions.all L i.1 t ins.op <;> rw [hm] at hT hf <;>
      simp only [CollOrUb] at hT <;> simp only [Fires] at hf
    · obtain ⟨_, _, hE, -⟩ := hf; rw [hE]; rfl
    · obtain ⟨_, _, hE, -⟩ := hf; rw [hE]; rfl
    · rename_i f
      obtain ⟨hE, -⟩ := hf
      exact absurd (by rw [hE]) (hu f)

/-- **A warp-collective event is exactly one at a pc of `collPcs`.** -/
theorem coll_iff_pc (hX : Consistent L kernel Assumptions.all m X) (he : X.get i = some e)
    (hu : ∀ f, e.kind ≠ .ub f) : isWarpColl e = true ↔ e.pc ∈ collPcs :=
  ⟨coll_event_pc hX he, coll_of_pc hX he hu⟩

private theorem pcs_ck : collPcs.all (fun pc => match kernel.code[pc]? with
    | some ins => collInsB ins
    | none => false) = true := by
  decide +kernel

private theorem ins_ck : kernel.code.zipIdx.all (fun x =>
    !collInsB x.1 || decide (x.2 ∈ collPcs)) = true := by
  decide +kernel

/-- The instructions at the pcs of `collPcs` are `CollIns`. -/
theorem collPcs_ins {pc : Nat} (h : pc ∈ collPcs) :
    ∃ ins, kernel.code[pc]? = some ins ∧ CollIns ins := by
  have := List.all_eq_true.mp pcs_ck pc h
  cases hc : kernel.code[pc]? with
  | none => simp [hc] at this
  | some ins =>
    rw [hc] at this
    exact ⟨ins, rfl, by simpa [collInsB, CollIns] using this⟩

/-- A `CollIns` instruction is at a pc of `collPcs`. -/
theorem collIns_pc {pc : Nat} {ins : Instr} (h : kernel.code[pc]? = some ins) (hc : CollIns ins) :
    pc ∈ collPcs := by
  have := List.all_eq_true.mp ins_ck _ (zip_mem h)
  have hb : collInsB ins = true := by simpa [collInsB, CollIns] using hc
  simpa [hb] using this

private theorem ret_ck : kernel.code.zipIdx.all (fun x =>
    (match x.1.op with | .ret | .exit => decide (x.2 = 3611) | _ => true)) = true := by
  decide +kernel

/-- **An exit event is at the final `ret`, pc 3611.** -/
theorem exit_event_pc (hX : Consistent L kernel Assumptions.all m X) {pc : Nat}
    (he : X.get i = some ⟨pc, .exit⟩) : pc = 3611 := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hi, hf⟩
  · simp at hf
  · have h := List.all_eq_true.mp ret_ck _ (zip_mem hi)
    rcases fires_exit_op hf rfl with hr | hr <;> simp_all

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
