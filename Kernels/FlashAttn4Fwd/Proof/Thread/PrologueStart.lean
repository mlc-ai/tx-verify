-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Prologue

@[expose] public section

/-! # The prologue's first site

From the launch state, the thread reads the words of the parameter objects the roles use
(`seqlen_k`, the two divmod objects: one `ld.param` each, taken as one step with the bytes the
launch supplies, `exec_ldParamObject`), the four tensor-map parameter addresses and the dynamic
shared base, and reaches the shuffle of the shared base. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g w rk : Nat}

/-- A local step that writes the registers `ws` with their table values reaches the next
instruction with the table's facts, when every register live there is written or was live. -/
theorem at_written {t t' : TState} {pc : Nat} {ws : List Nat}
    (h : At t pc (factsAt L g w rk pc)) (hpc : t'.pc = pc + 1) (hs : t'.sub = t.sub)
    (ha : t'.acc = t.acc) (hf : t'.fault = t.fault)
    (hw : ∀ r ∈ ws, t'.regs r = some (valueOf L g w rk r))
    (hfr : ∀ r, r ∉ ws → t'.regs r = t.regs r)
    (hl : ∀ r ∈ Flow.live (pc + 1), r ∈ ws ∨ r ∈ Flow.live pc) :
    At t' (pc + 1) (factsAt L g w rk (pc + 1)) := by
  refine ⟨hpc, hs.trans h.2.1, ha.trans h.2.2.1, hf.trans h.2.2.2.1,
    holds_of_pointwise fun r hr => ?_⟩
  by_cases hm : r ∈ ws
  · exact hw r hm
  · rw [hfr r hm]
    rcases hl r hr with h' | h'
    · exact absurd h' hm
    · exact holds_mem h.2.2.2.2 (mem_factsFrom h')

/-- An `ld.param` of a parameter object into one register, as one step to the next
instruction's facts. -/
theorem ld_one {t : TState} {pc wd dw off d : Nat} {p : String} {ty : DType} {ext : MemExt}
    (hc : kernel.code[pc]? = some ⟨none, .mem
      { kind := .load, space := some .param, sem := .weak, elem := ty, vec := 1, ext,
        addr := ⟨.param p true, (off : Int)⟩, dsts := [some d] }⟩)
    (hs : ParamSupplied L p off (wd / 8 * [d].length)) (h : At t pc (factsAt L g w rk pc))
    (hv : paramElem wd dw (paramNat L p off (wd / 8)) = valueOf L g w rk d)
    (hl : ∀ r ∈ Flow.live (pc + 1), r ∈ [d] ∨ r ∈ Flow.live pc)
    (hsf : Assumption.SegFreePc asms pc := by seg_free_pc) (hw : ty.width = wd := by rfl)
    (hext : ext = if dw = wd then .same else .zero dw := by decide)
    (hr : MemAccess.rule
      { kind := .load, space := some .param, sem := .weak, elem := ty, vec := 1, ext,
        addr := ⟨.param p true, (off : Int)⟩, dsts := [some d] } = some .threadMove := by rfl) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' (pc + 1) (factsAt L g w rk (pc + 1)) := by
  subst hext
  refine ⟨_, run_local hc rfl h
    (exec_ldParamObject (ds := [d]) hs (Assumption.SegFreePc.of_eq h.1 hsf) asms_localRule_none
      hw hr),
    at_written h ?_ rfl rfl rfl ?_ ?_ hl⟩
  · simp [loadParamRegs, setReg, PTX.next, h.1]
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    simp [loadParamRegs, setReg, PTX.next, hv]
  · intro r hr
    simp only [List.mem_singleton] at hr
    simp [loadParamRegs, setReg, PTX.next, Function.update_of_ne hr]

/-- An `ld.param` of two consecutive elements of a parameter object, as one step. -/
theorem ld_two {t : TState} {pc wd dw off d d' : Nat} {p : String} {ty : DType} {ext : MemExt}
    (hc : kernel.code[pc]? = some ⟨none, .mem
      { kind := .load, space := some .param, sem := .weak, elem := ty, vec := 2, ext,
        addr := ⟨.param p true, (off : Int)⟩, dsts := [some d, some d'] }⟩)
    (hs : ParamSupplied L p off (wd / 8 * [d, d'].length)) (h : At t pc (factsAt L g w rk pc))
    (hd : d ≠ d')
    (hv : paramElem wd dw (paramNat L p off (wd / 8)) = valueOf L g w rk d)
    (hv' : paramElem wd dw (paramNat L p (off + wd / 8) (wd / 8)) =
      valueOf L g w rk d')
    (hl : ∀ r ∈ Flow.live (pc + 1), r ∈ [d, d'] ∨ r ∈ Flow.live pc)
    (hsf : Assumption.SegFreePc asms pc := by seg_free_pc) (hw : ty.width = wd := by rfl)
    (hext : ext = if dw = wd then .same else .zero dw := by decide)
    (hr : MemAccess.rule
      { kind := .load, space := some .param, sem := .weak, elem := ty, vec := 2, ext,
        addr := ⟨.param p true, (off : Int)⟩, dsts := [some d, some d'] } = some .threadMove :=
        by rfl) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' (pc + 1) (factsAt L g w rk (pc + 1)) := by
  subst hext
  refine ⟨_, run_local hc rfl h
    (exec_ldParamObject (ds := [d, d']) hs (Assumption.SegFreePc.of_eq h.1 hsf) asms_localRule_none
      hw hr),
    at_written h ?_ rfl rfl rfl ?_ ?_ hl⟩
  · simp [loadParamRegs, setReg, PTX.next, h.1]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [loadParamRegs, setReg, PTX.next, Function.update_of_ne hd, hv]
    · simp [loadParamRegs, setReg, PTX.next, hv']
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [loadParamRegs, setReg, PTX.next, Function.update_of_ne hr.1, Function.update_of_ne hr.2]

/-- Evaluate a prologue segment from `h` and close the facts of its end state. -/
syntax "pro_seg" term:max term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| pro_seg $h $hpre $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      have hbase := ($hpre).sharedRange
      unfold sharedBytes at hbase
      seg_fp $h using
        try pro_values
        all_goals (try launch_norm $hpre)
        all_goals (try seg_close [sb, $extra,*])
        all_goals (try simp only [b32, sb, Value.bits.injEq, true_and,
          $extra,*])
        all_goals decide +kernel))

/-- The opening local code reaches the shuffle of the shared base. -/
theorem start (hpre : Pre P L mem0) :
    ∃ t, Relation.ReflTransGen (Tau kernel asms L g) {} t ∧
      At t Site.shfl0.pc (facts L g ⟨.shfl0⟩) := by
  have h0 : At ({} : TState) 0 (factsAt L g (warpOf L g) (rankOf L g) 0) := ⟨rfl, rfl, rfl, rfl, by
    simp only [factsAt]
    rw [show Flow.live 0 = [] by table_decide]
    trivial⟩
  obtain ⟨t1, hr1, h1⟩ := ld_one (wd := 32) (dw := 32) (off := 0) Flow.code_0
    (supplied_sk hpre) h0 rfl (by table_decide)
  obtain ⟨t5, hr5, h5⟩ : ∃ t5, run kernel asms L g 4 t1 = some t5 ∧
      At t5 (Site.shfl0.pc - 7) (factsAt L g (warpOf L g) (rankOf L g) (Site.shfl0.pc - 7)) := by
    pro_seg h1 hpre
  obtain ⟨t6, hr6, h6⟩ := ld_two (wd := 8) (dw := 16) (off := 8) Flow.code_5
    (supplied_block hpre (by decide)) h5 (by decide) rfl rfl (by table_decide)
  obtain ⟨t7, hr7, h7⟩ := ld_one (wd := 32) (dw := 32) (off := 4) Flow.code_6
    (supplied_block hpre (by decide)) h6 rfl (by table_decide)
  obtain ⟨t8, hr8, h8⟩ := ld_one (wd := 32) (dw := 32) (off := 0) Flow.code_7
    (supplied_block hpre (by decide)) h7 rfl (by table_decide)
  obtain ⟨t9, hr9, h9⟩ := ld_two (wd := 8) (dw := 16) (off := 8) Flow.code_8
    (supplied_head hpre (by decide)) h8 (by decide) rfl rfl (by table_decide)
  obtain ⟨t10, hr10, h10⟩ := ld_one (wd := 32) (dw := 32) (off := 4) Flow.code_9
    (supplied_head hpre (by decide)) h9 rfl (by table_decide)
  obtain ⟨t11, hr11, h11⟩ := ld_one (wd := 32) (dw := 32) (off := 0) Flow.code_10
    (supplied_head hpre (by decide)) h10 rfl (by table_decide)
  obtain ⟨t12, hr12, h12⟩ : ∃ t12, run kernel asms L g 1 t11 = some t12 ∧
      At t12 Site.shfl0.pc (facts L g ⟨.shfl0⟩) := by
    pro_seg h11 hpre
  exact ⟨t12, run_rtg (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp
    hr1 hr5) hr6) hr7) hr8) hr9) hr10) (run_comp hr11 hr12)), h12⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
