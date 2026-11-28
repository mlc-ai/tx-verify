-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.LocalLanding
public import Lemmas.Flow.WarpUniformAt
public import Lemmas.Register.EventRegFrame
import Kernels.InklingRelDecode.Flow.Code.Part000
import Kernels.InklingRelDecode.Flow.Code.Part015
import Kernels.InklingRelDecode.Flow.Code.Part036

@[expose] public section

/-! # The guards of the guarded `.sync.aligned` `tcgen05` instructions agree in a warp

Besides the six poll branches, six instructions of the program compare a guard between the lanes
of a warp (`Instr.laneCompared`): `@%p3 tcgen05.alloc` (pc 11), `@%p3
tcgen05.relinquish_alloc_permit` (pc 15), `@%p3 tcgen05.dealloc` (pc 2851, 2854), and the two
`tcgen05.st` guarded by `%p172` (pc 1009) and `%p171` (pc 2328) (`guardPcs`, `lane_ok`).

The guard registers are written only by `mov.u32 %r1, %tid.x` (pc 8, register 462), `setp.lt.u32
%p3, %r1, 32` (pc 9, register 3), `mov.pred %p172, -1` (pc 1008) and `mov.pred %p171, -1`
(pc 2327); no other instruction writes them (`keeps_ok`). So at every state of a thread, from the
launch state on, register 462 is unset or `%tid.x`, register 3 is unset or `tid < 32`, and
registers 171 and 172 are unset or true (`GOk`, kept by every step: `step_ok`). The record of a
walk at one of the six positions then has no guard value or the warp's value, so two lanes of a
warp never disagree there (`not_divergentAt`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow PTX.EventFrame

noncomputable section
set_option maxRecDepth 100000

theorem trunc32Mod (x : Nat) :
    truncBits 32 (BitVec.ofNat 64 x) = BitVec.ofNat 64 (x % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat]
  have h : (2 : Nat) ^ 32 ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by decide)
  rw [Nat.mod_mod_of_dvd _ h]

/-- In a launch whose CTA is `(block, 1, 1)`, `%tid.x` is the thread's index in the CTA. -/
theorem tidOfX {L : Launch} (hn : L.ntid = ⟨L.block, 1, 1⟩) (g : Nat) :
    ((L.tidOf g).get .x) = g % L.block := by
  simp only [Launch.tidOf, Dim3.coord, hn, Nat.mod_mod, Nat.mod_one, Nat.mul_one]
  rcases Nat.eq_zero_or_pos L.block with h0 | hpos
  · simp [h0, Dim3.get]
  · simp [Dim3.get]

/-- An operation that is neither a floating instruction nor a conversion takes the Core rule: no
assumption of the kernel has a local rule for it. -/
theorem asmsNone {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hf : ∀ f, op ≠ .float f) (hc : ∀ c, op ≠ .cvt c) :
    ∀ a ∈ Assumptions.all, a.localRule L g t op = none := by
  have h1 : Assumption.FloatForm.ofOp op = none := by
    cases op <;> first | rfl | exact absurd rfl (hf _) | exact absurd rfl (hc _)
  have h2 : Assumption.ApproxForm.ofOp op = none := by
    cases op <;> first | rfl | exact absurd rfl (hf _)
  intro a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · exact Assumption.idealReal_localRule_none fun f h => by rw [h1] at h; cases h
  · exact Assumption.approxExact_localRule_none fun f h => by rw [h2] at h; cases h
  · rfl
  all_goals first | rfl | simp only [Assumptions.lg2Exact, Assumptions.divFullExact,
    Assumptions.negExact, Assumptions.bf16Exact]
  all_goals cases op <;> first | exact absurd rfl (hf _) | exact absurd rfl (hc _) | simp

/-! ## The positions and the static checks -/

/-- The guarded `.sync.aligned` `tcgen05` instructions. -/
def guardPcs : List Nat := [11, 15, 1009, 2328, 2851, 2854]

/-- The positions of `guardPcs`. -/
def U (pc : Nat) : Prop := pc ∈ guardPcs

/-- The guard register of each of `guardPcs`. -/
def guardReg (pc : Nat) : Nat := if pc = 1009 then 172 else if pc = 2328 then 171 else 3

/-- The registers that hold `%tid.x` and the three guards, and their writers. -/
def gRegs : List Nat := [462, 3, 171, 172]
def gWriters : List Nat := [8, 9, 1008, 2327]

/-- Every lane-comparing instruction is a poll branch or one of `guardPcs`. -/
theorem laneOk_true : kernel.code.zipIdx.all (fun p => !p.1.laneCompared ||
    kernel.pollBranch p.2 || guardPcs.contains p.2) = true := by
  decide +kernel

theorem lane_ok : ∀ pc ins, kernel.code[pc]? = some ins → ins.laneCompared = true →
    kernel.pollBranch pc = true ∨ U pc := by
  intro pc ins hc hl
  have h := List.all_eq_true.mp laneOk_true (ins, pc) (List.mem_zipIdx_iff_getElem?.mpr hc)
  simp only [hl, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
  rcases h with h | h
  · exact .inl h
  · exact .inr (by simpa [U] using h)

/-- No instruction but the writers writes a register of `gRegs`. -/
theorem keepsOk_true : kernel.code.zipIdx.all (fun p => gWriters.contains p.2 ||
    gRegs.all fun r => !(writesRegs p.1.op).contains r && !(eventWrites p.1.op).contains r) =
      true := by
  decide +kernel

theorem keeps_ok {pc : Nat} {ins : Instr} (hc : kernel.code[pc]? = some ins)
    (hw : pc ∉ gWriters) {r : Nat} (hr : r ∈ gRegs) :
    r ∉ writesRegs ins.op ∧ r ∉ eventWrites ins.op := by
  have h := List.all_eq_true.mp keepsOk_true (ins, pc) (List.mem_zipIdx_iff_getElem?.mpr hc)
  have hw' : gWriters.contains pc = false := by simpa using hw
  rw [hw', Bool.false_or] at h
  have := List.all_eq_true.mp h r hr
  simpa using this

/-- No software `exp2` instance writes a register of `gRegs`, and the instruction at each site
is a floating instruction. -/
theorem emuOk_true : Assumptions.emuSites.all (fun pc => (gRegs.all fun r =>
    !(emuW pc).contains r) && (match kernel.code[pc]? with
      | some ⟨_, .float _⟩ => true | _ => false)) = true := by
  decide +kernel

theorem emu_keeps {pc : Nat} (hs : Assumptions.emuSites.contains pc = true) {r : Nat}
    (hr : r ∈ gRegs) : r ∉ emuW pc := by
  have h := (Bool.and_eq_true _ _).mp
    (List.all_eq_true.mp emuOk_true pc (by simpa using hs))
  have := List.all_eq_true.mp h.1 r hr
  simpa using this

theorem emu_float {pc : Nat} (hs : Assumptions.emuSites.contains pc = true) {ins : Instr}
    (hc : kernel.code[pc]? = some ins) : ∃ f, ins.op = .float f := by
  have h := (Bool.and_eq_true _ _).mp
    (List.all_eq_true.mp emuOk_true pc (by simpa using hs))
  have h2 := h.2
  rw [hc] at h2
  obtain ⟨gd, op⟩ := ins
  cases op <;> simp at h2
  exact ⟨_, rfl⟩

/-- Each of `guardPcs` is a uniform instruction guarded by its `guardReg`, and no `brx.idx`. -/
theorem guardOk_true : guardPcs.all (fun pc => match kernel.code[pc]? with
    | some ins => ins.guard == some (guardReg pc, false) && ins.op.uniform &&
        (match ins.op with | .brx .. => false | _ => true) && ins.op.uniformScope == .warp
    | none => false) = true := by
  decide +kernel

theorem guard_at {pc : Nat} (hp : U pc) : ∃ ins, kernel.code[pc]? = some ins ∧
    ins.guard = some (guardReg pc, false) ∧ ins.op.uniform = true ∧
    (∀ i ts u, ins.op ≠ .brx i ts u) ∧ ins.op.uniformScope = .warp := by
  have h := List.all_eq_true.mp guardOk_true pc hp
  cases hc : kernel.code[pc]? with
  | none => simp [hc] at h
  | some ins =>
    rw [hc] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨ins, rfl, h1, h2, fun i ts u he => ?_, h4⟩
    rw [he] at h3
    cases h3

/-- The writers are local instructions. -/
theorem writers_local : gWriters.all (fun pc => match kernel.code[pc]? with
    | some ins => ins.op.isLocal | none => false) = true := by
  decide +kernel

/-! ## The invariant -/

variable {L : Launch} {g : Nat}

/-- Register `r` is unset or holds `v`. -/
def Tr (r : Nat) (v : Value) (t : TState) : Prop := t.regs r = none ∨ t.regs r = some v

/-- The value of `%p3`: the thread is in warp 0 of its CTA. -/
def p3v (L : Launch) (g : Nat) : Bool := decide (g % L.block < 32)

/-- The registers of `gRegs` hold `%tid.x`, `tid < 32`, true, true, or are unset. -/
def GOk (L : Launch) (g : Nat) (t : TState) : Prop :=
  Tr 462 (b32 (g % L.block)) t ∧ Tr 3 (.pred (p3v L g)) t ∧ Tr 171 (.pred true) t ∧
    Tr 172 (.pred true) t

theorem gOk_init : GOk L g {} := ⟨.inl rfl, .inl rfl, .inl rfl, .inl rfl⟩

theorem GOk.of_regs {s u : TState} (h : GOk L g s) (hk : ∀ r ∈ gRegs, u.regs r = s.regs r) :
    GOk L g u := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Tr; rw [hk 462 (by simp [gRegs])]; exact h1
  · unfold Tr; rw [hk 3 (by simp [gRegs])]; exact h2
  · unfold Tr; rw [hk 171 (by simp [gRegs])]; exact h3
  · unfold Tr; rw [hk 172 (by simp [gRegs])]; exact h4

/-! ## The writers' steps -/

theorem exec_8 (hn : L.ntid = ⟨L.block, 1, 1⟩) (hb : L.block = 256) {t : TState} (ht : t.pc = 8)
    {ins : Instr} (hc : kernel.code[t.pc]? = some ins) :
    execLocalA Assumptions.all L g t ins.op = .ok (next (setReg t 462 (b32 (g % L.block)))) := by
  rw [ht, Flow.code_8] at hc
  cases hc
  rw [(segFree (pc := 8) (by decide)).exec ht,
    execLocalRule_of_none (asmsNone (by simp) (by simp))]
  have hpos : g % L.block % 4294967296 = g % L.block := Nat.mod_eq_of_lt (by rw [hb]; omega)
  rw [execLocal]
  · simp [execMove, readValue, readBits, sregValue, SReg.width, tidOfX hn, trunc32Mod,
      hpos, b32, Value.bytes, bind, Except.bind, pure, Except.pure, DType.width]
  · rfl

theorem exec_9 (hb : L.block = 256) {t : TState} (ht : t.pc = 9) {ins : Instr}
    (hc : kernel.code[t.pc]? = some ins) (h : t.regs 462 = some (b32 (g % L.block))) :
    execLocalA Assumptions.all L g t ins.op = .ok (next (setReg t 3 (.pred (p3v L g)))) := by
  rw [ht, Flow.code_9] at hc
  cases hc
  rw [(segFree (pc := 9) (by decide)).exec ht,
    execLocalRule_of_none (asmsNone (by simp) (by simp))]
  rw [execLocal]
  · have hpos : g % L.block % 4294967296 = g % L.block := Nat.mod_eq_of_lt (by rw [hb]; omega)
    simp [execInt, readBits, readReg, h, b32, trunc32Mod, hpos, PTX.compare,
      bind, Except.bind, pure, Except.pure, DType.width, DType.kind?, p3v]
    rw [hb]
    congr 4
    apply propext
    omega
  · rfl

theorem exec_9_none {t : TState} (ht : t.pc = 9) {ins : Instr}
    (hc : kernel.code[t.pc]? = some ins) (h : t.regs 462 = none) {u : TState} :
    execLocalA Assumptions.all L g t ins.op ≠ .ok u := by
  rw [ht, Flow.code_9] at hc
  cases hc
  rw [(segFree (pc := 9) (by decide)).exec ht,
    execLocalRule_of_none (asmsNone (by simp) (by simp))]
  rw [execLocal]
  · simp [execInt, readBits, readReg, h, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw]
  · rfl

theorem exec_pred {t : TState} (ht : t.pc = 1008 ∨ t.pc = 2327) {ins : Instr}
    (hc : kernel.code[t.pc]? = some ins) :
    execLocalA Assumptions.all L g t ins.op =
      .ok (next (setReg t (if t.pc = 1008 then 172 else 171) (.pred true))) := by
  rcases ht with ht | ht
  · rw [ht, Flow.code_1008] at hc
    cases hc
    rw [(segFree (pc := 1008) (by decide)).exec ht,
      execLocalRule_of_none (asmsNone (by simp) (by simp)), ht]
    rw [execLocal]
    · simp [execMove, readPred, bind, Except.bind, pure, Except.pure]
    · rfl
  · rw [ht, Flow.code_2327] at hc
    cases hc
    rw [(segFree (pc := 2327) (by decide)).exec ht,
      execLocalRule_of_none (asmsNone (by simp) (by simp)), ht]
    rw [execLocal]
    · simp [execMove, readPred, bind, Except.bind, pure, Except.pure]
    · rfl

/-! ## Every step keeps the invariant -/

/-- A local step: the guard is false and the instruction is skipped, or the guard holds and the
instruction's local step runs. -/
theorem tau_cases {A : List Assumption} {s u : TState} (ht : Tau kernel A L g s u) :
    ∃ ins, kernel.code[s.pc]? = some ins ∧
      ((guardHolds s ins.guard = .ok false ∧ u = skip s) ∨
        (guardHolds s ins.guard = .ok true ∧ execLocalA A L g s ins.op = .ok u)) := by
  unfold Tau out at ht
  cases hf : s.fault with
  | some f => simp [hf] at ht
  | none =>
    simp only [hf] at ht
    cases hc : kernel.code[s.pc]? with
    | none => simp [hc] at ht
    | some ins =>
      simp only [hc] at ht
      refine ⟨ins, rfl, ?_⟩
      cases hg : guardHolds s ins.guard with
      | error f => simp [hg] at ht
      | ok b =>
        cases b with
        | false =>
          simp only [hg, Out.tau.injEq] at ht
          exact .inl ⟨rfl, ht.symm⟩
        | true =>
          simp only [hg] at ht
          split at ht
          · split at ht
            · rename_i t1 hex
              simp only [Out.tau.injEq] at ht
              subst ht
              exact .inr ⟨rfl, hex⟩
            · cases ht
          · cases ht

/-- The registers of an integer, move or conversion instruction are those of its form with the
values of changing special registers substituted. -/
theorem writesRegs_withSregValues {op : Op} (vs : List Nat)
    (hop : (∃ i, op = .int i) ∨ (∃ m, op = .move m) ∨ ∃ c, op = .cvt c) :
    writesRegs (op.withSregValues vs) = writesRegs op ∧ eventWrites op = writesRegs op := by
  rcases hop with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, rfl⟩ <;> exact ⟨rfl, rfl⟩

/-- **Every step of a thread keeps `GOk`.** -/
theorem step_ok (hn : L.ntid = ⟨L.block, 1, 1⟩) (hb : L.block = 256) {s s' : TState}
    {ev : Option Event} (hs : GOk L g s) (hst : WStep kernel Assumptions.all L g s ev s') :
    GOk L g s' := by
  rcases hst with ⟨-, ht⟩ | ⟨e, -, he⟩
  · obtain ⟨ins, hc, ⟨-, rfl⟩ | ⟨hg, hex⟩⟩ := tau_cases ht
    · exact hs.of_regs fun _ _ => rfl
    · by_cases hw : s.pc ∈ gWriters
      · simp only [gWriters, List.mem_cons, List.not_mem_nil, or_false] at hw
        obtain ⟨h1, h2, h3, h4⟩ := hs
        rcases hw with hw | hw | hw | hw
        · rw [exec_8 hn hb hw hc, Except.ok.injEq] at hex
          subst hex
          refine ⟨.inr ?_, ?_, ?_, ?_⟩ <;> simp_all [Tr, next, setReg]
        · rcases h1 with h1 | h1
          · exact absurd hex (exec_9_none hw hc h1)
          · rw [exec_9 hb hw hc h1, Except.ok.injEq] at hex
            subst hex
            refine ⟨?_, .inr ?_, ?_, ?_⟩ <;> simp_all [Tr, next, setReg]
        · rw [exec_pred (.inl hw) hc, Except.ok.injEq] at hex
          subst hex
          refine ⟨?_, ?_, ?_, .inr ?_⟩ <;> simp_all [Tr, next, setReg]
        · rw [exec_pred (.inr hw) hc, Except.ok.injEq] at hex
          subst hex
          refine ⟨?_, ?_, .inr ?_, ?_⟩ <;> simp_all [Tr, next, setReg]
      · exact hs.of_regs fun r hr => localA_regs hex r (keeps_ok hc hw hr).1
          (fun he => emu_keeps he hr)
  · obtain ⟨ins, hc, hl, -⟩ := estep_event_source he
    by_cases hw : s.pc ∈ gWriters
    · have h := List.all_eq_true.mp writers_local s.pc hw
      simp only [hc, hl] at h
      cases h
    · have hk := estep_regsKept he hc fun hop vs u hu r hr => by
        obtain ⟨h1, h2⟩ := writesRegs_withSregValues vs hop
        rw [h2] at hr
        refine localA_regs hu r (by rw [h1]; exact hr) fun hes => ?_
        obtain ⟨f, hf⟩ := emu_float hes hc
        rcases hop with ⟨i, hi⟩ | ⟨m, hm⟩ | ⟨c, hc'⟩
        · rw [hf] at hi; cases hi
        · rw [hf] at hm; cases hm
        · rw [hf] at hc'; cases hc'
      exact hs.of_regs fun r hr => hk r (keeps_ok hc hw hr).2

/-! ## The records at the six positions -/

/-- At one of `guardPcs`, the record of a step from a state of `GOk` has no index, and its guard
is unset or the warp's value: `tid < 32` for `%p3`, true for `%p171` and `%p172`. -/
theorem visit_guard {s : TState} {ev : Option Event} (hs : GOk L g s) (hp : U s.pc) :
    (visit kernel L g s ev).index = none ∧ ((visit kernel L g s ev).guard = none ∨
      (visit kernel L g s ev).guard = some (if guardReg s.pc = 3 then p3v L g else true)) := by
  obtain ⟨ins, hc, hgd, hu, hnb, -⟩ := guard_at hp
  have hidx : uniIndex L g s ins.op = none := by
    unfold uniIndex
    split
    · rename_i i ts he
      exact absurd he (hnb _ _ _)
    · rfl
  refine ⟨by simp [visit, hc, hidx], ?_⟩
  simp only [visit, hc, hgd, hu, Option.isSome_some, Bool.and_self, ↓reduceIte]
  obtain ⟨h1, h2, h3, h4⟩ := hs
  have hR : guardReg s.pc = 3 ∨ guardReg s.pc = 171 ∨ guardReg s.pc = 172 := by
    unfold guardReg; split_ifs <;> simp
  rcases hR with hR | hR | hR <;> rw [hR]
  · rcases h2 with h | h <;> simp [guardHolds, readReg, h, Except.toOption, bind,
      Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
  · rcases h3 with h | h <;> simp [guardHolds, readReg, h, Except.toOption, bind,
      Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
  · rcases h4 with h | h <;> simp [guardHolds, readReg, h, Except.toOption, bind,
      Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]

/-- Two lanes of a warp have one value of `%p3`. -/
theorem p3v_warp {g h : Nat} (hw : SameWarp L g h) : p3v L g = p3v L h := by
  have := hw.2
  unfold p3v
  apply decide_eq_decide.mpr
  omega

/-- **No two lanes of a warp disagree at the guarded `.sync.aligned` `tcgen05` instructions.** -/
theorem not_divergentAt (hn : L.ntid = ⟨L.block, 1, 1⟩) (hb : L.block = 256) {X : Execution} :
    ¬ WarpDivergentAt U L kernel Assumptions.all X := by
  rintro ⟨g, h, -, -, -, eg, eh, vg, vh, -, -, hwg, hwh, i, j, pc, vi, vj, hU, hvi, hvj, hpi,
    hpj, hgrp, hdis, -⟩
  obtain ⟨s, ev, hsI, rfl⟩ := hwg.inv (fun _ _ _ => step_ok hn hb) gOk_init hvi
  obtain ⟨t, ev', htI, rfl⟩ := hwh.inv (fun _ _ _ => step_ok hn hb) gOk_init hvj
  simp only [visit_pc] at hpi hpj
  subst hpi
  obtain ⟨hi1, hi2⟩ := visit_guard (ev := ev) hsI hU
  obtain ⟨hj1, hj2⟩ := visit_guard (ev := ev') htI (hpj ▸ hU)
  obtain ⟨ins, hc, -, -, -, hsc⟩ := guard_at hU
  have hw : SameWarp L g h := by
    simpa [Kernel.uniformScopeAt, hc, hsc, SameUniformGroup] using hgrp
  rcases hdis with ⟨b, b', hb1, hb2, hne⟩ | ⟨x, y, hx, -, -⟩
  · rw [hpj] at hj2
    rcases hi2 with hi2 | hi2 <;> rcases hj2 with hj2 | hj2
    · rw [hi2] at hb1; cases hb1
    · rw [hi2] at hb1; cases hb1
    · rw [hj2] at hb2; cases hb2
    · rw [hi2] at hb1
      rw [hj2] at hb2
      simp only [Option.some.injEq] at hb1 hb2
      subst hb1 hb2
      rw [p3v_warp hw] at hne
      exact hne rfl
  · rw [hi1] at hx; cases hx

end
end PTX.Kernels.InklingRelDecode.Proof.Lib
