-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.RoleRun
public import Kernels.Fp16Gemm8192.Proof.Thread.RegDefs
public import Lemmas.Flow.NotRegister
public import Lemmas.Flow.OpPcsFast

@[expose] public section

/-! # The register request along a thread's run

A thread's register request fires at its request site (decided on the code: `reg_site`), and a
step keeps the requests of a thread's events counting its state's (`reg_step`). The step is one
conjunct of the run invariant `ClInv` of `ClusterCount.lean`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- A consumer never returns to its first site. -/
theorem Consumer.next_site_ne {c c' : Consumer.D} {e : Event}
    (h : Consumer.next L g c e = some (some c')) : c'.site ≠ .setMaxReg := by
  obtain ⟨site, m, n, m', n', cp, ap, resp, x, acc, base⟩ := c
  cases site <;> simp only [Consumer.next] at h
  all_goals repeat' (first | split_ifs at h | split at h)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at h)
  all_goals (try (simp only [Option.map_eq_some_iff, Option.some.injEq] at h; obtain ⟨_, -, rfl⟩ :=
    h))
  all_goals (try subst h)
  all_goals simp

/-- A prologue step off the request site keeps the state's request count. -/
theorem Prologue.next_regOps {p : Prologue.D} {e : Event} {d' : ThreadD}
    (hn : Prologue.next L g p e = some (some d')) (hs : p.site ≠ .setMaxReg) :
    ThreadD.regOps (Sum.inl p) = d'.regOps := by
  obtain ⟨site, w⟩ := p
  cases site
  case setMaxReg => exact absurd rfl hs
  all_goals
    simp only [Prologue.next] at hn
    repeat' split at hn
  all_goals first
    | (cases hn; done)
    | (cases hn; simp [ThreadD.regOps, Prologue.afterInits, Prologue.afterElect]; done)
    | (cases hn; simp [ThreadD.regOps, Prologue.consStart, Prologue.afterInits,
        Prologue.afterElect]; try (split_ifs <;> simp_all))

/-- The kernel's register adjustments are at its two request sites (decided on the code, in one
pass). -/
theorem kernel_reg_pcs : OpPcsFast kernel.code setMaxRegOp [Flow.setMaxReg_0, Flow.setMaxReg_1] =
    true := by
  decide +kernel

/-- A register request fires at a register request site. -/
theorem reg_site {d : ThreadD} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o) (h : isSetMaxReg e = true) :
    d.AtSetMaxReg := by
  unfold isSetMaxReg at h
  split at h
  · rename_i inc n inst hk
    have hop := fires_setMaxReg_op hf hk
    have hpc := OpPcsFast.mem kernel_reg_pcs hc (by rw [hop]; rfl)
    clear hc hf hk hop h
    rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
        ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
    all_goals change site.pc ∈ _ at hpc
    all_goals (cases site <;> first
      | (simp [ThreadD.AtSetMaxReg]; done)
      | (exfalso; clear * - hpc; revert hpc; decide +revert))
  · cases h

/-- A state at its register request fires it: the request of its site. -/
theorem reg_fire {d : ThreadD} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : d.AtSetMaxReg) (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o) :
    ∃ inst, e = ⟨d.regRequest.1, .setMaxReg d.regRequest.2.1 d.regRequest.2.2 inst⟩ := by
  rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
  · change site = .setMaxReg at hat
    subst hat
    change kernel.code[Flow.setMaxReg_0]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_0)
    exact fires_of_setMaxReg_op (n := 56) (by decide) hf
  · exact hat.elim
  · exact hat.elim
  · exact hat.elim
  · change site = .setMaxReg at hat
    subst hat
    change kernel.code[Flow.setMaxReg_1]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_1)
    exact fires_of_setMaxReg_op (n := 224) (by decide) hf

set_option maxHeartbeats 8000000 in
/-- **A step keeps the register requests**: the requests of a thread's events count its state's. -/
theorem reg_step {d d' : ThreadD} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    {pre : List Event} (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o)
    (hn : (code L g).next d e = some (some d')) (hq : regOps pre = d.regOps) :
    regOps (pre ++ [e]) = d'.regOps := by
  have hsnoc : regOps (pre ++ [e]) = regOps pre + (if isSetMaxReg e then 1 else 0) := by
    simp [regOps, List.countP_append]
  rw [hsnoc, hq]
  by_cases hat : d.AtSetMaxReg
  · obtain ⟨inst, he⟩ := reg_fire hat hc hf
    have hse : isSetMaxReg e = true := by rw [he]; rfl
    simp only [hse, ↓reduceIte]
    rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
        ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
    · change site = .setMaxReg at hat
      subst hat
      change Prologue.next L g ⟨.setMaxReg, w⟩ e = some (some d') at hn
      simp only [Prologue.next] at hn
      repeat' split at hn
      all_goals first
        | (cases hn; done)
        | (cases hn; simp [ThreadD.regOps])
    · exact hat.elim
    · exact hat.elim
    · exact hat.elim
    · change site = .setMaxReg at hat
      subst hat
      obtain ⟨c', hn', rfl⟩ := next_of_cons hn
      have := Consumer.next_site_ne hn'
      simp [ThreadD.regOps, this]
  · have hne : isSetMaxReg e = false := by
      by_contra h
      exact hat (reg_site hc hf (by simpa using h))
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
        ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
    · exact Prologue.next_regOps hn (by simpa [ThreadD.AtSetMaxReg] using hat)
    · obtain ⟨l', -, rfl⟩ := next_of_loader hn; rfl
    · obtain ⟨m', -, rfl⟩ := next_of_mma hn; rfl
    · obtain ⟨s', -, rfl⟩ := next_of_sched hn; rfl
    · obtain ⟨c', hn', rfl⟩ := next_of_cons hn
      have := Consumer.next_site_ne hn'
      have hat' : ¬ site = .setMaxReg := by simpa [ThreadD.AtSetMaxReg] using hat
      simp [ThreadD.regOps, this, hat']

end
end PTX.Kernels.Fp16Gemm8192.Proof
