-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Spec
public import Init.Data.Nat.ToString
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Kernels.TmlFa4Fwd.Flow.Code.Part002
public import Kernels.TmlFa4Fwd.Flow.Code.Part029
public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Lemmas.Flow.Regs
public import Lemmas.Isa.Rule

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX Proof

noncomputable section
set_option maxRecDepth 2000

private theorem localStep {l : Launch} {g : Nat} {t u : TState} {op : Op}
    (hf : t.fault = none) (hc : kernel.code[t.pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true) (he : execLocal l g t op = .ok u) :
    tauStep kernel [] l g t = some u := by
  have he' : execLocalA [] l g t op = .ok u := he
  simp only [tauStep, out, hf, hc, guardHolds, pure, Except.pure, hl, ↓reduceIte, he']

private theorem branchStep {l : Launch} {g : Nat} {t : TState} {r dst : Nat}
    (hf : t.fault = none)
    (hc : kernel.code[t.pc]? = some ⟨some (r, false), .bra dst false⟩)
    (hr : t.regs r = some (.pred true)) :
    tauStep kernel [] l g t = some { t with pc := dst } := by
  simp [tauStep, out, hf, hc, hr, guardHolds, readReg, Op.isLocal, execLocalA,
    execLocalRule, execLocal, Op.rule, execBranch, bind, Except.bind, pure, Except.pure]

private theorem kernelName : kernel.name =
    "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_object_at__tenso\
    r000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf16gmemalign16o1i64div8_\
    0" := rfl

private theorem decimal19 : toString (19 : Nat) = "19" := by
  rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
  simp only [show (19 / 10 : Nat) = 1 by decide, show (19 % 10 : Nat) = 9 by decide,
    Nat.repr_of_lt (n := 1) (by decide), Nat.repr_of_lt (n := 9) (by decide),
    Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_nine.mpr rfl]
  rfl

/-- The eight local steps from the CTA barrier to warp 13's scheduler register hint.
Every register outside the dispatch's write set keeps its barrier state value. -/
theorem warp13DispatchWith {A : List Assumption} [StartupAgreement A]
    {p : Params} {l : Launch} {m : Mem0} (hpre : Pre p l m)
    (g : Nat) (t : TState) (hg : g < l.threads) (hpc : t.pc = 174) (hf : t.fault = none)
    (hw : t.regs 1062 = some (.bits 32 (BitVec.ofNat 64 13)))
    (hs : t.regs 2535 = some (.bits 32 (BitVec.ofNat 64 l.sharedBase))) :
    ∃ u, run kernel A l g 8 t = some u ∧ u.pc = Flow.setMaxReg_2 ∧ u.fault = none ∧
      u.regs 1072 = some (.bits 32 (BitVec.ofNat 64 (g / l.block))) ∧
      u.regs 1178 = some (.bits 32 (BitVec.ofNat 64 (l.sharedBase + 68608))) ∧
      u.regs 7228 = some (.bits 32 (BitVec.ofNat 64 p.batch)) ∧
      u.sub = t.sub ∧ u.acc = t.acc ∧
      ∀ r ∉ [1072, 1706, 60, 1178, 263, 7228], u.regs r = t.regs r := by
  have hcta := (sregValue_oneDim hpre.cluster.2.2 g).2.2.1
  have hbound : g / l.block < 2 ^ 32 := by
    have hb : 0 < l.block := by rw [hpre.block]; decide
    have h := (Nat.div_lt_iff_lt_mul hb).2 (show g < l.grid * l.block from hg)
    exact lt_trans h (lt_trans hpre.grid.2.2 (by decide))
  have hshared : l.sharedBase + 68608 < 2 ^ 32 := by have := hpre.shared.2.1; omega
  have hsbase : l.sharedBase < 2 ^ 32 := by omega
  obtain ⟨hbatch, hparam⟩ := hpre.values (19, p.batch) (by simp [Params.scalarWords])
  let t1 := next (setReg t 1072 (.bits 32 (BitVec.ofNat 64 (g / l.block))))
  let t2 := next (setReg t1 1706 (.bits 32 (BitVec.ofNat 64 12)))
  let t3 := next (setReg t2 60 (.pred true))
  let t4 := { t3 with pc := 1901 }
  let t5 := next (setReg t4 1178 (.bits 32 (BitVec.ofNat 64 (l.sharedBase + 68608))))
  let t6 := next (setReg t5 263 (.pred true))
  let t7 := { t6 with pc := 2768 }
  let t8 := next (setReg t7 7228 (.bits 32 (BitVec.ofNat 64 p.batch)))
  have h1 : tauStep kernel [] l g t = some t1 := by
    apply localStep hf (by rw [hpc]; exact Flow.code_174) rfl
    rw [execLocal_move rfl]
    simp [execMove, readValue, readBits, SReg.width, DType.width, Value.bytes, hcta,
      bind, Except.bind, pure, Except.pure, t1,
      truncBits_ofNat hbound (by decide)]
  have h2 : tauStep kernel [] l g t1 = some t2 := by
    have hp1 : t1.pc = 175 := by change t.pc + 1 = 175; rw [hpc]
    have hw1 : t1.regs 1062 = some (.bits 32 (BitVec.ofNat 64 13)) := by
      simpa [t1, next, setReg] using hw
    apply localStep (t := t1) hf (by rw [hp1]; exact Flow.code_175) rfl
    rw [execLocal_int rfl]
    simp only [execInt, DType.width, readBits, readReg, hw1, bind, Except.bind,
      pure, Except.pure]
    rfl
  have h3 : tauStep kernel [] l g t2 = some t3 := by
    have hp2 : t2.pc = 176 := by change t.pc + 1 + 1 = 176; rw [hpc]
    have hw2 : t2.regs 1706 = some (.bits 32 (BitVec.ofNat 64 12)) := by
      simp [t2, next, setReg]
    apply localStep (t := t2) hf (by rw [hp2]; exact Flow.code_176) rfl
    rw [execLocal_int rfl]
    simp only [execInt, DType.width, readBits, readReg, hw2, bind, Except.bind,
      pure, Except.pure]
    rfl
  have h4 : tauStep kernel [] l g t3 = some t4 := by
    have hp3 : t3.pc = 177 := by change t.pc + 1 + 1 + 1 = 177; rw [hpc]
    exact branchStep (t := t3) hf (by rw [hp3]; exact Flow.code_177) (by simp [t3, next, setReg])
  have h5 : tauStep kernel [] l g t4 = some t5 := by
    have hp4 : t4.pc = 1901 := rfl
    have hs4 : t4.regs 2535 = some (.bits 32 (BitVec.ofNat 64 l.sharedBase)) := by
      simpa [t4, t3, t2, t1, next, setReg] using hs
    apply localStep (t := t4) hf (by rw [hp4]; exact Flow.code_1901) rfl
    rw [execLocal_int rfl]
    simp only [execInt, DType.width, readValue, readBits, readReg, hs4, bind, Except.bind,
      pure, Except.pure, truncBits_ofNat hsbase (by decide)]
    change (Except.ok (next (setReg t4 1178 (.bits 32 (truncBits 32
      (BitVec.ofNat 64 l.sharedBase + BitVec.ofNat 64 68608))))) : Exec TState) = .ok t5
    rw [← BitVec.ofNat_add, truncBits_ofNat hshared (by decide)]
  have h6 : tauStep kernel [] l g t5 = some t6 := by
    have hp5 : t5.pc = 1902 := rfl
    have hw5 : t5.regs 1062 = some (.bits 32 (BitVec.ofNat 64 13)) := by
      simpa [t5, t4, t3, t2, t1, next, setReg] using hw
    apply localStep (t := t5) hf (by rw [hp5]; exact Flow.code_1902) rfl
    rw [execLocal_int rfl]
    simp only [execInt, DType.width, readBits, readReg, hw5, bind, Except.bind,
      pure, Except.pure]
    rfl
  have h7 : tauStep kernel [] l g t6 = some t7 := by
    have hp6 : t6.pc = 1903 := rfl
    exact branchStep (t := t6) hf (by rw [hp6]; exact Flow.code_1903) (by simp [t6, next, setReg])
  have h8 : tauStep kernel [] l g t7 = some t8 := by
    have hp7 : t7.pc = 2768 := rfl
    apply localStep (t := t7) hf (by rw [hp7]; exact Flow.code_2768) rfl
    rw [execLocal_mem rfl]
    have hn : param 19 = "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttention\
      ForwardSm100_object_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_\
      tensorptrbf16gmemalign16o1i64div8_0_param_19" := by
      unfold param
      rw [kernelName, decimal19]
      rfl
    change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at hparam
    rw [hn] at hparam
    simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq, hparam,
      DType.width, MemExt.extendBits_same, pure, Except.pure, truncBits_ofNat hbatch (by decide)]
    rfl
  refine ⟨t8, ?_, rfl, hf, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · have lift {s v : TState} (hc : StartupPc s.pc)
        (hs : tauStep kernel [] l g s = some v) : tauStep kernel A l g s = some v :=
      startupTau hc hs
    have s1 := lift (.inl (by rw [hpc]; decide)) h1
    have s2 := lift (.inl (by change t.pc + 1 < 179; rw [hpc]; decide)) h2
    have s3 := lift (.inl (by change t.pc + 2 < 179; rw [hpc]; decide)) h3
    have s4 := lift (.inl (by change t.pc + 3 < 179; rw [hpc]; decide)) h4
    have s5 := lift (show StartupPc 1901 by decide) h5
    have s6 := lift (show StartupPc 1902 by decide) h6
    have s7 := lift (show StartupPc 1903 by decide) h7
    have s8 := lift (show StartupPc 2768 by decide) h8
    simp only [run, s1, s2, s3, s4, s5, s6, s7, s8, Option.bind_some]
  · simp [t8, t7, t6, t5, t4, t3, t2, t1, next, setReg]
  · simp [t8, t7, t6, t5, next, setReg]
  · simp [t8, next, setReg]
  · intro r hr
    have hne (n : Nat) (hn : n ∈ [1072, 1706, 60, 1178, 263, 7228]) : r ≠ n := by
      rintro rfl; exact hr hn
    simp [t8, t7, t6, t5, t4, t3, t2, t1, next, setReg, hne 1072 (by decide),
      hne 1706 (by decide), hne 60 (by decide), hne 1178 (by decide), hne 263 (by decide),
      hne 7228 (by decide)]

theorem warp13Dispatch {p : Params} {l : Launch} {m : Mem0} (hpre : Pre p l m)
    (g : Nat) (t : TState) (hg : g < l.threads) (hpc : t.pc = 174) (hf : t.fault = none)
    (hw : t.regs 1062 = some (.bits 32 (BitVec.ofNat 64 13)))
    (hs : t.regs 2535 = some (.bits 32 (BitVec.ofNat 64 l.sharedBase))) :
    ∃ u, run kernel [] l g 8 t = some u ∧ u.pc = Flow.setMaxReg_2 ∧ u.fault = none ∧
      u.regs 1072 = some (.bits 32 (BitVec.ofNat 64 (g / l.block))) ∧
      u.regs 1178 = some (.bits 32 (BitVec.ofNat 64 (l.sharedBase + 68608))) ∧
      u.regs 7228 = some (.bits 32 (BitVec.ofNat 64 p.batch)) ∧
      ∀ r ∉ [1072, 1706, 60, 1178, 263, 7228], u.regs r = t.regs r := by
  obtain ⟨u, hr, hp, hFault, hCta, hBuffer, hBatch, _, _, hFrame⟩ :=
    warp13DispatchWith (A := []) hpre g t hg hpc hf hw hs
  exact ⟨u, hr, hp, hFault, hCta, hBuffer, hBatch, hFrame⟩

end
end PTX.Kernels.TmlFa4Fwd.Prologue
