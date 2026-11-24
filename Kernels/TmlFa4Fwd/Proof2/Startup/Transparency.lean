-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Flow.Code.Part000
public import Kernels.TmlFa4Fwd.Flow.Code.Part001
public import Kernels.TmlFa4Fwd.Flow.Code.Part002
public import Kernels.TmlFa4Fwd.Flow.Code.Part029
public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX

noncomputable section

/-- Shared startup, the warp-13 dispatch branch, and its initial scheduler read and shuffle. -/
def StartupPc (pc : Nat) : Prop :=
  pc < 179 ∨ (1901 ≤ pc ∧ pc ≤ 1903) ∨ (2768 ≤ pc ∧ pc ≤ 2779)

instance (pc : Nat) : Decidable (StartupPc pc) := by
  unfold StartupPc
  infer_instance

private def CoreAt (pc : Nat) : Prop :=
  ∃ ins, kernel.code[pc]? = some ins ∧ Assumptions.coreOp ins.op = true

private theorem coreFrom0 (i : Fin 64) : CoreAt (0 + i.val) := by
  fin_cases i
  · exact ⟨_, Flow.code_0, rfl⟩
  · exact ⟨_, Flow.code_1, rfl⟩
  · exact ⟨_, Flow.code_2, rfl⟩
  · exact ⟨_, Flow.code_3, rfl⟩
  · exact ⟨_, Flow.code_4, rfl⟩
  · exact ⟨_, Flow.code_5, rfl⟩
  · exact ⟨_, Flow.code_6, rfl⟩
  · exact ⟨_, Flow.code_7, rfl⟩
  · exact ⟨_, Flow.code_8, rfl⟩
  · exact ⟨_, Flow.code_9, rfl⟩
  · exact ⟨_, Flow.code_10, rfl⟩
  · exact ⟨_, Flow.code_11, rfl⟩
  · exact ⟨_, Flow.code_12, rfl⟩
  · exact ⟨_, Flow.code_13, rfl⟩
  · exact ⟨_, Flow.code_14, rfl⟩
  · exact ⟨_, Flow.code_15, rfl⟩
  · exact ⟨_, Flow.code_16, rfl⟩
  · exact ⟨_, Flow.code_17, rfl⟩
  · exact ⟨_, Flow.code_18, rfl⟩
  · exact ⟨_, Flow.code_19, rfl⟩
  · exact ⟨_, Flow.code_20, rfl⟩
  · exact ⟨_, Flow.code_21, rfl⟩
  · exact ⟨_, Flow.code_22, rfl⟩
  · exact ⟨_, Flow.code_23, rfl⟩
  · exact ⟨_, Flow.code_24, rfl⟩
  · exact ⟨_, Flow.code_25, rfl⟩
  · exact ⟨_, Flow.code_26, rfl⟩
  · exact ⟨_, Flow.code_27, rfl⟩
  · exact ⟨_, Flow.code_28, rfl⟩
  · exact ⟨_, Flow.code_29, rfl⟩
  · exact ⟨_, Flow.code_30, rfl⟩
  · exact ⟨_, Flow.code_31, rfl⟩
  · exact ⟨_, Flow.code_32, rfl⟩
  · exact ⟨_, Flow.code_33, rfl⟩
  · exact ⟨_, Flow.code_34, rfl⟩
  · exact ⟨_, Flow.code_35, rfl⟩
  · exact ⟨_, Flow.code_36, rfl⟩
  · exact ⟨_, Flow.code_37, rfl⟩
  · exact ⟨_, Flow.code_38, rfl⟩
  · exact ⟨_, Flow.code_39, rfl⟩
  · exact ⟨_, Flow.code_40, rfl⟩
  · exact ⟨_, Flow.code_41, rfl⟩
  · exact ⟨_, Flow.code_42, rfl⟩
  · exact ⟨_, Flow.code_43, rfl⟩
  · exact ⟨_, Flow.code_44, rfl⟩
  · exact ⟨_, Flow.code_45, rfl⟩
  · exact ⟨_, Flow.code_46, rfl⟩
  · exact ⟨_, Flow.code_47, rfl⟩
  · exact ⟨_, Flow.code_48, rfl⟩
  · exact ⟨_, Flow.code_49, rfl⟩
  · exact ⟨_, Flow.code_50, rfl⟩
  · exact ⟨_, Flow.code_51, rfl⟩
  · exact ⟨_, Flow.code_52, rfl⟩
  · exact ⟨_, Flow.code_53, rfl⟩
  · exact ⟨_, Flow.code_54, rfl⟩
  · exact ⟨_, Flow.code_55, rfl⟩
  · exact ⟨_, Flow.code_56, rfl⟩
  · exact ⟨_, Flow.code_57, rfl⟩
  · exact ⟨_, Flow.code_58, rfl⟩
  · exact ⟨_, Flow.code_59, rfl⟩
  · exact ⟨_, Flow.code_60, rfl⟩
  · exact ⟨_, Flow.code_61, rfl⟩
  · exact ⟨_, Flow.code_62, rfl⟩
  · exact ⟨_, Flow.code_63, rfl⟩

private theorem coreFrom64 (i : Fin 64) : CoreAt (64 + i.val) := by
  fin_cases i
  · exact ⟨_, Flow.code_64, rfl⟩
  · exact ⟨_, Flow.code_65, rfl⟩
  · exact ⟨_, Flow.code_66, rfl⟩
  · exact ⟨_, Flow.code_67, rfl⟩
  · exact ⟨_, Flow.code_68, rfl⟩
  · exact ⟨_, Flow.code_69, rfl⟩
  · exact ⟨_, Flow.code_70, rfl⟩
  · exact ⟨_, Flow.code_71, rfl⟩
  · exact ⟨_, Flow.code_72, rfl⟩
  · exact ⟨_, Flow.code_73, rfl⟩
  · exact ⟨_, Flow.code_74, rfl⟩
  · exact ⟨_, Flow.code_75, rfl⟩
  · exact ⟨_, Flow.code_76, rfl⟩
  · exact ⟨_, Flow.code_77, rfl⟩
  · exact ⟨_, Flow.code_78, rfl⟩
  · exact ⟨_, Flow.code_79, rfl⟩
  · exact ⟨_, Flow.code_80, rfl⟩
  · exact ⟨_, Flow.code_81, rfl⟩
  · exact ⟨_, Flow.code_82, rfl⟩
  · exact ⟨_, Flow.code_83, rfl⟩
  · exact ⟨_, Flow.code_84, rfl⟩
  · exact ⟨_, Flow.code_85, rfl⟩
  · exact ⟨_, Flow.code_86, rfl⟩
  · exact ⟨_, Flow.code_87, rfl⟩
  · exact ⟨_, Flow.code_88, rfl⟩
  · exact ⟨_, Flow.code_89, rfl⟩
  · exact ⟨_, Flow.code_90, rfl⟩
  · exact ⟨_, Flow.code_91, rfl⟩
  · exact ⟨_, Flow.code_92, rfl⟩
  · exact ⟨_, Flow.code_93, rfl⟩
  · exact ⟨_, Flow.code_94, rfl⟩
  · exact ⟨_, Flow.code_95, rfl⟩
  · exact ⟨_, Flow.code_96, rfl⟩
  · exact ⟨_, Flow.code_97, rfl⟩
  · exact ⟨_, Flow.code_98, rfl⟩
  · exact ⟨_, Flow.code_99, rfl⟩
  · exact ⟨_, Flow.code_100, rfl⟩
  · exact ⟨_, Flow.code_101, rfl⟩
  · exact ⟨_, Flow.code_102, rfl⟩
  · exact ⟨_, Flow.code_103, rfl⟩
  · exact ⟨_, Flow.code_104, rfl⟩
  · exact ⟨_, Flow.code_105, rfl⟩
  · exact ⟨_, Flow.code_106, rfl⟩
  · exact ⟨_, Flow.code_107, rfl⟩
  · exact ⟨_, Flow.code_108, rfl⟩
  · exact ⟨_, Flow.code_109, rfl⟩
  · exact ⟨_, Flow.code_110, rfl⟩
  · exact ⟨_, Flow.code_111, rfl⟩
  · exact ⟨_, Flow.code_112, rfl⟩
  · exact ⟨_, Flow.code_113, rfl⟩
  · exact ⟨_, Flow.code_114, rfl⟩
  · exact ⟨_, Flow.code_115, rfl⟩
  · exact ⟨_, Flow.code_116, rfl⟩
  · exact ⟨_, Flow.code_117, rfl⟩
  · exact ⟨_, Flow.code_118, rfl⟩
  · exact ⟨_, Flow.code_119, rfl⟩
  · exact ⟨_, Flow.code_120, rfl⟩
  · exact ⟨_, Flow.code_121, rfl⟩
  · exact ⟨_, Flow.code_122, rfl⟩
  · exact ⟨_, Flow.code_123, rfl⟩
  · exact ⟨_, Flow.code_124, rfl⟩
  · exact ⟨_, Flow.code_125, rfl⟩
  · exact ⟨_, Flow.code_126, rfl⟩
  · exact ⟨_, Flow.code_127, rfl⟩

private theorem coreFrom128 (i : Fin 51) : CoreAt (128 + i.val) := by
  fin_cases i
  · exact ⟨_, Flow.code_128, rfl⟩
  · exact ⟨_, Flow.code_129, rfl⟩
  · exact ⟨_, Flow.code_130, rfl⟩
  · exact ⟨_, Flow.code_131, rfl⟩
  · exact ⟨_, Flow.code_132, rfl⟩
  · exact ⟨_, Flow.code_133, rfl⟩
  · exact ⟨_, Flow.code_134, rfl⟩
  · exact ⟨_, Flow.code_135, rfl⟩
  · exact ⟨_, Flow.code_136, rfl⟩
  · exact ⟨_, Flow.code_137, rfl⟩
  · exact ⟨_, Flow.code_138, rfl⟩
  · exact ⟨_, Flow.code_139, rfl⟩
  · exact ⟨_, Flow.code_140, rfl⟩
  · exact ⟨_, Flow.code_141, rfl⟩
  · exact ⟨_, Flow.code_142, rfl⟩
  · exact ⟨_, Flow.code_143, rfl⟩
  · exact ⟨_, Flow.code_144, rfl⟩
  · exact ⟨_, Flow.code_145, rfl⟩
  · exact ⟨_, Flow.code_146, rfl⟩
  · exact ⟨_, Flow.code_147, rfl⟩
  · exact ⟨_, Flow.code_148, rfl⟩
  · exact ⟨_, Flow.code_149, rfl⟩
  · exact ⟨_, Flow.code_150, rfl⟩
  · exact ⟨_, Flow.code_151, rfl⟩
  · exact ⟨_, Flow.code_152, rfl⟩
  · exact ⟨_, Flow.code_153, rfl⟩
  · exact ⟨_, Flow.code_154, rfl⟩
  · exact ⟨_, Flow.code_155, rfl⟩
  · exact ⟨_, Flow.code_156, rfl⟩
  · exact ⟨_, Flow.code_157, rfl⟩
  · exact ⟨_, Flow.code_158, rfl⟩
  · exact ⟨_, Flow.code_159, rfl⟩
  · exact ⟨_, Flow.code_160, rfl⟩
  · exact ⟨_, Flow.code_161, rfl⟩
  · exact ⟨_, Flow.code_162, rfl⟩
  · exact ⟨_, Flow.code_163, rfl⟩
  · exact ⟨_, Flow.code_164, rfl⟩
  · exact ⟨_, Flow.code_165, rfl⟩
  · exact ⟨_, Flow.code_166, rfl⟩
  · exact ⟨_, Flow.code_167, rfl⟩
  · exact ⟨_, Flow.code_168, rfl⟩
  · exact ⟨_, Flow.code_169, rfl⟩
  · exact ⟨_, Flow.code_170, rfl⟩
  · exact ⟨_, Flow.code_171, rfl⟩
  · exact ⟨_, Flow.code_172, rfl⟩
  · exact ⟨_, Flow.code_173, rfl⟩
  · exact ⟨_, Flow.code_174, rfl⟩
  · exact ⟨_, Flow.code_175, rfl⟩
  · exact ⟨_, Flow.code_176, rfl⟩
  · exact ⟨_, Flow.code_177, rfl⟩
  · exact ⟨_, Flow.code_178, rfl⟩

private theorem coreFrom1901 (i : Fin 3) : CoreAt (1901 + i.val) := by
  fin_cases i
  · exact ⟨_, Flow.code_1901, rfl⟩
  · exact ⟨_, Flow.code_1902, rfl⟩
  · exact ⟨_, Flow.code_1903, rfl⟩

private theorem coreFrom2768 (i : Fin 12) : CoreAt (2768 + i.val) := by
  fin_cases i
  · exact ⟨_, Flow.code_2768, rfl⟩
  · exact ⟨_, Flow.code_2769, rfl⟩
  · exact ⟨_, Flow.code_2770, rfl⟩
  · exact ⟨_, Flow.code_2771, rfl⟩
  · exact ⟨_, Flow.code_2772, rfl⟩
  · exact ⟨_, Flow.code_2773, rfl⟩
  · exact ⟨_, Flow.code_2774, rfl⟩
  · exact ⟨_, Flow.code_2775, rfl⟩
  · exact ⟨_, Flow.code_2776, rfl⟩
  · exact ⟨_, Flow.code_2777, rfl⟩
  · exact ⟨_, Flow.code_2778, rfl⟩
  · exact ⟨_, Flow.code_2779, rfl⟩

private theorem coreAtStartup {pc : Nat} (h : StartupPc pc) : CoreAt pc := by
  rcases h with hp | hp | hp
  · by_cases h₀ : pc < 64
    · simpa only [Nat.zero_add] using coreFrom0 ⟨pc, h₀⟩
    · by_cases h₁ : pc < 128
      · have hₓ : 64 + (pc - 64) = pc := by omega
        have := coreFrom64 ⟨pc - 64, by omega⟩
        simpa only [hₓ] using this
      · have hₓ : 128 + (pc - 128) = pc := by omega
        have := coreFrom128 ⟨pc - 128, by omega⟩
        simpa only [hₓ] using this
  · have hₓ : 1901 + (pc - 1901) = pc := by omega
    have := coreFrom1901 ⟨pc - 1901, by omega⟩
    simpa only [hₓ] using this
  · have hₓ : 2768 + (pc - 2768) = pc := by omega
    have := coreFrom2768 ⟨pc - 2768, by omega⟩
    simpa only [hₓ] using this

private theorem startupOffSegments {pc : Nat} (hpc : StartupPc pc) :
    pc ∉ Assumptions.swExp2Sites := by
  intro h
  simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at h
  unfold StartupPc at hpc
  omega

/-- Assumptions that agree with Core on the certified startup instructions. -/
class StartupAgreement (A : List Assumption) : Prop where
  out_eq {l : Launch} {g : Nat} {t : TState} (hpc : StartupPc t.pc) :
    out kernel A l g t = out kernel [] l g t

instance : StartupAgreement [] where
  out_eq _ := rfl

instance : StartupAgreement Assumptions.all where
  out_eq := by
    intro l g t hpc
    obtain ⟨_, hc, hop⟩ := coreAtStartup hpc
    have hload : t.pc ∉ Assumptions.tcLdDataflowSites := by
      intro h
      simp only [Assumptions.tcLdDataflowSites, List.mem_cons, List.not_mem_nil, or_false] at h
      unfold StartupPc at hpc
      omega
    have hstore : t.pc ∉ Assumptions.delayedTmemSites := by
      intro h
      simp only [Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false] at h
      unfold StartupPc at hpc
      omega
    exact Assumptions.out_all_eq_nil (startupOffSegments hpc) hload hstore hc hop

theorem startupOut {A : List Assumption} [StartupAgreement A] {l : Launch} {g : Nat}
    {t : TState} (hpc : StartupPc t.pc) {o : Out} (h : out kernel [] l g t = o) :
    out kernel A l g t = o :=
  (StartupAgreement.out_eq hpc).trans h

theorem startupTau {A : List Assumption} [StartupAgreement A] {l : Launch} {g : Nat}
    {t u : TState} (hpc : StartupPc t.pc) (h : tauStep kernel [] l g t = some u) :
    tauStep kernel A l g t = some u := by
  simpa only [tauStep, StartupAgreement.out_eq (A := A) hpc] using h

theorem startupOne {A : List Assumption} [StartupAgreement A] {l : Launch} {g : Nat}
    {t u : TState} (hpc : StartupPc t.pc) (h : run kernel [] l g 1 t = some u) :
    run kernel A l g 1 t = some u := by
  simpa only [run, tauStep, StartupAgreement.out_eq (A := A) hpc] using h

end
end PTX.Kernels.TmlFa4Fwd.Prologue
