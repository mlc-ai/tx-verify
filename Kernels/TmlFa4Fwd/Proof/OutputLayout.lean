-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueBroadcast
public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Lemmas.Flow.Run
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases
public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX
noncomputable section

def pollPc : Fin 2 → Nat
  | 0 => 2958
  | 1 => 2972

theorem outEventShared {l : Launch} {g : Nat} {t : TState} {op : Op}
    (hf : t.fault = none) (hc : kernel.code[t.pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = false) :
    out kernel [] l g t = .ev (eventTmpl [] l g t op) :=
  PTX.Proof.out_event hf hc rfl hl

theorem tauLocalShared {l : Launch} {g : Nat} {t u : TState} {op : Op}
    (hf : t.fault = none) (hc : kernel.code[t.pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true) (he : execLocal l g t op = .ok u) :
    tauStep kernel [] l g t = some u := by
  have he' : execLocalA [] l g t op = .ok u := he
  simp only [tauStep, out, hf, hc, guardHolds, pure, Except.pure, hl, ↓reduceIte, he']

theorem branchTrueShared {l : Launch} {g : Nat} {t : TState} {r dst : Nat}
    (hf : t.fault = none)
    (hc : kernel.code[t.pc]? = some ⟨some (r, false), .bra dst false⟩)
    (hr : t.regs r = some (.pred true)) :
    tauStep kernel [] l g t = some { t with pc := dst } := by
  simp [tauStep, out, hf, hc, hr, guardHolds, readReg, Op.isLocal, execLocalA,
    execLocalRule, execLocal, Op.rule, execBranch, bind, Except.bind, pure, Except.pure]

/-- Once the scheduler has run out of tiles, warps 12 and 13 take both role-dependent branches
to the common return. -/
theorem finishSchedulerOfWarpWith {A : List Assumption} {warp : Nat}
    (l : Launch) (g : Nat) (t : TState)
    (hModel : ∀ {s : TState}, s.pc ∈ [3099, 3100, 7742, 7743, 7744, 9205] →
      out kernel A l g s = out kernel [] l g s)
    (hpc : t.pc = 3099) (hf : t.fault = none)
    (hWarp : warp = 12 ∨ warp = 13) (hw : t.regs 1062 = some (.bits 32 (BitVec.ofNat 64 warp))) :
    ∃ u, run kernel A l g 5 t = some u ∧ u.pc = Flow.exit_0 ∧
      out kernel A l g u = .ev .exit := by
  let t1 := next (setReg t 437 (.pred true))
  let t2 := { t1 with pc := 7742 }
  let t3 := next (setReg t2 5867 (.bits 32 12))
  let t4 := next (setReg t3 681 (.pred true))
  let t5 := { t4 with pc := 9205 }
  have h1 : tauStep kernel [] l g t = some t1 := by
    apply tauLocalShared hf (by rw [hpc]; exact Flow.code_3099) rfl
    rw [execLocal_int rfl]
    rcases hWarp with rfl | rfl <;> simp only [execInt, DType.width, readBits, readReg, hw, bind,
      Except.bind, pure, Except.pure] <;> rfl
  have h2 : tauStep kernel [] l g t1 = some t2 := by
    have hp : t1.pc = 3100 := by change t.pc + 1 = 3100; rw [hpc]
    exact branchTrueShared (t := t1) hf (by rw [hp]; exact Flow.code_3100)
      (by simp [t1, next, setReg])
  have h3 : tauStep kernel [] l g t2 = some t3 := by
    have hw2 : t2.regs 1062 = some (.bits 32 (BitVec.ofNat 64 warp)) := by
      simpa [t2, t1, next, setReg] using hw
    apply tauLocalShared (t := t2) hf Flow.code_7742 rfl
    rw [execLocal_int rfl]
    rcases hWarp with rfl | rfl <;> simp only [execInt, DType.width, readBits, readReg, hw2,
      bind, Except.bind, pure, Except.pure] <;> rfl
  have h4 : tauStep kernel [] l g t3 = some t4 := by
    have hw3 : t3.regs 5867 = some (.bits 32 12) := by simp [t3, next, setReg]
    apply tauLocalShared (t := t3) hf Flow.code_7743 rfl
    rw [execLocal_int rfl]
    simp only [execInt, DType.width, readBits, readReg, hw3, bind, Except.bind, pure, Except.pure]
    rfl
  have h5 : tauStep kernel [] l g t4 = some t5 :=
    branchTrueShared (t := t4) hf Flow.code_7744 (by simp [t4, next, setReg])
  have lift {s v : TState} (hs : s.pc ∈ [3099, 3100, 7742, 7743, 7744, 9205])
      (hr : tauStep kernel [] l g s = some v) : tauStep kernel A l g s = some v := by
    simpa only [tauStep, hModel hs] using hr
  have s1 := lift (by rw [hpc]; decide) h1
  have s2 := lift (by change t.pc + 1 ∈ _; rw [hpc]; decide) h2
  have s3 := lift (show 7742 ∈ [3099, 3100, 7742, 7743, 7744, 9205] by decide) h3
  have s4 := lift (show 7743 ∈ [3099, 3100, 7742, 7743, 7744, 9205] by decide) h4
  have s5 := lift (show 7744 ∈ [3099, 3100, 7742, 7743, 7744, 9205] by decide) h5
  refine ⟨t5, by simp only [run, s1, s2, s3, s4, s5, Option.bind_some], rfl, ?_⟩
  rw [hModel (show 9205 ∈ [3099, 3100, 7742, 7743, 7744, 9205] by decide)]
  exact outEventShared (t := t5) hf Flow.code_9205 rfl

section
variable {p : Params} {l : Launch} {m : Mem0}

/-- Each output tile stage is issued as four 32-column subboxes. -/
def storePc (stage : Fin 2) (subbox : Fin 4) : Nat :=
  if stage = 0 then 2963 + 2 * subbox.val else 2976 + subbox.val

def sharedSlot (l : Launch) (g : Nat) (stage : Fin 2) (subbox : Fin 4) : Loc :=
  ⟨.shared, g / l.block, l.sharedBase + (3072 + 65536 * stage.val + 16384 * subbox.val)⟩

def readyLoc (l : Launch) (g : Nat) (stage : Fin 2) : Loc :=
  ⟨.shared, g / l.block, l.sharedBase + (208 + 8 * stage.val)⟩

def stageRow (tile : Nat) (stage : Fin 2) : Nat := 256 * tile + 128 * stage.val

end

def freePc : Fin 2 → Nat
  | 0 => 2983
  | 1 => 2985

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
