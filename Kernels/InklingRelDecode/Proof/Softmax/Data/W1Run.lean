-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.RunAdv
public import Kernels.InklingRelDecode.Gen.SoftmaxW1A
public import Kernels.InklingRelDecode.Gen.SoftmaxW1B
public import Kernels.InklingRelDecode.Gen.SoftmaxW1C
public import Kernels.InklingRelDecode.Gen.SoftmaxW1D
import Kernels.InklingRelDecode.Proof.Softmax.GenRules

@[expose] public section

/-! # The runs of the first window as steps of a register file

Each generated run of pcs 1299 to 1837 (`Gen/SoftmaxW1*`) as a `RunData`: its start and length,
its facts at the start and at the end as templates over the start values, and its condition. A
`RunData` that checks (`Ok`: the facts are the live registers' values, the code is local, no
assumption takes a segment there) moves a state that knows registers `K` under `V` to one that
knows the registers it kept and the run's facts under `valueEx V (fs1 V)` (`RunData.adv`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code

noncomputable section

/-- A generated run: a template over the values at its start. -/
structure RunData where
  s : Nat
  n : Nat
  fs0 : (Nat → Value) → List (Nat × Value)
  fs1 : (Nat → Value) → List (Nat × Value)
  C : (Nat → Value) → Prop
  run : ∀ (L : Launch) (g : Nat) (V : Nat → Value),
    SegD kernel Assumptions.all L g n s (fs0 V) (s + n) (fs1 V) (C V)

namespace RunData

/-- The registers the run reads. -/
def live (r : RunData) : List Nat := (r.fs0 fun _ => b32 0).map Prod.fst
/-- The registers the run states at its end. -/
def outs (r : RunData) : List Nat := (r.fs1 fun _ => b32 0).map Prod.fst
/-- The instructions of the run. -/
def ins (r : RunData) : List Instr := (kernel.code.drop r.s).take r.n
/-- The registers known after the run, from those known before. -/
def K' (r : RunData) (K : List Nat) : List Nat := keep r.ins K ++ r.outs
/-- The register file after the run. -/
def V' (r : RunData) (V : Nat → Value) : Nat → Value := valueEx V (r.fs1 V)

/-- The run's checks: its facts, its code, and the segments no assumption takes. -/
structure Ok (r : RunData) : Prop where
  h0 : ∀ V, r.fs0 V = factsFrom r.live V
  h1 : ∀ V, (r.fs1 V).map Prod.fst = r.outs
  loc : r.ins.all (fun i => i.op.isLocal && noJump i.op) = true
  len : r.ins.length = r.n
  free : ∀ i < r.n, Assumption.SegFreePc Assumptions.all (r.s + i)

variable {L : Launch} {g : Nat}

/-- **A run as a step of a register file.** -/
theorem adv (r : RunData) (ok : r.Ok) {K : List Nat} (V : Nat → Value)
    (hl : r.live.all (fun x => K.contains x) = true) :
    SegU kernel Assumptions.all L g r.s (factsFrom K V) (r.s + r.n)
      (factsFrom (r.K' K) (r.V' V)) := by
  have seg := r.run L g V
  rw [ok.h0 V] at seg
  have h := segU_adv (K := K) seg rfl ok.len ok.free hl ok.loc
  rwa [ok.h1 V] at h

end RunData

def runP : RunData := ⟨1299, 3, Gen.w1p_facts0, Gen.w1p_facts1, Gen.w1p_cond, Gen.w1p_run⟩
def runA : RunData := ⟨1303, 163, Gen.w1a_facts0, Gen.w1a_facts6, Gen.w1a_cond, Gen.w1a_run⟩
def runB : RunData := ⟨1467, 133, Gen.w1b_facts0, Gen.w1b_facts5, Gen.w1b_cond, Gen.w1b_run⟩
def runC : RunData := ⟨1600, 156, Gen.w1c_facts0, Gen.w1c_facts5, Gen.w1c_cond, Gen.w1c_run⟩
def runT : RunData := ⟨1756, 8, Gen.w1t_facts0, Gen.w1t_facts1, Gen.w1t_cond, Gen.w1t_run⟩
def runM : RunData := ⟨1764, 74, Gen.w1m_facts0, Gen.w1m_facts3, Gen.w1m_cond, Gen.w1m_run⟩

private theorem free_of (s n : Nat) (h0 : 1000 ≤ s) (h : s + n ≤ 1913) :
    ∀ i < n, Assumption.SegFreePc Assumptions.all (s + i) := fun i hi =>
  smSegFree (by simp only [intPc, decide_eq_true_eq]; omega)

theorem runP_ok : runP.Ok := ⟨fun _ => rfl, fun _ => rfl, by decide +kernel, by decide +kernel,
  free_of _ _ (by decide) (by decide)⟩
theorem runA_ok : runA.Ok := ⟨fun _ => rfl, fun _ => rfl, by decide +kernel, by decide +kernel,
  free_of _ _ (by decide) (by decide)⟩
theorem runB_ok : runB.Ok := ⟨fun _ => rfl, fun _ => rfl, by decide +kernel, by decide +kernel,
  free_of _ _ (by decide) (by decide)⟩
theorem runC_ok : runC.Ok := ⟨fun _ => rfl, fun _ => rfl, by decide +kernel, by decide +kernel,
  free_of _ _ (by decide) (by decide)⟩
theorem runT_ok : runT.Ok := ⟨fun _ => rfl, fun _ => rfl, by decide +kernel, by decide +kernel,
  free_of _ _ (by decide) (by decide)⟩
theorem runM_ok : runM.Ok := ⟨fun _ => rfl, fun _ => rfl, by decide +kernel, by decide +kernel,
  free_of _ _ (by decide) (by decide)⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
