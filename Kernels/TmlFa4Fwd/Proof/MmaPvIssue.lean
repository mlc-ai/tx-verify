-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQkIssue
public import Kernels.TmlFa4Fwd.Flow.Code.Part036
public import Kernels.TmlFa4Fwd.Flow.Code.Part038
public import Kernels.TmlFa4Fwd.Flow.Code.Part040
public import Kernels.TmlFa4Fwd.Flow.Code.Part041
public import Lemmas.Flow.TcMmaTs

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

structure PvSite where
  pc : Nat
  guard : Nat
  dst : Nat
  a : Nat
  b : Nat
  id : Nat
  enable : Nat
  stage : Fin 2

/-- The loop and tail PV assembly each issue on the two Q stages. -/
def pvSite : Fin 4 → PvSite
  | 0 => ⟨2319, 9671, 9674, 9675, 9679, 9673, 9672, 0⟩
  | 1 => ⟨2434, 9699, 9702, 9703, 9707, 9701, 9700, 1⟩
  | 2 => ⟨2570, 9727, 9730, 9731, 9735, 9729, 9728, 0⟩
  | 3 => ⟨2610, 9738, 9741, 9742, 9746, 9740, 9739, 1⟩

/-- The final two PV issues are separated from the initial six by the tail poll. -/
def pvPc (block : Fin 4) (step : Fin 8) : Nat :=
  (pvSite block).pc + 3 * step.val + if step.val < 6 then 0 else 3

def pvEnable (block : Fin 4) (step : Fin 8) : Opnd :=
  if step.val = 0 then .reg (pvSite block).enable else .imm 1

private def pvMma (block : Fin 4) (step : Fin 8) : TcMmaInstr :=
  let site := pvSite block
  .dense .one false .f16 site.dst (.tmem site.a (8 * (step.val : Int)))
    (.reg site.b) (.reg site.id) (List.replicate 4 (.imm 0)) (pvEnable block step)

private theorem pvCodeAudit : ∀ (block : Fin 4) (step : Fin 8),
    (kernel.code[pvPc block step]?).bind mmaFields =
      some (some ((pvSite block).guard, false), pvMma block step) := by
  decide +kernel

theorem pvCode (block : Fin 4) (step : Fin 8) :
    let site := pvSite block
    kernel.code[pvPc block step]? = some ⟨some (site.guard, false),
      .tcMma (.dense .one false .f16 site.dst (.tmem site.a (8 * (step.val : Int)))
        (.reg site.b) (.reg site.id) (List.replicate 4 (.imm 0)) (pvEnable block step))⟩ :=
  codeOfMmaFields (pvCodeAudit block step)

theorem pvRange (block : Fin 4) (step : Fin 8) :
    1904 ≤ pvPc block step ∧ pvPc block step < 2768 := by
  fin_cases block <;> fin_cases step <;> decide

def pvFragment (step : Fin 8) : Nat := 2048 * step.val

/-- Each PV fragment uses eight probability columns and a V slice from the selected ring slot. -/
def pvOperands (l : Launch) (g : Nat) (block : Fin 4) (step : Fin 8) (use : Nat) :
    TcMma.OperandSpec :=
  let b := sharedDescriptor (kvStart l use + pvFragment step) 16384
  ⟨pvDescriptor, b, b, g / l.block, g / l.block,
    some (probabilityColumn (pvSite block).stage + 8 * step.val), {}⟩

/-- Register checkpoint at a guarded PV issue. The first fragment uses the loop carry predicate. -/
def pvIssueFacts (l : Launch) (block : Fin 4) (step : Fin 8) (use : Nat)
    (accumulated : Bool) : List (Nat × Value) :=
  let site := pvSite block
  [(site.guard, .pred true), (site.dst, b32 (outputColumn site.stage)),
    (site.a, b32 (probabilityColumn site.stage)),
    (site.b, b64 (sharedDescriptorWord (kvStart l use + pvFragment step) 16384)),
    (site.id, b32 0x8210490), (site.enable, .pred accumulated)]

private theorem pvBAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (step : Fin 8) (use : Nat) :
    kvStart l use + pvFragment step < 2 ^ 18 ∧ (kvStart l use + pvFragment step) % 16 = 0 := by
  have hShared := hp.shared.2.1
  have hAlign := hp.shared.1
  have hSlot : kvSlot use < 3 := Nat.mod_lt _ (by decide)
  have hFrag := step.isLt
  unfold kvStart pvFragment
  exact ⟨by omega, by omega⟩

/-- The encoded A displacement selects this fragment within its probability block. -/
theorem pvAOffset (stage : Fin 2) (step : Fin 8) :
    tmemOffset (probabilityColumn stage) (8 * (step.val : Int)) =
      .ok (probabilityColumn stage + 8 * step.val) := by
  have hs := step.isLt
  have hStage := stage.isLt
  have h : probabilityColumn stage % 2 ^ 16 + 8 * step.val < 2 ^ 16 := by
    unfold probabilityColumn scoreColumn
    omega
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using tmemOffset_of h

/-- The elected-lane instruction resolves the physical PV input and output fragments. -/
theorem pvIssueOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) (block : Fin 4) (step : Fin 8) (use : Nat)
    (accumulated : Bool) {t : TState}
    (ht : At t (pvPc block step) (pvIssueFacts l block step use accumulated)) :
    out kernel Assumptions.all l g t =
      .ev (.tc (.mma (outputColumn (pvSite block).stage) (pvOperands l g block step use)
        (if step.val = 0 then accumulated else true) (List.replicate 4 0)) (next t)) := by
  let site := pvSite block
  let b := kvStart l use + pvFragment step
  let d := sharedDescriptor b 16384
  let base : TcMma.OperandSpec := ⟨pvDescriptor, d, d, g / l.block, g / l.block, none, {}⟩
  have hCode := pvCode block step
  rw [← ht.1] at hCode
  have hRange := pvRange block step
  have hGuard : guardHolds t (some (site.guard, false)) = .ok true := by
    have h : t.regs site.guard = some (.pred true) := ht.2.2.2.2.1
    simp [guardHolds, readReg, h, bind, Except.bind, pure, Except.pure]
  rw [out_eq_core (by rw [ht.1]; exact hRange.1) (by rw [ht.1]; exact hRange.2),
    out_event ht.2.2.2.1 hCode hGuard rfl]
  have hAddr := pvBAddress hp step use
  have hBound := sharedDescriptorWord_lt hAddr.1 hAddr.2 (Or.inr rfl)
  have hDec := sharedDescriptor_decode hAddr.1 hAddr.2 (Or.inr rfl)
  have hDst : outputColumn site.stage < 2 ^ 32 := by
    have := site.stage.isLt
    unfold outputColumn
    omega
  have hTmem : probabilityColumn site.stage < 2 ^ 32 := by
    have := site.stage.isLt
    unfold probabilityColumn scoreColumn
    omega
  have hMask : (List.replicate 4 (.imm 0)).mapM (readBits l g t 32) =
      .ok (List.replicate 4 (0 : BitVec 64)) := rfl
  have hEnableReg : t.regs site.enable = some (.pred accumulated) := ht.2.2.2.2.2.2.2.2.2.1
  have hEnable : mmaEnable t (pvEnable block step) =
      .ok (if step.val = 0 then accumulated else true) := by
    by_cases h : step.val = 0
    · simp [pvEnable, h, mmaEnable, readReg, site] at hEnableReg ⊢
      simp [hEnableReg, bind, Except.bind, pure, Except.pure]
    · simp [pvEnable, h, mmaEnable, pure, Except.pure]
  have hCta : TcMma.makeOperands l (g / l.block) pvDescriptor d d = some base := by
    simp [TcMma.makeOperands, pvDescriptor, base, singleCtaGroup hp hg]
  have hT := tc_mmaTs (L := l) (g := g) (group := .one) (kind := .f16) hg ht.2.2.2.2.2.1 hDst
    ht.2.2.2.2.2.2.1 hTmem (pvAOffset site.stage step) ht.2.2.2.2.2.2.2.1 hBound
    ht.2.2.2.2.2.2.2.2.1 (by decide) hMask (by decide) hEnable hDec pvDescriptor_decode rfl hCta
  exact congrArg Out.ev hT

/-- The normalized PV issue event, including the first fragment's accumulation flag. -/
def pvIssueEvent (l : Launch) (g : Nat) (block : Fin 4) (step : Fin 8) (use : Nat)
    (accumulated : Bool) : Event :=
  ⟨pvPc block step, .tc (.mma (outputColumn (pvSite block).stage) (pvOperands l g block step use)
    (if step.val = 0 then accumulated else true) (List.replicate 4 0))⟩

/-- The actual elected-lane issue consumes one trace event at the current PV fragment. -/
theorem pvIssueAt {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g pos : Nat} (hg : g < l.threads) (block : Fin 4) (step : Fin 8) (use : Nat)
    (accumulated : Bool) {t : TState}
    (ht : At t (pvPc block step) (pvIssueFacts l block step use accumulated))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    X.get (g, pos) = some (pvIssueEvent l g block step use accumulated) ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (pos + 1)) none := by
  let kind := TcKind.mma (outputColumn (pvSite block).stage) (pvOperands l g block step use)
    (if step.val = 0 then accumulated else true) (List.replicate 4 0)
  have hn : Next kernel Assumptions.all l g t t (.tc kind (next t)) :=
    ⟨.refl, pvIssueOut hp hg block step use accumulated ht⟩
  obtain ⟨e, u, he, hf, hu⟩ := hn.continuing_at (by
    rintro e ⟨_, hNone⟩
    cases hNone) hr
  obtain ⟨rfl, hu'⟩ := hf
  obtain rfl := Option.some.inj hu'
  exact ⟨by simpa only [pvIssueEvent, ht.1] using he, hu⟩

end PTX.Kernels.TmlFa4Fwd.Mma
