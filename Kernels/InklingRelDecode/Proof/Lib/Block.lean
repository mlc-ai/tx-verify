-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.ResPcs
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotTcData
public import Lemmas.Flow.NotRegister
public import Lemmas.Flow.NotAsyncWait
public import Lemmas.Kernel.Frame
public import Lemmas.Kernel.Progress.Warp
public import Lemmas.Kernel.Progress.Released

@[expose] public section

/-! # The events that can block, and the ones that precede a warp collective

`blockPcs`: every instruction whose event the progress layer may find unreleased (barrier, register
request, paired Tensor Memory operation, collective `tcgen05` data event). `pairs`: the ones that
directly precede a warp collective (pc 14, 15 before the startup shuffle, the prologue's
barriers, the Softmax's `wait::ld` and barrier, the MMA warp's first barrier). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

def blockOp (op : Op) : Bool :=
  barOp op || setMaxRegOp op || tmemOp op || tcDataOp op || bulkWaitOp op || clusterOp op ||
    asyncWaitOp op

def blockPcs : List Nat := [11, 12, 14, 15, 27, 180, 192, 201, 212, 222, 227, 236, 243, 254, 264,
  269, 278, 285, 296, 306, 311, 573, 574, 575, 999, 1009, 1010, 1012, 1265, 1298, 2241, 2251, 2260,
  2261, 2326, 2328, 2329, 2333, 2334, 2335, 2336, 2337, 2338, 2344, 2346, 2419, 2420, 2422, 2424,
  2554, 2555, 2557, 2558, 2607, 2608, 2846, 2847, 2849, 2850, 2851, 2853, 2854]

/-- The blocking events that directly precede a warp collective, with the collective's pc. -/
def pairs : List (Nat × Nat) := [(14, 17), (15, 17), (201, 202), (212, 213), (222, 223), (227, 228),
  (243, 244), (254, 255), (264, 265), (269, 270), (285, 286), (296, 297), (306, 307), (311, 312),
  (1298, 1838), (2241, 2242), (2424, 2461), (2424, 2509), (2424, 2550)]

theorem kernel_block_pcs : OpPcsFast kernel.code blockOp blockPcs = true := by decide +kernel

/-- **A fault-free event that may block is at one of the blocking positions.** -/
theorem blocked_pc {L m X i e} (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get i = some e) (hu : ∀ f, e.kind ≠ .ub f) (hb : ¬ Sched.Unblocking e.kind) :
    e.pc ∈ blockPcs := by
  obtain ⟨_, bad⟩ | ⟨t, ins, o, hpc, code, fire⟩ := get_source hX he
  · exact absurd bad (hu _)
  refine OpPcsFast.mem kernel_block_pcs code ?_
  obtain ⟨pc, kd⟩ := e
  cases kd <;> simp only [Sched.Unblocking, not_true_eq_false] at hb
  case cluster cop => rw [fires_cluster_op fire rfl]; rfl
  case setMaxReg inc n inst => rw [fires_setMaxReg_op fire rfl]; rfl
  case bar id c md => simp [blockOp, fires_bar_op fire rfl]
  case bulkWait md r => simp [blockOp, fires_bulkWait_op fire rfl]
  case asyncWait n => simp [blockOp, fires_asyncWait_op fire rfl]
  case tc tk =>
    cases tk
    case resource grp dst act => simp [blockOp, fires_resource_op fire rfl]
    case ld a vals sh => simp [blockOp, fires_tcData_op fire (by simp [isTcData])]
    case waitLd => simp [blockOp, fires_tcData_op fire (by simp [isTcData])]
    case st a vals sh => simp [blockOp, fires_tcData_op fire (by simp [isTcData])]
    case waitSt => simp [blockOp, fires_tcData_op fire (by simp [isTcData])]
    all_goals exact absurd (by simp [isTcColl]) hb

/-- No blocking instruction is a warp instruction. -/
theorem blockPcs_not_warp : ∀ pc ∈ blockPcs,
    (kernel.code[pc]?.any fun ins => Descent.opKind ins.op == Descent.NextKind.warp) = false := by
  decide +kernel

/-- The instructions that directly precede a warp collective are barriers, paired Tensor Memory
operations and collective `tcgen05` data instructions. -/
def pairOp (op : Op) : Bool := barOp op || tmemOp op || tcDataOp op

theorem pairs_op : ∀ pc ∈ pairs.map Prod.fst, (kernel.code[pc]?.any fun ins => pairOp ins.op) =
    true := by
  decide +kernel

/-- **A blocking event before a warp collective is a barrier, a paired Tensor Memory operation or
a `tcgen05` data event.** -/
theorem pairs_kind {L m X i e c} (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get i = some e) (hu : ∀ f, e.kind ≠ .ub f) (hb : ¬ Sched.Unblocking e.kind)
    (hp : (e.pc, c) ∈ pairs) :
    (∃ id cnt md, e.kind = .bar id cnt md) ∨
      (∃ grp dst act, e.kind = .tc (.resource grp dst act)) ∨ isTcData e = true := by
  obtain ⟨_, bad⟩ | ⟨t, ins, o, hpc, code, fire⟩ := get_source hX he
  · exact absurd bad (hu _)
  have hop := pairs_op e.pc (List.mem_map.mpr ⟨_, hp, rfl⟩)
  rw [code] at hop
  simp only [Option.any_some] at hop
  obtain ⟨pc, kd⟩ := e
  cases kd <;> simp only [Sched.Unblocking, not_true_eq_false] at hb
  case cluster cop => rw [fires_cluster_op fire rfl] at hop; cases hop
  case setMaxReg inc n inst => rw [fires_setMaxReg_op fire rfl] at hop; cases hop
  case bar id c md => exact .inl ⟨_, _, _, rfl⟩
  case bulkWait md r =>
    have := fires_bulkWait_op fire rfl
    cases hq : ins.op <;> simp_all [pairOp, barOp, tmemOp, tcDataOp, bulkWaitOp]
  case asyncWait n =>
    have := fires_asyncWait_op fire rfl
    cases hq : ins.op <;> simp_all [pairOp, barOp, tmemOp, tcDataOp, asyncWaitOp]
  case tc tk =>
    cases tk
    case resource grp dst act => exact .inr (.inl ⟨_, _, _, rfl⟩)
    case ld a vals sh => exact .inr (.inr (by simp [isTcData]))
    case waitLd => exact .inr (.inr (by simp [isTcData]))
    case st a vals sh => exact .inr (.inr (by simp [isTcData]))
    case waitSt => exact .inr (.inr (by simp [isTcData]))
    all_goals exact absurd (by simp [isTcColl]) hb

/-- A lane's machine is at a state with the property `P` before its `j`-th event. -/
def StateAt {K : Kernel} {A : List Assumption} {L : Launch}
    (C : (g : Nat) → Flow.Code K A L g) (X : Execution) (g j : Nat) (P : (C g).D → Prop) : Prop :=
  ∃ σ, Frame.stateAt C X g j = some (some σ) ∧ P σ

/-- A lane's machine has stopped by its `j`-th event. -/
def StateGone {K : Kernel} {A : List Assumption} {L : Launch}
    (C : (g : Nat) → Flow.Code K A L g) (X : Execution) (g j : Nat) : Prop :=
  Frame.stateAt C X g j = none

/-- What follows the blocking event `e` of lane `g` at its `k`-th place: the machine was not at a
collective, has not stopped, and is at a collective only after the events of `pairs`. -/
def BlockFacts {K : Kernel} {A : List Assumption} {L : Launch}
    (C : (g : Nat) → Flow.Code K A L g) (AtColl : ∀ g, (C g).D → Prop) (X : Execution)
    (g k : Nat) (e : Event) : Prop :=
  StateAt C X g k (fun σ0 => ¬ AtColl g σ0) ∧ ¬ StateGone C X g (k + 1) ∧
    ∀ c, StateAt C X g (k + 1) (fun σ' => AtColl g σ' ∧ (C g).pc σ' = c) → (e.pc, c) ∈ pairs

/-- The facts of a blocking event from the states before and after it. -/
theorem BlockFacts.of_step {K : Kernel} {A : List Assumption} {L : Launch}
    {C : (g : Nat) → Flow.Code K A L g} {AtColl : ∀ g, (C g).D → Prop} {X : Execution}
    {g k : Nat} {e : Event} {σ0 σ' : (C g).D} (h0 : Frame.stateAt C X g k = some (some σ0))
    (hn : ¬ AtColl g σ0) (h1 : Frame.stateAt C X g (k + 1) = some (some σ'))
    (hp : AtColl g σ' → (e.pc, (C g).pc σ') ∈ pairs) : BlockFacts C AtColl X g k e := by
  refine ⟨⟨_, h0, hn⟩, fun h => ?_, fun c ⟨_, h2, hcc, e'⟩ => ?_⟩
  · unfold StateGone at h; rw [h1] at h; cases h
  · rw [h1] at h2; cases h2
    exact e' ▸ hp hcc

end PTX.Kernels.InklingRelDecode.Proof.Lib
