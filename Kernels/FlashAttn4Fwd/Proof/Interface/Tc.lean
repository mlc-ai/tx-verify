-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface
public import Kernels.FlashAttn4Fwd.Proof.Interface.Cluster
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tmem
public import Kernels.FlashAttn4Fwd.Proof.Interface.Score
public import Kernels.FlashAttn4Fwd.Proof.Interface.Stats
public import Lemmas.Flow.RegBits

@[expose] public section

/-! # What the thread layer exports for the commits, the MMA issues and the stops

* **Commits.** Every `tcgen05.commit` is the leader CTA's MMA warp's (warp 12), to a table
  barrier of its own CTA other than the handshake barrier, `cta_group::2` with mask `3` over the
  pair from its CTA (`Mma.cSpec`, `Mma.cBar`: S-full, KV-empty, Q-empty, O-full).
* **Initializations.** A thread of warp 0 that reaches its cluster arrival initialized every
  barrier of its CTA but the handshake barrier before it, unless a full-mask election before it
  returned another lane (the prologue's elected lane initializes the 36 table barriers).
* **MMA issues.** Every MMA's lane masks are zero, so each of its result cells is written
  (`mma_reads`, and it writes one: `mma_cell`); a QK MMA reads its A operand from shared memory
  (`qk_smem`); its shape, masks, CTA group, shared descriptors and addresses are those the
  MMA sites' templates check (`mma_shape`, from `Mma.qk_isMma`, `Mma.pv_isMma`).
* **Stops.** No site of a machine has an undefined-behaviour template, so undefined behaviour
  fires only after the thread's machine stopped (`ub_stop`). The machines stop only at the
  thread's exit (its last event) or after a read they do not follow (`stop_cause`, `BadRead`):
  a `tcgen05.ld` returning a value that is not a single-precision float (softmax `.ld`,
  correction `rldW`/`fldW`); a correction thread's
  `ld.shared` whose bytes do not rebuild to a canonical single-precision word (`F32Read`: a float
  payload or a pattern with no bit above bit 31; `ldA`, `ldL` and
  the `credit 4|5` division that follows); warp 12's read of its base word whose bytes rebuild
  to nothing or to a value with no bit pattern (`Value.regBits`: the machine stops at the
  read-back, `Mma.ldBase`, or at the hand-off poll before the deallocation that reads it); or
  a broadcast shuffle returning a value other than the thread's own source value (the
  prologue's, the loader's `head`, the MMA warp's `shflQ`/`shfl`: every lane holds the value
  lane 0 broadcasts). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

/-- Every value of a load is a single-precision float. -/
def F32s (vals : List Value) : Prop := ∀ v ∈ vals, ∃ x, v = .float .f32 x

/-- Event `j` of thread `g` is a read whose value its machine does not follow. -/
def BadRead (L : Launch) (X : Execution) (g j : Nat) : Prop :=
  (∃ pc a vals, X.get (g, j) = some ⟨pc, .tc (.ld a vals .s32x32b)⟩ ∧ ¬ F32s vals) ∨
  (∃ pc a bs, X.get (g, j) = some ⟨pc, .rd a bs⟩ ∧ 8 ≤ warpOf L g ∧ warpOf L g < 12 ∧
    ¬ ∃ x, F32Read bs x) ∨
  (∃ pc a bs, X.get (g, j) = some ⟨pc, .rd a bs⟩ ∧ warpOf L g = 12 ∧
    a.loc = baseLoc L (ctaOf L g) ∧ a.size = 4 ∧
    ∀ v, rebuild 3 bs = .ok v → v.regBits = none) ∨
  (∃ pc md a b c recv ok, X.get (g, j) = some ⟨pc, .shfl md a b c recv ok⟩ ∧ recv ≠ a)

/-- The thread layer's facts for the commits, the MMA issues and the stops. -/
structure TcFacts (L : Launch) (X : Execution) : Prop where
  /-- A commit is warp 12's of a leader CTA, to a barrier of its CTA other than the handshake
  barrier, over the pair from its CTA with mask 3. -/
  commit_spec : ∀ {g k pc : Nat} {sp : TcCommit.Spec}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩ →
      warpOf L g = 12 ∧ ctaOf L g % 2 = 0 ∧ ∃ b : FBar, b ≠ .dealloc ∧
        sp = ⟨.two, b.loc L (ctaOf L g), 3, ctaOf L g, 2⟩
  /-- A thread of warp 0 that reaches its cluster arrival initialized every barrier of its CTA
  but the handshake barrier before it, unless a full-mask election before it returned another
  lane. -/
  init_done : ∀ {g : Nat}, g < L.threads → warpOf L g = 0 → clFirst X g < (X.tr g).length →
    (∀ b : FBar, b ≠ .dealloc → ∃ k < clFirst X g, ∃ pc n,
      X.get (g, k) = some ⟨pc, .mbInit (b.loc L (ctaOf L g)) n⟩) ∨
    ∃ k < clFirst X g, ∃ pc inst l, X.Elect (g, k) pc 4294967295 inst l ∧ l ≠ laneOf L g
  /-- Every result cell of an MMA is written (its lane masks are zero). -/
  mma_reads : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {row col : Nat} {cell : Cell}, X.MmaIssue i d s acc mask →
    resultCell s d row col = some cell → X.MmaCell i cell
  /-- Every MMA writes a cell. -/
  mma_cell : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
    X.MmaIssue i d s acc mask → ∃ cell, X.MmaCell i cell
  /-- An MMA writing a cell of stage `st < 2`'s scores reads its A operand from shared memory. -/
  qk_smem : ∀ {i : EvId} {d st : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {cell : Cell}, st < 2 → X.MmaIssue i d s acc mask → X.MmaCell i cell → InS st cell →
      s.aTmem = none
  /-- An MMA has the issue shape its site's template checks. -/
  mma_shape : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
    X.MmaIssue i d s acc mask → IssueShape L i d s mask
  /-- Undefined behaviour fires only after the thread's machine stopped. -/
  ub_stop : ∀ {g k pc : Nat} {f : Fault}, g < L.threads → X.get (g, k) = some ⟨pc, .ub f⟩ →
    St L X g k = none ∨ St L X g k = some none
  /-- A machine stops only at the thread's exit or after a read it does not follow. -/
  stop_cause : ∀ {g i : Nat} {d : ThreadD}, g < L.threads → St L X g i = some (some d) →
    (St L X g (i + 1) = none ∨ St L X g (i + 1) = some none) →
      (∃ pc, X.get (g, i) = some ⟨pc, .exit⟩) ∨ ∃ j ≤ i, BadRead L X g j

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- Two threads of one warp group (four warps) loading or storing one Tensor Memory cell are one
thread: the cell's CTA, lane quarter and lane are the thread's. -/
theorem cell_thread (hpre : Pre P L mem0) {h h' a a' j j' : Nat}
    (hst : warpOf L h / 4 = warpOf L h' / 4)
    (hc : tcDataCell32 L h a j = tcDataCell32 L h' a' j') : h = h' := by
  simp only [tcDataCell32, laneBase, laneOf, Cell.mk.injEq] at hc
  obtain ⟨h1, h2, -⟩ := hc
  unfold warpOf at *
  rw [hpre.block] at *
  omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof
