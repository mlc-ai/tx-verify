-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainEntry
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainFold

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- Scheduler state reused by later scans and the final ballot. -/
def drainPersistent : List Nat := [1201, 1062, 7147, 7506, 1072, 7138, 7230, 7235, 7236, 1210]

private def drainBounded (lo hi : Nat) (kept : List Nat) (ins : Instr) : Bool :=
  (match ins.op with
    | .bra pc _ => decide (lo ≤ pc ∧ pc ≤ hi)
    | .brx .. => false
    | _ => true) && kept.all (fun r => !(writesRegs ins.op).contains r)

/-- The post-shuffle entry PC for either copy of the tile-count arithmetic. -/
def drainPreparePc (later : Bool) := if later then 3046 else 2991

private theorem drainPrepareCode (later : Bool) :
    let lo := drainPreparePc later
    let hi := drainScanPc later 0
    ((kernel.code.drop lo).take (hi - lo)).all (drainBounded lo hi drainPersistent) = true := by
  cases later <;> kernel_rfl

private theorem drainBoundedPc {lo hi pc next : Nat} {kept : List Nat} {ins : Instr}
    (hc : drainBounded lo hi kept ins = true) (hp : lo ≤ pc) (hhi : pc < hi)
    (h : next = nextPc ins.op pc ∨ BrxTarget ins.op next) :
    lo ≤ next ∧ next ≤ hi := by
  have hfall : lo ≤ pc + 1 ∧ pc + 1 ≤ hi := by omega
  simp only [drainBounded, Bool.and_eq_true] at hc
  obtain ⟨hOp, _⟩ := hc
  cases ins with
  | mk guard op => cases op <;> simp_all [nextPc, BrxTarget]

/-- A slice audit transports a local run up to its next event while preserving the
scheduler registers that the slice leaves untouched. -/
private theorem drainRegionRun {l : Launch} {g n lo hi : Nat} {t u : TState}
    {kept : List Nat} {op : Op} (hLo : 2991 ≤ lo) (hHi : hi ≤ 3086)
    (hCode : ((kernel.code.drop lo).take (hi - lo)).all (drainBounded lo hi kept) = true)
    (hEnd : kernel.code[hi]? = some ⟨none, op⟩) (hEvent : op.isLocal = false)
    (hStart : lo ≤ t.pc ∧ t.pc ≤ hi) (hr : run kernel [] l g n t = some u) :
    run kernel Assumptions.all l g n t = some u ∧
      ∀ r ∈ kept, u.regs r = t.regs r := by
  have hModel {s : TState} (hs : lo ≤ s.pc ∧ s.pc ≤ hi) :
      out kernel Assumptions.all l g s = out kernel [] l g s :=
    epilogue_out_all_eq_nil (.inl ⟨by omega, by omega⟩)
  have hStep {s v : TState} (hs : lo ≤ s.pc ∧ s.pc ≤ hi) (ht : Tau kernel [] l g s v) :
      (lo ≤ v.pc ∧ v.pc ≤ hi) ∧ ∀ r ∈ kept, v.regs r = s.regs r := by
    have hStrict : s.pc < hi := by
      by_contra! h
      have he : s.pc = hi := by omega
      exact tau_core_not_event (by rwa [he]) hEvent ht
    obtain ⟨ins, hInstr⟩ := tau_core_has_code ht
    have hMem : ins ∈ (kernel.code.drop lo).take (hi - lo) := by
      apply List.mem_of_getElem? (i := s.pc - lo)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
        Nat.add_sub_of_le hs.1]
      exact hInstr
    have hIns := List.all_eq_true.mp hCode ins hMem
    rcases tau_core_frame hInstr ht with rfl | hf
    · exact ⟨by change lo ≤ s.pc + 1 ∧ s.pc + 1 ≤ hi; omega, fun _ _ => rfl⟩
    · refine ⟨drainBoundedPc hIns hs.1 hStrict hf.pc, fun r hReg => hf.regs r ?_⟩
      rw [drainBounded, Bool.and_eq_true] at hIns
      have hNo := List.all_eq_true.mp hIns.2 r hReg
      simpa using hNo
  obtain ⟨h', _, hf⟩ := run_core_region
    (region := fun pc => lo ≤ pc ∧ pc ≤ hi) (kept := fun r => r ∈ kept)
    (fun {_} => hModel) (fun {_ _} => hStep) hr hStart
  exact ⟨h', hf⟩

/-- Both lanes' tile-count paths and predicate setup stay in the scan region
until the first up shuffle and preserve the scheduler state. -/
theorem drainPrepareRun {l : Launch} {g n : Nat} {t u : TState} (later : Bool)
    (hStart : t.pc = drainPreparePc later) (hr : run kernel [] l g n t = some u) :
    run kernel Assumptions.all l g n t = some u ∧
      ∀ r ∈ drainPersistent, u.regs r = t.regs r := by
  have hLo : 2991 ≤ drainPreparePc later := by cases later <;> decide
  have hHi : drainScanPc later 0 ≤ 3086 := by cases later <;> decide
  have hAt : drainPreparePc later ≤ t.pc ∧ t.pc ≤ drainScanPc later 0 := by
    rw [hStart]
    cases later <;> decide
  exact drainRegionRun hLo hHi (drainPrepareCode later) (drainScanCode later 0) rfl hAt hr

/-- The first down shuffle provides the exact fields for the first five up shuffles. -/
theorem drainFirstPrepared {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (hl : laneOf l g < 32) :
    let lane := laneOf l g
    let source := (shflSource .down lane 1 31).1
    At t 2991 [(7229, b32 (drainCuQ p lane)), (2401, b32 (drainCuQ p source)),
      (268, .pred (!decide (laneHasRequest lane p.batch))), (1201, b32 lane)] →
    ∃ n u, run kernel Assumptions.all l g n t = some u ∧ At u (drainScanPc false 0)
      [(7232, b32 (groupLaneTiles p 0 lane))] ∧
      (∀ stage : Fin 5, u.regs (drainScanGuardReg false stage) =
        some (.pred (drainScanGuard stage lane))) ∧
      (∀ r ∈ drainPersistent, u.regs r = t.regs r) := by
  dsimp only
  intro ht
  obtain ⟨hBegin, hFinish, hMono, hLength, hTiles⟩ := drainWordTiles hp 0 (laneOf l g)
  simp only [Nat.zero_add] at hBegin hFinish hMono hLength hTiles
  let active := decide (laneHasRequest (laneOf l g) p.batch)
  let n := if active then 13 else 3
  obtain ⟨v, hr, hv⟩ := drainFirstLaneTiles l g active hBegin hFinish hMono hLength t
    (ht.mono (by exact ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, trivial⟩))
  obtain ⟨_, hKeep⟩ := drainPrepareRun false ht.1 (n := n) hr
  have hLane : At v (drainScanPc false 0 - 5) [(1201, b32 (laneOf l g))] := by
    apply hv.mono
    exact ⟨(hKeep 1201 (by decide)).trans (holds_mem ht.2.2.2.2 (by simp)), trivial⟩
  obtain ⟨u, hRun, hu⟩ := drainScanPrepare false l g hl v hLane
  have hStep : u.regs 7232 = v.regs 7232 := by
    have hSpecs : ((kernel.code.drop 3004).take 5).all
        (drainBounded 3004 3009 [7232]) = true := by kernel_rfl
    have hvpc : v.pc = 3004 := hv.1
    have hAt : 3004 ≤ v.pc ∧ v.pc ≤ 3009 := by omega
    have hKeep' := (drainRegionRun (lo := 3004) (hi := 3009) (by decide) (by decide) hSpecs
      (drainScanCode false 0) rfl hAt hRun).2
    exact hKeep' 7232 (by simp)
  have huTiles : u.regs 7232 = some (b32 (groupLaneTiles p 0 (laneOf l g))) := by
    rw [hStep, ← hTiles]
    exact hv.2.2.2.2.1
  have hAllCore := run_comp hr hRun
  obtain ⟨hAll, hFrame⟩ := drainPrepareRun false ht.1 hAllCore
  refine ⟨n + 5, u, hAll, hu.mono ⟨huTiles, trivial⟩, ?_, hFrame⟩
  intro stage
  fin_cases stage <;> exact holds_mem hu.2.2.2.2 (by simp [drainScanGuardReg, drainScanGuard])

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
