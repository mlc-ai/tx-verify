-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaFirstScan
public import Kernels.TmlFa4Fwd.Proof.EpilogueGroup
public import Kernels.TmlFa4Fwd.Proof.SchedulerScanObservations
public import Lemmas.Flow.WarpScan

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue Prologue

noncomputable section

def scanReg (round : Nat) : Nat :=
  if h : round < 5 then scanSrc ⟨round, h⟩ else 7197

/-- Actual terminated warp cursors at the doubling rounds of the first scheduler group. -/
structure MmaScan (p : Params) (l : Launch) (X : Execution) (g round : Nat) where
  pos : Nat → Nat
  state : Nat → TState
  ordinals : WarpOrdinals l X g pos (5 + round) 0
  checkpoint : ∀ lane < 32, At (state lane) (1960 + 4 * round)
    [(scanReg round, b32 (prefixWindow (groupLaneTiles p 0) (2 ^ round) lane)),
      (1180, b32 lane), (7139, b32 p.heads)]
  continuation : ∀ lane < 32, Run kernel Assumptions.all l (warpLane l g lane) (state lane)
    ((X.tr (warpLane l g lane)).drop (pos lane)) none

/-- The scan round keeps its control registers and names the next prefix operand. -/
theorem roundInfo (stage : Fin 5) :
    scanDst stage ≠ scanSrc stage ∧ scanDst stage ≠ 1180 ∧ scanDst stage ≠ 7139 ∧
      scanResult stage = scanReg (stage.val + 1) := by
  fin_cases stage <;> decide

private theorem roundWrites (stage : Fin 5) :
    ((kernel.code.drop (scanPc stage + 1)).take 3).all
      (fun ins => [1180, 7139].all (fun r => !(writesRegs ins.op).contains r)) = true := by
  set_option maxRecDepth 100000 in
  fin_cases stage <;> kernel_rfl

/-- The arithmetic after a scan shuffle follows sequential control flow. -/
theorem roundStraight (stage : Fin 5) :
    ((kernel.code.drop (scanPc stage + 1)).take 2).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
  set_option maxRecDepth 100000 in
  fin_cases stage <;> kernel_rfl

/-- One actual up-shuffle round doubles the correct prefix window. -/
theorem MmaScan.advance {p : Params} {l : Launch} {m : Mem0} {X : Execution} {g round : Nat}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hg : g < l.threads)
    (hRound : round < 5) (cur : MmaScan p l X g round) :
    Nonempty (MmaScan p l X g (round + 1)) := by
  classical
  let _ : Nonempty Value := ⟨b32 0⟩
  let _ : Nonempty TState := ⟨{}⟩
  let stage : Fin 5 := ⟨round, hRound⟩
  let part := prefixWindow (groupLaneTiles p 0) (2 ^ round)
  let thread := warpLane l g
  let step (lane : Nat) (recv : Value) := next (setReg (cur.state lane) (scanDst stage) recv)
  let shift := 2 ^ round
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hAt (lane : Nat) (hl : lane < 32) :
      At (cur.state lane) (scanPc stage)
        [(scanSrc stage, b32 (part lane)), (1180, b32 lane), (7139, b32 p.heads)] := by
    change At (cur.state lane) (1960 + 4 * round) _
    simpa only [scanReg, dite_eq_left hRound] using cur.checkpoint lane hl
  have hEvent (lane : Nat) (hl : lane < 32) : ∃ recv ok,
      X.get (thread lane, cur.pos lane) =
        some ⟨scanPc stage, .shfl .up (b32 (part lane)) shift 0 recv ok⟩ ∧
      Run kernel Assumptions.all l (thread lane) (step lane recv)
        ((X.tr (thread lane)).drop (cur.pos lane + 1)) none := by
    have ht := hAt lane hl
    have hOut := scanTemplate hp (thread lane) (cur.state lane) stage (part lane)
      ht.1 ht.2.2.2.1 ht.2.2.2.2.1
    let hn : Next kernel Assumptions.all l (thread lane) (cur.state lane) (cur.state lane)
        (.shfl .up (b32 (part lane)) shift 0 (fun v _ => step lane v)) := ⟨.refl, hOut⟩
    obtain ⟨recv, ok, he, _, hr⟩ := hn.shuffle_at (cur.continuation lane hl)
      (cur.ordinals.shfl lane hl)
    exact ⟨recv, ok, by simpa only [ht.1] using he, hr⟩
  choose! recv ok he hRest using hEvent
  have hSh := cur.ordinals.shuffle_value hX hBlock hg (fun _ => scanPc stage) .up
    (fun lane => b32 (part lane)) recv (fun _ => shift) (fun _ => 0) ok he
  have hOrd := (cur.ordinals.shuffle (fun _ => scanPc stage) .up
    (fun lane => b32 (part lane)) recv (fun _ => shift) (fun _ => 0) ok he).2
  have hNext (lane : Nat) (hl : lane < 32) : ∃ u,
      At u (1960 + 4 * (round + 1))
        [(scanReg (round + 1), b32 (prefixWindow (groupLaneTiles p 0) (2 ^ (round + 1)) lane)),
          (1180, b32 lane), (7139, b32 p.heads)] ∧
      Run kernel Assumptions.all l (thread lane) u ((X.tr (thread lane)).drop (cur.pos lane + 1))
        none := by
    have hInfo := roundInfo stage
    have hS : At (step lane (recv lane)) (scanPc stage + 1)
        [(scanDst stage, recv lane), (scanSrc stage, b32 (part lane)), (1180, b32 lane),
          (7139, b32 p.heads)] := (hAt lane hl).set (by
      intro pair hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact hInfo.1.symm
      · exact hInfo.2.1.symm
      · exact hInfo.2.2.1.symm)
    let source := (shflSource .up lane shift 0).1
    have hValue : recv lane = b32 (part source) := (hSh lane hl).1
    have hArgs : At (step lane (recv lane)) (scanPc stage + 1)
        [(1180, b32 lane), (scanSrc stage, b32 (part lane)), (scanDst stage, b32 (part source))] :=
      hS.mono ⟨hS.2.2.2.2.2.2.1, hS.2.2.2.2.2.1, hValue ▸ hS.2.2.2.2.1, trivial⟩
    obtain ⟨u, hCore, hu⟩ := scanFold stage l (thread lane) (groupLaneTiles p 0) hl
      (groupPrefixOperands_fit hp (Nat.zero_le p.batch) hl stage) _ hArgs
    have hRange : 1904 ≤ scanPc stage + 1 ∧ scanPc stage + 1 + 3 ≤ 2768 := by
      have hs := stage.isLt
      unfold scanPc
      omega
    have hLocal := localRun hRange.1 hRange.2 hS.1 (roundStraight stage) hCore
    have hFrame {r : Nat} (hr : r ∈ [1180, 7139]) : u.regs r = (step lane (recv lane)).regs r :=
      schedulerLocalFrame (lo := scanPc stage + 1) (len := 3) (roundWrites stage)
        (roundStraight stage) hCore hS.1.ge (by rw [hS.1]) hr
    have hPc : scanPc stage + 4 = 1960 + 4 * (round + 1) := by
      simp [scanPc, stage, Nat.mul_add, Nat.add_assoc]
    have hWin : 2 * 2 ^ stage.val = 2 ^ (round + 1) := by
      simpa only [stage, Nat.pow_succ] using Nat.mul_comm 2 (2 ^ round)
    have hOut : At u (scanPc stage + 4)
        [(scanResult stage, b32 (prefixWindow (groupLaneTiles p 0) (2 * 2 ^ stage.val) lane)),
          (1180, b32 lane), (7139, b32 p.heads)] :=
      hu.mono ⟨hu.2.2.2.2.1, (hFrame (by decide)).trans hS.2.2.2.2.2.2.1,
        (hFrame (by decide)).trans hS.2.2.2.2.2.2.2.1, trivial⟩
    exact ⟨u, by simpa only [hPc, hWin, hInfo.2.2.2] using hOut,
      (hRest lane hl).after_local (run_rtg hLocal)⟩
  choose! state hAt' hRun' using hNext
  exact ⟨⟨fun lane => cur.pos lane + 1, state, by simpa [Nat.add_assoc] using hOrd, hAt', hRun'⟩⟩

/-- The scan reads the launch head count in its final local setup instruction. -/
theorem loadHeadsWord {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} (hpc : t.pc = 1959) (hf : t.fault = none) :
    run kernel Assumptions.all l g 1 t = some (next (setReg t 7139 (b32 p.heads))) := by
  have hName : param 17 =
      "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_object_at__ten\
      sor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf16gmemalign16o1i64\
      div8_0_param_17" := by
    have hDec : toString (17 : Nat) = "17" := by
      rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
      simp only [show (17 / 10 : Nat) = 1 by decide, show (17 % 10 : Nat) = 7 by decide,
        Nat.repr_of_lt (n := 1) (by decide), Nat.repr_of_lt (n := 7) (by decide),
        Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_seven.mpr rfl]
      rfl
    unfold param
    rw [hDec]
    set_option maxRecDepth 2000 in rfl
  obtain ⟨hHeads, hParam⟩ := hp.values (17, p.heads) (by simp [Params.scalarWords])
  change l.params (param 17) = some (BitVec.ofNat 64 p.heads) at hParam
  rw [hName] at hParam
  have he : execLocalA [] l g t (kernel.code[1959]?.getD (⟨none, .exit⟩ : Instr)).op =
      .ok (next (setReg t 7139 (b32 p.heads))) := by
    rw [Flow.code_1959, Option.getD_some, execLocalA_nil, execLocal_mem rfl]
    simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq,
      hParam, DType.width, MemExt.extendBits_same, pure, Except.pure,
      truncBits_ofNat hHeads (by decide)]
    rfl
  have hRun : run kernel [] l g 1 t = some (next (setReg t 7139 (b32 p.heads))) := by
    rw [Flow.code_1959, Option.getD_some] at he
    simp only [run, tauStep, out, hpc, hf, Flow.code_1959, guardHolds, pure, Except.pure, he]
    rfl
  exact localRun (by decide) (by decide) hpc rfl hRun

/-- The initial five actual scan rounds yield the complete inclusive scan. -/
theorem MmaScan.complete {p : Params} {l : Launch} {m : Mem0} {X : Execution} {g : Nat}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hg : g < l.threads)
    (start : MmaScan p l X g 0) : Nonempty (MmaScan p l X g 5) := by
  obtain ⟨a⟩ := start.advance hp hX hg (by decide)
  obtain ⟨b⟩ := a.advance hp hX hg (by decide)
  obtain ⟨c⟩ := b.advance hp hX hg (by decide)
  obtain ⟨d⟩ := c.advance hp hX hg (by decide)
  exact d.advance hp hX hg (by decide)

/-- The final scan broadcast returns the last lane’s inclusive total. -/
theorem scanTotalTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {sum : Nat} (ht : At t 1980 [(7197, b32 sum)]) :
    out kernel Assumptions.all l g t = .ev (.shfl .idx (b32 sum) 31 31
      (fun value _ => next (setReg t 7198 value))) := by
  rw [out_eq_core (by rw [ht.1]; decide) (by rw [ht.1]; decide),
    out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_1980) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 7198 none (.reg 7197) (.imm 31) (.imm 31) (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  simp [shflTmpl, readValue, readReg, ht.2.2.2.2.1, hBlock, Value.bytes, b32, readBits,
    pure, Except.pure]
  rfl

/-- The actual lane-31 broadcast returns the first group's total tile count in every MMA lane. -/
theorem MmaScan.total {p : Params} {l : Launch} {m : Mem0} {X : Execution} {g : Nat}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hg : g < l.threads)
    (cur : MmaScan p l X g 5) :
    WarpOrdinals l X g (fun lane => cur.pos lane + 1) 11 0 ∧
      ∀ lane < 32, ∃ u, At u 1981
        [(7198, b32 (tilePrefix p (min p.batch 31))),
          (7197, b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p 0 j)),
          (1180, b32 lane), (7139, b32 p.heads)] ∧
        Run kernel Assumptions.all l (warpLane l g lane) u
          ((X.tr (warpLane l g lane)).drop (cur.pos lane + 1)) none := by
  classical
  let _ : Nonempty Value := ⟨b32 0⟩
  let part := prefixWindow (groupLaneTiles p 0) 32
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hRead (lane : Nat) (hl : lane < 32) : ∃ recv ok,
      X.get (warpLane l g lane, cur.pos lane) =
        some ⟨1980, .shfl .idx (b32 (part lane)) 31 31 recv ok⟩ ∧
      Run kernel Assumptions.all l (warpLane l g lane) (next (setReg (cur.state lane) 7198 recv))
        ((X.tr (warpLane l g lane)).drop (cur.pos lane + 1)) none := by
    have ht : At (cur.state lane) 1980 [(7197, b32 (part lane))] :=
      (cur.checkpoint lane hl).mono ⟨(cur.checkpoint lane hl).2.2.2.2.1, trivial⟩
    have hn : Next kernel Assumptions.all l (warpLane l g lane) (cur.state lane) (cur.state lane)
        (.shfl .idx (b32 (part lane)) 31 31 (fun v _ => next (setReg (cur.state lane) 7198 v))) :=
      ⟨.refl, scanTotalTemplate hp ht⟩
    obtain ⟨recv, ok, he, _, hr⟩ := hn.shuffle_at (cur.continuation lane hl)
      (cur.ordinals.shfl lane hl)
    exact ⟨recv, ok, by simpa only [ht.1] using he, hr⟩
  choose! recv ok he hr using hRead
  have hOrd := (cur.ordinals.shuffle (fun _ => 1980) .idx (fun lane => b32 (part lane))
    recv (fun _ => 31) (fun _ => 31) ok he).2
  have hValue := cur.ordinals.shuffle_value hX hBlock hg (fun _ => 1980) .idx
    (fun lane => b32 (part lane)) recv (fun _ => 31) (fun _ => 31) ok he
  refine ⟨hOrd, ?_⟩
  intro lane hl
  have hSource : shflSource .idx lane 31 31 = (31, true) := by interval_cases lane <;> decide
  have hRecv := (hValue lane hl).1
  rw [hSource] at hRecv
  have hFull : part 31 = tilePrefix p (min p.batch 31) := by
    unfold part
    rw [prefixWindow_warp _ (by decide : (31 : Nat) < 32)]
    have h := groupTiles_eq p (Nat.zero_le p.batch) (by decide : (32 : Nat) ≤ 32)
    simpa [tilePrefix, Nat.min_comm] using h
  rw [hFull] at hRecv
  have hRest := hr lane hl
  rw [hRecv] at hRest
  have ht : At (cur.state lane) 1980
      [(7197, b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p 0 j)),
        (1180, b32 lane), (7139, b32 p.heads)] := by
    have ht := cur.checkpoint lane hl
    change At (cur.state lane) 1980
      [(7197, b32 (prefixWindow (groupLaneTiles p 0) 32 lane)),
        (1180, b32 lane), (7139, b32 p.heads)] at ht
    simpa only [prefixWindow_warp _ hl] using ht
  have hAt := ht.set (r := 7198) (v := b32 (tilePrefix p (min p.batch 31))) (by
    intro pair hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> exact of_decide_eq_true rfl)
  exact ⟨_, hAt, hRest⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
