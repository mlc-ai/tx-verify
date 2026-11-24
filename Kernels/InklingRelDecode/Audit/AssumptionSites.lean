-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.WarpUniform
public import Lemmas.Flow.AccessLocal

@[expose] public section

/-!
# Site audit of the Inkling assumptions

The pc lists of the kernel-local assumptions are exactly the instructions of the decoded program
that have the form each assumption reads: the 16 software-`exp2` instances start at the
`max.ftz.f32` of an 11-instruction block whose second instruction is the kernel's only
`add.rm.ftz.f32`, and match the template; `lg2`, `div.full` and `neg` each occur once, at their
site; `inputReadSites` are exactly the 203 plain `ld.global` instructions (11 of 32 bits, 192 of
16 bits), and no other instruction may read global memory.
-/

namespace PTX.Kernels.InklingRelDecode.Assumptions
open PTX

/-- The `add.rm` instructions of the kernel are exactly the second instruction of each template
instance. -/
theorem addRm_sites : (kernel.code.zipIdx.filter (fun p => match p.1.op with
      | .float f => f.op == .add && f.rnd == some .rm
      | _ => false)).map (·.2) = emuSites.map (· + 1) := by
  decide +kernel

/-- Each instance matches the template, with one register per slot. -/
theorem emu_matches :
    ∀ pc ∈ emuSites, (matchEmu emuBody (kernel.code.drop pc) []).isSome = true := by
  decide +kernel

/-- `lg2`, `div.full` and `neg` occur exactly at their sites. -/
theorem lg2_sites : (kernel.code.zipIdx.filter (fun p => match p.1.op with
      | .float f => f.op == .lg2
      | _ => false)).map (·.2) = lg2Sites := by
  decide +kernel

theorem divFull_sites : (kernel.code.zipIdx.filter (fun p => match p.1.op with
      | .float f => f.op == .div && f.mode == .full
      | _ => false)).map (·.2) = divFullSites := by
  decide +kernel

theorem neg_sites : (kernel.code.zipIdx.filter (fun p => match p.1.op with
      | .float f => f.op == .neg
      | _ => false)).map (·.2) = negSites := by
  decide +kernel

/-- The program has four `tcgen05.commit`s (`s_ready`, `kv_empty`, `o_done`, `o_final`);
`commitOrderSites` are the second and the third. -/
theorem commitOrder_site : (kernel.code.zipIdx.filter (fun p => match p.1.op with
      | .tcCommit .. => true
      | _ => false)).map (·.2) = [2499, 2546, 2548, 2553] ∧
    commitOrderSites = [2546, 2548] := by
  refine ⟨?_, rfl⟩
  decide +kernel

/-- Every `mbarrier.try_wait` of the program is followed by a poll branch, and the instruction after
each `try_wait` is exactly the six sites of `pollAgreeSites`. -/
theorem pollAgree_sites :
    (kernel.code.zipIdx.filter (fun p => match p.1.op with
      | .mbarWait .. => true
      | _ => false)).map (fun p => p.2 + 1) = pollAgreeSites ∧
    pollAgreeSites.all (fun pc => kernel.pollBranch pc) = true := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- The program counters at which the instruction is `setmaxnreg.inc 256`. -/
def inc256 (pc : Nat) : Bool :=
  match (kernel.code[pc]?).map (·.op) with
  | some (PTX.Op.setMaxReg true 256) => true
  | _ => false

/-- The program counters at which the instruction is `bra.uni` to `target`. -/
def braUniTo (target pc : Nat) : Bool :=
  match (kernel.code[pc]?).map (·.op) with
  | some (PTX.Op.bra t true) => t == target
  | _ => false

/-- `regSyncSites` is the loop-head `setmaxnreg.inc 256` of the worker dispatch loop: it follows
another `setmaxnreg.inc 256` (pc 2336) and both role tails restore 256 (pc 2420 and 2555) and
branch straight back to it (pc 2421 and 2556). -/
theorem regSync_site :
    inc256 2336 = true ∧ inc256 2337 = true ∧ inc256 2420 = true ∧ braUniTo 2337 2421 = true ∧
    inc256 2555 = true ∧ braUniTo 2337 2556 = true ∧ regSyncSites = [2337] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> decide +kernel

/-- A plain (not `.nc`) weak `ld.global` of a single `b32` or `b16` value. -/
def plainGlobalLoad (w : Nat) (op : Op) : Bool :=
  match op with
  | .mem a => a.kind == .load && a.space == some .global && !a.nc && a.sem == .weak &&
      a.vec == 1 && a.elem == .int (.b) w
  | _ => false

/-- **`inputReadSites` are exactly the `ld.global` instructions of the program**, and each is a
plain weak scalar load: 11 of 32 bits (the request words `cu_seqlens_q`, `seq_lens` and the
eight block-table words) and 192 of 16 bits (64 query and 128 bias loads). -/
theorem inputRead_sites :
    (kernel.code.zipIdx.filter (fun p => match p.1.op with
      | .mem a => a.kind == .load && a.space == some .global
      | _ => false)).map (·.2) = inputReadSites ∧
    (kernel.code.zipIdx.filter (fun p => plainGlobalLoad 32 p.1.op)).map (·.2) =
      [34, 37, 41, 197, 220, 241, 262, 283, 304, 2382, 2399] ∧
    (kernel.code.zipIdx.filter (fun p => plainGlobalLoad 16 p.1.op)).length = 192 ∧
    inputReadSites.length = 203 := by
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide +kernel

/-- **No instruction but the sites may read global memory**: every other load names a space other
than global memory (shared memory or the parameters), and the program's `movmatrix` loads, if any,
read shared memory. -/
theorem inputRead_only : kernel.code.zipIdx.all (fun p =>
    !Flow.readOp p.1.op || inputReadSites.contains p.2 || match p.1.op with
      | .mem a => a.space != some .global && a.space != none
      | _ => true) = true := by
  decide +kernel

end PTX.Kernels.InklingRelDecode.Assumptions
