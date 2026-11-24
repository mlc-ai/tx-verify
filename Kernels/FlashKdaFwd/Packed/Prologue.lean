-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Bfloat
public import Kernels.FlashKdaFwd.Packed.Pointer
public import Lemmas.Flow.Run
public import Kernels.FlashKdaFwd.Packed.Decode.Parameters
public import Kernels.FlashKdaFwd.Packed.Decode.Scalars
public import Kernels.FlashKdaFwd.Packed.Decode.Compose
public import Tactics.KernelRfl
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Prologue
open PTX

noncomputable def assumptions (base : Nat → Nat → Nat) :=
  [Pointer.representation base, Bfloat.exactNarrow, Activation.arithmetic, Activation.approximate]

set_option maxRecDepth 60000 in
private theorem conversion_site : Transfers.slice 12 1 = some [globalPointer] := by kernel_rfl

theorem sites : Transfers.slice 0 13 =
    some ((List.range 11).map address ++ [offsets, globalPointer]) := by
  have p : Transfers.slice 11 1 = some [offsets] := readOffsets
  exact Transfers.appendSlice (pc := 0) (n := 11) (k := 2) (by decide) descriptor_sites
    (Transfers.appendSlice (pc := 11) (n := 1) (k := 1) (by decide) p conversion_site)

def setAddress (t : TState) (i : Nat) :=
  next (setReg t (2251+i) (.ptr 64 false (.param (param i)) 0))

def state : Nat → TState
  | 0 => {}
  | i+1 => setAddress (state i) i

theorem address_exec (b : Nat → Nat → Nat) (L : Launch) (g i : Nat) (t : TState) :
    execLocalA (assumptions b) L g t (address i).op = .ok (setAddress t i) := by
  change execMove L g t (address i).op = _
  simp [execMove, address, readValue, setAddress, DType.width, Value.bytes, bind, Except.bind,
    pure, Except.pure]

theorem position (n : Nat) : (state n).pc = n ∧ (state n).fault = none := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ i ih => exact ⟨congrArg (·+1) ih.1, ih.2⟩

theorem object (n i : Nat) (hi : i < n) :
    (state n).regs (2251+i) = some (.ptr 64 false (.param (param i)) 0) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with lt | eq
    · simpa [state, setAddress, next, setReg, Nat.ne_of_lt lt] using ih lt
    · subst i
      simp [state, setAddress, next, setReg]

theorem addresses (b : Nat → Nat → Nat) (L : Launch) (K : Kernel) (g n : Nat)
    (fetch : ∀ i < n, K.code[i]? = some (address i)) :
    run K (assumptions b) L g n {} = some (state n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply run_comp (ih (fun i hi => fetch i (by omega)))
    have ⟨pc, safe⟩ := position n
    have locally : (address n).op.isLocal = true := rfl
    have guard : guardHolds (state n) (address n).guard = .ok true := rfl
    simp only [run, tauStep, out, safe, pc, fetch n (by omega), guard, locally, ↓reduceIte,
      address_exec, Option.bind_some]
    rfl

private theorem truncate (x : BitVec 64) : truncBits 64 x = x := by
  unfold truncBits
  rw [Nat.mod_eq_of_lt x.isLt]
  simp

def loaded (bits : BitVec 64) := next (setReg (state 11) 2262 (.bits 64 bits))

def ready (bits : BitVec 64) := next (setReg (loaded bits) 2247 (.bits 64 bits))

theorem offset_load (b : Nat → Nat → Nat) (L : Launch) (g : Nat) (bits : BitVec 64)
    (host : L.params (param 15) = some bits) :
    execLocalA (assumptions b) L g (state 11) offsets.op = .ok (loaded bits) := by
  change execMove L g (state 11) offsets.op = _
  simp [execMove, offsets, MemAccess.regs, host, MemExt.extendBits, DType.width, truncate, loaded,
    pure, Except.pure]

theorem pointer_conversion (b : Nat → Nat → Nat) (L : Launch) (g : Nat) (bits : BitVec 64) :
    execLocalA (assumptions b) L g (loaded bits) globalPointer.op = .ok (ready bits) := by
  change execCvta L g (loaded bits) (.cvta true .global 64 2247 (.reg 2262)) = _
  simp [execCvta, readBits, readReg, loaded, next, setReg, truncate, ready, bind, Except.bind,
    pure, Except.pure]

private theorem one {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {pc : Nat}
    {t u : TState} {i : Instr} (atPc : t.pc = pc) (good : t.fault = none)
    (fetch : K.code[pc]? = some i) (guard : guardHolds t i.guard = .ok true)
    (loc : i.op.isLocal = true) (exec : execLocalA A L g t i.op = .ok u) :
    run K A L g 1 t = some u := by
  simp only [run, tauStep, out, atPc, good, fetch, guard, loc, ↓reduceIte, exec, Option.bind_some]

theorem bind_launch (b : Nat → Nat → Nat) (L : Launch) (K : Kernel) (g : Nat) (bits : BitVec 64)
    (host : L.params (param 15) = some bits)
    (first : ∀ i < 11, K.code[i]? = some (address i))
    (read : K.code[11]? = some offsets) (convert : K.code[12]? = some globalPointer) :
    run K (assumptions b) L g 13 {} = some (ready bits) := by
  have addr := addresses b L K g 11 first
  have a := one (position 11).1 (position 11).2 read rfl rfl (offset_load b L g bits host)
  have c := one (t := loaded bits) (pc := 12) rfl rfl convert rfl rfl
    (pointer_conversion b L g bits)
  exact run_comp (run_comp addr a) c

theorem bindings (bits : BitVec 64) :
    (ready bits).pc = 13 ∧ (ready bits).regs 2247 = some (.bits 64 bits) ∧
      ∀ i < 11, (ready bits).regs (2251+i) = some (.ptr 64 false (.param (param i)) 0) := by
  refine ⟨rfl, by simp [ready, next, setReg], ?_⟩
  intro i hi
  have a : 2251+i ≠ 2262 := by omega
  have c : 2251+i ≠ 2247 := by omega
  simpa [ready, loaded, next, setReg, a, c] using object 11 i hi

end FlashKda.Packed.Prologue
