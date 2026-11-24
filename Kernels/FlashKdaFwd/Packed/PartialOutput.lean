-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Tail
public import Kernels.FlashKdaFwd.Packed.Bfloat
public import Kernels.FlashKdaFwd.Packed.Pointer
public import Lemmas.Flow.TensorStoreOrigin
public import Tactics.KernelRfl
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.PartialOutput
open PTX

def registers := [1126,1127,1128,1129]

def load : MemAccess := {
  kind := .load, space := some (.shared .cta), sem := .weak, elem := .int .b 32, vec := 4,
  addr := ⟨.reg 2116 32, 0⟩, dsts := registers.map some }

def unpack (i : Nat) : Instr := ⟨none, .move {
  kind := .unpack, ty := .int .b 32, dsts := [some (106+2*i),some (107+2*i)],
  srcs := [.reg (1129-i)] }⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 60000 in
theorem sites : Transfers.slice 3019 5 = some (⟨none,.mem load⟩ :: (List.range 4).map unpack) := by
  kernel_rfl

theorem read (A : List Assumption) (L : Launch) (g base : Nat) (t : TState) (i : Fin 4)
    (addr : t.regs 2116 = some (Proof.b32 base)) (fits : base < 2^32)
    (aligned : base%16 = 0) (word : t.sub = i.val) :
    memTmpl A L g t load = .read {
      loc := ⟨.shared, g/L.block, base+4*i.val⟩, size := 4, elem := i.val}
        (afterLoad t registers) := by
  change loadTmpl A L g t .shared false 32 registers 2116 0 = _
  have eff := Flow.sharedEffAddr_b32 (L := L) (g := g) addr fits
  unfold loadTmpl
  change (match sharedEffAddr L g t false 2116 0 >>= fun l => elemAcc l 4 4 t.sub with
    | .error f => Tmpl.ub f | .ok a => .read a (afterLoad t registers)) = _
  rw [eff]
  simp only [bind, Except.bind, word]
  rw [Proof.elemAcc_ok (n := 4) (count := 4) (j := i.val) (by decide)
    (by change base%16 = 0; exact aligned)]
  rfl

def value (f : Nat → ℝ) (i : Nat) : Value := .float .bf16 (f i)

def word (f : Nat → ℝ) (i : Nat) := Value.pair (value f (2*i)) (value f (2*i+1))

def bytes (f : Nat → ℝ) (i : Nat) :=
  ((value f (2*i)).toBytes ++ (value f (2*i+1)).toBytes).map some

theorem rebuild_word (f : Nat → ℝ) (i : Nat) : rebuild 3 (bytes f i) = .ok (word f i) := by
  change rebuild 3 [some (value f (2*i),0), some (value f (2*i),1),
    some (value f (2*i+1),0), some (value f (2*i+1),1)] = _
  simp [value, word, rebuild, rebuild.halves, intByte, Value.toBytes, Value.byteAt, Value.bytes,
    FloatFmt.bytes, List.range_succ, bind, Except.bind, pure, Except.pure]

noncomputable def loaded (t : TState) (f : Nat → ℝ) :=
  (List.range 4).foldl (fun s i => afterLoad s registers (bytes f i)) t

theorem load_result (t : TState) (f : Nat → ℝ) (start : t.sub = 0) (fresh : t.acc = []) :
    loaded t f = {setRegs t registers ((List.range 4).map (word f)) with
      pc := t.pc+1, sub := 0, acc := []} := by
  simp [loaded, List.range_succ, afterLoad, registers, rebuild_word, start, fresh, setRegs, setReg]

def split (f : Nat → ℝ) (t : TState) (i : Nat) :=
  let j := 2*(3-i)
  next (setReg (setReg t (106+2*i) (value f j)) (107+2*i) (value f (j+1)))

noncomputable def splitTo (t : TState) (f : Nat → ℝ) : Nat → TState
  | 0 => loaded t f
  | n+1 => split f (splitTo t f n) n

noncomputable section
variable (b : Nat → Nat → Nat)
local notation "A" =>
  [Pointer.representation b, Bfloat.exactNarrow, Activation.arithmetic, Activation.approximate]

theorem unpack_word (L : Launch) (g : Nat) (t : TState) (f : Nat → ℝ) (i : Nat)
    (src : t.regs (1129-i) = some (word f (3-i))) :
    execLocalA A L g t (unpack i).op = .ok (split f t i) := by
  change execMove L g t (unpack i).op = _
  simp [execMove, unpack, readValue, readReg, src, word, value, Value.bytes, FloatFmt.bytes,
    DType.width, splitValue, split, bind, Except.bind, pure, Except.pure]

theorem packed_source (t : TState) (f : Nat → ℝ) (i : Fin 4)
    (start : t.sub = 0) (fresh : t.acc = []) :
    (splitTo t f i.val).regs (1129-i.val) = some (word f (3-i.val)) := by
  fin_cases i <;> simp [splitTo, split, load_result t f start fresh, registers, List.range_succ,
    setRegs, setReg, next]

theorem unpack_run (L : Launch) (g : Nat) (t : TState) (f : Nat → ℝ)
    (start : t.sub = 0) (fresh : t.acc = []) (n : Nat) (hn : n ≤ 4) :
    ((List.range n).map unpack).foldlM (m := Exec) (fun u i => execLocalA A L g u i.op)
      (loaded t f) = .ok (splitTo t f n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldlM_append, ih (by omega)]
    have step := unpack_word b L g _ f n (packed_source t f ⟨n,by omega⟩ start fresh)
    simp only [List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil, bind, Except.bind,
      step, pure, Except.pure]
    rfl

theorem destinations (t : TState) (f : Nat → ℝ) (i : Fin 8) :
    (splitTo t f 4).regs (Tail.source i.val) = some (value f i.val) := by
  fin_cases i <;> simp [splitTo, split, next, setReg, Tail.source]

theorem transferred (L : Launch) (g base : Nat) (t : TState) (f : Nat → ℝ)
    (start : t.sub = 0) (fresh : t.acc = [])
    (ptr : t.regs 3414 = some (Proof.b64 (base+8))) (aligned : base%2 = 0) (fits : base+16 ≤ 2^64) :
    ∃ u, ((List.range 4).map unpack).foldlM (m := Exec) (fun s i => execLocalA A L g s i.op)
      (loaded t f) = .ok u ∧ ∀ i : Fin 8, memTmpl A L g u (Tail.store i.val) =
        .write {loc := ⟨.global, 0, base+2*i.val⟩, size := 2} (value f i.val).toBytes
          (afterStore u [.reg (Tail.source i.val)]) := by
  refine ⟨_, unpack_run b L g t f start fresh 4 (by decide), ?_⟩
  intro i
  apply Tail.write A _ i _ rfl _ _ (destinations t f i) aligned fits
  · simp [splitTo, split, next, setReg, load_result t f start fresh]
  · simpa [splitTo, split, next, setReg, load_result t f start fresh, registers, List.range_succ,
      setRegs] using ptr

end
end FlashKda.Packed.PartialOutput
