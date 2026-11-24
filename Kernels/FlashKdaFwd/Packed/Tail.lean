-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Spec
public import Lemmas.Flow.MemTmpl
public import Lemmas.Flow.UbFree
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Tail
open PTX PTX.Proof PTX.Flow

def source (i : Nat) := 112 - 2*(i/2) + i%2

def store (i : Nat) : MemAccess := {
  kind := .store, space := some .global, sem := .weak, elem := .int .b 16,
  addr := ⟨.reg 3414 64, (2*i : Nat) - (8 : Int)⟩, srcs := [.reg (source i)] }

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 60000 in
theorem sites : Transfers.slice 3024 8 =
    some ((List.range 8).map fun i => ⟨none, .mem (store i)⟩) := by rfl

theorem address {L : Launch} {g base : Nat} (t : TState) (i : Fin 8)
    (pointer : t.regs 3414 = some (b64 (base+8))) (fits : base+16 ≤ 2^64) :
    effAddr L g t .global 3414 ((store i.val).addr.off) = .ok ⟨.global, 0, base+2*i.val⟩ := by
  rw [effAddr_global_bits pointer]
  have trunc (v : BitVec 64) : truncBits 64 v = v := by
    unfold truncBits
    rw [Nat.mod_eq_of_lt v.isLt]
    simp
  rw [trunc]
  change Except.ok (⟨.global, 0, (BitVec.ofNat 64 (base+8) +
    BitVec.ofInt 64 ((2*i.val : Nat) - (8 : Int))).toNat⟩ : Loc) = _
  rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_add, show ((base+8 : Nat) : Int) +
    (((2*i.val : Nat) : Int)-8) = (↑(base+2*i.val) : Int) by omega, BitVec.ofInt_natCast,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem write (A : List Assumption) {L : Launch} {g base : Nat} (t : TState) (i : Fin 8)
    (val : Value) (two : val.bytes = 2) (start : t.sub = 0)
    (pointer : t.regs 3414 = some (b64 (base+8))) (data : t.regs (source i.val) = some val)
    (aligned : base%2 = 0) (fits : base+16 ≤ 2^64) :
    memTmpl A L g t (store i.val) =
      .write {loc := ⟨.global, 0, base+2*i.val⟩, size := 2} val.toBytes
        (afterStore t [.reg (source i.val)]) := by
  change storeTmpl L g t .global 16 3414 (store i.val).addr.off [.reg (source i.val)] = _
  unfold storeTmpl
  rw [address t i pointer fits]
  simp only [bind, Except.bind, List.length_singleton, start]
  rw [elemAcc_ok (by decide) (by change (base+2*i.val)%2 = 0; omega)]
  simp [Loc.at, readValue, readReg, data, storeValue_of_bytes (w := 16) two,
    pure, Except.pure]

theorem output_word (p : Problem) (seq head block row : Nat) (group : Fin 16) (i : Fin 8) :
    let token := Batches.firstToken p.length seq + 16*block+row
    let base := p.outputBase + 256*(token*p.heads+head) + 16*group.val
    base+2*i.val = (p.outputLoc seq head (16*block+row)
      ⟨8*group.val+i.val, by omega⟩).addr := by
  dsimp [Problem.outputLoc]
  ring

end FlashKda.Packed.Tail
