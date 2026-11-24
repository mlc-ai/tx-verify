-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Reads
public import Kernels.InklingRelDecode.Proof.Interface.ShapeTrace

@[expose] public section

/-!
# A read of an input word returns the word

`input_word`: a four-byte read at a global address whose four bytes are inputs
(`Params.reads`) with the launch contents of the 32-bit word `x` (`i32Byte x j`) returns the
bytes of `x`. The block-table, `cu_seqlens_q` and `seq_lens` reads are of this form
(`Pre.btInput`, `cuInput`, `seqInput`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem i32Byte_eq (x k : Nat) : i32Byte x k = (b32 x).byteAt k := rfl

theorem toBytes_b32 (x : Nat) : (b32 x).toBytes = [i32Byte x 0, i32Byte x 1, i32Byte x 2,
    i32Byte x 3] := by
  simp [Value.toBytes, Value.bytes, List.range_succ, i32Byte_eq, b32]

/-- **A four-byte read of input bytes returns the bytes of their word**, given that each byte it
returns is the launch byte. -/
theorem word_of_bytes (hX : Consistent L kernel asms mem0 X) {g k pc : Nat} {a : Acc}
    {bs : List (Option Byte)} (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) {A : Nat}
    (hloc : a.loc = ⟨.global, 0, A⟩) (hsz : a.size = 4) (x : Nat)
    (hx : ∀ j < 4, Q.reads (A + j) ∧ mem0 ⟨.global, 0, A + j⟩ = some (some (i32Byte x j)))
    (hbyte : ∀ j < 4, Q.reads (a.loc.at j).addr →
      ∃ c, mem0 (a.loc.at j) = some (some c) ∧ bs[j]? = some (some c)) :
    bs = (b32 x).toBytes.map some := by
  have hr : X.MemReads (.thread (g, k)) a bs := Or.inl ⟨pc, he⟩
  have hlen : bs.length = 4 := by
    have := Consistent.read_length hX hr
    omega
  rw [toBytes_b32]
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 4
  · obtain ⟨hrd, hm⟩ := hx j hj
    obtain ⟨c, hc, hb⟩ := hbyte j hj (by rw [hloc]; exact hrd)
    have hc' : mem0 (a.loc.at j) = some (some (i32Byte x j)) := by rw [hloc]; exact hm
    rw [hc] at hc'
    have := Option.some.inj (Option.some.inj hc')
    subst this
    rw [hb]
    interval_cases j <;> simp
  · have h1 : bs[j]? = none := List.getElem?_eq_none (by omega)
    rw [h1]
    simp
    omega

/-- **A four-byte read of input bytes returns the bytes of their word.** -/
theorem input_word (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) {A : Nat} (hloc : a.loc = ⟨.global, 0, A⟩)
    (hsz : a.size = 4) (x : Nat)
    (hx : ∀ j < 4, Q.reads (A + j) ∧ mem0 ⟨.global, 0, A + j⟩ = some (some (i32Byte x j))) :
    bs = (b32 x).toBytes.map some :=
  word_of_bytes hX he hloc hsz x hx fun j hj hrd =>
    read_launch_byte hpre hX hf (show X.MemReads (.thread (g, k)) a bs from Or.inl ⟨pc, he⟩)
      (by rw [hloc]) (by rw [hloc]) (k := j) (by omega) hrd

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
