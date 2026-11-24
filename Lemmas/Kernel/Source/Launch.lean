-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.MemTmpl
public import Core.Assembly.Correctness

@[expose] public section

/-! # Source of a returned value: a launch input

A proof tool. A read of a read-only input returns, byte by byte, the bytes the launch gave it: a
kernel obtains that from its read-only input assumption (which names its own sites and regions,
so it is a constructor of the kernel's `Assumptions`, not of the library). From the bytes the
returned value follows without any fact about the other events of the execution:

* `bytes_of_pointwise`: read bytes that are pointwise the bytes of a value `v` are `v`'s bytes;
* `read_value_of_bytes`: such bytes rebuild (`BYTES`) to `v` itself when `v` is a scalar whose
  first byte names it, as every value a launch writes is (a word, a float, a pointer).

The read-only input assumptions of the kernels have one form (`LaunchReads`: a plain read at one
of the assumption's sites returns the launch byte at every byte of its input region where the
launch has one; `LaunchReads.of_forall` for an assumption without a region); from it a read of
a launch value at a known address returns the value (`LaunchReads.bytes`, `LaunchReads.value`).
The address of an element of an input array lies in the 64-bit address space when the array does
(`elem_addr_lt`, `elem_addr_mod`): the closed form of a block-table or query load's address is the
kernel's (its register table), the fact that it does not wrap is this one. -/

namespace PTX.Frame

open PTX PTX.Flow

/-- **Read bytes that are pointwise a value's bytes are its bytes.** -/
theorem bytes_of_pointwise {bs : List (Option Byte)} {v : Value} (hlen : bs.length = v.bytes)
    (hb : ∀ k < v.bytes, bs[k]? = some (some (v.byteAt k))) : bs = v.toBytes.map some := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < v.bytes
  · rw [hb k hk]
    simp [Value.toBytes, hk]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp [Value.toBytes]; omega)]

/-- **Bytes that are pointwise a scalar's bytes rebuild to the scalar.** -/
theorem read_value_of_bytes {bs : List (Option Byte)} {v : Value} (hlen : bs.length = v.bytes)
    (hb : ∀ k < v.bytes, bs[k]? = some (some (v.byteAt k))) (hv : 0 < v.bytes)
    (hs : v.byteAt 0 = (v, 0)) : rebuild 3 bs = .ok v := by
  rw [bytes_of_pointwise hlen hb]
  exact PTX.Proof.rebuild_scalar hv hs

/-- **The form of a read-only input assumption**: a plain read at one of `sites` returns the
launch byte at every byte of the input region `R` where the launch has one. -/
def LaunchReads (mem0 : Mem0) (X : Execution) (sites : List Nat) (R : Loc → Prop) : Prop :=
  ∀ e pc a bs, X.get e = some ⟨pc, .rd a bs⟩ → sites.contains pc = true →
    ∀ k < a.size, R (a.loc.at k) → ∀ c, mem0 (a.loc.at k) = some (some c) →
      bs[k]? = some (some c)

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {sites : List Nat} {R : Loc → Prop}

/-- An assumption that names no region is the form with every location. -/
theorem LaunchReads.of_forall
    (h : ∀ e pc a bs, X.get e = some ⟨pc, .rd a bs⟩ → sites.contains pc = true →
      ∀ k < a.size, ∀ c, mem0 (a.loc.at k) = some (some c) → bs[k]? = some (some c)) :
    LaunchReads mem0 X sites fun _ => True :=
  fun e pc a bs he hs k hk _ c hc => h e pc a bs he hs k hk c hc

/-- **A read at an input site of a launch value's bytes returns the value's bytes.** -/
theorem LaunchReads.bytes (hX : Consistent L K A mem0 X) (h : LaunchReads mem0 X sites R)
    {i : EvId} {pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get i = some ⟨pc, .rd a bs⟩) (hs : sites.contains pc = true) {v : Value}
    (hsz : a.size = v.bytes) (hR : ∀ k < v.bytes, R (a.loc.at k))
    (hm : ∀ k < v.bytes, mem0 (a.loc.at k) = some (some (v.byteAt k))) :
    bs = v.toBytes.map some := by
  have hlen : bs.length = a.size := (hX.rf (.thread i) a bs (Or.inl ⟨pc, he⟩)).1
  exact bytes_of_pointwise (by omega) fun k hk =>
    h i pc a bs he hs k (by omega) (hR k hk) _ (hm k hk)

/-- **A read at an input site of a launch scalar's bytes rebuilds to the scalar.** -/
theorem LaunchReads.value (hX : Consistent L K A mem0 X) (h : LaunchReads mem0 X sites R)
    {i : EvId} {pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get i = some ⟨pc, .rd a bs⟩) (hs : sites.contains pc = true) {v : Value}
    (hsz : a.size = v.bytes) (hR : ∀ k < v.bytes, R (a.loc.at k))
    (hm : ∀ k < v.bytes, mem0 (a.loc.at k) = some (some (v.byteAt k)))
    (hv : 0 < v.bytes) (h0 : v.byteAt 0 = (v, 0)) : rebuild 3 bs = .ok v := by
  rw [LaunchReads.bytes hX h he hs hsz hR hm]
  exact PTX.Proof.rebuild_scalar hv h0

/-- **An element of an array inside the address space lies inside it**: byte `j` of element `i`
of an array of `n` elements of `w` bytes at `base`. -/
theorem elem_addr_lt {base w n i j : Nat} (hi : i < n) (hj : j < w) (hr : base + w * n ≤ 2 ^ 64) :
    base + w * i + j < 2 ^ 64 := by
  have : w * i + w ≤ w * n := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left w hi
  omega

/-- **The 64-bit address of an array element does not wrap.** -/
theorem elem_addr_mod {base w n i j : Nat} (hi : i < n) (hj : j < w)
    (hr : base + w * n ≤ 2 ^ 64) : (base + w * i + j) % 2 ^ 64 = base + w * i + j :=
  Nat.mod_eq_of_lt (elem_addr_lt hi hj hr)

end PTX.Frame
