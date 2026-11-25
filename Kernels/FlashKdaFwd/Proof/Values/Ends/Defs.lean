-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Contract
public import Kernels.FlashKdaFwd.Proof.Values.Ends.Gen.Tables
public import Kernels.FlashKdaFwd.Proof.Thread.PtrEval

@[expose] public section

/-!
# The state in shared memory: layout and contents at the ends of the tile loop

The tile loop works on the state of one thread block (one sequence `s`, one head `h`): a
128 × 128 array of real numbers, indexed by the *value channel* and the *key feature*. Before
and after the loop the state is in shared memory in two forms, and this file names where each
entry is and what its bytes are. Nothing here mentions an execution.

**Element index.** Both forms store entry (value channel `ch`, key feature `k`) at the *element
index* `elemOf ch k = 1024 (k / 8) + 8 ch + k % 8` (`chanOf`, `keyOf` are the inverse). This is
the order in which the sixteen tensor loads of the initial state fill their buffer: load `i`
brings the key features `8 i` to `8 i + 7` of all 128 channels, eight consecutive 4-byte
entries per channel.

* **The bfloat16 copy `state_acc`** (window bytes 0 to 32767; "window" = the block's shared
  memory from the address of `shared_mem`): element `e` is the two bytes at `2 e`
  (`Values.accInitByte` is its content after the conversion loop).
* **The FP32 state buffer** (window bytes 32768 to 98303): element `e` is the four bytes at
  the **swizzled** address of `32768 + 4 e`. The swizzle (`swzAddr`) is what the kernel's
  generic pointers compute (`shr.u64 x, p, 3`, `and.b64 y, x, 16`, `xor.b64 q, y, p`): bit 4 of
  the address is flipped when bit 7 is set, so in every second 128-byte row the two 16-byte
  halves of each 32-byte group are exchanged. It acts on the absolute shared address, and
  `Launch.sharedBase` is only known to be a multiple of 128, so the content of a buffer byte is
  stated with the base (`bufByte base S o`): the byte at buffer offset `o` belongs to the entry
  at the unswizzled offset `swzAddr (base + 32768 + o) - (base + 32768)`.

`initBuf` is the buffer after the sixteen loads of the initial state (the bytes of the FP32
payloads of `P.initial`), `finalBuf` the buffer after the 128 final stores of each compute
thread (those of the state after the last token). A *payload* is a value `Value.float fmt x`
of the model: a real number tagged with a format.

**The carries.** A compute thread (index `tid < 128` in its block; warp `tid / 32`, lane
`tid % 32`) holds 128 entries of the state in registers across the tile loop. Entry `j` of the
generated table `Gen.carryTable` (the order of the 128 loads before the loop and of the 128
stores after it) gives the register (`carryReg j`), the entry (`carryElem j tid`, from the key
block, value block, half and accumulator register of the table and the fragment maps `cRow`,
`cCol` of the multiply-accumulate) and the constant its load and store add to the thread's base
pointer (`carryConst j`); the base pointer is `shared_mem + 4 * laneOff tid`. `carry_addr`
says the two descriptions of the address agree.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values.Ends
open PTX PTX.Flow PTX.WarpMatrix
open PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Math.Fragments (halfBase)

noncomputable section

/-! ## The swizzle of the generic shared pointers -/

/-- **The swizzled address**: bit 4 of `a` is flipped when bit 7 is set (on natural numbers;
`swzAddr_toNat` says it is the thread layer's `Rules.swz` on pointer offsets). -/
def swzAddr (a : ℕ) : ℕ := a ^^^ (a >>> 3 &&& 16)

/-- The thread layer's swizzled offset, as a number. -/
theorem swzAddr_toNat (off : BitVec 64) : (Rules.swz off).toNat = swzAddr off.toNat := by
  simp only [Rules.swz, swzAddr, BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat]

/-- The form in which a pointer run gives the address: the swizzle of the offset `a`. -/
theorem swzAddr_ofNat {a : ℕ} (ha : a < 2 ^ 64) :
    (Rules.swz (BitVec.ofNat 64 a)).toNat = swzAddr a := by
  rw [swzAddr_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

private theorem mask16 (a : ℕ) : a >>> 3 &&& 16 = if a / 128 % 2 = 1 then 16 else 0 := by
  rw [Nat.shiftRight_eq_div_pow]
  have hd : (a / 2 ^ 3 &&& 16) / 2 ^ 5 = 0 := by
    rw [Nat.and_div_two_pow]
    simp
  have hm : (a / 2 ^ 3 &&& 16) % 2 ^ 5 = a / 2 ^ 3 % 2 ^ 5 &&& 16 := by
    rw [Nat.and_mod_two_pow]
  have hr : ∀ r < 32, r &&& 16 = if r / 16 % 2 = 1 then 16 else 0 := by
    intro r hr
    interval_cases r <;> rfl
  have h := hr (a / 2 ^ 3 % 2 ^ 5) (Nat.mod_lt _ (by decide))
  rw [← hm] at h
  have e : (a / 2 ^ 3 % 2 ^ 5) / 16 % 2 = a / 128 % 2 := by omega
  rw [e] at h
  split_ifs at h ⊢ <;> omega

private theorem xor16 (a : ℕ) : a ^^^ 16 = if a / 16 % 2 = 1 then a - 16 else a + 16 := by
  have hd : (a ^^^ 16) / 2 ^ 5 = a / 2 ^ 5 := by
    rw [Nat.xor_div_two_pow]
    simp
  have hm : (a ^^^ 16) % 2 ^ 5 = a % 2 ^ 5 ^^^ 16 := by
    rw [Nat.xor_mod_two_pow]
  have hr : ∀ r < 32, r ^^^ 16 = if r / 16 % 2 = 1 then r - 16 else r + 16 := by
    intro r hr
    interval_cases r <;> rfl
  have h := hr (a % 2 ^ 5) (Nat.mod_lt _ (by decide))
  rw [← hm] at h
  split_ifs at h ⊢ <;> omega

/-- **The swizzle in arithmetic**: in a 128-byte row with an odd row number the two 16-byte
halves of each 32-byte group are exchanged. -/
theorem swzAddr_eq (a : ℕ) :
    swzAddr a = if a / 128 % 2 = 1 then (if a / 16 % 2 = 1 then a - 16 else a + 16) else a := by
  unfold swzAddr
  rw [mask16]
  by_cases h7 : a / 128 % 2 = 1
  · simp only [h7, ↓reduceIte]
    exact xor16 a
  · simp only [h7, ↓reduceIte]
    exact Nat.xor_zero a

/-- The swizzle keeps an address in its 32-byte group. -/
theorem swzAddr_div (a : ℕ) : swzAddr a / 32 = a / 32 := by
  rw [swzAddr_eq]
  split_ifs <;> omega

/-- The swizzle keeps the position in a 16-byte half. -/
theorem swzAddr_mod (a : ℕ) : swzAddr a % 16 = a % 16 := by
  rw [swzAddr_eq]
  split_ifs <;> omega

/-- The swizzle is its own inverse. -/
theorem swzAddr_swzAddr (a : ℕ) : swzAddr (swzAddr a) = a := by
  rw [swzAddr_eq (swzAddr a), swzAddr_eq a]
  split_ifs <;> omega

/-- The swizzle commutes with a move inside a 16-byte half. -/
theorem swzAddr_add {a i : ℕ} (h : a % 16 + i < 16) : swzAddr (a + i) = swzAddr a + i := by
  rw [swzAddr_eq (a + i), swzAddr_eq a]
  split_ifs <;> omega

/-- The offset from the buffer of the swizzled address of the buffer offset `o`. -/
theorem swzAddr_sub {base o : ℕ} (hb : base % 32 = 0) :
    base + 32768 ≤ swzAddr (base + 32768 + o) ∧
      (swzAddr (base + 32768 + o) - (base + 32768)) / 32 = o / 32 := by
  have := swzAddr_div (base + 32768 + o)
  omega

/-! ## The element index -/

/-- The element index of the entry of value channel `ch` and key feature `k`. -/
def elemOf (ch k : ℕ) : ℕ := 1024 * (k / 8) + 8 * ch + k % 8

/-- The value channel of element `e` (in the form of `Values.accInitByte`). -/
def chanOf (e : ℕ) : ℕ := 8 * (e / 64 % 16) + e / 8 % 8

/-- The key feature of element `e`. -/
def keyOf (e : ℕ) : ℕ := 8 * (e / 1024) + e % 8

theorem chanOf_lt (e : ℕ) : chanOf e < 128 := by
  unfold chanOf
  omega

theorem keyOf_lt {e : ℕ} (h : e < 16384) : keyOf e < 128 := by
  unfold keyOf
  omega

theorem elemOf_lt {ch k : ℕ} (hch : ch < 128) (hk : k < 128) : elemOf ch k < 16384 := by
  unfold elemOf
  omega

theorem chanOf_elemOf {ch k : ℕ} (hch : ch < 128) : chanOf (elemOf ch k) = ch := by
  unfold chanOf elemOf
  omega

theorem keyOf_elemOf {ch k : ℕ} (hch : ch < 128) : keyOf (elemOf ch k) = k := by
  unfold keyOf elemOf
  omega

/-- A state of one thread block: a real number per value channel and key feature. -/
abbrev State := Fin 128 → Fin 128 → ℝ

/-- **The entry of a state at an element index** (zero outside the array). -/
def entry (S : State) (e : ℕ) : ℝ :=
  if h : chanOf e < 128 ∧ keyOf e < 128 then S ⟨_, h.1⟩ ⟨_, h.2⟩ else 0

theorem entry_elemOf (S : State) (ch k : Fin 128) : entry S (elemOf ch k) = S ch k := by
  have hc := chanOf_elemOf (k := k.val) ch.isLt
  have hk := keyOf_elemOf (k := k.val) ch.isLt
  unfold entry
  have hcond : chanOf (elemOf ch k) < 128 ∧ keyOf (elemOf ch k) < 128 :=
    ⟨by rw [hc]; exact ch.isLt, by rw [hk]; exact k.isLt⟩
  simp only [hcond, and_self, ↓reduceDIte]
  congr 1 <;> exact Fin.ext (by assumption)

/-! ## The bytes of the two copies -/

/-- **The byte at offset `u` of an FP32 state in the unswizzled layout**: byte `u % 4` of the
binary32 payload of element `u / 4`. -/
def stateByte (S : State) (u : ℕ) : Option Byte :=
  if u < 65536 then some ((Value.float .f32 (entry S (u / 4))).byteAt (u % 4)) else none

/-- **The byte at offset `o` of the FP32 state buffer** (window offset `32768 + o`) of a block
whose shared memory starts at `base`, when the buffer holds the state `S` behind the swizzle. -/
def bufByte (base : ℕ) (S : State) (o : ℕ) : Option Byte :=
  stateByte S (swzAddr (base + 32768 + o) - (base + 32768))

/-- The initial state of the thread block `c` (sequence `c % N`, head `c / N`). -/
def initState (P : Params) (c : ℕ) : State := P.initial (c % P.sequences) (c / P.sequences)

/-- The state of the thread block `c` after the last token of its sequence. -/
def finalState (P : Params) (c : ℕ) : State :=
  fun v => P.state (c % P.sequences) (c / P.sequences) v (P.length (c % P.sequences))

/-- **The FP32 state buffer of block `c` after the sixteen loads of the initial state.** -/
def initBuf (P : Params) (L : Launch) (c : ℕ) : ℕ → Option Byte :=
  bufByte L.sharedBase (initState P c)

/-- **The FP32 state buffer of block `c` after the final stores of its compute threads.** -/
def finalBuf (P : Params) (L : Launch) (c : ℕ) : ℕ → Option Byte :=
  bufByte L.sharedBase (finalState P c)

/-- The four bytes of an element of the buffer: at the swizzled address of the element, the
buffer holds the bytes of its payload. -/
theorem bufByte_elem {base : ℕ} (S : State) (hb : base % 32 = 0) {e i : ℕ} (he : e < 16384)
    (hi : i < 4) :
    bufByte base S (swzAddr (base + 32768 + 4 * e) - (base + 32768) + i) =
      some ((Value.float .f32 (entry S e)).byteAt i) := by
  have h1 := (swzAddr_sub (o := 4 * e) hb).1
  have h2 := swzAddr_mod (base + 32768 + 4 * e)
  have h3 : base + 32768 + (swzAddr (base + 32768 + 4 * e) - (base + 32768) + i) =
      swzAddr (base + 32768 + 4 * e) + i := by omega
  unfold bufByte
  rw [h3, swzAddr_add (by omega), swzAddr_swzAddr]
  have h5 : base + 32768 + 4 * e + i - (base + 32768) = 4 * e + i := by omega
  have h8 : 4 * e + i < 65536 := by omega
  rw [h5, stateByte]
  simp only [h8, ↓reduceIte]
  have h6 : (4 * e + i) / 4 = e := by omega
  have h7 : (4 * e + i) % 4 = i := by omega
  rw [h6, h7]

/-- The content of `state_acc` after the conversion loop, by element. -/
theorem accInitByte_elem (P : Params) (s h : ℕ) {e i : ℕ} (he : e < 16384) (hi : i < 2) :
    accInitByte P s h (2 * e + i) =
      some ((Value.float .bf16 (entry (P.initial s h) e)).byteAt i) := by
  have h1 : (2 * e + i) / 2 = e := by omega
  have h2 : (2 * e + i) % 2 = i := by omega
  have hk := keyOf_lt he
  have hc := chanOf_lt e
  unfold accInitByte
  simp only [h1, h2]
  have hcond : 8 * (e / 64 % 16) + e / 8 % 8 < 128 ∧ 8 * (e / 1024) + e % 8 < 128 := ⟨hc, hk⟩
  have hcond' : chanOf e < 128 ∧ keyOf e < 128 := ⟨hc, hk⟩
  unfold entry
  simp only [hcond, hcond', and_self, ↓reduceDIte]
  rfl

/-! ## The carries -/

/-- Entry `j` of the table of the carries. -/
def carryRow (j : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ := Gen.carryTable.getD j (0, 0, 0, 0, 0, 0)

/-- The register of the `j`-th carry. -/
def carryReg (j : ℕ) : ℕ := (carryRow j).1

/-- The constant the load and the store of the `j`-th carry add to the base pointer. -/
def carryConst (j : ℕ) : ℕ := (carryRow j).2.2.2.2.2

/-- The key feature of the `j`-th carry of the thread with index `tid` in its block. -/
def carryKey (j tid : ℕ) : ℕ := 16 * (carryRow j).2.1 + cRow (tid % 32) (carryRow j).2.2.2.2.1

/-- The value channel of the `j`-th carry of the thread with index `tid`. -/
def carryChan (j tid : ℕ) : ℕ :=
  halfBase (tid / 32) (carryRow j).2.2.1 (carryRow j).2.2.2.1 +
    cCol (tid % 32) (carryRow j).2.2.2.2.1

/-- The element index of the `j`-th carry of the thread with index `tid`. -/
def carryElem (j tid : ℕ) : ℕ := elemOf (carryChan j tid) (carryKey j tid)

/-- The offset of a compute thread's base pointer from `shared_mem`, in 4-byte entries:
`16 (lane % 4) + lane / 4 + 256 warp`. -/
def laneOff (tid : ℕ) : ℕ := 16 * (tid % 4) + tid % 32 / 4 + 256 * (tid / 32)

/-- Every row of the table is in range, and its constant is that of its entry. -/
theorem carryTable_ok : Gen.carryTable.all (fun p =>
    decide (p.2.1 < 8 ∧ p.2.2.1 < 2 ∧ p.2.2.2.1 < 2 ∧ p.2.2.2.2.1 < 4 ∧
      p.2.2.2.2.2 = 32768 + 4 * (2048 * p.2.1 + 1024 * (p.2.2.2.2.1 / 2) + 128 * p.2.2.1 +
        64 * p.2.2.2.1 + 8 * (p.2.2.2.2.1 % 2)) ∧ 2118 ≤ p.1 ∧ p.1 < 2246)) = true := by
  decide +kernel

theorem carryTable_length : Gen.carryTable.length = 128 := by decide +kernel

/-- The carry registers are distinct. -/
theorem carryReg_inj : ∀ i < 128, ∀ j < 128, carryReg i = carryReg j → i = j := by
  decide +kernel

theorem carryRow_ok {j : ℕ} (hj : j < 128) :
    (carryRow j).2.1 < 8 ∧ (carryRow j).2.2.1 < 2 ∧ (carryRow j).2.2.2.1 < 2 ∧
      (carryRow j).2.2.2.2.1 < 4 ∧
      carryConst j = 32768 + 4 * (2048 * (carryRow j).2.1 + 1024 * ((carryRow j).2.2.2.2.1 / 2) +
        128 * (carryRow j).2.2.1 + 64 * (carryRow j).2.2.2.1 + 8 * ((carryRow j).2.2.2.2.1 % 2)) ∧
      2118 ≤ carryReg j ∧ carryReg j < 2246 := by
  have hm : carryRow j ∈ Gen.carryTable := by
    unfold carryRow
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [carryTable_length]; exact hj), Option.getD_some]
    exact List.getElem_mem _
  simpa [carryConst, carryReg] using List.all_eq_true.mp carryTable_ok _ hm

theorem carryKey_lt {j tid : ℕ} (hj : j < 128) : carryKey j tid < 128 := by
  obtain ⟨h1, -, -, h4, -⟩ := carryRow_ok hj
  unfold carryKey cRow
  omega

theorem carryChan_lt {j tid : ℕ} (hj : j < 128) (ht : tid < 128) : carryChan j tid < 128 := by
  obtain ⟨-, h2, h3, h4, -⟩ := carryRow_ok hj
  have ht' : tid / 32 < 4 := Nat.div_lt_of_lt_mul ht
  unfold carryChan cCol halfBase
  omega

theorem carryElem_lt {j tid : ℕ} (hj : j < 128) (ht : tid < 128) : carryElem j tid < 16384 :=
  elemOf_lt (carryChan_lt hj ht) (carryKey_lt hj)

/-- **The address of a carry, two ways**: the base pointer of the thread plus the constant of
the instruction is the buffer offset of the carry's element. -/
theorem carry_addr {j : ℕ} (tid : ℕ) (hj : j < 128) :
    4 * laneOff tid + carryConst j = 32768 + 4 * carryElem j tid := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := carryRow_ok hj
  rw [h5]
  unfold carryElem elemOf carryKey carryChan laneOff cRow cCol halfBase
  omega

/-- **The site of the `j`-th carry load**, and for `j = 128` the site after the last of them
(the proxy fence at instruction 1401). -/
def carrySite (j : ℕ) : Site := if h : j < 128 then .load ⟨31 + j, by omega⟩ else .fenceProxy 1

/-- **The carry registers of a compute thread hold the state `S`**: each of the 128 registers
holds the binary32 payload of its entry. -/
def CarriesHold (S : State) (tid : ℕ) (val : ℕ → Value) : Prop :=
  ∀ j < 128, val (carryReg j) = .float .f32 (entry S (carryElem j tid))

end

end PTX.Kernels.FlashKdaFwd.Proof.Values.Ends
