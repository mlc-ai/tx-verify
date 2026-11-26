-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Compute.Reach
public import Kernels.FlashKdaFwd.Proof.Ref.Kinds
public import Kernels.FlashKdaFwd.Proof.Values.Contract

@[expose] public section

/-! # The Compute phase: the memory accesses by position, in the value layer's forms

Tools for `ExportsValues.lean` (the exports of the Compute phase to the value layer's contract
`Values.ComputeRef` and to the frame fields of `Top.DirectFacts`). The core of the phase
(`Access.lean`) has one lemma per accessing position of a tile (`acc_<n>`: the event is the read
or the write of a stated footprint). This file puts them in one statement and compares the
footprints with the address forms of the value layer.

**Words.** A *position* `n < 268` is an index in the straight line of the 268 events of one
tile of a compute thread (`Inv.lean`); `skOf n` is the kind of its site. A position is
*accessing* when its event reads or writes memory: the row read of an `ldmatrix` (44
positions), the row write of an `stmatrix` (18) and a scalar load (18); `accPos` lists the 80 of
them. The *window* of a block is its shared memory, which starts at the address
`S = P.sharedBase`. `tid g` is the index of thread `g` in its block (below 128 for a compute
thread).

* `kindOf`, `siteOf`: the kind (`SiteKind`, of `Ref/Kinds`) and one site (hence the
  instruction index) of the sites of a kind `SK` of the phase; `kind_of_at`, `pc_of_at`.
* `accPos`, `acc_of_kind`: the accessing positions are the positions whose site is a read or a
  write.
* `AccEv`, `access_at`: **the event at an accessing position**: at the instruction of the
  site, the read (or, at a row write, the write of the bytes carried by the site) of `sz` bytes
  at the address `regVal P g t r + c` in the window of the thread's own block, where
  `(r, c, sz)` is the position's entry of the core's table `addrTab`.
* `addr_frame`: that footprint lies in the first 95104 bytes of the window (the bfloat16 state
  copy, the three input stages and the two output stages).
* `Form`, `Form.val`: an address of the tile loop as the value layer writes it: `S + c +
  s * (t % 3) + o * (t % 2) + k * gate + bits`, where `t` is the tile, `t % 3` its input stage,
  `t % 2` its output stage, `gate` the position of the tile's first gate logit in its buffer
  (`gate P g`) and `bits` a sum of weights over the set bits of the thread index
  (`Values.bitsOff`). `regForms` gives the form of each of the 48 address registers and
  `regForms_ok` proves it against the core's closed forms (`regVal`); `posForm n` is the form
  and the size of the access at position `n`, and `posForm_val` its correctness.
* `ld_table`, `st_table`, `sc_table`: the forms of the positions are the entries of the value
  layer's generated tables `Values.Gen.loadForms` (the `j`-th `ldmatrix`), `storeForms` (the
  `j`-th `stmatrix`) and `scalarForms` (the scalar load at an instruction index). Both sides
  come from `Gen/Tables/matrix_table.json`; the kernel of Lean compares them here.

Abbreviations: `S = P.sharedBase`; `%rN` is register `306 + N` of the thread machine. The
declarations are in the namespace `Ref.Compute.Vals`, apart from those of the other export
files of the phase. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute.Vals
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {g t : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
  {tt : TState} {ins : Instr} {e : Event} {o : Option TState}

/-! ### The kind and the instruction of a site of the phase -/

/-- The kind (`SiteKind`, the constructor of the site) of the sites of kind `k`. -/
def kindOf : SK → SiteKind
  | .wait _ => .mbarWait
  | .ld _ => .matrixLoad
  | .ldMx _ => .matrixLoadMx
  | .mma _ => .warpMma
  | .mv _ => .matrixMove
  | .st _ => .matrixStore
  | .stWr _ => .matrixStoreWr
  | .load _ => .load
  | .bar _ => .bar
  | .fence _ => .fenceProxy
  | .arrive _ => .mbarArrive

/-- One site of kind `k`: for the two kinds whose sites carry the bytes of the instruction's
first event, the site that carries none. All sites of a kind are at one instruction. -/
def siteOf : SK → Site
  | .wait j => .mbarWait j
  | .ld j => .matrixLoad j
  | .ldMx j => .matrixLoadMx j []
  | .mma j => .warpMma j
  | .mv j => .matrixMove j
  | .st j => .matrixStore j
  | .stWr j => .matrixStoreWr j []
  | .load j => .load j
  | .bar j => .bar j
  | .fence j => .fenceProxy j
  | .arrive j => .mbarArrive j

/-- A site of kind `k` has the kind `kindOf k`. -/
theorem kind_of_at {k : SK} {s : Site} (h : k.At s) : s.kind = kindOf k := by
  cases k <;> simp only [SK.At] at h <;> first
    | (subst h; rfl)
    | (obtain ⟨row, rfl⟩ := h; rfl)

/-- A site of kind `k` is at the instruction of `siteOf k`. -/
theorem pc_of_at {k : SK} {s : Site} (h : k.At s) : s.pc = (siteOf k).pc := by
  cases k <;> simp only [SK.At] at h <;> first
    | (subst h; rfl)
    | (obtain ⟨row, rfl⟩ := h; rfl)

/-! ### The accessing positions -/

/-- The 80 accessing positions of a tile: the row reads of the 44 `ldmatrix`, the row writes of
the 18 `stmatrix` and the 18 scalar loads. -/
def accPos : List Nat :=
  [2, 4, 6, 8, 14, 16, 18, 24, 30, 32, 34, 40, 46, 48, 50, 56, 62, 64, 66, 72, 78, 80, 82, 88, 94,
   96, 98, 104, 110, 112, 114, 120, 130, 132, 134, 136, 137, 150, 165, 167, 168, 170, 171, 176,
   178, 179, 181, 183, 188, 190, 191, 193, 195, 200, 202, 203, 205, 207, 212, 214, 215, 217, 219,
   224, 226, 227, 229, 231, 236, 238, 239, 241, 243, 248, 250, 251, 253, 255, 261, 263]

/-- The kinds of sites that fire a memory read, a memory write or a tensor copy. -/
def accKinds : List SiteKind :=
  [.load, .loadEl1, .loadEl2, .loadEl3, .matrixLoad, .store, .matrixStoreWr, .tensorCopy]

/-- The sites of the three kinds of accessing positions are in `accKinds`. -/
theorem ld_acc : SiteKind.matrixLoad ∈ accKinds := by decide
theorem stWr_acc : SiteKind.matrixStoreWr ∈ accKinds := by decide
theorem load_acc : SiteKind.load ∈ accKinds := by decide

/-- **A position whose site reads or writes memory is an accessing position.** -/
theorem acc_of_kind : ∀ n < 268, kindOf (skOf n) ∈ accKinds → n ∈ accPos := by decide +kernel

/-- An accessing position is a position of a tile. -/
theorem accPos_lt : ∀ n ∈ accPos, n < 268 := by decide +kernel

/-- **The event of an accessing position** `n` of tile `t`, at the site `site`: at the
instruction of the site, a read of the footprint that the position's entry `(r, c, sz)` of
`addrTab` names (`sz` bytes at `regVal P g t r + c` in the window of the thread's own block)
at a position that is no row write, or, at the second event of an `stmatrix`, the write of that
footprint with the bytes the site carries. -/
def AccEv (P : Params) (L : Launch) (g t n : Nat) (site : Site) (e : Event) : Prop :=
  ∃ r c sz, addrTab[n]? = some (r, c, sz) ∧ e.pc = site.pc ∧
    ((∃ bs, kindOf (skOf n) ≠ .matrixStoreWr ∧ e.kind =
        .rd { loc := ⟨.shared, g / L.block, regVal P g t r + c⟩, size := sz } bs) ∨
      ∃ j row, site = .matrixStoreWr j row ∧ e.kind =
        .wr { loc := ⟨.shared, g / L.block, regVal P g t r + c⟩, size := sz } row.reduceOption)

set_option hygiene false in
/-- An accessing position with a read, from its lemma of `Access.lean`. -/
local macro "acc_rd " lem:ident : tactic => `(tactic| (
  obtain rfl : site = _ := hs
  obtain ⟨bs, rfl⟩ := $lem hpre h hat hc hf
  exact ⟨_, _, _, rfl, rfl, .inl ⟨bs, by decide, rfl⟩⟩))

set_option hygiene false in
/-- An accessing position with a write, from its lemma of `Access.lean`. -/
local macro "acc_wr " lem:ident : tactic => `(tactic| (
  obtain ⟨row, rfl⟩ : ∃ row, site = .matrixStoreWr _ row := hs
  obtain rfl := $lem hpre h hat hc hf
  exact ⟨_, _, _, rfl, rfl, .inr ⟨_, row, rfl, rfl⟩⟩))

/-- **The event at an accessing position**, from the facts of the position, the concrete state
and the firing fact of the site's instruction: the 80 lemmas `acc_<n>` in one statement. -/
theorem access_at (hpre : Pre P L mem0) {n : Nat} {site : Site} (h : Tile P L g t n w p x)
    (hs : (skOf n).At site) (hat : (code L g).AtD ⟨site, w, p, x⟩ tt)
    (hc : kernel.code[site.pc]? = some ins)
    (hf : Fires site.pc (eventTmpl Assumptions.all L g tt ins.op) e o) (hn : n ∈ accPos) :
    AccEv P L g t n site e := by
  simp only [accPos, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · acc_rd acc_2
  · acc_rd acc_4
  · acc_rd acc_6
  · acc_rd acc_8
  · acc_rd acc_14
  · acc_rd acc_16
  · acc_rd acc_18
  · acc_rd acc_24
  · acc_rd acc_30
  · acc_rd acc_32
  · acc_rd acc_34
  · acc_rd acc_40
  · acc_rd acc_46
  · acc_rd acc_48
  · acc_rd acc_50
  · acc_rd acc_56
  · acc_rd acc_62
  · acc_rd acc_64
  · acc_rd acc_66
  · acc_rd acc_72
  · acc_rd acc_78
  · acc_rd acc_80
  · acc_rd acc_82
  · acc_rd acc_88
  · acc_rd acc_94
  · acc_rd acc_96
  · acc_rd acc_98
  · acc_rd acc_104
  · acc_rd acc_110
  · acc_rd acc_112
  · acc_rd acc_114
  · acc_rd acc_120
  · acc_rd acc_130
  · acc_rd acc_132
  · acc_rd acc_134
  · acc_rd acc_136
  · acc_rd acc_137
  · acc_rd acc_150
  · acc_wr acc_165
  · acc_wr acc_167
  · acc_rd acc_168
  · acc_rd acc_170
  · acc_rd acc_171
  · acc_rd acc_176
  · acc_rd acc_178
  · acc_rd acc_179
  · acc_wr acc_181
  · acc_wr acc_183
  · acc_rd acc_188
  · acc_rd acc_190
  · acc_rd acc_191
  · acc_wr acc_193
  · acc_wr acc_195
  · acc_rd acc_200
  · acc_rd acc_202
  · acc_rd acc_203
  · acc_wr acc_205
  · acc_wr acc_207
  · acc_rd acc_212
  · acc_rd acc_214
  · acc_rd acc_215
  · acc_wr acc_217
  · acc_wr acc_219
  · acc_rd acc_224
  · acc_rd acc_226
  · acc_rd acc_227
  · acc_wr acc_229
  · acc_wr acc_231
  · acc_rd acc_236
  · acc_rd acc_238
  · acc_rd acc_239
  · acc_wr acc_241
  · acc_wr acc_243
  · acc_rd acc_248
  · acc_rd acc_250
  · acc_rd acc_251
  · acc_wr acc_253
  · acc_wr acc_255
  · acc_wr acc_261
  · acc_wr acc_263

/-! ### The footprint lies in the data part of the window -/

/-- The class of the address of each accessing position: a row of 16 bytes at a register of
the bfloat16 state copy, of the input stage or of the output stage; a gate logit (2 bytes at
`%r1642` plus 36864 or 36880); a decay factor (4 bytes at `%r1708` plus a multiple of 4 from
49280 to 49760). -/
theorem addr_class : ∀ n ∈ accPos,
    ((addrTab.getD n (0, 0, 0)).2.1 = 0 ∧ (addrTab.getD n (0, 0, 0)).2.2 = 16 ∧
      ((addrTab.getD n (0, 0, 0)).1 ∈ accRegs ∨ (addrTab.getD n (0, 0, 0)).1 ∈ inRegs ∨
        (addrTab.getD n (0, 0, 0)).1 ∈ outRegs)) ∨
    ((addrTab.getD n (0, 0, 0)).1 = 1948 ∧
      ((addrTab.getD n (0, 0, 0)).2.1 = 36864 ∨ (addrTab.getD n (0, 0, 0)).2.1 = 36880) ∧
      (addrTab.getD n (0, 0, 0)).2.2 = 2) ∨
    ((addrTab.getD n (0, 0, 0)).1 = 2014 ∧ 49280 ≤ (addrTab.getD n (0, 0, 0)).2.1 ∧
      (addrTab.getD n (0, 0, 0)).2.1 ≤ 49760 ∧ (addrTab.getD n (0, 0, 0)).2.1 % 4 = 0 ∧
      (addrTab.getD n (0, 0, 0)).2.2 = 4) := by
  decide +kernel

/-- **The footprint of an accessing position lies in the first 95104 bytes of the window** of
the block: the bfloat16 state copy (bytes 0 to 32767), the three input stages (32768 to 86911)
and the two output stages (86912 to 95103). The eleven mbarriers are at 98304 and above. -/
theorem addr_frame (hpre : Pre P L mem0) (hc : tid g < 128) {n r c sz : Nat} (hn : n ∈ accPos)
    (ha : addrTab[n]? = some (r, c, sz)) :
    P.sharedBase ≤ regVal P g t r + c ∧ regVal P g t r + c + sz ≤ P.sharedBase + 95104 := by
  have h := addr_class n hn
  have hd : addrTab.getD n (0, 0, 0) = (r, c, sz) := by
    rw [List.getD_eq_getElem?_getD, ha]
    rfl
  simp only [hd] at h
  have b3 : t % 3 < 3 := Nat.mod_lt _ (by decide)
  have b2 : t % 2 < 2 := Nat.mod_lt _ (by decide)
  rcases h with ⟨rfl, rfl, hr | hr | hr⟩ | ⟨rfl, hcc, rfl⟩ | ⟨rfl, h1, h2, h3, rfl⟩
  · have := acc_addr hpre hc (t := t) hr
    omega
  · have := in_addr hpre hc (t := t) hr
    omega
  · have := out_addr hpre hc (t := t) hr
    omega
  · have := gate_addr hpre hc (t := t) hcc
    omega
  · have := decay_addr hpre hc (t := t) h1 h2 h3
    omega

/-! ### The addresses in the value layer's form -/

/-- **The form of a shared address of the tile loop**: the address is
`S + c + s * (t % 3) + o * (t % 2) + k * gate + bits`, with `t` the tile, `gate` the position
of the tile's first gate logit in its buffer, and `bits` the sum of the weights `ws` over the
set bits of the thread's index in its block. -/
structure Form where
  /-- The constant offset from the start of the window. -/
  c : Nat
  /-- The coefficient of the input stage `t % 3` (18048, the size of an input stage, or 0). -/
  s : Nat
  /-- The coefficient of the output stage `t % 2` (4096, the size of an output stage, or 0). -/
  o : Nat
  /-- The coefficient of the gate position (2 for the gate logits, else 0). -/
  k : Nat
  /-- The weights of the seven bits of the thread index. -/
  ws : List Nat
  deriving DecidableEq

/-- The address of a form, for tile `t` of thread `g`. -/
def Form.val (f : Form) (P : Params) (g t : Nat) : Nat :=
  P.sharedBase +
    (f.c + f.s * (t % 3) + f.o * (t % 2) + f.k * gate P g + Values.bitsOff f.ws (tid g))

/-- The weights of the lane's row in a 512-byte piece of an input array: `16 * lane`. -/
def wLane : List Nat := [16, 32, 64, 128, 256, 0, 0]
/-- The weights of the lane's row in the warp's part of `v` and of the output stage. -/
def wWarp : List Nat := [16, 32, 64, 128, 256, 1024, 2048]
/-- The weights of the lane's first row of the bfloat16 state copy. -/
def wAcc : List Nat := [16, 32, 64, 2048, 128, 512, 1024]
/-- The weights of the lane's row of a piece of `k_restored` (read transposed). -/
def wKr : List Nat := [16, 32, 64, 256, 128, 0, 0]
/-- The weights of the lane's pair of gate logits. -/
def wGate : List Nat := [0, 0, 2, 4, 8, 0, 0]
/-- The weights of the lane's entry of the FP32 decay factors. -/
def wDecay : List Nat := [0, 0, 4, 8, 16, 0, 0]

/-! The sum of each list of weights over the bits of a thread index below 128, in the form of
the core's offsets (`laneOff`, `warpOff`, `accOff`, `krOff`, `gateOff`, `gtOff`). -/

theorem bits_lane : ∀ x < 128, Values.bitsOff wLane x = 16 * (x % 32) := by decide +kernel
theorem bits_warp : ∀ x < 128, Values.bitsOff wWarp x = 1024 * (x / 32) + 16 * (x % 32) := by
  decide +kernel
theorem bits_acc : ∀ x < 128, Values.bitsOff wAcc x =
    512 * (x / 32) + 16 * (x % 8) + 128 * (x / 16 % 2) + 2048 * (x / 8 % 2) := by
  decide +kernel
theorem bits_kr : ∀ x < 128, Values.bitsOff wKr x =
    16 * (x % 8) + 256 * (x / 8 % 2) + 128 * (x / 16 % 2) := by
  decide +kernel
theorem bits_gate : ∀ x < 128, Values.bitsOff wGate x = 2 * (x / 4 % 8) := by decide +kernel
theorem bits_decay : ∀ x < 128, Values.bitsOff wDecay x = 4 * (x / 4 % 8) := by decide +kernel

/-- **The form of each address register of the tile loop** (48 registers: the sixteen rows of
the bfloat16 state copy, the 28 rows of the input stage, the two rows of the output stage, the
base of the gate logits `%r1642` and the base of the decay factors `%r1708`). -/
def regForms : List (Nat × Form) :=
  [(1160, ⟨0, 0, 0, 0, wAcc⟩), (1916, ⟨28928, 0, 0, 0, wAcc⟩), (1887, ⟨24832, 0, 0, 0, wAcc⟩),
   (1857, ⟨20736, 0, 0, 0, wAcc⟩), (1827, ⟨16640, 0, 0, 0, wAcc⟩), (1797, ⟨12544, 0, 0, 0, wAcc⟩),
   (1767, ⟨8448, 0, 0, 0, wAcc⟩), (1737, ⟨4352, 0, 0, 0, wAcc⟩), (1467, ⟨28672, 0, 0, 0, wAcc⟩),
   (1416, ⟨24576, 0, 0, 0, wAcc⟩), (1365, ⟨20480, 0, 0, 0, wAcc⟩), (1314, ⟨16384, 0, 0, 0, wAcc⟩),
   (1263, ⟨12288, 0, 0, 0, wAcc⟩), (1212, ⟨8192, 0, 0, 0, wAcc⟩), (1177, ⟨4096, 0, 0, 0, wAcc⟩),
   (1161, ⟨256, 0, 0, 0, wAcc⟩), (1158, ⟨36992, 18048, 0, 0, wLane⟩),
   (1159, ⟨41088, 18048, 0, 0, wLane⟩), (1175, ⟨37504, 18048, 0, 0, wLane⟩),
   (1176, ⟨41600, 18048, 0, 0, wLane⟩), (1210, ⟨38016, 18048, 0, 0, wLane⟩),
   (1211, ⟨42112, 18048, 0, 0, wLane⟩), (1261, ⟨38528, 18048, 0, 0, wLane⟩),
   (1262, ⟨42624, 18048, 0, 0, wLane⟩), (1312, ⟨39040, 18048, 0, 0, wLane⟩),
   (1313, ⟨43136, 18048, 0, 0, wLane⟩), (1363, ⟨39552, 18048, 0, 0, wLane⟩),
   (1364, ⟨43648, 18048, 0, 0, wLane⟩), (1414, ⟨40064, 18048, 0, 0, wLane⟩),
   (1415, ⟨44160, 18048, 0, 0, wLane⟩), (1465, ⟨40576, 18048, 0, 0, wLane⟩),
   (1466, ⟨44672, 18048, 0, 0, wLane⟩), (1556, ⟨32768, 18048, 0, 0, wWarp⟩),
   (1561, ⟨33280, 18048, 0, 0, wWarp⟩), (1562, ⟨49792, 18048, 0, 0, wLane⟩),
   (1948, ⟨0, 18048, 0, 2, wGate⟩), (1619, ⟨50304, 18048, 0, 0, wLane⟩),
   (1672, ⟨86912, 0, 4096, 0, wWarp⟩), (1677, ⟨87424, 0, 4096, 0, wWarp⟩),
   (1682, ⟨45184, 18048, 0, 0, wKr⟩), (2014, ⟨0, 18048, 0, 0, wDecay⟩),
   (1703, ⟨45696, 18048, 0, 0, wKr⟩), (1732, ⟨46208, 18048, 0, 0, wKr⟩),
   (1762, ⟨46720, 18048, 0, 0, wKr⟩), (1792, ⟨47232, 18048, 0, 0, wKr⟩),
   (1822, ⟨47744, 18048, 0, 0, wKr⟩), (1852, ⟨48256, 18048, 0, 0, wKr⟩),
   (1882, ⟨48768, 18048, 0, 0, wKr⟩)]

/-- **The registers hold the addresses of their forms**: the closed form `regVal` of each
address register is the value of its form, for a compute thread. -/
theorem regForms_ok (hc : tid g < 128) : ∀ q ∈ regForms, regVal P g t q.1 = q.2.val P g t := by
  have h1 := bits_lane (tid g) hc
  have h2 := bits_warp (tid g) hc
  have h3 := bits_acc (tid g) hc
  have h4 := bits_kr (tid g) hc
  have h5 := bits_gate (tid g) hc
  have h6 := bits_decay (tid g) hc
  simp only [regForms, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  all_goals
    rv_simp
    simp only [Form.val, h1, h2, h3, h4, h5, h6, laneOff, warpOff, accOff, krOff, gtOff, gateOff]
    omega

/-- The form of the address register `r` (none for a register that holds no address). -/
def regForm (r : Nat) : Option Form := (regForms.find? fun q => q.1 == r).map (·.2)

/-- **The form and the size of the access at position `n`**: the form of the position's
address register with the instruction's constant added, and the number of bytes (none for a
position without an access). -/
def posForm (n : Nat) : Option (Form × Nat) :=
  match addrTab[n]? with
  | some (r, c, sz) => (regForm r).map fun f => ({ f with c := f.c + c }, sz)
  | none => none

/-- **The address of the access at a position is the value of the position's form.** -/
theorem posForm_val (hc : tid g < 128) {n r c sz sz' : Nat} {f : Form}
    (ha : addrTab[n]? = some (r, c, sz)) (hf : posForm n = some (f, sz')) :
    sz = sz' ∧ regVal P g t r + c = f.val P g t := by
  simp only [posForm, ha, regForm, Option.map_eq_some_iff, Prod.mk.injEq] at hf
  obtain ⟨f0, ⟨q, hq, rfl⟩, rfl, rfl⟩ := hf
  have hm := List.mem_of_find?_eq_some hq
  have hr : q.1 = r := by simpa using List.find?_some hq
  have hv := regForms_ok (P := P) (t := t) hc q hm
  rw [hr] at hv
  refine ⟨rfl, ?_⟩
  rw [hv]
  simp only [Form.val]
  omega

/-! ### The value layer's tables -/

/-- **The row read of the `j`-th `ldmatrix`** has the form of the `j`-th entry of the value
layer's `loadForms` (constant, coefficient of the input stage, weights) and 16 bytes. -/
theorem ld_table : ∀ j : Fin 44, posForm (skTab.idxOf (.ld j)) =
    (Values.Gen.loadForms[j.val]?).map fun q => (⟨q.1, q.2.1, 0, 0, q.2.2⟩, 16) := by
  decide +kernel

/-- **The row write of the `j`-th `stmatrix`** has the form of the `j`-th entry of the value
layer's `storeForms` (constant, coefficient of the output stage, weights) and 16 bytes. -/
theorem st_table : ∀ j : Fin 18, posForm (skTab.idxOf (.stWr j)) =
    (Values.Gen.storeForms[j.val]?).map fun q => (⟨q.1, 0, q.2.1, 0, q.2.2⟩, 16) := by
  decide +kernel

/-- **The scalar loads**: a position whose site is at the instruction of an entry
`(pc, sz, c, ck, ws)` of the value layer's `scalarForms` is a scalar load with the entry's
form (the coefficient of the input stage is 18048) and size. -/
theorem sc_table : ∀ q ∈ Values.Gen.scalarForms, ∀ n < 268, (siteOf (skOf n)).pc = q.1 →
    kindOf (skOf n) = .load ∧
      posForm n = some (⟨q.2.2.1, 18048, 0, q.2.2.2.1, q.2.2.2.2⟩, q.2.1) := by
  decide +kernel

/-- No entry of `scalarForms` is at the instruction of the phase's entry (`bar_5`). -/
theorem sc_entry : ∀ q ∈ Values.Gen.scalarForms, q.1 ≠ (Site.bar 5).pc := by decide +kernel

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute.Vals
