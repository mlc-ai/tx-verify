-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Spec
public import Kernels.TcGemm.Flow.Sites
public import Kernels.TcGemm.Flow.Code
public import Lemmas.Flow.Code
public import Lemmas.Flow.Facts
public import Lemmas.Tcgen05.TcCommit

@[expose] public section

/-! # `tc_gemm`: the sites of a thread and its code machine

Warp 0 allocates the Tensor Memory columns (`alloc`); its lane 0, thread 0, stores the returned
address (`allocSt`), initializes the two mbarriers, fences, arms `bar0` and issues the two bulk
copies. Every thread passes the first barrier (`bar0`), reads the address back (`load`) and keeps
its column `c` (`rdCol`): thread 0 then polls `bar0`, issues the MMA and commits it to `bar1`;
every thread polls `bar1`, fences, loads its row of the result (`ld`, the words `vals`), waits
for the load and stores the eight words (`st j`), fences, passes the second barrier and fences;
warp 0 frees the columns (`dealloc`); every thread exits.

The flag of `bar0` and `load` says whether the thread holds thread 0's issue registers. A read
whose bytes give no column, and a store of a word that is not four bytes, stop the machine. The
register facts at each site are the generated live registers (`liveAt`, without thread 0's issue
registers where the thread has none) valued by one table (`values`). -/

namespace PTX.Kernels.TcGemm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-! ### Locations, descriptors and the MMA -/

def tslot (S : Nat) : Loc := ⟨.shared, 0, S + 4368⟩
def bar0 (S : Nat) : Loc := ⟨.shared, 0, S + 4352⟩
def bar1 (S : Nat) : Loc := ⟨.shared, 0, S + 4360⟩
def sA (S : Nat) : Loc := ⟨.shared, 0, S⟩
def sB (S : Nat) : Loc := ⟨.shared, 0, S + 4096⟩
def gA (A : Nat) : Loc := ⟨.global, 0, A⟩
def gB (B : Nat) : Loc := ⟨.global, 0, B⟩
/-- Row `g` of `D`. -/
def gD (D g : Nat) : Loc := ⟨.global, 0, D + 32 * g⟩

/-- The K-major, unswizzled shared descriptors of `A` and `B`. -/
def descA (S : Nat) : TcShared.Descriptor := ⟨S, 128, 256, 0, false, false, .none⟩
def descB (S : Nat) : TcShared.Descriptor := ⟨S + 4096, 128, 256, 0, false, false, .none⟩
/-- `tcgen05.mma.cta_group::1.kind::i8`, signed, 128 x 8. -/
def mmaDesc : TcMma.Descriptor :=
  ⟨.one, .i8 true true false, 128, 8, false, false, false, false, false⟩
def mmaSpec (S : Nat) : TcMma.OperandSpec :=
  { descriptor := mmaDesc, a := descA S, b := descB S, lowCta := 0, highCta := 0, aTmem := none }
def mmaMask : List Nat := [0, 0, 0, 0]
/-- The unmasked group-1 commit of the single-CTA cluster targets `bar1` only. -/
def commitSpec (S : Nat) : TcCommit.Spec := TcCommit.unicast (bar1 S)

/-- The Tensor Memory address thread `g`'s warp loads from, for an allocation at column `c`. -/
def taddr (g c : Nat) : Nat := c + g / 32 * 2097152

/-- Word `j` of a load. -/
def word (vals : List Value) (j : Nat) : Value := vals.getD j (b32 0)

/-- A 32-bit store of `v` writes: `storeValue` accepts it. -/
def StoreOk (v : Value) : Prop := ∃ v', storeValue 32 v = .ok v'

/-- The bytes a 32-bit store of `v` writes (none when it faults). -/
def stBytes (v : Value) : List Byte :=
  match storeValue 32 v with
  | .ok v' => v'.toBytes
  | .error _ => []

theorem storeOk_of_bytes {v : Value} (h : v.bytes = 4) : StoreOk v :=
  ⟨v, storeValue_of_bytes (by rw [h])⟩

theorem stBytes_of_bytes {v : Value} (h : v.bytes = 4) : stBytes v = v.toBytes := by
  rw [stBytes, storeValue_of_bytes (by rw [h])]

/-- The bits an integer instruction reads from a register holding `v`, before truncation. -/
def wordOf : Value → Option (BitVec 64)
  | .bits _ x => some x
  | .ptr .. => none
  | v => v.bitPattern.map (BitVec.ofNat 64)

/-- The low 16 bits of a 32-bit word (what `and.b32 %r8, %r8, 65535` computes). -/
def mask16 (x : BitVec 64) : BitVec 64 := truncBits 32 x &&& truncBits 32 (BitVec.ofInt 64 65535)

/-- The column a read of the address gives, if its bytes are one word. -/
def rdCol (bs : List (Option Byte)) : Option Nat :=
  match rebuild 3 bs with
  | .ok v => (wordOf v).map fun x => (mask16 x).toNat
  | .error _ => none

/-- The access of store `j` of row `g`: element `j % 4` of the vector store at `16 (j / 4)`. -/
def stAcc (D g j : Nat) : Acc :=
    { loc := ⟨.global, 0, D + 32 * g + 4 * j⟩, size := 4, elem := j % 4 }

/-! ### Sites -/

/-- The event instructions of a thread. -/
inductive Site where
  | alloc | allocSt | init0 | init1 | fence | arrive | bulkA | bulkB
  /-- The first barrier; `z`: the thread holds thread 0's issue registers. -/
  | bar0 (z : Bool)
  /-- The read of the address; `z` as for `bar0`. -/
  | load (z : Bool)
  | wait0 | mma | commit | wait1 | fence1 | ld | waitLd
  /-- Store `j` of the eight words of the row. -/
  | st (j : Nat)
  | fenceB | bar1 | fence2 | dealloc | exit
  deriving DecidableEq

def Site.pc : Site → Nat
  | .alloc | .allocSt => Flow.tmemAlloc_0
  | .init0 => Flow.mbarInit_0 | .init1 => Flow.mbarInit_1 | .fence => Flow.fenceProxy_0
  | .arrive => Flow.mbarArrive_0 | .bulkA => Flow.bulkCopy_0 | .bulkB => Flow.bulkCopy_1
  | .bar0 _ => Flow.bar_0 | .load _ => Flow.load_0 | .wait0 => Flow.mbarWait_0
  | .mma => Flow.mma_0 | .commit => Flow.tcCommit_0 | .wait1 => Flow.mbarWait_1
  | .fence1 => Flow.tcFence_0 | .ld => Flow.tmemLoad_0 | .waitLd => Flow.tmemWait_0
  | .st j => if j < 4 then Flow.store_0 else Flow.store_1
  | .fenceB => Flow.tcFence_1 | .bar1 => Flow.bar_1 | .fence2 => Flow.tcFence_2
  | .dealloc => Flow.tmemDealloc_0 | .exit => Flow.exit_0

/-- The sub-step of a site inside its instruction: the address store of the allocation, and the
elements of the vector stores. -/
def Site.sub : Site → Nat
  | .allocSt => 1
  | .st j => j % 4
  | _ => 0

/-- An abstract state: the site, the column `c` kept from the address (once read) and the words
`vals` loaded from Tensor Memory (once loaded). -/
structure ThreadD where
  site : Site
  c : Nat
  vals : List Value

/-! ### Register facts -/

/-- The registers thread 0 alone writes, before it issues the copies. -/
def issueRegs : List Nat := [12, 13]

/-- Live registers without thread 0's issue registers. -/
def trimIssue (l : List Nat) : List Nat := l.filter fun r => !issueRegs.contains r

/-- The registers live at a site that the thread holds. -/
def liveAt : Site → List Nat
  | .alloc => trimIssue (Flow.live Flow.tmemAlloc_0)
  | .allocSt => trimIssue (Flow.live Flow.tmemAlloc_0)
  | .bar0 false => trimIssue (Flow.live Flow.bar_0)
  | .load false => trimIssue (Flow.live Flow.load_0)
  | s => Flow.live s.pc

/-- The value of every register a thread uses. -/
def values (L : Launch) (A B D g : Nat) (d : ThreadD) : List (Nat × Value) :=
  [(7, b32 g), (8, b32 (g / 32)), (9, b32 (L.sharedBase + 4352)),
   (10, b32 (L.sharedBase + 4360)), (11, b32 (L.sharedBase + 4368)),
   (1, .pred (decide (g / 32 ≠ 0))), (2, .pred (decide (g ≠ 0))),
   (37, b64 A), (38, b64 B), (39, b64 A), (40, b64 B),
   (12, b32 L.sharedBase), (13, b32 (L.sharedBase + 4096)),
   (14, b32 d.c), (4, .pred (decide (g ≠ 0))), (19, b32 134349984), (30, b32 0),
   (42, b64 (L.sharedBase / 16 + 524288 + 70437463654400)),
   (44, b64 ((L.sharedBase + 4096) / 16 + 524288 + 70437463654400)),
   (21, b32 (taddr g d.c)),
   (22, word d.vals 0), (23, word d.vals 1), (24, word d.vals 2), (25, word d.vals 3),
   (26, word d.vals 4), (27, word d.vals 5), (28, word d.vals 6), (29, word d.vals 7),
   (45, b64 D), (46, b64 D), (47, b64 (D + 32 * g))]

def valueOf (L : Launch) (A B D g : Nat) (d : ThreadD) (r : Nat) : Value :=
  ((values L A B D g d).lookup r).getD (b32 0)

abbrev facts (L : Launch) (A B D g : Nat) (d : ThreadD) : List (Nat × Value) :=
  Flow.factsFrom (liveAt d.site) (valueOf L A B D g d)

/-! ### Transitions -/

/-- The successor after event `e`. A read whose bytes give no column and a store of a word that is
not four bytes stop the machine; nothing follows the exit. -/
def next (g : Nat) (d : ThreadD) (e : Event) : Option (Option ThreadD) :=
  match d.site with
  | .alloc => some (some { d with site := if g = 0 then .allocSt else .bar0 false })
  | .allocSt => some (some { d with site := .init0 })
  | .init0 => some (some { d with site := .init1 })
  | .init1 => some (some { d with site := .fence })
  | .fence => some (some { d with site := .arrive })
  | .arrive => some (some { d with site := .bulkA })
  | .bulkA => some (some { d with site := .bulkB })
  | .bulkB => some (some { d with site := .bar0 true })
  | .bar0 z => some (some { d with site := .load z })
  | .load z => match e.kind with
    | .rd _ bs => (rdCol bs).map fun c => some { d with site := if z then .wait0 else .wait1, c }
    | _ => none
  | .wait0 => match e.kind with
    | .wait _ _ ok _ _ => some (some { d with site := if ok then .mma else .wait0 })
    | _ => none
  | .mma => some (some { d with site := .commit })
  | .commit => some (some { d with site := .wait1 })
  | .wait1 => match e.kind with
    | .wait _ _ ok _ _ => some (some { d with site := if ok then .fence1 else .wait1 })
    | _ => none
  | .fence1 => some (some { d with site := .ld })
  | .ld => match e.kind with
    | .tc (.ld _ vals _) => some (some { d with site := .waitLd, vals })
    | _ => none
  | .waitLd => some (some { d with site := .st 0 })
  | .st j => match e.kind with
    | .wr .. => some (some { d with site := if j < 7 then .st (j + 1) else .fenceB })
    | _ => none
  | .fenceB => some (some { d with site := .bar1 })
  | .bar1 => some (some { d with site := .fence2 })
  | .fence2 => some (some { d with site := if g / 32 = 0 then .dealloc else .exit })
  | .dealloc => some (some { d with site := .exit })
  | .exit => none

/-- The sites only thread 0 reaches. -/
def Site.zero : Site → Bool
  | .allocSt | .init0 | .init1 | .fence | .arrive | .bulkA | .bulkB | .bar0 true | .load true
  | .wait0 | .mma | .commit => true
  | _ => false

/-- What holds of an abstract state: thread 0's sites are thread 0's, the first barrier and the
read without the issue registers are another thread's, warp 0's sites warp 0's, the column is a
16-bit column once read, a store's index is below eight, and the load returned eight words. -/
structure Inv (g : Nat) (d : ThreadD) : Prop where
  zero : d.site.zero = true → g = 0
  nz : (d.site = .bar0 false ∨ d.site = .load false) → g ≠ 0
  warp : (d.site = .alloc ∨ d.site = .dealloc) → g / 32 = 0
  col : d.c < 2 ^ 16
  st : ∀ j, d.site = .st j → j < 8
  vals : (d.site = .waitLd ∨ ∃ j, d.site = .st j) → d.vals.length = 8

/-- The code machine of thread `g`. -/
def code (L : Launch) (A B D g : Nat) : Code kernel [] L g where
  D := ThreadD
  init := { site := if g / 32 = 0 then .alloc else .bar0 false, c := 0, vals := [] }
  pc := fun d => d.site.pc
  facts := facts L A B D g
  sub := fun d => d.site.sub
  inv := Inv g
  next := next g

/-! ### The launch -/

section
variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {g : Nat}

theorem threads_eq (hpre : Pre L A B D a b mem0) : L.threads = 128 := by
  unfold Launch.threads; rw [hpre.grid, hpre.block]

theorem lt_block (hpre : Pre L A B D a b mem0) (hg : g < L.threads) : g < 128 := by
  rw [threads_eq hpre] at hg; exact hg

/-- Every thread is in CTA `0`. -/
theorem cta_zero (hpre : Pre L A B D a b mem0) (hg : g < 128) : g / L.block = 0 := by
  rw [hpre.block]; omega

/-- The launch's clusters are of one CTA. -/
theorem clusterSize_eq (hpre : Pre L A B D a b mem0) : L.clusterSize.val = 1 := by
  have h := hpre.oneDimLaunch
  unfold Launch.oneDimLaunch at h
  rw [hpre.grid] at h
  exact Nat.le_antisymm (Nat.le_of_dvd Nat.one_pos (Nat.dvd_of_mod_eq_zero h.2)) L.clusterSize.pos

end

end

end PTX.Kernels.TcGemm.Proof
