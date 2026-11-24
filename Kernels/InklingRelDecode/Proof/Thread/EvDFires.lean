-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvDBar
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.Code
public import Lemmas.Flow.Facts
public import Lemmas.Flow.Next
public import Lemmas.Flow.Async
public import Lemmas.Flow.MemTmpl
public import Lemmas.Flow.Events
public import Lemmas.Flow.TmemOperands
public import Lemmas.Flow.NotTcData
public import Lemmas.Flow.NotRegister
public import Lemmas.Flow.NotShfl
public import Lemmas.Flow.WaitAcquire
public import Lemmas.Flow.NotObject
public import Lemmas.Flow.Hooks
public import Lemmas.Tensor.TensorMulticast
public import Lemmas.Flow.TensorBox

@[expose] public section

/-!
# Which event an instruction fires, from the values of its operands

General facts about `Fires` for the kinds of event instruction the epilogue and the prologue
use. Each takes the register values of the operands (the facts of the site's abstract state give
them) and returns the event: its kind with the location, the bytes or the operands, and the
instruction's own source position `pc`. They are statements about the instruction semantics, not
about this kernel; the role files instantiate them with the values of the state tables.

* `fires_st_global32`: `st.global.b32 [%rd], %r` writes the four bytes of `storeValue 32` of its
  source at the 64-bit address in `%rd`, which is four-byte aligned;
* `fires_barSync_imm`: `bar.sync id` with an immediate id arrives at barrier `id`, no count;
* `fires_tcLd_at`: `tcgen05.ld` returns one value per destination register, from the address in
  its address register;
* `fires_wait_at`: a poll names the shared location in its address register and the parity in its
  parity register.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.EvD
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {pc : Nat} {e : Event}

/-- `st.global.b32 [%rd base], %r src`, as the decoder gives it. -/
def gstore32 (base src : Nat) : MemAccess :=
  { kind := .store, space := some .global, sem := .weak, scope := none, elem := .int .b 32,
    vec := 1, ext := .same, nc := false, noftz := false,
    hints := { cop := none, l1 := none, l2 := none, prefetch := none, policy := none },
    addr := { base := .reg base 64, off := 0 }, dsts := [], srcs := [.reg src], mmio := false }

/-- **A global 32-bit store writes the bytes of its source at its address.** The address register
holds the 64-bit word `a`, the source register the value `v`; a continuing event is the write of
`storeValue 32 v` to the four bytes at `a`, and `a` is four-byte aligned. -/
theorem fires_st_global32 {base src a : Nat} {v : Value} (hs : t.sub = 0)
    (hr : t.regs base = some (b64 a)) (ha : a < 2 ^ 64) (hv : t.regs src = some v)
    (hf : Fires pc (eventTmpl A L g t (.mem (gstore32 base src))) e (some u)) :
    ∃ v', storeValue 32 v = .ok v' ∧
      e = ⟨pc, .wr { loc := ⟨.global, 0, a⟩, size := 4 } v'.toBytes⟩ ∧ a % 4 = 0 := by
  have hrule : (gstore32 base src).rule = some .threadAccess := by
    unfold gstore32; rfl
  have hloc : (gstore32 base src).locSpace? = some .global := by
    unfold gstore32; rfl
  rw [eventTmpl, memTmpl_store hrule hloc rfl rfl rfl] at hf
  have hw : (gstore32 base src).elem.width = 32 := rfl
  rw [hw] at hf
  by_cases hal : a % 4 = 0
  · have hst := storeTmpl_global (L := L) (g := g) (t := t) (base := base) (src := src) (w := 32)
      (a := a) (v := v) hs hr ha (by omega) (by simpa using hal) hv
    change Fires pc (storeTmpl L g t .global 32 base 0 [.reg src]) e (some u) at hf
    rw [hst] at hf
    rcases hsv : storeValue 32 v with f | v'
    · simp only [hsv] at hf
      exact absurd hf.2 (by simp)
    · simp only [hsv] at hf
      exact ⟨v', rfl, by rw [hf.1], hal⟩
  · exfalso
    change Fires pc (storeTmpl L g t .global 32 base 0 [.reg src]) e (some u) at hf
    have : storeTmpl L g t .global 32 base 0 [.reg src] = .ub .misaligned := by
      unfold storeTmpl
      rw [effAddr_global hr ha]
      simp only [bind, Except.bind, List.length_singleton, hs]
      unfold elemAcc
      simp [hal, throw, throwThe, MonadExceptOf.throw]
    rw [this] at hf
    exact absurd hf.2 (by simp)

/-- **A `bar.sync` on an immediate barrier arrives at it**, without a count. -/
theorem fires_barSync_imm {o : Option TState} {id : Nat} {al : Bool} (hid : id < 16)
    (hf : Fires pc (eventTmpl A L g t (.barSync (.imm id) al)) e o) :
    e = ⟨pc, .bar id none .sync⟩ := by
  have himm : readBits L g t 32 (Opnd.imm (id : Int)) = .ok (BitVec.ofNat 64 id) := by
    simp only [readBits, truncBits]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
    omega
  simp only [eventTmpl, barTmpl, himm, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show id < 2 ^ 64 by omega), show ¬ 16 ≤ id by omega, ↓reduceIte] at hf
  exact hf.1

/-- **A `tcgen05.ld` returns one value per destination**, from the Tensor Memory address its
address register holds (the event's address is that word). -/
theorem fires_tcLd_at {ds : List Nat} {ta n : Nat} {sh : TcShape} {u : TState}
    (hsh : ∀ s, sh ≠ .packed16 s) (hr : t.regs ta = some (b32 n)) (hn : n < 2 ^ 32)
    (hf : Fires pc (eventTmpl A L g t (.tcLd ds ta sh)) e (some u))
    (hw : A.any (·.tcLdWait t.pc) = false) :
    ∃ vals, vals.length = ds.length ∧ e = ⟨pc, .tc (.ld n vals sh)⟩ := by
  rw [eventTmpl_tcLd_noWait hw, tcTmpl_tcLd_none hsh] at hf
  rw [readBits_b32 (L := L) (g := g) hr hn] at hf
  simp only [ofExec, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)] at hf
  split_ifs at hf <;> simp only [Fires] at hf
  all_goals first
    | (simp at hf; done)
    | (obtain ⟨vals, hl, rfl, -⟩ := hf
       exact ⟨vals, hl, rfl⟩)

/-- **A poll names the shared object its address register holds and the parity its parity
operand reads.** Where no assumption widens the scope of the poll, its flags are the
instruction's. -/
theorem fires_wait_at {p base a q : Nat} {par : Opnd} {acq : Bool} {sc : MbarScope} {u : TState}
    (hr : t.regs base = some (b32 a)) (ha : a < 2 ^ 32)
    (hq : readBits L g t 32 par = .ok (BitVec.ofNat 64 q)) (hq32 : q < 2 ^ 32)
    (hA : A.any (·.clusterScopeMbar t.pc) = false)
    (hf : Fires pc (eventTmpl A L g t (.mbarWait p base 0 par acq sc)) e (some u)) :
    ∃ ok, e = ⟨pc, .wait ⟨.shared, g / L.block, a⟩ (q % 2) ok acq sc⟩ := by
  have hq' : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hloc := effAddr_b32 (L := L) (g := g) (t := t) hr ha
  by_cases hal : a % 8 = 0
  · have hm : mbarLoc L g t base 0 = .ok ⟨.shared, g / L.block, a⟩ := by
      simp only [mbarLoc, hloc, bind, Except.bind, hal, ↓reduceIte, pure, Except.pure]
    simp only [eventTmpl, tmaTmpl, hm, hq, hq', bind, Except.bind, pure, Except.pure, ofExec,
      widenMbarScope, hA, Bool.false_eq_true, ↓reduceIte, Fires] at hf
    obtain ⟨ok, he, -⟩ := hf
    exact ⟨ok, he⟩
  · exfalso
    have hm : mbarLoc L g t base 0 = .error .misaligned := by
      simp only [mbarLoc, hloc, bind, Except.bind, hal, ↓reduceIte, throw, throwThe,
        MonadExceptOf.throw]
    simp only [eventTmpl, tmaTmpl, hm, bind, Except.bind, ofExec, widenMbarScope, hA,
      Bool.false_eq_true, ↓reduceIte, Fires] at hf
    exact absurd hf.2 (by simp)

/-- The 32-bit wrap of `x + n` as the address of a shared symbol plus an offset is its residue. -/
theorem wrapAddr32_ofNat (x n : Nat) :
    wrapAddr 32 (BitVec.ofNat 64 x) (n : Int) = (x + n) % 2 ^ 32 := by
  simp only [wrapAddr, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  have h : ((n : Int) % ((2 ^ 64 : Nat) : Int)).toNat = n % 2 ^ 64 := by
    omega
  rw [h]
  omega

/-- **An mbarrier initialization names the object its address register holds, and its count.** -/
theorem fires_mbInit_at {r a n : Nat} {u : TState}
    (hr : t.regs r = some (b32 a)) (ha : a < 2 ^ 32) (hn : 0 < n) (hn' : n < 2 ^ 20)
    (hal : a % 8 = 0)
    (hf : Fires pc (eventTmpl A L g t (.mbarInit r 0 (.imm n))) e (some u)) :
    e = ⟨pc, .mbInit ⟨.shared, g / L.block, a⟩ n⟩ := by
  have hi := tma_mbarInit (L := L) (g := g) (t := t) hr ha hal hn hn'
  simp only [eventTmpl, hi, widenMbarScope] at hf
  split_ifs at hf <;> exact hf.1

/-- **An mbarrier arrival with immediate byte and arrival counts** names the object its address
register holds. Where no assumption widens the scope, the flags are the instruction's. -/
theorem fires_arrive_at {r a tx n : Nat} {rel : Bool} {sc : MbarScope} {u : TState}
    (hr : t.regs r = some (b32 a)) (ha : a < 2 ^ 32) (hal : a % 8 = 0) (htx : tx < 2 ^ 32)
    (hn : n < 2 ^ 32) (hA : A.any (·.clusterScopeMbar t.pc) = false)
    (hf : Fires pc (eventTmpl A L g t (.mbarArrive r 0 (.imm tx) (.imm n) false rel sc none))
      e (some u)) :
    e = ⟨pc, .arrive ⟨.shared, g / L.block, a⟩ tx n rel sc⟩ := by
  have htx' := readBits_imm (L := L) (g := g) (t := t) htx
  have hn' := readBits_imm (L := L) (g := g) (t := t) hn
  have hm := mbarLoc_b32 (L := L) (g := g) (t := t) hr ha hal
  simp only [eventTmpl, tmaTmpl, Bool.false_eq_true, ↓reduceIte, hm, htx', hn', bind,
    Except.bind, pure, Except.pure, ofExec, widenMbarScope, hA, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show tx < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega),
    Fires] at hf
  exact hf.1

/-- **An election with the full member mask** fires an election event of that mask. -/
theorem fires_elect_full {dst : Option Nat} {p : Nat} {ty : Option DType} {u : TState}
    (hf : Fires pc (eventTmpl A L g t
      (.warp ⟨.elect, ty, [dst, some p], [], some (.imm (-1))⟩)) e (some u)) :
    ∃ inst leader, e = ⟨pc, .elect 4294967295 inst leader⟩ := by
  have hm : readBits L g t 32 (Opnd.imm (-1)) = .ok (BitVec.ofNat 64 4294967295) := by
    simp [readBits, truncBits, pure, Except.pure]
  rcases fires_elect_mask hm hf with ⟨inst, leader, he⟩ | ⟨f, he⟩
  · exact ⟨inst, leader, by simpa using he⟩
  · obtain ⟨mk, inst, leader, he', -⟩ := fires_elect hf
    rw [he] at he'
    cases he'

/-- **A `bar.sync 0, 128`** arrives at barrier 0 with count 128, in a block of another size. -/
theorem fires_barSyncN_128 {o : Option TState} {al : Bool} (hb : L.block ≠ 128)
    (hf : Fires pc (eventTmpl A L g t (.barSyncN (.imm 0) (.imm 128) al)) e o) :
    e = ⟨pc, .bar 0 (some 128) .sync⟩ :=
  fires_barSyncN_imm (by decide) (by decide) (by decide) (by decide) (Ne.symm hb) hf

/-- **A proxy fence of the async proxy on shared memory**. -/
theorem fires_fenceProxy_async {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t
      (.fence (.proxy (.async (some (.shared .cta))) none none))) e o) :
    e = ⟨pc, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
  simp only [eventTmpl, fenceTmpl, Option.map_none] at hf
  exact hf.1

/-- An immediate below `2 ^ 32` reads as the 32-bit value it names. -/
theorem readValue_imm32 {n : Nat} (hn : n < 2 ^ 32) :
    readValue L g t 32 (Opnd.imm (n : Int)) = .ok (b32 n) := by
  have himm : readBits L g t 32 (Opnd.imm (n : Int)) = .ok (BitVec.ofNat 64 n) :=
    readBits_imm hn
  simp [readValue, himm, b32, bind, Except.bind, pure, Except.pure]

/-- The footprint of a plain four-byte access at `l`, element `elem` of its vector access. -/
def wordAcc (l : Loc) (elem : Nat := 0) : Acc := { loc := l, size := 4, elem := elem }

/-- `st.shared.v<vec>.b32 [global_smem + off], {srcs}`, as the decoder gives it. -/
def symStore (vec : Nat) (off : Int) (srcs : List Opnd) : MemAccess :=
  { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 32, vec := vec,
    addr := { base := .sharedSym 0, off := off }, srcs := srcs }

theorem symStore_rule {vec : Nat} {off : Int} {srcs : List Opnd} (hl : srcs.length = vec)
    (hv : vec = 1 ∨ vec = 2 ∨ vec = 4) : (symStore vec off srcs).rule = some .threadAccess := by
  unfold symStore
  rcases hv with rfl | rfl | rfl <;> simp [MemAccess.rule, memTypeOk, DType.width, hl]

theorem symStore_loc (vec : Nat) (off : Int) (srcs : List Opnd) :
    (symStore vec off srcs).locSpace? = none := rfl

/-- The instruction at `pc` is the unguarded `st.shared.v<vec>.b32 [global_smem + off], {srcs}`. -/
def isSymStore (pc vec : Nat) (off : Int) (srcs : List Opnd) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .mem a⟩ => decide (a = symStore vec off srcs)
  | _ => false

theorem isSymStore_spec {pc vec : Nat} {off : Int} {srcs : List Opnd}
    (h : isSymStore pc vec off srcs = true) :
    kernel.code[pc]? = some ⟨none, .mem (symStore vec off srcs)⟩ := by
  unfold isSymStore at h
  split at h
  · rename_i a hc
    simp only [decide_eq_true_eq] at h
    subst h
    exact hc
  · cases h

/-- **A store to a shared symbol plus an offset** writes element `j` (the thread's sub-step) of its
vector access: four bytes `storeValue 32` of the element's source, at `sharedBase + off + 4 j`
(modulo `2 ^ 32`) of the thread's CTA. -/
theorem fires_st_sym {vec j : Nat} {off : Int} {srcs : List Opnd} {o : Opnd} {v : Value}
    {u : TState} {op : Op} (hop : op = .mem (symStore vec off srcs)) (hoff : 0 ≤ off)
    (hsub : t.sub = j) (ho : srcs[j]? = some o)
    (hv : readValue L g t 32 o = .ok v)
    (hl : srcs.length = vec) (hvec : vec = 1 ∨ vec = 2 ∨ vec = 4)
    (hf : Fires pc (eventTmpl A L g t op) e (some u)) :
    ∃ v', storeValue 32 v = .ok v' ∧
      e = ⟨pc, .wr (wordAcc ⟨.shared, g / L.block, (L.sharedBase + off.toNat) % 2 ^ 32 + 4 * j⟩ j)
        v'.toBytes⟩ := by
  subst hop
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hoff
  simp only [Int.toNat_natCast]
  have hm : memTmpl A L g t (symStore vec (n : Int) srcs) =
      accessTmpl A L g t (symStore vec (n : Int) srcs) := by
    simp [memTmpl, symStore_rule hl hvec, symStore_loc]
  simp only [eventTmpl] at hf
  change Fires pc (memTmpl A L g t (symStore vec (n : Int) srcs)) e (some u) at hf
  rw [hm] at hf
  simp only [accessTmpl, symStore] at hf
  rw [accessAcc_of_weak rfl] at hf
  have hw : wrapAddr 32 (BitVec.ofNat 64 (L.sharedBase + 0)) (n : Int) =
      (L.sharedBase + 0 + n) % 2 ^ 32 := wrapAddr32_ofNat (L.sharedBase + 0) n
  simp only [accessLoc, pure, Except.pure, bind, Except.bind, hsub, elemAcc, hw] at hf
  simp [DType.width, ho, hv, CacheHints.globalOnly] at hf
  have hv8 : vec ≠ 8 := by rcases hvec with rfl | rfl | rfl <;> decide
  simp only [hv8, ↓reduceIte] at hf
  by_cases hal : (L.sharedBase + n) % 4294967296 % (4 * vec) = 0
  · simp only [hal, ↓reduceIte] at hf
    rcases hsv : storeValue 32 v with f | v'
    · simp only [hsv, Fires] at hf
      exact absurd hf.2 (by simp)
    · simp only [hsv, Fires, Loc.at] at hf
      exact ⟨v', rfl, by rw [hf.1]; rfl⟩
  · simp only [hal, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, Fires] at hf
    exact absurd hf.2 (by simp)

/-- `ld.global.b<w> {%r dst}, [%rd base + 0]`, as the decoder gives it (`w` is 16 or 32). -/
def gload (base dst w : Nat) : MemAccess :=
  { kind := .load, space := some .global, sem := .weak, scope := none, elem := .int .b w,
    vec := 1, ext := .same, nc := false, noftz := false,
    hints := { cop := none, l1 := none, l2 := none, prefetch := none, policy := none },
    addr := { base := .reg base 64, off := 0 }, dsts := [some dst], srcs := [], mmio := false }

/-- The address register of the global load at `pc` (zero if the instruction is not one). -/
def gloadBase (pc : Nat) : Nat :=
  match kernel.code[pc]? with
  | some ⟨_, .mem a⟩ => match a.addr.base with
    | .reg r _ => r
    | _ => 0
  | _ => 0

/-- The destination register of the global load at `pc`. -/
def gloadDst (pc : Nat) : Nat :=
  match kernel.code[pc]? with
  | some ⟨_, .mem a⟩ => match a.dsts with
    | [some d] => d
    | _ => 0
  | _ => 0

/-- The instruction at `pc` is a guarded `ld.global.b<w> {%r dst}, [%rd base + 0]`. -/
def isGload (pc w : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨_, .mem a⟩ => decide (a = gload (gloadBase pc) (gloadDst pc) w)
  | _ => false

theorem isGload_spec {pc w : Nat} (h : isGload pc w = true) :
    ∃ gd, kernel.code[pc]? = some ⟨gd, .mem (gload (gloadBase pc) (gloadDst pc) w)⟩ := by
  unfold isGload at h
  split at h
  · rename_i gd a hc
    simp only [decide_eq_true_eq] at h
    subst h
    exact ⟨gd, hc⟩
  · cases h

/-- **A global load reads the bytes at its address.** The address register holds the 64-bit word
`a`, which is aligned to the load's width (else the load is undefined behaviour); a continuing
event is the read of `w / 8` bytes at `a`. -/
theorem fires_ld_global {base dst a w : Nat} {u : TState} {op : Op}
    (hop : op = .mem (gload base dst w)) (hs : t.sub = 0)
    (hr : t.regs base = some (b64 a)) (ha : a < 2 ^ 64) (hw : w = 16 ∨ w = 32)
    (hf : Fires pc (eventTmpl A L g t op) e (some u)) :
    ∃ bs : List (Option Byte), bs.length = w / 8 ∧
      e = ⟨pc, .rd { loc := ⟨.global, 0, a⟩, size := w / 8 } bs⟩ := by
  subst hop
  have hrule : (gload base dst w).rule = some .threadAccess := by
    unfold gload; rcases hw with rfl | rfl <;> rfl
  have hloc : (gload base dst w).locSpace? = some .global := by
    unfold gload; rfl
  rw [eventTmpl, memTmpl_load hrule hloc rfl rfl rfl] at hf
  have hww : (gload base dst w).elem.width = w := by
    unfold gload; rcases hw with rfl | rfl <;> rfl
  have hreg : (gload base dst w).regs = [dst] := rfl
  have hnc : (gload base dst w).nc = false := rfl
  have hoff : (gload base dst w).addr.off = 0 := rfl
  rw [hww, hreg, hnc, hoff] at hf
  have hw8 : 0 < w / 8 := by rcases hw with rfl | rfl <;> decide
  by_cases hal : a % (w / 8) = 0
  · rw [loadTmpl_global hs hr ha hw8 hal] at hf
    obtain ⟨bs, hl, he, -⟩ := hf
    exact ⟨bs, hl, he⟩
  · exfalso
    have : loadTmpl A L g t .global false w [dst] base 0 = .ub .misaligned := by
      unfold loadTmpl
      rw [effAddr_global hr ha]
      simp only [bind, Except.bind, List.length_singleton, hs]
      unfold elemAcc
      simp [hal, throw, throwThe, MonadExceptOf.throw]
    rw [this] at hf
    exact absurd hf.2 (by simp)

/-- `st.shared.v<vec>.b32 [%r base + 0], {srcs}`, as the decoder gives it. -/
def sstoreV (vec base : Nat) (srcs : List Opnd) : MemAccess :=
  { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 32, vec := vec,
    addr := { base := .reg base 32, off := 0 }, srcs := srcs }

/-- The source register `j` of the memory instruction at `pc` (zero if there is none). -/
def memSrc (pc j : Nat) : Nat :=
  match kernel.code[pc]? with
  | some ⟨_, .mem a⟩ => match a.srcs[j]? with
    | some (.reg r) => r
    | _ => 0
  | _ => 0

/-- The instruction at `pc` is a guarded `st.shared.v4.b32 [%r base + 0], {srcs}` with the base
register and the four source registers the instruction names. -/
def isSstore4 (pc : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨_, .mem a⟩ => decide (a = sstoreV 4 (gloadBase pc)
    [.reg (memSrc pc 0), .reg (memSrc pc 1), .reg (memSrc pc 2), .reg (memSrc pc 3)])
  | _ => false

theorem isSstore4_spec {pc : Nat} (h : isSstore4 pc = true) :
    ∃ gd, kernel.code[pc]? = some ⟨gd, .mem (sstoreV 4 (gloadBase pc)
      [.reg (memSrc pc 0), .reg (memSrc pc 1), .reg (memSrc pc 2), .reg (memSrc pc 3)])⟩ := by
  unfold isSstore4 at h
  split at h
  · rename_i gd a hc
    simp only [decide_eq_true_eq] at h
    subst h
    exact ⟨gd, hc⟩
  · cases h

/-- **A shared store through a 32-bit register** writes element `j` (the thread's sub-step) of its
vector access: four bytes `storeValue 32` of the element's source at `a + 4 j` of the thread's
CTA, where `a` is the address register's value. -/
theorem fires_st_reg {vec base a j : Nat} {srcs : List Opnd} {o : Opnd} {v : Value} {u : TState}
    {op : Op} (hop : op = .mem (sstoreV vec base srcs)) (hsub : t.sub = j)
    (hr : t.regs base = some (b32 a)) (ha : a < 2 ^ 32) (ho : srcs[j]? = some o)
    (hv : readValue L g t 32 o = .ok v) (hl : srcs.length = vec)
    (hvec : vec = 1 ∨ vec = 2 ∨ vec = 4)
    (hf : Fires pc (eventTmpl A L g t op) e (some u)) :
    ∃ v', storeValue 32 v = .ok v' ∧
      e = ⟨pc, .wr (wordAcc ⟨.shared, g / L.block, a + 4 * j⟩ j) v'.toBytes⟩ := by
  subst hop
  have hrule : (sstoreV vec base srcs).rule = some .threadAccess := by
    unfold sstoreV
    rcases hvec with rfl | rfl | rfl <;> simp [MemAccess.rule, memTypeOk, DType.width, hl]
  have hloc : (sstoreV vec base srcs).locSpace? = some .shared := by
    unfold sstoreV; rfl
  rw [eventTmpl, memTmpl_store hrule hloc rfl rfl rfl] at hf
  have hww : (sstoreV vec base srcs).elem.width = 32 := rfl
  have hoff : (sstoreV vec base srcs).addr.off = 0 := rfl
  have hsrc : (sstoreV vec base srcs).srcs = srcs := rfl
  rw [hww, hoff, hsrc] at hf
  change Fires pc (storeTmpl L g t .shared 32 base 0 srcs) e (some u) at hf
  unfold storeTmpl at hf
  rw [effAddr_b32 hr ha] at hf
  simp only [bind, Except.bind, hsub, elemAcc] at hf
  have hv8 : ¬ (32 / 8 = 0) := by decide
  by_cases hal : a % (32 / 8 * srcs.length) = 0
  · simp only [hv8, hal, ne_eq, not_true_eq_false, false_or, ↓reduceIte, pure, Except.pure,
      ho, hv, Loc.at] at hf
    rcases hsv : storeValue 32 v with f | v'
    · simp only [hsv, Fires] at hf
      exact absurd hf.2 (by simp)
    · simp only [hsv, Fires] at hf
      exact ⟨v', rfl, by rw [hf.1]; rfl⟩
  · simp only [hv8, hal, ne_eq, not_false_eq_true, false_or, ↓reduceIte, throw, throwThe,
      MonadExceptOf.throw, Fires] at hf
    exact absurd hf.2 (by simp)

/-- **A tensor load's issue is the copy `tensorLoadCopy` computes**, for any addressing: a
continuing event is one tensor issue of the map at the address the map operand evaluates to and
of the copy the operands give. -/
theorem fires_cpTensor_copy_any {ca grp : Bool} {dst mb : Nat} {off moff : Int} {map : Opnd}
    {cs : List Opnd} {lm : TensorMode} {pol : Option Opnd} {u : TState}
    (hf : Fires pc (eventTmpl A L g t (.cpTensor ca grp dst off map cs mb moff none lm pol)) e
      (some u)) :
    ∃ a s, e = ⟨pc, .tensorIssue a s⟩ ∧
      tensorLoadCopy L g t ca grp dst off map cs mb moff lm = .ok (a, s) := by
  have hf' : Fires pc (tensorTmpl L g t (.cpTensor ca grp dst off map cs mb moff none lm pol)) e
      (some u) := hf
  simp only [tensorTmpl, ofExec, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hf'
  rcases hp : cachePolicyRead L g t pol with f | ⟨⟩ <;> rw [hp] at hf'
  · simp [Fires] at hf'
  · rcases hc : tensorLoadCopy L g t ca grp dst off map cs mb moff lm with f | ⟨a', s'⟩ <;>
      rw [hc] at hf'
    · simp [Fires] at hf'
    · dsimp only at hf'
      split_ifs at hf'
      · obtain ⟨he, -⟩ := hf'
        exact ⟨a', s', he, rfl⟩
      · simp [Fires] at hf'

/-- The coordinates of a tensor load's origin are its coordinate operands' low 32 bits. -/
theorem tensorLoadCopy_origin_all' {ca grp : Bool}
    {dst mb : Nat} {off moff : Int} {map : Opnd} {cs : List Opnd} {lm : TensorMode} {a : Nat}
    {s : TensorCopy.Spec} {vs : List (BitVec 64)}
    (h : tensorLoadCopy L g t ca grp dst off map cs mb moff lm = .ok (a, s))
    (hvs : cs.mapM (readBits L g t 32) = .ok vs) :
    ∀ i : Fin (s.outer + 1), s.origin i = (BitVec.ofNat 32 (vs.getD i.val 0).toNat).toInt := by
  unfold tensorLoadCopy at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    hvs] at h
  rcases hm : tensorMap L g t map cs lm with f | ⟨a', outer, d⟩ <;> rw [hm] at h
  · cases h
  rcases hd : sharedEffAddr L g t ca dst off with f | dl <;> simp only [hd] at h
  · cases h
  all_goals repeat' (split at h <;> (try (cases h; done)))
  all_goals cases h
  all_goals intro i
  all_goals rfl

/-- **A tile tensor load through a CTA address, from registers holding 32-bit words.** The
destination register holds `ad`, the two coordinate registers `vx` and `vy`, the mbarrier
register `am`; a continuing event is one tensor issue whose copy has the box's origin
`(vx, vy)` (as signed 32-bit coordinates), the shared destination `ad` and the barrier `am` of
the thread's own CTA, no cluster addressing, one CTA group, no row coordinates, and the
descriptor the launch publishes at the map's address. -/
theorem fires_cpTensor_tile {dst rx ry mb ad vx vy am : Nat} {map : Opnd} {u : TState}
    (hd : t.regs dst = some (b32 ad)) (hdl : ad < 2 ^ 32)
    (hx : t.regs rx = some (b32 vx)) (hxl : vx < 2 ^ 32)
    (hy : t.regs ry = some (b32 vy)) (hyl : vy < 2 ^ 32)
    (hm : t.regs mb = some (b32 am)) (hml : am < 2 ^ 32)
    (hf : Fires pc (eventTmpl A L g t
      (.cpTensor false false dst 0 map [.reg rx, .reg ry] mb 0 none .tile none)) e (some u)) :
    ∃ a s, e = ⟨pc, .tensorIssue a s⟩ ∧ s.clusterAddress = false ∧ s.group = .one ∧
      s.mbar = ⟨.shared, g / L.block, am⟩ ∧ s.sharedBase = ⟨.shared, g / L.block, ad⟩ ∧
      s.rows = none ∧
      (∀ i : Fin (s.outer + 1), s.origin i = (BitVec.ofNat 32 ([vx, vy].getD i.val 0)).toInt) ∧
      ∃ d, L.tensorMaps a = some ⟨s.outer, d⟩ ∧ s.descriptor = d := by
  obtain ⟨a, s, he, hc⟩ := fires_cpTensor_copy_any hf
  obtain ⟨-, hmb, d, hd', -, hdesc, hrows⟩ := tensorLoadCopy_ok hc
  obtain ⟨hsh, hca, hgrp⟩ := tensorLoadCopy_box hc
  have hsh' : s.sharedBase = ⟨.shared, g / L.block, ad⟩ := by
    have h1 : sharedEffAddr L g t false dst 0 = .ok ⟨.shared, g / L.block, ad⟩ :=
      effAddr_b32 hd hdl
    rw [h1] at hsh
    exact (Except.ok.inj hsh).symm
  have hmb' : s.mbar = ⟨.shared, g / L.block, am⟩ := by
    simp only [Bool.false_eq_true, ↓reduceIte, mbarLoc, effAddr_b32 hm hml, bind, Except.bind,
      pure, Except.pure] at hmb
    split_ifs at hmb with h8
    exact (Except.ok.inj hmb).symm
  have horig := tensorLoadCopy_origin_all' hc (vs := [BitVec.ofNat 64 vx, BitVec.ofNat 64 vy]) (by
    simp only [List.mapM_cons, List.mapM_nil, readBits_b32 hx hxl, readBits_b32 hy hyl, bind,
      Except.bind, pure, Except.pure])
  refine ⟨a, s, he, hca, ?_, hmb', hsh', ?_, ?_, d, hd', ?_⟩
  · simpa using hgrp
  · exact hrows.mpr rfl
  · intro i
    rw [horig i]
    rcases i with ⟨_ | _ | i, hi⟩
    · have e1 : vx % 18446744073709551616 = vx := Nat.mod_eq_of_lt (by omega)
      simp [BitVec.toNat_ofNat, e1]
    · have e1 : vy % 18446744073709551616 = vy := Nat.mod_eq_of_lt (by omega)
      simp [BitVec.toNat_ofNat, e1]
    · simp
  · simpa using hdesc

end

end PTX.Kernels.InklingRelDecode.Proof.EvD
